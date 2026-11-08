"""Run the fixed paired teacher--student experiment; no command-line options."""

import os
import sys

# Fix reduction threading before importing the numerical libraries.
for variable in ("OPENBLAS_NUM_THREADS", "OMP_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ[variable] = "1"
sys.dont_write_bytecode = True

from concurrent.futures import ProcessPoolExecutor
import csv
import hashlib
import json
from pathlib import Path
import platform

import numpy as np
import scipy
from scipy.optimize import minimize

import population as pb
from tables import INPUT_FIELDS, MODELS, SETTINGS, TRIAL_COUNT, FIT_THRESHOLD

HERE = Path(__file__).resolve().parent
RESULTS = HERE / "results"
SEED = 202611080064
LOG_MASS_BOUNDS = (-30.0, 30.0)
OPTIMIZER = dict(maxiter=5000, maxfun=10000, maxls=40, maxcor=20, ftol=0.0, gtol=1e-10)


def unit(rows):
    norms = np.linalg.norm(rows, axis=1)
    if np.any(~np.isfinite(norms)) or np.any(norms <= 1e-14):
        raise FloatingPointError("invalid direction parameter")
    return rows / norms[:, None]


def rng(m, trial, stream, d=0, n=0):
    return np.random.default_rng(np.random.SeedSequence([SEED, m, trial, stream, d, n]))


def digest(*arrays):
    h = hashlib.sha256()
    for a in arrays:
        a = np.ascontiguousarray(a, dtype=np.float64)
        h.update(str(a.shape).encode())
        h.update(a.tobytes())
    return h.hexdigest()


def inputs(m, n, d, teacher_geometry, trial):
    s = rng(m, trial, 2).uniform(0.5, 1.5, m)
    if teacher_geometry == "random":
        V = unit(rng(m, trial, 6, d).normal(size=(m, d)))
        latent = V
    else:
        latent = unit(rng(m, trial, 1).normal(size=(m, 2)))
        Q = np.eye(2) if d == 2 else np.linalg.qr(
            rng(m, trial, 3, d).normal(size=(d, 2)), mode="reduced"
        )[0]
        V = unit(latent @ Q.T)
    W = unit(rng(m, trial, 4, d, n).normal(size=(n, d)))
    c = rng(m, trial, 5, d, n).uniform(0.5, 1.5, n) * np.sum(s) / n
    return s, V, c, W, latent


class Objective:
    def __init__(self, model, s, V, n):
        self.model, self.s, self.V, self.n = model, s, V, n
        self.d = V.shape[1]
        self.energy = float(0.5 * s @ pb.Psi(np.clip(V @ V.T, -1, 1)) @ s / (2 * np.pi))

    def decode(self, x):
        c = np.exp(x[:self.n])
        A = x[self.n:self.n + self.n*self.d].reshape(self.n, self.d)
        W = unit(A)
        b = x[-self.d:] if self.model == "joint_skip" else np.zeros(self.d)
        return c, A, W, b

    def __call__(self, x):
        c, A, W, b = self.decode(x)
        if self.model == "plain":
            loss, g = pb.L_R(c, W, self.s, self.V), pb.grad_L_R(c, W, self.s, self.V)
        elif self.model == "joint_skip":
            loss = pb.L_skip(b, c, W, self.s, self.V, np.zeros(self.d))
            g = pb.grad_L_skip(b, c, W, self.s, self.V, np.zeros(self.d))
        else:
            loss, g = pb.L_C(c, W, self.s, self.V), pb.grad_L_C(c, W, self.s, self.V)
        if not np.isfinite(loss) or loss < -1024*np.finfo(float).eps*max(1.0, self.energy):
            raise FloatingPointError("invalid loss")
        grad = [c*g["grad_c"], (g["grad_W_tan"]/np.linalg.norm(A, axis=1)[:, None]).ravel()]
        if self.model == "joint_skip":
            grad.append(g["grad_b"])
        return max(float(loss), 0.0), np.concatenate(grad)


class PathMetrics:
    def __init__(self, objective, x0):
        self.objective = objective
        self.previous = objective.decode(x0)[2].copy()
        self.closest = np.argmax(self.previous @ objective.V.T, axis=1)
        self.swaps = 0
        self.distance = 0.0

    def __call__(self, x):
        W = self.objective.decode(x)[2]
        closest = np.argmax(W @ self.objective.V.T, axis=1)
        self.swaps += int(np.sum(closest != self.closest))
        angles = 2*np.arctan2(
            np.linalg.norm(W-self.previous, axis=1),
            np.linalg.norm(W+self.previous, axis=1),
        )
        self.distance += float(np.mean(angles))
        self.previous, self.closest = W.copy(), closest


def checked_loss(c, W, s, V, b, model):
    """Re-evaluate endpoint loss in extended precision for fit classification."""
    dt = np.longdouble
    if np.finfo(dt).eps >= np.finfo(float).eps:
        raise RuntimeError("extended precision unavailable; use Linux x86_64")
    W, V = W.astype(dt), V.astype(dt)
    W /= np.sqrt(np.sum(W*W, axis=1))[:, None]
    V /= np.sqrt(np.sum(V*V, axis=1))[:, None]
    c, s = c.astype(dt), s.astype(dt)
    U, a = np.concatenate((W, V)), np.concatenate((c, -s))
    rho = np.clip(U @ U.T, -1, 1)
    pi = np.arccos(dt(-1))
    phi = rho*np.arcsin(rho) + np.sqrt(np.maximum(0, 1-rho*rho))
    value = (a @ phi @ a)/(4*pi)
    if model != "profiled_skip":
        odd = b.astype(dt) + (c @ W-s @ V)/2
        value += np.sum(odd*odd)/2
    scale = dt(512)*np.finfo(dt).eps*np.sum(np.abs(a))**2
    if value < -scale or not np.isfinite(value):
        raise FloatingPointError("extended-precision loss inconsistent")
    return float(max(value, 0)), float(scale)


def run_case(case):
    m, n, d, teacher_geometry, trial = case
    s, V, c0, W0, V2 = inputs(*case)
    base = dict(m=m, n=n, d=d, teacher_geometry=teacher_geometry, trial=trial,
                latent_teacher_hash=digest(s, V2), input_hash=digest(s, V, c0, W0))
    records = []
    for model in MODELS:
        objective = Objective(model, s, V, n)
        x0 = np.concatenate((np.log(c0), W0.ravel(),
                             np.zeros(d) if model == "joint_skip" else np.empty(0)))
        path = PathMetrics(objective, x0)
        bounds = [LOG_MASS_BOUNDS]*n + [(None, None)]*(len(x0)-n)
        result = minimize(objective, x0, jac=True, method="L-BFGS-B", bounds=bounds,
                          callback=path, options=OPTIMIZER)
        path(result.x)
        c, _, W, b = objective.decode(result.x)
        loss, uncertainty = checked_loss(c, W, s, V, b, model)
        threshold = FIT_THRESHOLD*objective.energy
        if abs(loss-threshold) <= uncertainty:
            raise FloatingPointError(f"ambiguous fit classification: {case}, {model}")
        records.append(dict(
            base, model=model, fit=int(loss <= threshold), relative_loss=loss/objective.energy,
            closest_teacher_swaps=path.swaps, angular_distance_radians_per_unit=path.distance,
            optimizer_success=int(result.success), optimizer_message=str(result.message),
        ))
    return records


def validate():
    """Check the analytic objectives, gradients, pairing and path measurements."""
    if platform.python_version_tuple()[:2] != ("3", "11"):
        raise RuntimeError("use Python 3.11 with the pinned requirements")
    if (np.__version__, scipy.__version__) != ("2.4.6", "1.17.1"):
        raise RuntimeError("install the pinned requirements before running")
    for m, n in ((3, 3), (5, 10)):
        low = inputs(m, n, 2, "planar", 0)
        high = inputs(m, n, 800, "embedded", 0)
        random_teacher = inputs(m, n, 800, "random", 0)
        assert np.array_equal(high[0], random_teacher[0])
        assert np.array_equal(high[2], random_teacher[2])
        assert np.array_equal(high[3], random_teacher[3])
        assert np.linalg.matrix_rank(random_teacher[1]) == m
        assert digest(low[0], low[4]) == digest(high[0], high[4])
        assert np.allclose(low[1]@low[1].T, high[1]@high[1].T, atol=2e-14, rtol=0)
        assert len({digest(*inputs(m, n, 2, "planar", t)[:2]) for t in range(TRIAL_COUNT)}) == TRIAL_COUNT
        for s, V, c, W, _ in (low, high, random_teacher):
            d = V.shape[1]
            for model in MODELS:
                objective = Objective(model, s, V, n)
                x = np.concatenate((np.log(c), W.ravel(),
                                    np.zeros(d) if model == "joint_skip" else np.empty(0)))
                f, g = objective(x)
                direction = rng(m, 0, 99, d).normal(size=x.size)
                direction /= np.linalg.norm(direction)
                eps = 1e-5
                numerical = (objective(x+eps*direction)[0]-objective(x-eps*direction)[0])/(2*eps)
                assert abs(numerical-g@direction) < 2e-7
                matched = pb.b_match(c, W, s, V, np.zeros(d))
                assert abs(pb.L_skip(matched, c, W, s, V, np.zeros(d))-pb.L_C(c, W, s, V)) < 1e-13
                replay, _ = checked_loss(c, W, s, V, np.zeros(d), model)
                assert abs(f-replay) < 1e-12
                tracking = PathMetrics(objective, x)
                tracking(x)
                assert tracking.swaps == 0 and tracking.distance == 0
    # An exact quarter turn changes the closest teacher once and travels pi/2.
    objective = Objective("plain", np.ones(2), np.eye(2), 1)
    tracking = PathMetrics(objective, np.array([0.0, 1.0, 0.0]))
    tracking(np.array([0.0, 0.0, 1.0]))
    assert tracking.swaps == 1 and abs(tracking.distance-np.pi/2) < 1e-15


def source_hashes():
    return {name: hashlib.sha256((HERE/name).read_bytes()).hexdigest()
            for name in ("run.py", "population.py", "tables.py", "requirements.txt")}


def main():
    if len(sys.argv) != 1:
        raise SystemExit("run.py takes no arguments; the experiment is fixed")
    validate()
    hashes = source_hashes()
    cases = [(*setting, t) for setting in SETTINGS for t in range(TRIAL_COUNT)]
    available = len(os.sched_getaffinity(0)) if hasattr(os, "sched_getaffinity") else (os.cpu_count() or 1)
    workers = min(16, available)
    RESULTS.mkdir(exist_ok=True)
    temporary = RESULTS / "trials.csv.tmp"
    with temporary.open("w", newline="", encoding="utf-8") as stream:
        writer = csv.DictWriter(stream, fieldnames=INPUT_FIELDS)
        writer.writeheader()
        with ProcessPoolExecutor(max_workers=workers) as pool:
            for i, records in enumerate(pool.map(run_case, cases), 1):
                writer.writerows(records)
                stream.flush()
                if i % 32 == 0:
                    print(f"Completed {3*i}/{3*len(cases)} model runs", flush=True)
    if source_hashes() != hashes:
        raise RuntimeError("source changed while the experiment was running")
    temporary.replace(RESULTS / "trials.csv")
    manifest = dict(
        seed=SEED, trials_per_setting=TRIAL_COUNT, model_runs=3*len(cases),
        python=platform.python_version(), numpy=np.__version__, scipy=scipy.__version__,
        architecture=platform.machine(), longdouble_precision_bits=int(np.finfo(np.longdouble).nmant),
        blas_threads=1, optimizer={"method": "L-BFGS-B", **OPTIMIZER},
        log_mass_bounds=LOG_MASS_BOUNDS, fit_relative_tolerance=FIT_THRESHOLD,
        source_sha256=hashes,
        trials_csv_sha256=hashlib.sha256((RESULTS / "trials.csv").read_bytes()).hexdigest(),
    )
    (RESULTS / "manifest.json").write_text(json.dumps(manifest, indent=2)+"\n", encoding="utf-8")
    print("Finished. Run python code/tables.py to regenerate the CSV summary and LaTeX table.", flush=True)


if __name__ == "__main__":
    main()
