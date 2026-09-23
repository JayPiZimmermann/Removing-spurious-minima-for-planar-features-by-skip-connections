"""Separate, TeX-labeled pull/push panels for main.tex.

python3 paper_tools/figures/pull_push_step/generate_panels.py
Optional PNG previews: --preview-dir /path/to/temporary/directory.
The original combined asset remains used by the separate main.tex manuscript.
"""
import argparse
import hashlib
import json
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import Polygon
import numpy as np

ROOT = Path(__file__).resolve().parent
TEACHER, STUDENT, INK = "#0072B2", "#D55E00", "#25282D"
DATA_WIDTH = .75
GUIDE_TOP = 1.05
BETA = np.pi * np.array([.2, .8])
THETA = np.pi * np.array([.38, 1.05])
PROBE = 1.6 * np.pi
POSITIONS = (*THETA, PROBE)
STEP_SCALE = .6
VALUE_RANGE = (-7.5, 4.8)


def kernel(x, plain=False):
    x = np.asarray(x)
    c = np.cos(x)
    return c*np.arcsin(np.clip(c, -1, 1)) + np.abs(np.sin(x)) + (np.pi/2*c if plain else 0)


def kernel_slope(x, plain=False):
    x = np.asarray(x)
    return -np.sin(x)*(np.arcsin(np.clip(np.cos(x), -1, 1)) + (np.pi/2 if plain else 0))


def components(gamma, plain=False):
    """Return (teacher, negated-student-and-self, sum), each (slope, value)."""
    pull = np.array([sum(kernel_slope(gamma-b, plain) for b in BETA),
                     sum(kernel(gamma-b, plain) for b in BETA)])
    push = np.array([-sum(kernel_slope(gamma-t, plain) for t in THETA),
                     -sum(kernel(gamma-t, plain) for t in THETA)-kernel(0, plain)])
    return pull, push, pull + push


def residual(probe_angle, probe_mass, evaluation, plain=False):
    """Actual residual of one added probe; source/evaluation are separate."""
    return (sum(kernel(evaluation-t, plain) for t in THETA)
            + probe_mass*kernel(evaluation-probe_angle, plain)
            - sum(kernel(evaluation-b, plain) for b in BETA))


def loss(probe_angle, probe_mass, plain=False):
    """Gaussian half-square loss via its full finite kernel Gram sum."""
    angles = np.array([*THETA, probe_angle, *BETA])
    signed_masses = np.array([1., 1., probe_mass, -1., -1.])
    return np.sum(np.outer(signed_masses, signed_masses)
                  * kernel(angles[:, None]-angles[None, :], plain))/(4*np.pi)


def check_mathematics():
    grid = np.linspace(0, 2*np.pi, 2049)
    assert np.allclose(kernel(grid+np.pi), kernel(grid), atol=1e-12)
    assert np.all(kernel(grid) >= 1-1e-12)
    assert np.allclose(kernel(grid, True)-kernel(grid), np.pi/2*np.cos(grid))
    for plain in (False, True):
        assert abs(kernel_slope(0, plain)) < 1e-14
        parts = components(grid, plain)
        assert np.allclose(parts[2][1], -residual(grid, 1, grid, plain))
        assert all(np.min(p[1]) > VALUE_RANGE[0] and np.max(p[1]) < VALUE_RANGE[1]
                   for p in parts)
        for gamma in POSITIONS:
            pull, push, total = components(gamma, plain)
            assert np.allclose(pull+push, total)
            h = 1e-5
            # Check the *actual loss* gradient, also at a collided probe/student.
            negative_gradient = -np.array([
                (loss(gamma+h, 1, plain)-loss(gamma-h, 1, plain))/(2*h),
                (loss(gamma, 1+h, plain)-loss(gamma, 1-h, plain))/(2*h)])
            assert np.allclose(total/(2*np.pi), negative_gradient, atol=2e-8)
            base = np.array([gamma, 0.])
            for tip in (base+STEP_SCALE*pull, base+STEP_SCALE*total):
                assert 0 < tip[0] < 2*np.pi and VALUE_RANGE[0] < tip[1] < VALUE_RANGE[1]


def exact_arrow(ax, start, end, color):
    """Full shaft and a filled head with its apex exactly at end.

    Construct the head in display points, then map back to data coordinates.
    This avoids arrow-style endpoint retraction and preserves the exact join.
    """
    line, = ax.plot(*np.array([start, end]).T, color=color, lw=DATA_WIDTH,
                    solid_capstyle="butt", zorder=5, gid="step-shaft")
    start_px, end_px = ax.transData.transform([start, end])
    unit = (end_px-start_px)/np.linalg.norm(end_px-start_px)
    normal = np.array([-unit[1], unit[0]])
    points_to_px = ax.figure.dpi/72
    base_px = end_px-3.2*points_to_px*unit
    vertices = ax.transData.inverted().transform([
        end_px, base_px+1.1*points_to_px*normal, base_px-1.1*points_to_px*normal])
    head = Polygon(vertices, closed=True, facecolor=color, edgecolor="none",
                   linewidth=0, zorder=5, gid="step-head")
    ax.add_patch(head)


def make_panel(plain=False, grayscale=False):
    plt.rcParams.update({"font.family": "serif", "font.serif": ["Computer Modern Roman"],
                        "text.usetex": True, "text.latex.preamble": r"\usepackage{amsmath,amssymb}",
                        "font.size": 8, "axes.labelsize": 8, "xtick.labelsize": 7.5,
                        "ytick.labelsize": 7.5, "text.color": INK})
    fig = plt.figure(figsize=(2.75, 1.85), facecolor="white")
    # Reserve a right-hand legend column instead of a separate row above.
    ax = fig.add_axes([.13, .176/1.85, 1.70/2.75, 1.45/1.85])
    ax.set(xlim=(0, 2*np.pi), ylim=VALUE_RANGE)
    ax.set_xticks(np.arange(5)*np.pi/2, [r"$0$", r"$\pi/2$", r"$\pi$", r"$3\pi/2$", r"$2\pi$"])
    ax.set_yticks([-6, -4, -2, 0, 2, 4])
    ax.tick_params(length=2, width=.45, colors="#777777", pad=2)
    for spine in ax.spines.values():
        spine.set(color="#AAAAAA", linewidth=.55)
    ax.grid(color="#E6E6E6", linewidth=.30, zorder=0)
    # Style the existing zero gridline, rather than drawing a second line on it.
    for value, tick in zip(ax.get_yticks(), ax.yaxis.get_major_ticks()):
        if value == 0:
            tick.gridline.set(color="#777777", linewidth=.6, gid="zero-axis")
    blue, orange = ("#666666", "#444444") if grayscale else (TEACHER, STUDENT)
    for angles, symbol, color in ((BETA, r"\beta", blue), (THETA, r"\theta", orange)):
        for index, gamma in enumerate(angles, start=1):
            ax.annotate(rf"${symbol}_{index}$", (gamma, GUIDE_TOP), color=color,
                        xycoords=ax.get_xaxis_transform(), xytext=(2, 0),
                        textcoords="offset points", ha="left", va="center",
                        annotation_clip=False, gid="unit-axis-label")
    ax.annotate(r"$\gamma$", (PROBE, GUIDE_TOP), color=INK,
                xycoords=ax.get_xaxis_transform(), xytext=(2, 0),
                textcoords="offset points", ha="left", va="center",
                annotation_clip=False, gid="probe-axis-label")
    for angles, color in ((BETA, blue), (THETA, orange)):
        for gamma in angles:
            ax.axvline(gamma, ymax=GUIDE_TOP, color=color, lw=DATA_WIDTH,
                       linestyle=(0, (2.6, 1.8)), alpha=.8,
                       clip_on=False, zorder=1, gid="unit-guide")
    ax.axvline(PROBE, ymax=GUIDE_TOP, color="#888888", lw=DATA_WIDTH,
               clip_on=False, zorder=1, gid="probe-guide")
    grid = np.linspace(0, 2*np.pi, 2049)
    values = components(grid, plain)
    curves = []
    model = "R" if plain else "C"
    for part, color, label in zip(values, (blue, orange, INK),
            (rf"$P_{model}$", rf"$(-S_{model})$", rf"$(-F_{model})$")):
        line, = ax.plot(grid, part[1], color=color, lw=DATA_WIDTH, linestyle="-",
                        label=label, zorder=3, gid="potential-curve")
        curves.append(line)
    fig.legend(handles=curves, loc="upper left", bbox_to_anchor=(2.12/2.75, 1.626/1.85),
               ncol=1, frameon=False, fontsize=6.8, handlelength=1.6,
               labelcolor="linecolor", handletextpad=.75, labelspacing=.8,
               borderaxespad=0, borderpad=0)

    for gamma in POSITIONS:
        pull, push, total = [STEP_SCALE*p for p in components(gamma, plain)]
        base = np.array([gamma, 0.])
        teacher_tip = base+pull
        for start, end, color in ((base, teacher_tip, blue),
                                   (teacher_tip, teacher_tip+push, orange),
                                   (base, base+total, INK)):
            exact_arrow(ax, start, end, color)
        ax.plot(gamma, 0, "o", ms=3.2, color=INK, zorder=6, gid="probe-origin")
    return fig


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--preview-dir", type=Path)
    args = parser.parse_args()
    check_mathematics()
    paths = [Path(__file__)]
    if args.preview_dir:
        args.preview_dir.mkdir(parents=True, exist_ok=True)
    for plain, name in ((False, "centered"), (True, "plain")):
        fig = make_panel(plain)
        pdf = ROOT / f"pull_push_{name}.pdf"
        fig.savefig(pdf, metadata={"CreationDate": None, "ModDate": None,
                                  "Title": f"Pull, push, and descent: {name}"})
        paths.append(pdf)
        if args.preview_dir:
            fig.savefig(args.preview_dir / f"pull_push_{name}.png", dpi=250)
            gray = make_panel(plain, grayscale=True)
            gray.savefig(args.preview_dir / f"pull_push_{name}_grayscale.png", dpi=180)
            plt.close(gray)
        plt.close(fig)
    record = dict(consumers=["paper/main.tex#fig:pull-push-step"],
        teacher_angles_over_pi=[.2, .8], student_angles_over_pi=[.38, 1.05],
        masses="All background masses and the single added probe mass equal one.",
        independent_probe_positions_over_pi=[.38, 1.05, 1.6],
        arrow_scale=STEP_SCALE, value_range=VALUE_RANGE,
        primary_line_width_pt=DATA_WIDTH,
        legend="Three rows outside the upper-right plot edge, with equal short solid samples and 6.8 pt labels P, (-S), (-F). Panel-specific C/R. S and F belong to the probe-adjoined configuration evaluated at the probe angle; S includes the self-term Phi(0).",
        arrowheads="Filled triangular heads; apex at the exact shaft endpoint, no retraction.",
        arrow_coordinates="(angle change, mass change), same factor in data coordinates; origins on y=0.",
        checks="Kernel identities, residual identity, exact arrow addition, finite differences of the actual Gaussian loss including at collided probes.",
        evidence="Illustrative single-probe negative gradients, not trajectories or stationary points.",
        invocation="python3 paper_tools/figures/pull_push_step/generate_panels.py",
        sha256={p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in paths})
    (ROOT / "panels.metadata.json").write_text(json.dumps(record, indent=2)+"\n")
    print("Both panels generated; residual and Gaussian-loss gradient checks passed.")


if __name__ == "__main__":
    main()
