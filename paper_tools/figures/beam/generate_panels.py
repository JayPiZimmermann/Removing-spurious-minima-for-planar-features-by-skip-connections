"""Residual, one Green function, and angular kernel comparison.

Run with --preview-dir DIR for disposable raster previews. The Newton panel is
an uncertified numerical illustration. The first two panels use the same student
gap; the middle shows one unscaled Green function, not the residual sum.
"""
import argparse
import hashlib
import json
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.lines import Line2D
from matplotlib.transforms import Bbox
import numpy as np

ROOT = Path(__file__).resolve().parent
BLUE, ORANGE, INK = "#0072B2", "#D55E00", "#25282D"
WIDTH = .75
TEACHER_GUIDE = dict(lw=WIDTH, linestyle="--", alpha=.75, zorder=1)
BETA = np.array([0., .5, 1.6, 2.1])
TEACHER_MASSES = np.array([1., .6, .8, 1.2])


def kernel(x, order=0):
    c, s = np.cos(x), np.sin(x)
    a = np.arcsin(np.clip(c, -1, 1))
    return (c*a+np.abs(s), -s*a, -c*a+np.abs(s))[order]


def residual(x, masses, theta, order=0):
    x = np.asarray(x)
    return (kernel(x[..., None]-theta, order) @ masses
            - kernel(x[..., None]-BETA, order) @ TEACHER_MASSES)


def critical_configuration():
    theta = np.array([.5, 1.65, 2.6])

    def equations(angles):
        masses = np.linalg.solve(kernel(angles[:, None]-angles),
                                 kernel(angles[:, None]-BETA) @ TEACHER_MASSES)
        return residual(angles, masses, angles, 1), masses

    for _ in range(50):
        slopes, masses = equations(theta)
        if np.max(np.abs(slopes)) < 1e-13:
            break
        h = 1e-6
        jac = np.column_stack([(equations(theta+h*e)[0]-equations(theta-h*e)[0])/(2*h)
                               for e in np.eye(3)])
        theta -= np.linalg.solve(jac, slopes)
    slopes, masses = equations(theta)
    assert np.max(np.abs(slopes)) < 1e-12
    assert np.max(np.abs(residual(theta, masses, theta))) < 1e-12
    assert np.all(masses > 0)
    assert 0 < theta[0] < theta[1] < theta[2] < np.pi
    assert np.min(np.abs(theta[:, None]-BETA)) > 1e-6
    assert np.count_nonzero((theta[0] < BETA) & (BETA < theta[1])) == 2
    lifted = (BETA-theta[0]) % np.pi + theta[0]
    counts = [np.count_nonzero((a < lifted) & (lifted < b))
              for a, b in zip(theta, np.r_[theta[1:], theta[0]+np.pi])]
    assert counts == [2, 1, 1]
    gaps = np.diff(np.r_[theta, theta[0]+np.pi])
    assert gaps[0] > 1.5*max(gaps[1:])
    return theta, masses


def selected_gap(theta):
    mask = (theta[0] < BETA) & (BETA < theta[1])
    return theta[1]-theta[0], BETA[mask]-theta[0], TEACHER_MASSES[mask]


def basis(z, order=0):
    c, s = np.cos(z), np.sin(z)
    return np.array(((c, s, z*c, z*s),
                     (-s, c, c-z*s, s+z*c),
                     (-c, -s, -2*s-z*c, 2*c-z*s),
                     (s, -c, -3*c+z*s, -3*s-z*c),
                     (c, s, 4*s+z*c, -4*c+z*s))[order])


def green_coefficients(length, source):
    """Independent piecewise-beam solve: four clamps, three matches, one jump."""
    zeros = np.zeros(4)
    rows = [np.r_[basis(0, j), zeros] for j in (0, 1)]
    rows += [np.r_[zeros, basis(length, j)] for j in (0, 1)]
    rows += [np.r_[basis(source, j), -basis(source, j)] for j in range(3)]
    rows += [np.r_[-basis(source, 3), basis(source, 3)]]
    return np.linalg.solve(rows, [0]*7+[1]).reshape(2, 4)


def psi(x):
    return np.sin(x)-x*np.cos(x)


def green(z, length, source):
    """The manuscript's explicit Green formula, eq:green-function."""
    q = length-source
    determinant = length**2-np.sin(length)**2
    chi = lambda x: x*np.sin(x)
    m0 = psi(length)*chi(q)-psi(q)*chi(length)
    a = chi(length)*chi(q)-psi(q)*(np.sin(length)+length*np.cos(length))
    return ((m0*chi(z)-a*psi(z))/(2*determinant)
            + np.where(np.asarray(z) > source, psi(np.asarray(z)-source)/2, 0))


def check_mathematics():
    theta, masses = critical_configuration()
    grid = np.linspace(0, np.pi, 2049)
    values = residual(grid, masses, theta)
    assert np.max(values) < 1e-10
    assert np.all(residual(theta, masses, theta, 2) < 0)
    length, sources, source_masses = selected_gap(theta)
    gap_checks, single_errors, sum_errors = [], [], []
    for source in sources:
        left, right = green_coefficients(length, source)
        for j in (0, 1):
            assert abs(left @ basis(0, j)) < 1e-12
            assert abs(right @ basis(length, j)) < 1e-12
        for j in range(3):
            assert abs((right-left) @ basis(source, j)) < 1e-12
        assert abs((right-left) @ basis(source, 3)-1) < 1e-12
        zs = np.linspace(0, length, 1001)
        solved = np.where(zs <= source, left @ basis(zs), right @ basis(zs))
        explicit = green(zs, length, source)
        single_errors.append(float(np.max(np.abs(solved-explicit))))
        assert np.allclose(solved, explicit, atol=1e-12, rtol=0)
        assert np.min(green(zs[1:-1], length, source)) > 0
        for coeff in (left, right):
            assert np.max(np.abs(coeff @ (basis(zs, 4)+2*basis(zs, 2)+basis(zs)))) < 1e-12
        curvatures = [float(left @ basis(0, 2)), float(right @ basis(length, 2))]
        assert min(curvatures) > 0
        gap_checks.append(curvatures)
    # Independent gap assembly: a beam solve on all three intervals, not only
    # the two already constructed single-source Green functions.
    breaks = np.r_[0, sources, length]
    rows, rhs = [], []
    for interval, endpoint in ((0, 0), (2, length)):
        for order in (0, 1):
            row = np.zeros(12)
            row[4*interval:4*interval+4] = basis(endpoint, order)
            rows.append(row); rhs.append(0)
    for i, source in enumerate(sources):
        for order in range(4):
            row = np.zeros(12)
            row[4*i:4*i+4] = -basis(source, order)
            row[4*i+4:4*i+8] = basis(source, order)
            rows.append(row); rhs.append(4*source_masses[i] if order == 3 else 0)
    coefficients = np.linalg.solve(rows, rhs).reshape(3, 4)
    for i in range(3):
        zs = np.linspace(breaks[i], breaks[i+1], 101)
        total = sum(4*t*green(zs, length, p) for t, p in zip(source_masses, sources))
        solved = coefficients[i] @ basis(zs)
        sum_errors.append(float(np.max(np.abs(solved-total))))
        assert np.allclose(solved, total, atol=1e-11, rtol=0)
    # Most importantly: the dashed contributions reproduce the actual global
    # kernel residual on the selected student gap, not an arbitrary local model.
    zs = np.linspace(0, length, 1001)
    total = sum(-4*t*green(zs, length, p) for t, p in zip(source_masses, sources))
    actual = residual(theta[0]+zs, masses, theta)
    assert np.allclose(actual, total, atol=1e-11, rtol=0)
    return dict(student_angles=theta.tolist(), student_masses=masses.tolist(),
                gap_length=float(length), sources=sources.tolist(), source_masses=source_masses.tolist(),
                teachers_per_student_gap=[2, 1, 1],
                student_gap_lengths=np.diff(np.r_[theta, theta[0]+np.pi]).tolist(),
                stationarity_error=float(max(np.max(np.abs(residual(theta, masses, theta))),
                                             np.max(np.abs(residual(theta, masses, theta, 1))))),
                green_endpoint_curvatures=gap_checks,
                green_formula_max_error=max(single_errors),
                superposition_max_error=max(sum_errors),
                actual_residual_superposition_max_error=float(np.max(np.abs(actual-total))))


def make_panel(gap=False, grayscale=False, angular=False):
    plt.rcParams.update({"font.family": "serif", "font.serif": ["Computer Modern Roman"],
                        "text.usetex": True, "text.latex.preamble": r"\usepackage{amsmath,amssymb}",
                        "font.size": 8, "xtick.labelsize": 7.5, "ytick.labelsize": 7.5})
    blue, orange = ("#666666", "#444444") if grayscale else (BLUE, ORANGE)
    canvas_width = 2.05 if gap or angular else 2.05*38/29
    legend_space = .57 if gap or angular else .67
    plot_width = canvas_width-.48-legend_space
    fig = plt.figure(figsize=(canvas_width, 1.55), facecolor="white")
    ax = fig.add_axes([.45/canvas_width, .19/1.55, plot_width/canvas_width, 1.20/1.55])
    ax.tick_params(length=2, width=.45, colors="#777777", pad=2)
    # Grid lines are drawn as part of the axis, whose z-order overrides the
    # grid Line2D's own z-order. Keep them below the blue source guides,
    # especially where the Green source coincides with the zeta tick.
    ax.set_axisbelow(True)
    for spine in ax.spines.values():
        spine.set(color="#AAAAAA", linewidth=.55)
    ax.grid(color="#E6E6E6", linewidth=.3, zorder=0)
    theta, masses = critical_configuration()
    length, sources, source_masses = selected_gap(theta)
    if angular:
        grid = np.linspace(0, 2*np.pi, 2049)
        ax.set(xlim=(0, 2*np.pi), ylim=(0, 1.05*np.pi))
        ax.set_xticks([0, np.pi, 2*np.pi], [r"$0$", r"$\pi$", r"$2\pi$"])
        ax.set_yticks([0, 1, np.pi/2, np.pi], [r"$0$", r"$1$", r"$\pi/2$", r"$\pi$"])
        ax.axhspan(1, np.pi/2, color="#777777", alpha=.09, zorder=0)
        centered, = ax.plot(grid, kernel(grid), color=blue, lw=WIDTH,
                            label=r"$\Phi_C$", gid="data-curve")
        plain, = ax.plot(grid, kernel(grid)+np.pi/2*np.cos(grid), color=orange,
                         lw=WIDTH, linestyle="--", label=r"$\Phi_R$", gid="data-curve")
        ax.plot(np.pi, 0, "o", mec=orange, mfc="white", mew=WIDTH, ms=3.5,
                clip_on=False)
        handles = [centered, plain]
    elif not gap:
        grid = np.linspace(0, np.pi, 2049)
        values = residual(grid, masses, theta)
        ax.set(xlim=(0, np.pi), ylim=(1.12*np.min(values), 0))
        ax.set_xticks([0, np.pi/2, np.pi], [r"$0$", r"$\pi/2$", r"$\pi$"])
        # Compute tick positions without expanding the nonpositive range.
        ax.yaxis.set_major_locator(plt.MaxNLocator(nbins=3, steps=[1, 2, 5, 10]))
        curve, = ax.plot(grid, values, color=INK, lw=WIDTH, label=r"$F_C$", gid="data-curve")
        ax.axvspan(theta[0], theta[1], color="#777777", alpha=.07, zorder=0)
        zs = np.linspace(0, length, 1001)
        handles = [curve]
        for j, (p, t) in enumerate(zip(sources, source_masses), 1):
            line, = ax.plot(theta[0]+zs, -4*t*green(zs, length, p), color=INK,
                            lw=WIDTH, linestyle=":", label=rf"$G(\cdot,\beta_{j+1})$",
                            gid="data-curve")
            handles.append(line)
        for beta in BETA:
            ax.axvline(beta, color=blue, **TEACHER_GUIDE)
        # A teacher inside the selected gap is marked on its own dotted Green
        # contribution; the others, which have no dotted curve, stay on F_C.
        in_gap = {round(theta[0]+p, 12): -4*t*green(np.array([p]), length, p)[0]
                  for p, t in zip(sources, source_masses)}
        teacher_y = np.array([in_gap.get(round(beta, 12), residual(beta, masses, theta))
                              for beta in BETA])
        teacher, = ax.plot(BETA, teacher_y, "o", color=blue,
                           ms=3.2, clip_on=False, label=r"$\beta_k$")
        student, = ax.plot(theta, np.zeros_like(theta), "o", mec=orange, mfc="white",
                           mew=WIDTH, ms=3.5, clip_on=False, label=r"$\theta_i$")
        handles.extend([
            Line2D([], [], color=blue, lw=WIDTH, linestyle="--", marker="o",
                   markersize=3.2, label=r"$\beta_k$"),
            Line2D([], [], color=orange, linestyle="none", marker="o", mfc="white",
                   markeredgewidth=WIDTH, markersize=3.5, label=r"$\theta_i$")])
    else:
        zs = np.linspace(0, length, 2049)
        source = sources[0]
        values = green(zs, length, source)
        ax.set(xlim=(0, length), ylim=(0, 1.08*np.max(values)))
        ax.set_xticks([0, source, length], [r"$0$", r"$\zeta$", r"$l$"])
        ax.yaxis.set_major_locator(plt.MaxNLocator(nbins=3))
        curve, = ax.plot(zs, values, color=INK, lw=WIDTH, label=r"$G_1$", gid="data-curve")
        handles = [curve]
        ax.axvline(source, color=blue, **TEACHER_GUIDE)
        ax.plot(source, green(source, length, source), "o", color=blue, ms=3.2)
    if not gap:
        fig.legend(handles=handles, loc="upper left", bbox_to_anchor=((canvas_width-legend_space)/canvas_width, 1.39/1.55),
                   ncol=1, frameon=False, fontsize=6.8, handlelength=1.0,
                   handletextpad=.6, labelspacing=.8, borderaxespad=0, borderpad=0)
    return fig


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--preview-dir", type=Path)
    args = parser.parse_args()
    checks = check_mathematics()
    if args.preview_dir:
        args.preview_dir.mkdir(parents=True, exist_ok=True)
    outputs = []
    panels = ((False, False, "planar_residual"), (True, False, "clamped_green"),
              (False, True, "angular_profiles"))
    figures = [make_panel(gap, angular=angular) for gap, angular, _ in panels]
    for fig in figures:
        fig.canvas.draw()
    bounds = [fig.get_tightbbox(fig.canvas.get_renderer()) for fig in figures]
    bottom, top = min(b.y0 for b in bounds)-.02, max(b.y1 for b in bounds)+.02
    crops = [Bbox.from_extents(b.x0-.02, bottom, b.x1+.02, top) for b in bounds]
    for (gap, angular, name), fig, crop in zip(panels, figures, crops):
        path = ROOT / f"{name}.pdf"
        fig.savefig(path, bbox_inches=crop, metadata={"CreationDate": None, "ModDate": None, "Title": name})
        outputs.append(path)
        if args.preview_dir:
            fig.savefig(args.preview_dir / f"{name}.png", dpi=250, bbox_inches=crop)
            gray = make_panel(gap, grayscale=True, angular=angular)
            gray.savefig(args.preview_dir / f"{name}_grayscale.png", dpi=180, bbox_inches=crop)
            plt.close(gray)
        plt.close(fig)
    record = dict(consumer="paper/main.tex#fig:residual-green",
                  teacher_angles=BETA.tolist(), teacher_masses=TEACHER_MASSES.tolist(),
                  checks=checks, primary_line_width_pt=WIDTH,
                  exported_panel_inches=[[b.width, b.height] for b in crops],
                  tex_width_fractions=[.99*b.width/sum(c.width for c in crops) for b in crops],
                  evidence="Uncertified three-student, four-teacher Newton critical configuration. Three cyclic student gaps contain 2, 1, 1 teachers. The wider first gap has teacher masses 0.6 and 0.8; the two narrower gaps have masses 1.2 and 1. Middle: one unscaled Green function on the two-teacher gap. Right: angular kernels.",
                  normalization="Left black dotted curves -4*t_k*G(z;zeta_k) sum to the actual F_C(a+z) inside the selected gap. Legend G(dot,beta_k) identifies each source profile; caption supplies the weights and local-angle shift. Middle shows unscaled G(z;zeta) as unit-teacher-mass reference: mass one contributes -4G, distinct from G's unit operator source. Right: Phi_R(tau)=Phi_C(tau)+(pi/2)*cos(tau).",
                  validation="Single-source jet matching and unit jumps; explicit formula versus 8x8 solve; sum versus independent three-interval 12x12 solve AND actual global kernel residual; sampled signs.",
                  formula_sources={"residual": "paper_lean_formalization/Preliminaries.lean:969 eq_residual_potential_paper",
                                   "green": "paper_lean_formalization/Planar.lean:1415 eq_green_function",
                                   "green_definitions": "paper_lean_formalization/Planar.lean:984-995",
                                   "scope": "Existing Lean identities were inspected for formula/normalization agreement; floating-point rendering and Newton output are not formally certified."},
                  invocation="python3 paper_tools/figures/beam/generate_panels.py",
                  sha256={p.name: hashlib.sha256(p.read_bytes()).hexdigest()
                          for p in [Path(__file__), *outputs]})
    (ROOT / "panels.metadata.json").write_text(json.dumps(record, indent=2)+"\n")
    print(json.dumps(checks))


if __name__ == "__main__":
    main()
