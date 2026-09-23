"""Paper-native notation/interlacing figures included in main.tex.

Run: python3 paper_tools/figures/notation_interlacing/generate.py
Exact angle inputs are rational multiples of pi. Floating point is used only
for rendering, not as evidence of stationarity or local minimality.
"""
from pathlib import Path
from fractions import Fraction
import hashlib
import json
import math
import argparse

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import Circle, Arc, Wedge
import numpy as np

ROOT = Path(__file__).resolve().parent
STUDENT, TEACHER = "#D55E00", "#0072B2"
INK, GUIDE = "#25282D", "#A5A7AA"
DATA_WIDTH, GUIDE_WIDTH, AXIS_WIDTH = 1.05, .55, .50
RADIAL_CUTOFF = 1.55
THETA = [Fraction(1, 4), Fraction(7, 12), Fraction(11, 12)]
BETA = [Fraction(1, 12), Fraction(5, 12), Fraction(3, 4)]
MASSES = [Fraction(3, 2), Fraction(4, 5), Fraction(7, 5)]
INTERLACING_THETA = [THETA[0], THETA[1], THETA[2] + 1]
INTERLACING_BETA = [BETA[0], BETA[1] + 1, BETA[2]]


def check_geometry():
    assert len(set(THETA + BETA)) == 6
    assert all(0 <= x < 1 for x in THETA + BETA)
    assert all(s > 0 for s in MASSES)
    # Antipodal direction choices leave the interlacing lines unchanged.
    assert [a % 1 for a in INTERLACING_THETA] == THETA
    assert [a % 1 for a in INTERLACING_BETA] == BETA
    # Includes the cyclic gap across pi, not just the highlighted gap.
    for a, b in zip(THETA, THETA[1:] + [THETA[0] + 1]):
        assert sum(a < x + shift < b for x in BETA for shift in (0, 1)) == 1
    assert BETA[1] > THETA[0] and BETA[1] < THETA[1]
    for angle, mass in zip(THETA, MASSES):
        w = direction(angle)
        assert np.isclose(w @ w, 1)
        assert np.isclose(np.linalg.norm(float(mass) * w), float(mass))
        assert np.allclose(direction(angle + 1), -w)


def direction(angle):
    return np.array([math.cos(float(angle) * math.pi), math.sin(float(angle) * math.pi)])


def arrow(ax, endpoint, color, alpha=1):
    ax.annotate("", xy=endpoint, xytext=(0, 0),
                arrowprops=dict(arrowstyle="->", color=color, lw=DATA_WIDTH,
                                mutation_scale=8, shrinkA=0, shrinkB=0, alpha=alpha),
                zorder=4)


def diameter(ax, v, *, color, width, dashed=False, alpha=1, zorder=1):
    line, = ax.plot(*np.array([-RADIAL_CUTOFF*v, RADIAL_CUTOFF*v]).T,
                    color=color, lw=width, ls=(0, (3, 2)) if dashed else "-",
                    alpha=alpha, zorder=zorder)
    line.set_gid("radial-unit-line" if dashed else "radial-axis")


def base(ax, reference=False):
    ax.set(xlim=(-1.75, 1.75), ylim=(-1.62, 1.85), aspect="equal")
    ax.axis("off")
    ax.add_patch(Circle((0, 0), 1, fill=False, color=GUIDE, lw=GUIDE_WIDTH))
    diameter(ax, np.array([1, 0]), color=INK if reference else "#D0D1D3",
             width=AXIS_WIDTH, zorder=2 if reference else 0)
    diameter(ax, np.array([0, 1]), color="#D0D1D3", width=AXIS_WIDTH, zorder=0)
    ax.plot(0, 0, ".", color=INK, ms=2.5, zorder=6)


def make_figure(panel="student", grayscale=False):
    plt.rcParams.update({"font.family": "serif", "font.serif": ["Computer Modern Roman"],
                        "text.usetex": True,
                        "text.latex.preamble": r"\usepackage{amsmath,amssymb}",
                        "font.size": 8.5,
                        "text.color": INK, "pdf.fonttype": 42,
                        "svg.fonttype": "path", "svg.hashsalt": "notation-interlacing"})
    assert panel in ("student", "interlacing")
    fig = plt.figure(figsize=(2.35 if panel == "student" else 4.1, 2.2), facecolor="white")
    ax = fig.add_axes([.015, .015, .97 if panel == "student" else .535, .97])
    base(ax, reference=True)
    orange = "#555555" if grayscale else STUDENT
    blue = "#555555" if grayscale else TEACHER
    if panel == "interlacing":
        draw_interlacing(fig, ax, orange, blue)
        return fig
    left = ax
    # The horizontal line is the reference cut for angles modulo pi.
    # Darken it without changing line width; its two rays represent one line.
    left.text(1.35, -.19, r"$0\equiv\pi$", color=INK, ha="center")

    # The two other units establish that the highlighted unit belongs to a network.
    for angle, mass in zip([THETA[1] + 1, THETA[2]], MASSES[1:]):
        arrow(left, float(mass) * direction(angle), orange, alpha=.35)
    for angle in THETA[1:]:
        diameter(left, direction(angle), color=orange, width=GUIDE_WIDTH,
                 dashed=True, alpha=.5)
    left.add_patch(Wedge((0, 0), 1.32, 45, 105, width=.19,
                        facecolor="#EEEEEE" if grayscale else "#FBEADC",
                        edgecolor="none", zorder=0))
    left.add_patch(Arc((0, 0), 2.64, 2.64, theta1=45, theta2=105,
                      color=orange, lw=GUIDE_WIDTH))
    left.text(.36, 1.65, "student gap", color=orange, ha="center")
    left.text(.29, 1.37, r"$l_i$", color=orange, ha="center")
    w = direction(THETA[0])
    diameter(left, w, color=orange, width=GUIDE_WIDTH, dashed=True)
    arrow(left, float(MASSES[0]) * w, orange)
    left.plot(*w, "o", color=orange, ms=3.4, zorder=5)
    left.plot(*(-w), "o", color=orange, ms=3.4, zorder=5)
    left.text(.84, .58, r"$w_i=e(\theta_i)$", color=orange, ha="left")
    left.text(1.10, 1.05, r"$s_iw_i$", color=orange, va="center")
    left.text(-.89, -.64, r"$-w_i$", ha="right", color=orange)
    left.text(-1.21, -1.10, r"$\ell(w_i)$", color=orange, ha="right")
    left.text(.94, -.60, r"$\mathbb{S}^{1}$", color="#777777", ha="left")
    left.add_patch(Arc((0, 0), .69, .69, theta1=0, theta2=45,
                       color=INK, lw=GUIDE_WIDTH))
    left.text(.46, .13, r"$\theta_i$", ha="center")
    return fig


def draw_interlacing(fig, right, orange, blue):
    # Only the alternating lines and their chosen unit directions are shown.
    right.text(-1.35, -.19, r"$\pi\equiv0$", color=INK, ha="center")
    for angles, color, symbol in [(INTERLACING_BETA, blue, "v"),
                                  (INTERLACING_THETA, orange, "w")]:
        for i, angle in enumerate(angles):
            v = direction(angle)
            diameter(right, v, color=color, width=GUIDE_WIDTH, dashed=True, alpha=.65)
            arrow(right, v, color)
            # All marks are filled: colors and direct v/w labels encode role, not sign.
            right.plot(*v, "o", color=color, ms=2.5, zorder=5)
            pos = 1.16*v + .15*np.array([-v[1], v[0]])
            right.text(*pos, rf"${symbol}_{i+1}$", color=color,
                       ha="center", va="center")
    # Compact legend beside the drawing; headings belong to LaTeX, not assets.
    fig.text(.575, .65, r"Students: $\Lambda_w=S_+$", color=orange)
    fig.text(.575, .50, r"Teachers: $\Lambda_v=S_-$", color=blue)
    fig.text(.575, .35, "Positive masses; no shared lines", fontsize=8)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--preview-dir", type=Path,
                        help="Optional temporary directory for color/grayscale PNG previews.")
    args = parser.parse_args()
    if args.preview_dir:
        args.preview_dir.mkdir(parents=True, exist_ok=True)
    check_geometry()
    paths = [Path(__file__)]
    for panel in ("student", "interlacing"):
        fig = make_figure(panel)
        stem = "student_notation" if panel == "student" else "strict_interlacing"
        pdf = ROOT / (stem + ".pdf")
        fig.savefig(pdf, metadata={"CreationDate": None, "ModDate": None,
                                  "Title": stem.replace("_", " ")})
        if args.preview_dir:
            fig.savefig(args.preview_dir / (stem + ".png"), dpi=250)
        plt.close(fig)
        if args.preview_dir:
            gray = make_figure(panel, grayscale=True)
            gray.savefig(args.preview_dir / (stem + "_grayscale.png"), dpi=180)
            plt.close(gray)
        paths.append(pdf)
    registry = dict(status="included", consumers=["paper/main.tex#fig:interlacing"],
                    invocation="python3 paper_tools/figures/notation_interlacing/generate.py",
                    teacher_angles_over_pi=[str(a) for a in BETA],
                    student_angles_over_pi=[str(a) for a in THETA],
                    student_masses=[str(s) for s in MASSES],
                    teacher_masses=[1, 1, 1],
                    interlacing_student_directions_over_pi=[str(a) for a in INTERLACING_THETA],
                    interlacing_teacher_directions_over_pi=[str(a) for a in INTERLACING_BETA],
                    radial_cutoff=RADIAL_CUTOFF,
                    evidence_boundary="Illustrative positive, line-separated configuration; no stationarity claim.",
                    rendering="Exact rational inputs, floating-point trigonometric rendering.",
                    sha256={p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in paths})
    (ROOT / "metadata.json").write_text(json.dumps(registry, indent=2) + "\n")
    print("Geometry assertions passed; generated the two paper-native vector PDFs.")


if __name__ == "__main__":
    main()
