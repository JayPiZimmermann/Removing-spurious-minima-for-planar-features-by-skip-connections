"""Three compact, TeX-labeled panels reusing the checked zonotope mathematics.

Dependencies: NumPy, Matplotlib, PyCairo (for the legacy mathematical provider),
and LaTeX. Optional raster previews are written only to --preview-dir.
"""
import argparse
import hashlib
import json
from functools import lru_cache
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import Polygon, Patch
from matplotlib.lines import Line2D
from matplotlib.transforms import Bbox
import numpy as np
import generate_zonotope_harmonic as source

ROOT = Path(__file__).resolve().parent
WIDTH = .75
RAW, CENTERED, ODD = "#D55E00", "#AA4499", "#777777"
TRANSLATION = "#000000"
NAMES = ("polytope_translation", "support_functions", "fourier_spectrum")


@lru_cache(maxsize=1)
def checked_data():
    geometry = source.canonical_geometry()
    moments = source.verify_identities(*geometry)
    return geometry, moments


def make_panel(index, grayscale=False):
    plt.rcParams.update({"font.family": "serif", "font.serif": ["Computer Modern Roman"],
                        "text.usetex": True, "font.size": 8,
                        "text.latex.preamble": r"\usepackage{amsmath,amssymb}",
                        "xtick.labelsize": 7.5, "ytick.labelsize": 7.5})
    raw_color = "#777777" if grayscale else RAW
    centered_color = "#333333" if grayscale else CENTERED
    arrow_color = TRANSLATION
    (vectors, tau, raw_polygon, centered_polygon), data = checked_data()
    raw, centered, odd, raw_coeff, centered_coeff = map(np.asarray, data)
    fig = plt.figure(figsize=(2.05, 1.25), facecolor="white")
    ax = fig.add_axes([.33/2.05, .19/1.25, 1.10/2.05, .90/1.25])
    for spine in ax.spines.values():
        spine.set(color="#AAAAAA", linewidth=.55)
    ax.tick_params(length=2, width=.45, colors="#777777", pad=2)
    if index == 0:
        for vertices, color, linestyle in ((raw_polygon, raw_color, "--"),
                                           (centered_polygon, centered_color, "-")):
            ax.add_patch(Polygon(vertices, closed=True, facecolor=color, alpha=.09, lw=0))
            ax.add_patch(Polygon(vertices, closed=True, fill=False, edgecolor=color,
                                 linewidth=WIDTH, linestyle=linestyle, gid="data-outline"))
        for i in (0, 2, 4):
            ax.plot(*zip(centered_polygon[i], raw_polygon[i]), color="#AAAAAA", lw=.4,
                    linestyle=":", zorder=0)
        points = np.array([*raw_polygon, *centered_polygon])
        lo, hi = points.min(axis=0)-.12, points.max(axis=0)+.12
        midpoint = (lo+hi)/2
        y_span = max(hi[1]-lo[1], (hi[0]-lo[0])*.90/1.10)
        span = np.array([y_span*1.10/.90, y_span])
        lo, hi = midpoint-span/2, midpoint+span/2
        ax.set(xlim=(lo[0], hi[0]), ylim=(lo[1], hi[1]), xticks=[], yticks=[])
        # Equal physical scales preserve the actual angles and polygon shape.
        ax.set_aspect("equal", adjustable="box")
        ax.axhline(0, color="#CCCCCC", lw=.45, zorder=0)
        ax.axvline(0, color="#CCCCCC", lw=.45, zorder=0)
        ax.plot([tau[0]], [tau[1]], "o", color=raw_color, ms=2.5)
        ax.plot([0], [0], "o", color=centered_color, ms=2.5)
        ax.annotate("", xy=tau, xytext=(0, 0), gid="translation-arrow", zorder=10,
                    arrowprops=dict(arrowstyle="->", lw=WIDTH, color=arrow_color,
                                    shrinkA=0, shrinkB=0, mutation_scale=7))
        ax.annotate(r"$\tau$", xy=np.array(tau)/2, xytext=(-1.5, 2),
                    textcoords="offset points", fontsize=7, color=arrow_color,
                    ha="right", va="bottom", gid="translation-label", zorder=11)
        handles = [Line2D([], [], color=raw_color, lw=WIDTH, linestyle="--", label=r"$P$"),
                   Line2D([], [], color=centered_color, lw=WIDTH, label=r"$P_c$")]
    elif index == 1:
        angles = np.linspace(0, 2*np.pi, len(raw)+1)
        handles = []
        for values, color, style, label in ((raw, raw_color, "--", r"$f_P$"),
                                           (centered, centered_color, "-", r"$f_{P_c}$"),
                                           (odd, ODD, ":", r"$\langle\tau,u\rangle$")):
            line, = ax.plot(angles, np.r_[values, values[0]], color=color, lw=WIDTH,
                            linestyle=style, label=label, gid="data-curve")
            handles.append(line)
        ax.set(xlim=(0, 2*np.pi), ylim=(min(odd)*1.1, max(raw)*1.08))
        ax.set_xticks([0, np.pi, 2*np.pi], [r"$0$", r"$\pi$", r"$2\pi$"])
        ax.yaxis.set_major_locator(plt.MaxNLocator(nbins=3))
        ax.grid(color="#E6E6E6", linewidth=.3)
    else:
        modes = np.arange(1, source.MAX_FOURIER_MODE+1)
        raw_amplitude = np.linalg.norm(raw_coeff[1:], axis=1)
        centered_amplitude = np.linalg.norm(centered_coeff[1:], axis=1)
        ax.axvspan(.5, 1.5, color=raw_color, alpha=.06, zorder=0)
        ax.bar(modes-.16, raw_amplitude, width=.28, facecolor="white", edgecolor=raw_color,
               linewidth=WIDTH, zorder=3)
        ax.bar(modes+.16, centered_amplitude, width=.28, color=centered_color,
               linewidth=WIDTH, zorder=3)
        ax.plot(1.16, 0, "o", mfc="white", mec=centered_color, mew=WIDTH, ms=3,
                clip_on=False, zorder=4)
        ax.set(xlim=(.5, 8.5), ylim=(0, max(raw_amplitude)*1.12), xticks=[1, 2, 4, 6, 8])
        ax.yaxis.set_major_locator(plt.MaxNLocator(nbins=3))
        ax.grid(axis="y", color="#E6E6E6", linewidth=.3)
        handles = [Patch(facecolor="white", edgecolor=raw_color, linewidth=WIDTH, label=r"$f_P$"),
                   Patch(facecolor=centered_color, label=r"$f_{P_c}$")]
    fig.legend(handles=handles, loc="upper left", bbox_to_anchor=(1.48/2.05, 1.09/1.25),
               frameon=False, fontsize=6.5, handlelength=1.0, handletextpad=.45,
               labelspacing=.8, borderaxespad=0, borderpad=0)
    return fig


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--preview-dir", type=Path)
    args = parser.parse_args()
    checked_data()
    if args.preview_dir:
        args.preview_dir.mkdir(parents=True, exist_ok=True)
    outputs = []
    figures = [make_panel(index) for index in range(3)]
    for fig in figures:
        fig.canvas.draw()
    bounds = [fig.get_tightbbox(fig.canvas.get_renderer()) for fig in figures]
    bottom, top = min(b.y0 for b in bounds)-.02, max(b.y1 for b in bounds)+.02
    crops = [Bbox.from_extents(b.x0-.02, bottom, b.x1+.02, top) for b in bounds]
    for index, (name, fig, crop) in enumerate(zip(NAMES, figures, crops)):
        path = ROOT/f"{name}.pdf"
        fig.savefig(path, bbox_inches=crop, metadata={"CreationDate": None, "ModDate": None, "Title": name})
        outputs.append(path)
        if args.preview_dir:
            fig.savefig(args.preview_dir/f"{name}.png", dpi=250, bbox_inches=crop)
            gray = make_panel(index, grayscale=True)
            gray.savefig(args.preview_dir/f"{name}_grayscale.png", dpi=180, bbox_inches=crop)
            plt.close(gray)
        plt.close(fig)
    record = dict(consumer="paper/main.tex#fig:zonotope-first-harmonic",
                  masses=source.MASSES, direction_degrees=source.DIRECTION_DEGREES,
                  notation="P_c=P-tau; f_K is the support function of K",
                  colors=dict(raw=RAW, centered=CENTERED, translation=TRANSLATION),
                  arrow="From the center of P_c at zero to the center of P at tau; label +tau.",
                  checks="Independent polygon construction, support-function translation, pi periodicity, and discrete Fourier identities in the reused mathematical provider.",
                  scope="Floating-point illustration of exact identities, not a new formal certificate. Geometry uses equal axis scales; spectra are amplitudes of cosine/sine coefficient pairs for modes 1 through 8.",
                  panel_inches=[2.05, 1.25], primary_line_width_pt=WIDTH,
                  exported_panel_inches=[[b.width, b.height] for b in crops],
                  tex_width_fractions=[.99*b.width/sum(c.width for c in crops) for b in crops],
                  sha256={p.name: hashlib.sha256(p.read_bytes()).hexdigest()
                          for p in [Path(__file__), Path(source.__file__), *outputs]})
    (ROOT/"panels.metadata.json").write_text(json.dumps(record, indent=2)+"\n")


if __name__ == "__main__":
    main()
