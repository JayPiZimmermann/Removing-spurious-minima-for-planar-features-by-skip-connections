# Residual field and clamped beam Green function

## Split panels in main.tex

`generate_panels.py` writes `planar_residual.pdf`, `clamped_green.pdf`,
`angular_profiles.pdf`, and `panels.metadata.json`. These are the three panels used after the gap lemma
in `main.tex`, with TeX subheadings, no x-axis titles, and external
upper-right legends in the first and third panels. The Green panel has no legend
and labels its source simply $\zeta$. The left plot omits positive y-values; the middle omits
negative values and plots **one unscaled Green function**. The third panel contains
only the angular kernels, with an external right legend; angle difference is
explained in the TeX description, not an axis heading. All use the established
blue/orange colors and uniform 0.75 pt curves.

The wider left plot uses an uncertified three-student Newton critical configuration
for four teachers at angles 0, 0.5, 1.6 and 2.1 with masses 1, 0.6, 0.8 and 1.2.
The student angles are about 0.304972, 1.827344 and 2.658465, with positive masses
about 1.284899, 1.675115 and 0.632855. Its three cyclic gaps contain 2, 1 and 1 teachers.
The shaded first gap has length about 1.522372 and contains the teachers of masses
0.6 and 0.8 at 0.5 and 1.6; the two other gaps have lengths about 0.831121 and
0.788099 and contain teachers of masses 1.2 and 1. The black dotted contributions
$-2.4G(z;\zeta_1)$ and $-3.2G(z;\zeta_2)$ are drawn on the shaded gap and sum
to its actual kernel residual. This is underparameterized, not strictly
interlacing. The middle plot shows only $G(z;\zeta_1)$ on the same gap,
without a mass factor, factor four, or second source. It is the unit-teacher-mass
reference: mass one contributes $-4G_1$, whereas the first teacher in the highlighted
gap has mass 0.6. Only the blue source marker remains; its dashed guide uses the
same style and width as the left panel's teacher guides. The full numerical
configuration and local gap coordinates remain in the metadata.
The axes/grid layer stays below the guides, including the grid line at the
Green source tick; otherwise it masks the blue dashes. A regression test checks
both guide styles and their drawing order relative to the axes.
Exports trim unused horizontal margins and share one vertical crop. The TeX
panel widths follow the exported aspect ratios, occupying 99 percent of the
text width with the remaining 1 percent split between the panels. Equal physical
image and plot heights are preserved within the row; all panels use one scale.
The metadata records the exact export dimensions and TeX width fractions.
Both contributions and their legend swatches use the same black dotted style.
The legend labels $G(\cdot,\beta_2)$ and $G(\cdot,\beta_3)$ identify source profiles
by absolute teacher angles; the caption explicitly records the factors $-4t_k$
and the shift to local gap coordinates for the actual plotted contributions.
Separate legend entries retain the filled blue teacher marker/dashed guide and
the hollow orange student marker.

Formula checks: the renderer implements `eq_green_function` in
`paper_lean_formalization/Planar.lean` and `eq_residual_potential_paper` in
`Preliminaries.lean`, inspected for signs and normalization. Numerical checks
compare the Green formula with an independent 8-by-8 piecewise-beam solve,
verify the clamps, second-order continuity, third-derivative unit jump,
beam equation, sampled positivity and positive endpoint curvatures. A separate
12-by-12, three-interval solve checks the two-source sum, which is also checked
against the actual global kernel residual on the selected gap. These are floating-point
rendering checks, not a formal certificate of Newton convergence or pixels.

Run `python3 paper_tools/figures/beam/generate_panels.py` and
`python3 -m unittest discover -s paper_tools/figures/beam -p test_panels.py`.
Dependencies: NumPy, Matplotlib, and LaTeX (amsmath/amssymb).
Optional `--preview-dir DIR` produces disposable color/grayscale PNGs.

Validation: four tests check the layout, guide rendering order, angular kernel identities, and Green
formulas; formula/solve discrepancies are below 1e-14 and
the actual residual/superposition discrepancy is below 3e-13 for the plotted
data. PDF reruns are byte-identical and contain no raster images.
The combined placement is immediately after the gap lemma. The legacy combined
kernel figure is no longer included in `main.tex`, but remains an input of
the separate section-based manuscript and is preserved for that consumer.
The integrated three-panel layout was inspected on page 16. The official
pdfLaTeX build has 46 pages, no overfull boxes, and the same ten pre-existing
unresolved citation warnings.

## Legacy combined figure

The original combined PDF and generator below remain used by
`sections/appendix/figures_intuition.tex` and `build.sh` and are preserved.

Paper-native appendix figure.  Panel (a) is the centered residual
F_C(gamma) = sum_i c_i Phi_C(gamma-theta_i) - sum_k s_k Phi_C(gamma-beta_k) on one
projective period for the teacher lines (0, 1.1, 2.0) with unit masses and the
clean, positive, strictly interlaced centered-critical width-three student that the
generator recomputes by Newton's method (student lines about 0.4263, 1.5620, 2.6847
with masses about 0.884, 1.299, 0.807; centered loss about 5.65e-3).  Panel (b) is
the clamped Green function G_l(p,z) of (D^2+1)^2 on a gap of length l = 2 with unit
point load at p = 0.7, obtained from the two-piece resonant solve.

Generate from the repository root with

```sh
python3 paper_tools/figures/beam/generate_residual_and_green.py
```

The generator asserts: every student is a double zero of F_C; all masses are
positive; the six lines are distinct and strictly interlace; the centered loss is
positive; G and G' vanish at both ends, G, G', G'' are continuous at p, G''' jumps by
exactly 1 at p, (D^2+1)^2 G = 0 on each piece, G > 0 inside the gap, and both end
curvatures are positive.  Output PDF and JSON metadata are written next to the
script; PDF timestamps are pinned and the surface is restricted to PDF 1.5.  No
website asset is imported.
