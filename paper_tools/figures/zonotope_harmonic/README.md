# Zonotope translation and the first angular harmonic

## Split panels in main.tex

`generate_panels.py` reuses `canonical_geometry` and `verify_identities` from the
legacy generator below. It writes `polytope_translation.pdf`,
`support_functions.pdf`, `fourier_spectrum.pdf`, and `panels.metadata.json`.
The design canvases are 2.05 by 1.25 inches, with TeX labels and external upper-right
legends; (a)--(c) and axis meanings are supplied by the manuscript. Geometry
uses equal axis scales, and the function/spectrum panels use shorter vertical
plotting scales. The data are unchanged. The centered body is called $P_c$;
the support functions are $f_P$ and $f_{P_c}$. Fourier bars show amplitudes of
the cosine/sine coefficient pairs for positive degrees 1 through 8.
The centered body and its function/spectrum are purple; the raw body remains
orange. A black arrow drawn above the polygons and markers points from the centered body's center
at zero to the raw body's center at $\tau$, with a nearby $\tau$ label.
Exports trim horizontal whitespace while sharing one vertical crop. Proportional
TeX widths fill 99 percent of the text width, leaving 1 percent for inter-panel
gaps. The three panels have equal physical heights and uniform scaling; their
exact export dimensions and width fractions are recorded in the metadata.

Run the generator and `python3 -m unittest discover -s
paper_tools/figures/zonotope_harmonic -p test_panels.py` with NumPy,
Matplotlib, PyCairo and LaTeX installed. `--preview-dir DIR` writes disposable
color/grayscale previews. The checks cover the reused mathematical identities,
undistorted geometry, external legends and consistent data-line widths.
The original combined asset remains consumed by the section-based manuscript.

## Legacy combined figure

This paper-native figure visualizes the exact identity

```text
P = sum_i [0,c_i w_i] = Z+tau,
Z = sum_i [-c_i w_i/2,c_i w_i/2],
tau = (1/2) sum_i c_i w_i,
h_P(u) = h_Z(u)+tau dot u.
```

Generate it from the repository root with

```sh
python3 paper_tools/figures/zonotope_harmonic/generate_zonotope_harmonic.py
```

The generator encodes one fixed collection of positive masses and directions,
asserts the support-function identity on a uniform angular grid, checks the
polygon translation directly, and checks the discrete Fourier coefficients.
It then writes a vector PDF and a JSON record containing the source and output
hashes. PDF timestamps are fixed so the output is reproducible in a fixed
PyCairo environment. The Cairo surface is explicitly restricted to PDF 1.5,
and the generator asserts the emitted `%PDF-1.5` header before recording the
output hash, matching the paper's pdfLaTeX compatibility ceiling.

The renderer also asserts its paper-layout contract: aligned and disjoint data
rectangles, external legends, one width for comparable data marks, lighter named
widths for axes and grids, a final-size 396-point canvas, and a minimum 6.5-point label
size. Raw quantities use long dashes or hollow bars, centered quantities use
solid marks, and the removed odd component is dotted, so the argument remains
readable in grayscale.

The convex-body interpretation requires `c_i >= 0`. The algebraic ReLU parity
identity still makes sense for signed coefficients, but the centered signed sum
is then not generally the support function of a convex zonotope. Translating a
centrally symmetric zonotope removes precisely `tau dot u(theta)`, the degree-one
angular harmonic; it does not remove the constant or even harmonics.
