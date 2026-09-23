# Unit notation and strict interlacing

Included side by side in `paper/main.tex`, Figure `fig:interlacing`.
The two TeX-generated subheadings sit below the images. Both images use one
common inclusion height, preserving equal unit-circle radii, horizontal-axis
heights, text sizes, and primary stroke widths. The right canvas is wider only
to accommodate its three-line legend.

Reader question: how do mass, direction, angle, and line differ, and how does
strict interlacing order student and teacher lines?

Run `python3 paper_tools/figures/notation_interlacing/generate.py` and
`python3 -m unittest discover -s paper_tools/figures/notation_interlacing -p 'test_*.py'`.
The only generated assets retained are `student_notation.pdf` and
`strict_interlacing.pdf`. Their sizes are 2.35 by 2.2 inches and
4.1 by 2.2 inches. Neither has a baked-in heading: subcaptions belong in TeX.
For temporary raster previews, pass `--preview-dir /path/to/temporary/directory`
to the generator. It does not create unused image formats alongside the PDFs.
`metadata.json` is the local figure registry and records exact inputs, hashes,
invocation, evidence boundary, and manuscript consumer.
Dependencies are NumPy, Matplotlib, LaTeX with amsmath/amssymb, and dvipng
(rendered with Matplotlib 3.10.7). All labels use actual
LaTeX/Computer Modern, not Matplotlib mathtext. The sphere label is outside the circle.

Panel (a) has three student units, with one highlighted to distinguish its
unit direction from its mass-scaled generator. The mass ruler has been removed
at the owner's request. A dark horizontal reference line, labeled only with
the identification zero equivalent to pi, makes the
modulo-pi convention for lines explicit without identifying antipodal directions
as points of the unit circle. Both antipodal unit directions
belong to the same dashed line. All three student lines are drawn, and every line and axis in both
assets is cut at radius 1.55. The third student's mass is 1.4, putting its
arrow tip visibly beyond the unit circle. The middle unit is reversed without changing
its centered feature or its line. The gap between the selected unit and that
line is labeled l_i in the current counterclockwise ordering.
Panel (b) uses those same student lines
with three strictly interlacing teacher lines; v_2 and w_3 are drawn with
antipodal direction representatives. All angle labels, the gap arc, shading,
and the gap-length formula have been removed from this second figure. Its
right-hand legend has exactly three unbroken lines.
The horizontal axis is highlighted in both panels; the interlacing panel places
pi equivalent to zero on its left, mirroring the notation panel's right-hand label.
The identification of the two line sets with the signs of the net mass is specific to positive masses and disjoint
teacher/student lines. It is not a definition of the signs for arbitrary
configurations. No stationarity or minimum claim is made.

Blue/orange follows the owner's instruction and existing manuscript figures.
Role labels v/w make colors redundant; all unit markers are filled, so their
fill does not purport to encode net-mass sign. Other student generators in
panel (a) are muted solely to focus the notation explanation on unit i.
Zonotope polygons are omitted because they are already explained by another
figure and would obscure the distinction between a unit vector and a generator.
Formula rows have been removed; the role legend and its positive-mass,
no-shared-lines qualification sit to the right of the interlacing drawing.

Caption summary (the authoritative caption is in `main.tex`):
“Mass, direction, line, and strict interlacing in the centered model.
(a) One student network: the highlighted unit has mass s_i, unit direction
w_i=e(theta_i), and generator s_i w_i. The directions w_i and -w_i define
the same line ell(w_i). (b) Three student and three teacher lines strictly
interlace: each student gap contains exactly one teacher line. Flipping a
direction preserves its line. Positive masses and disjoint teacher/student
lines give Lambda_w=S_+ and Lambda_v=S_-. The configuration illustrates the
order condition only, not stationarity.”

Validation: five focused tests pass, including exact agreement of both
unit-circle scales and horizontal-axis heights. PDF reruns are byte-identical
and contain no raster images. The official pdfLaTeX build of `main.tex`
succeeds at 47 pages; Figure 4 was inspected on page 21. The ten pre-existing
unresolved citation warnings are unrelated to this integration. TeX labels,
citation groups, and reference targets are preserved. Temporary build and
preview files were removed after inspection; the PDFs regenerate from source.
