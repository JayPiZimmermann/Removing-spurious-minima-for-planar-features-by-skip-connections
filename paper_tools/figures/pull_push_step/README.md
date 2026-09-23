# The pull, the push, and the step they add up to

## Split panels in main.tex

`generate_panels.py` generates `pull_push_centered.pdf` and
`pull_push_plain.pdf`, included side by side in `main.tex`. The (a)/(b)
subheadings are TeX text, not baked into the images. These panels use the
notation/interlacing blue `#0072B2` and orange `#D55E00`, actual LaTeX labels,
equal canvases/axes, and one shared value range and arrow scale.
The x-axis titles are omitted; TeX subheadings identify the vertical values
as scaled mass rates, 2 pi times the mass velocity. All potential curves and
arrow shafts and vertical guides share the reduced 0.75 pt width. The zero
axis is a single styled gridline. Three-row legends sit outside the upper-right
edge of each plot, with equal short solid samples and 6.8 pt text for P, (-S) and (-F) and
color-matched labels. They use C/R for their
respective panels. S and F are the student potential and residual of the
probe-adjoined configuration evaluated at its probe angle; S includes the
constant self-term, as the caption states. All three function curves are solid; both teacher
and student vertical guides are dashed, as requested by the owner.
The vertical guides extend 5 percent of the plot height above the plot, ending
at the vertical centers of their labels, with
teacher angles beta1/beta2, student angles theta1/theta2 and gamma
beside their tips. The ordinary pi ticks remain unchanged;
there is no extra label row below the plot.
Moving the legends to the side reduces each panel canvas from 2.25 to 1.85
inches high at the same width; both plots retain identical scales and dimensions.
Filled triangular heads have
their apex at the exact shaft endpoint; the orange shaft starts at precisely
the blue apex, without renderer-dependent shortening. Tests check these
coordinates as well as the mathematical vector sums.

There are three independent probe placements: at the two existing student
angles and at 1.6 pi. The origin dots are on y=0; the last angle has a
solid guide. At a student angle the extra probe remains an extra unit, not
the original student: the self term must not be omitted.

For a potential contribution G, each arrow is 0.6 times (G', G) in data
coordinates, i.e. a common rescaling of the unit-mass probe's gradient-flow
contribution (G', G)/(2 pi). The blue arrow and the head-to-tail orange arrow
sum to the black arrow. Height determines mass growth/shrinkage; slope
determines right/left angular motion. Angular pull ascends the teacher
potential; angular push descends the student potential. Horizontal and
vertical axis units are different, so the caption does not equate the
pixel-space arrow angle with an uncalibrated Euclidean velocity ratio.

Generate with `python3 paper_tools/figures/pull_push_step/generate_panels.py`;
test with `python3 -m unittest discover -s paper_tools/figures/pull_push_step
-p 'test_panels.py'`. Dependencies are NumPy, Matplotlib, and LaTeX with
amsmath/amssymb. Optional PNG previews go only to `--preview-dir DIR`.
`panels.metadata.json` records the mathematical inputs, checks, and hashes.
Besides the residual and kernel identities, finite differences of the full
Gaussian Gram loss independently verify all three probe gradients, including
the collisions. These are illustrative gradients, not trajectories or minima.

Validation: all three focused tests pass, both PDFs contain no raster images,
and reruns are byte-identical. The official pdfLaTeX build of `main.tex`
remains 47 pages, with Figure 3 inspected on page 16 and no overfull boxes.
The ten existing unresolved citation warnings are unchanged. The caption is
about 31 percent shorter by whitespace-delimited source tokens (203 to 140),
while retaining its equation and theorem references. Temporary build products
and raster previews are removed after inspection; only the consumed vector
assets and reproducible sources are retained.

## Legacy combined asset

The older `pull_push_step.pdf` and its generator/metadata remain required by
`sections/appendix/figures_intuition.tex` and `build.sh`; they are not unused
build files and are intentionally preserved. The description below refers
to this unchanged legacy asset.

Paper-native appendix figure of the descent-step split of Section 2
(eq. residual-loss-pairing-main): for a hypothetical extra student ("probe")
of mass 1 at every probe angle gamma,

```text
pull_q(gamma) = sum_k s_k Phi_q(gamma - beta_k)                (teacher potential)
push_q(gamma) = -sum_j c_j Phi_q(gamma - theta_j) - Phi_q(0)   (negated student
                                                                potential + self term)
step_q(gamma) = pull_q + push_q = -F_q(gamma)   of the probe-adjoined configuration,
```

drawn for the centered and the plain-ReLU kernel on one shared value scale,
with head-to-tail arrows splitting one scaled descent step into its teacher
and student parts.  The fixed configuration (two unit-mass teachers at
0.2 pi, 0.8 pi; two unit-mass students at 0.38 pi, 1.05 pi) is the website
interactive's canonical default rotated by 0.2 pi so no direction sits on the
plot seam; everything is recomputed here from the paper's closed forms, and
no website asset is imported.

Generate from the repository root with

```sh
python3 paper_tools/figures/pull_push_step/generate_pull_push_step.py
```

Before drawing, the generator asserts the kernel branch formulas,
periodicities, the floor 1 <= Phi_C <= pi/2, the bridge
Phi_R = Phi_C + (pi/2) cos t, Phi_q'(0) = 0 (the self term has zero angular
derivative), the pointwise identity step = pull + push = -(residual of the
probe-adjoined configuration) computed two independent ways, the analytic
kernel slope against finite differences, the kernel-floor bound
pull_C >= 2 against the near-vanishing plain pull, and the exact
head-to-tail arrow sum equal to the scaled negative gradient of
eq. residual-loss-pairing-main.  Output PDF and JSON metadata (source/output
hashes, toolchain, font) are written next to the script; PDF timestamps are
pinned and the surface is restricted to PDF 1.5.

Consumer: `paper/main.tex`
(`fig:pull-push-step`, referenced from Section 2).  Evidence boundary: an
illustrative fixed configuration; every plotted identity is asserted by the
generator, and no claim about minima or dynamics beyond one negative-gradient
step is drawn.
