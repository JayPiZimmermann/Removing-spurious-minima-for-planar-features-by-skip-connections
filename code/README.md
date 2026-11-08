# Fixed synthetic experiment

Install and run using the four commands in the repository README. There are no
experiment options. `run.py` trains every model; `tables.py` validates the trial
CSV and regenerates the grouped tables without retraining.

The experiment uses teacher/student widths `(m,n) = (3,3)` and `(5,10)`.
For each width pair, 512 paired trials use each of three teacher conditions:
random directions in `d=2`, random directions in `d=800`, and the same planar
teachers from `d=2` embedded into `d=800` (labelled `800, emb`). Every trial
trains plain ReLU, joint skip, and profiled skip: 9,216 model runs in total.

## Sampling and objectives

The seed is `202611080064`. Independent NumPy PCG64 streams use
`SeedSequence([seed, m, trial, stream, d, n])`, with trials numbered 0--511.
Streams 1--5 respectively generate planar teacher directions, teacher masses,
the embedding, student directions, and student masses. The first two use
zero for `d,n`; the embedding stream uses zero for `n`. Stream 6 generates
the fully random teacher directions with `d=800,n=0`.

Planar teacher directions are independent normalized Gaussian vectors in two
dimensions. The embedded condition maps the same directions into dimension
800 through the thin QR factor of an independent 800-by-2 Gaussian matrix.
The fully random condition instead draws normalized independent Gaussian
directions directly in dimension 800, giving teacher rank `m` almost surely.
Teacher masses are independent Uniform(0.5,1.5), shared across conditions.
Student directions are normalized independent Gaussian vectors in the full
ambient dimension. Student masses are independent Uniform(0.5,1.5), multiplied
by total teacher mass divided by student width. Student initializations are
independent across dimensions and shared exactly across the three models.
Both dimension-800 teacher conditions also share student initializations.
There is no geometry-based rejection or trial selection.

With Gaussian inputs, all objectives are exact population half-squared losses:

- Plain minimizes the ReLU loss.
- Joint skip trains the ReLU network and a linear skip, initialized at zero.
- Profiled skip minimizes the centered loss with feature `|z|/2`. This is
  exactly the skip loss after analytically minimizing over the linear weights:
  `b = (sum_k teacher_mass_k * v_k - sum_i student_mass_i * w_i)/2`.

## Training and reported quantities

Each model has one L-BFGS-B run, with no restarts or early stopping at the fitting
threshold. Masses are exponentials of parameters bounded to [-30,30]; directions
are normalized unconstrained vectors. The analytic gradients include these
parameterization derivatives. Settings are `maxiter=5000`, `maxfun=10000`,
`maxls=40`, `maxcor=20`, `ftol=0`, `gtol=1e-10`. Arithmetic is float64, with
one BLAS thread per process. Endpoint losses are recomputed in extended
precision; a numerically ambiguous classification stops the run.

A fit means endpoint population loss divided by half the teacher's squared
L2 norm is at most `1e-10`, using the same denominator for every model. This
criterion is independent of the optimizer's termination flag and does not
certify a local minimum. The two trajectory quantities use accepted iterates,
including the initial state:

- **Closest-teacher switches:** sum over students of changes in the index
  maximizing the oriented dot product with a teacher direction. Exact ties use
  the first index; there is no tie margin or small-movement filter.
- **Angular travel per student unit:** cumulative spherical distance between successive
  student directions, averaged over units, in radians. This uses oriented
  directions for all three models, even though the centered objective is
  invariant under direction sign changes.

Tables report medians over all 512 trials, including nonfits. These describe
the recorded paths and are not measures of runtime or convergence guarantees.

## Outputs and reproducibility

`results/trials.csv` stores all 9,216 outcomes, the two trajectory quantities,
losses used for fitting, pairing hashes, and optimizer termination metadata.
`results/summary.csv` contains the 18 model/condition summaries. The generator
writes two table bodies directly into `paper/source/tables/`:
`experiments_main.tex` contains the 12 planar/embedded rows, and
`experiments_appendix.tex` contains all 18 rows. Both group rows by `(m,n)`,
then teacher condition and model. They require LaTeX's `booktabs` and
`multirow` packages; captions and explanatory text belong to
`paper/source/main.tex`.
`results/manifest.json` records anonymous software versions and training-time
source/data SHA-256 hashes. Table generation separately records its current
source and input CSV hashes, so presentation changes retain the training
provenance. Separate training batches are recorded when previously completed
conditions are retained. No machine names, local paths, or personal identifiers
are saved.

The reference environment uses Python 3.11.13, NumPy 2.4.6, and SciPy 1.17.1 on
Linux x86-64. Sampling is independent of scheduling and worker count. Exact
floating-point trajectories can depend on CPU/BLAS builds; fixed seeds alone
do not promise bitwise equality across different numerical environments.
Built-in checks verify the objective identities, analytic gradients, embedding,
and trajectory measurements before training. Table generation checks every
expected trial and verifies pairing before reporting results.
