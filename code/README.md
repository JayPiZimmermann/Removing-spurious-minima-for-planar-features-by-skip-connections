# Fixed synthetic experiment

Install and run using the four commands in the repository README. There are no
experiment options. `run.py` trains every model; `tables.py` validates the trial
CSV and regenerates both tables without retraining.

The experiment has 512 paired trials for each of `(m,n,d) = (3,3,2), (3,3,800),
(5,10,2), (5,10,800)`, where `m` is teacher width and `n` is student width.
Every trial trains plain ReLU, joint skip, and profiled skip: 6,144 model runs in total.

## Sampling and objectives

The seed is `202611080064`. Independent NumPy PCG64 streams use
`SeedSequence([seed, m, trial, stream, d, n])`, with trials numbered 0--511.
Teacher streams use zero for `d,n`; the embedding stream uses zero for `n`.
Streams 1--5 respectively generate teacher directions, teacher masses,
the embedding, student directions, and student masses.

Teacher directions are independent normalized Gaussian vectors in two
dimensions; their masses are independent Uniform(0.5,1.5). Each teacher is
shared across dimensions. In dimension 800 it is embedded through the thin QR
factor of an independent 800-by-2 Gaussian matrix, so it remains planar.
Student directions are normalized independent Gaussian vectors in the full
ambient dimension. Student masses are independent Uniform(0.5,1.5), multiplied
by total teacher mass divided by student width. Student initializations are
independent across dimensions and shared exactly across the three models.
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
- **Angular travel per unit:** cumulative spherical distance between successive
  student directions, averaged over units, in radians. This uses oriented
  directions for all three models, even though the centered objective is
  invariant under direction sign changes.

Tables report medians over all 512 trials, including nonfits. These describe
the recorded paths and are not measures of runtime or convergence guarantees.

## Outputs and reproducibility

`results/trials.csv` stores all 6,144 outcomes, the two trajectory quantities,
losses used for fitting, pairing hashes, and optimizer termination metadata.
`results/summary.csv` contains the 12 model/setting summaries. `results/fits.tex`
is the compact four-row fitting table; `results/metrics.tex` is the complete
12-row table. Both are `tabular` fragments requiring LaTeX's `booktabs` package.
`results/manifest.json` records anonymous software versions and source/data
SHA-256 hashes. No machine names, local paths, or personal identifiers are saved.

The reference environment uses Python 3.11.13, NumPy 2.4.6, and SciPy 1.17.1 on
Linux x86-64. Sampling is independent of scheduling and worker count. Exact
floating-point trajectories can depend on CPU/BLAS builds; fixed seeds alone
do not promise bitwise equality across different numerical environments.
Built-in checks verify the objective identities, analytic gradients, embedding,
and trajectory measurements before training. Table generation checks every
expected trial and verifies pairing before reporting results.
