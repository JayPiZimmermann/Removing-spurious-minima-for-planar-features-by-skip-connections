# Paper formalization

This is the official Lean codebase for the ICLR submission 'Removing spurious minima for planar features by skip connections'.

Start with [Overview_theorems.lean](Overview_theorems.lean): it contains the
five theorems we declare as our main contribution, with their proofs. All
project-specific definitions needed to read them are in
[Overview_definitions.lean](Overview_definitions.lean); each proof delegates to
the corresponding statement in [Theorems.lean](Theorems.lean).

| Contribution | Statement in the paper | Theorem in `Overview_theorems.lean` |
| --- | --- | --- |
| Benign loss landscape with linear skips | `thm:headline` | `Main` |
| Spurious minima at arbitrary overparameterization | `thm:plain-trap` | `PlainTrap` |
| Learning the teacher subspace | `prop:teacher-span-confinement` | `Confinement` |
| Effective width | `prop:plain-collision-ceiling` | `EffectiveWidth` |
| Transfer to empirical loss | `thm:fixed-radius-bridge` | `EmpiricalTransfer` |

| File | Contents |
| --- | --- |
| [Overview_theorems.lean](Overview_theorems.lean) | The five contributions with proofs: linear skip exact fit, the plain-ReLU trap, teacher-span confinement, effective width, and empirical transfer. |
| [Overview_definitions.lean](Overview_definitions.lean) | The losses and every definition needed to read the five contributions. |
| [Theorems.lean](Theorems.lean) | The full collection of paper statements, each proved from a chapter. |
| [Definitions.lean](Definitions.lean) | Additional kernels, residuals, and definitions used inside the proofs. |
| [Preliminaries.lean](Preliminaries.lean) | Networks, normalization, Gaussian moments, and loss derivatives. |
| [Skip.lean](Skip.lean) | The relation between linear skip and centered losses. |
| [Beam.lean](Beam.lean) | The beam operator, Green functions, and second variation. |
| [Planar.lean](Planar.lean) | Planar residuals, line counts, interlacing, and collisions. |
| [BentRing.lean](BentRing.lean) | The residual as a bent ring: Love's ring operator, Saint-Venant's squeezed ring, and the loss as bending energy. |
| [Geometry.lean](Geometry.lean) | Teacher-span confinement and the zero-loss results. |
| [Plain.lean](Plain.lean) | The fixed teacher counterexample, splitting, and width bounds. |
| [Empirical.lean](Empirical.lean) | Fixed-radius empirical minima and finite-sample accuracy. |
| [All.lean](All.lean) | Build entry point importing the entire formalization. |
| [EQUATIONS.md](EQUATIONS.md) | Navigation between paper equations and Lean declarations. |
| [verification.json](verification.json) | Exact statement types used by the five-contribution proof audit. |
| [verify.py](verify.py) | Checks the five contribution proofs against `verification.json` and audits their axioms. |
| [scripts/build_certificate.sh](scripts/build_certificate.sh) | Builds the whole development, checks every paper statement, and writes [BUILD_CERTIFICATE.txt](BUILD_CERTIFICATE.txt). |

## Notation in the paper

The definitions and statement index follow our paper: student masses and directions are `s, w`, teacher
masses and directions are `t, v`, and their angles are `θ, β`. Scalar
perturbations use `τ` to avoid confusion with teacher masses.

| Paper | Lean |
| --- | --- |
| Student/teacher linear skip vectors, $b^{\mathbf s}, b^{\mathbf t}$ | `bStudent`, `bTeacher` |
| Features $C, R$ | `.centered`, `.plainRelu` |
| Direction $e(γ)$ | `Angle γ` |
| Matching skip $b_{\mathrm{match}}$ | `MatchingSkip` |
| Average squared input radius $R_2$ | `DataSecondMoment` |
| Joint parameter distance $d_J$ | `JointDistance` |

Lean uses real angles; the effective-width statement counts oriented directions
with period `2π`. The empirical proposition states the deterministic fixed-radius
transfer theorem, with commented definitions for teacher-generated labels and
minimization on the joint parameter ball.

The supporting interlacing and sampling results remain in `Theorems.lean` as
`prop_locamin_are_line_separated`, `rem_finite_data_accuracy`, and
`rem_finite_data_accuracy_high_probability`.
Proof chapters may choose their own local variable names.

## Install and build on Linux

On Ubuntu or Debian, install the prerequisites and Lean's version manager,
[elan](https://lean-lang.org/install/manual/):

```bash
sudo apt update
sudo apt install -y git curl build-essential python3
curl -sSf https://elan.lean-lang.org/elan-init.sh | sh
source "$HOME/.elan/env"
```

Unpack the supplementary archive and run these commands from the repository
root, the directory that contains `lakefile.lean`:

```bash
lake exe cache get
ulimit -s 65536
lake build All
```

The repository's `lean-toolchain` selects **Lean 4.4.0** automatically; Lake uses
the pinned Mathlib dependency. `lake exe cache get` downloads compiled Mathlib
files. The final command compiles every Lean file in this folder and checks the
proofs. A successful build exits with status zero. The project uses the
`lakefile.lean` in the repository root.

To check the five contribution proofs against their recorded full types and
audit their axiom dependencies, run from the same directory:

```bash
python3 verify.py --manifest verification.json
```

## Agent skills

The development was produced with an agentic proof search.  The reusable
agent skills that steered it are included in [skills](skills) so that the
workflow is inspectable: formalization architecture, build discipline,
certificates, Lean and mathematical conventions, research search, and
mathematical exposition.  They are plain Markdown and are not needed to build
or check the formalization.  Project-specific paths, file names, and
identifying details have been removed; what remains is the transferable
instruction content.

## Paper tooling

Everything the manuscript takes from this development is generated, not
transcribed, by the scripts in [paper_tools](paper_tools):

| File | Contents |
| --- | --- |
| [paper_tools/links.json](paper_tools/links.json) | The machine-readable map from paper labels to Lean declarations: every displayed equation and named proof step, and every theorem, proposition, lemma, and remark, addressed by file, namespace, and name. |
| [paper_tools/gen_lean_links.py](paper_tools/gen_lean_links.py) | Regenerates from that map the equation and proof-step hyperlinks of the manuscript, refreshes every in-text pointer's line number from the declaration name, and writes the "Lean Certificates" appendix (the five contributions as Lean source and the statement-to-Lean table). |
| [paper_tools/gen_certificate_constants.py](paper_tools/gen_certificate_constants.py) | Reads the box-certificate literals of the plain-ReLU trap (center, radius, Gram witness, Hessian enclosure, curvature floor, gradient bounds) from `Plain.lean` and writes them as LaTeX macros to [paper_tools/generated/certificate_constants.tex](paper_tools/generated/certificate_constants.tex); `--check` compares them with a manuscript. |
| [paper_tools/figures](paper_tools/figures) | The generators, provenance records, and tests of the four manuscript figures (beam panels, notation and interlacing, pull–push step, zonotope harmonic), each with its own README. |

## Build certificate

[BUILD_CERTIFICATE.txt](BUILD_CERTIFICATE.txt) records one complete run of the
build and the audit.  It states the commit, the working-tree state, the
toolchain from `lean-toolchain`, the `lean` and `lake` versions, the SHA-256 of
the dependency lockfile `lake-manifest.json` and of `lakefile.lean`, and the
exit codes of `lake build All` and of the statement and axiom audit.

What it covers is the whole development, not only the five contributions.
`All.lean` imports every module, and the certificate fails if any module still
contains `sorry`, which Lean reports only as a warning.  It then prints the
transitive axiom dependencies of every paper statement, the 39 statements of
[Theorems.lean](Theorems.lean) and the five contributions of
[Overview_theorems.lean](Overview_theorems.lean), and fails on anything beyond
propositional extensionality, choice and quotient soundness, in particular on
`sorryAx` and `Lean.ofReduceBool`.  For the five contributions the audit also
elaborates each theorem against the exact statement recorded in
`verification.json`, so a proof of a weaker statement cannot pass.  The
certificate is a record of what was checked, not a proof: the trusted evidence
is the Lean source in this repository together with the Lean kernel.

Regenerate it from the repository root with

```bash
./scripts/build_certificate.sh
```

The same script runs in continuous integration on every push
(`.github/workflows/build-certificate.yml`), which builds from a clean
checkout and publishes the certificate as a workflow artifact.

## Read interactively

Install [VS Code](https://code.visualstudio.com/docs/setup/linux), then install
the official [Lean 4 extension](https://github.com/leanprover/vscode-lean4) and
open the repository root:

```bash
code --install-extension leanprover.lean4
code .
```

Open `Overview_theorems.lean` to read the five
theorems and their proofs with mathematical symbols and syntax highlighting.
Hover over names to see their types; press F12 to jump to a definition in
`Overview_definitions.lean` or to the paper statement in `Theorems.lean`, and
use the Lean Infoview to inspect goals and messages.
Lean checks source files; the editor displays them interactively.
