# Launcher: whole-paper natural-language proof simplification

Run a fresh, independent proof-discovery campaign for every mathematical result
and proof route in a frozen revision of the paper.  The goal is to find shorter
and more illuminating human proofs and, only for independently selected
candidates, prepare replacement-ready Lean alternatives.  This run does not edit
or integrate the paper or the production Lean tree.

Read and obey these modules in order:

1. [`natural-language-proof-simplification/00-scope-inventory.md`](natural-language-proof-simplification/00-scope-inventory.md)
2. [`natural-language-proof-simplification/10-stage-a-blind-discovery-and-judging.md`](natural-language-proof-simplification/10-stage-a-blind-discovery-and-judging.md)
3. [`natural-language-proof-simplification/20-stage-b-isolated-lean.md`](natural-language-proof-simplification/20-stage-b-isolated-lean.md)
4. [`natural-language-proof-simplification/30-artifacts-and-completion.md`](natural-language-proof-simplification/30-artifacts-and-completion.md)

These files are the complete required prompt suite.  Do not make an untracked,
dated, or historical prompt a required dependency, and do not let an older
prompt authorize live integration.

## Binding run facts

- Record `PAPER_BASE_REV`: the exact committed revision of the paper and formal
  sources this run audits.  Audit only sources reachable at that revision, and
  ignore later live-tree integration except to avoid interfering with it.
- Derive the paper inclusion graph and target inventory dynamically from that
  revision.  Record the expected census (theorem-level environments by kind, the
  labels attached to them, literal Claims, literal Steps, and the explicit-unit
  total) in the run configuration before dispatch, and require an independent
  audit to reproduce it.  A mismatch is `BLOCKED_CENSUS_MISMATCH`, never
  permission to revive an older roster.
- Every complete theorem-level environment is a mandatory, independently solved
  target.  Claims, Steps, material unnamed arrows, coherent multi-step routes,
  and other useful higher-granularity proof spines are additional independent
  targets; they do not replace whole-theorem attempts.
- Where a result has been sharpened or restated, the launcher records the
  current formulation with its exact constants and quantifiers.  Solvers receive
  only that formulation; never dispatch a superseded variant.
- Use maximum useful agent parallelism across whole theorems, substeps, proof
  spines, and independent lenses while retaining coordinator and hostile-judge
  capacity.  Stage A solvers and judges are procedurally blind, not claimed to be
  hermetically isolated.
- All executable checking runs off the interactive machine through the batch
  system, as specified in Module 30.  This campaign does not own the compute
  allocation: never start, stop, resize, or cancel it, and keep at most one
  campaign-owned task in flight so that other work keeps priority.
- On the interactive machine run no Lean, build, TeX, script, symbolic or
  numerical calculation, hashing, or dependency calculation.  If the submission
  route is unavailable, stop compute-dependent work as `HARNESS_UNAVAILABLE`;
  never fall back to local computation.
- Put every run artifact under a fresh campaign root, as specified in Module 30.
  Do not write to production paper or Lean paths.  Do not commit, push, merge,
  rebase, or adopt a proof.  Later rebase and adoption require separate
  authorization from the research lead.

Continue autonomously through inventory, Stage A discovery and hostile judging,
and isolated Stage B validation for every selected candidate.  Emit periodic
coverage, job, blocker, and ETA updates plus the final manifest required by
Module 30.  The strongest successful terminal state for this campaign is
`ADJUDICATION_READY`, never `INTEGRATED`.
