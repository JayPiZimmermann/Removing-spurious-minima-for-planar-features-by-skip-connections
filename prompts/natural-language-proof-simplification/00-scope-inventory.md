# Module 00: frozen scope, exhaustive inventory, and clean dossiers

## 1. Freeze the exact source

Set `PAPER_BASE_REV` to the exact committed revision this run audits and
materialize a read-only source snapshot below the fresh campaign root.  Use
committed bytes from that object, not `HEAD`, a dirty worktree, an old
annotation, or a directory whose name looks recent.  Record the exact source
paths and commit object used.  Any validation requiring scripting, hashing,
dependency analysis, Lean, TeX, symbolic algebra, or numerical work is a batch
task under Module 30, never a command on the interactive machine.

Resolve the genuine inclusion graph beginning at the manuscript's root source
file.  Inventory included main text and appendices, plus the exact current
paper-facing Lean statements and definitions needed to curate their mathematical
scope.  Historical notes and old campaign artifacts are leads only and cannot
define current scope.

## 2. Dynamic census gate

Derive the inventory from the frozen inclusion graph.  Do not begin solver
dispatch until an independent census audit, run at the same frozen source,
reproduces the expected counts recorded in `RUN_CONFIG.md` for each of:

- theorem environments;
- proposition environments;
- lemma environments;
- corollary environments;
- all theorem-level environments taken together;
- labels attached to those environments;
- literal Claims;
- literal Steps;
- explicit units in total.

Resolve any surplus theorem-level label as an alias attached to an already
counted environment.  Preserve all label-to-semantic-ID edges, but do not
dispatch an alias as another whole theorem.  If any figure differs, stop with
`BLOCKED_CENSUS_MISMATCH`, show the observed category counts and exact offending
spans, and do not substitute an obsolete registry.

Assign stable semantic IDs independent of printed numbers, labels, paths, and
line numbers.  For every explicit unit record its statement, proof ownership,
all aliases, source occurrence, definitions, hypotheses, conclusion, cases,
and parent/child proof relations.

## 3. Mandatory target graph

Create distinct task families:

- `WHOLE`: each complete theorem-level statement, with the entire conclusion as
  one independently solved problem;
- `CLAIM`: each literal Claim;
- `STEP`: each literal Step;
- `ARROW`: every material unnamed implication, case closure, normalization,
  calculation, bridge, or boundary argument whose omission would break a proof;
- `ROUTE`: coherent multi-step or higher-granularity proof routes, including each
  major proof spine and any natural grouping whose joint structure may reveal a
  simpler argument.

`WHOLE` targets are mandatory even when every child has a candidate.  A child
candidate never discharges its parent `WHOLE` cell.  A `WHOLE` candidate never
discharges any `CLAIM`, `STEP`, or `ARROW` cell.  It may inspire a later separately
judged candidate, but no answer or hint crosses the Stage-A firewall.  Record
coverage by `(semantic_id, target_family, lens)` and require one primary owner plus
the planned independent solvers and judges.

A result that has been sharpened or restated gets its own `WHOLE` target and
gives its proof steps their own child targets.  Its dossier must preserve the
exact current constants and quantifiers recorded by the launcher.

## 4. Curator firewall and dossier construction

Only repository-aware curators may inspect frozen paper/Lean sources.  For each
target, one curator reconstructs an exact clause ledger and writes two physically
separate artifacts:

- `private/PROVENANCE.md`: source locators, labels/aliases, exact paper and Lean
  interfaces, equivalence audit, incumbent-proof exposure, and curator notes;
- `stage-a/DOSSIER.md`: the only mathematical payload visible to Stage-A solvers.

The dossier is self-contained ordinary mathematics.  It states all quantifiers,
domains, topology, regularity, signs, widths, dimensions, distinctness,
normalizations, constants, endpoint/wraparound conventions, degenerate cases, and
the exact conclusion.  Introduce the underlying object before coordinates or a
derived scalar: matrix before determinant, measure before integral, perturbation
before quadratic form, and operator/boundary data before special functions.
Use minimal neutral notation and list only genuinely permitted elementary facts.

The dossier contains no proof, proof sketch, proof order, named target, printed
number, paper/project/repository/source path, Lean declaration or syntax, helper
name, import, dependency graph, tactic trace, certificate data, incumbent
mechanism, vulnerability note, or suggested route.  It may ask openly for a
stronger theorem, minimal assumptions, or counterexample without hinting at the
known proof.

A separate dossier auditor sees the private provenance and dossier but does not
solve the target.  It checks clause-for-clause fidelity, self-containment, notation
economy, boundary coverage, object-first exposition, and proof leakage.  Only
`READY_FOR_BLIND_DISPATCH` releases a dossier.  Otherwise revise and re-audit it;
never let a solver repair a malformed statement packet.

Emit `INCLUSION_GRAPH`, `TARGET_INVENTORY`, `ALIAS_MAP`, `PROOF_UNIT_GRAPH`,
`COVERAGE_MATRIX`, `CENSUS_RECEIPT`, curator provenance, clean dossiers, and a
pre-dispatch gate.  All are campaign artifacts, never production edits.
