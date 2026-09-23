# Module 10: Stage A blind discovery and hostile judging

Stage A seeks genuinely independent natural-language proofs.  It is an
information-firewalled procedure, not a technical claim that agents lack tools.
Every compliant solver and judge is labeled `PROCEDURALLY_BLIND`; never use
`STRICT_BLIND` or `HERMETIC_BLIND` without an external access-control transcript.

## 1. Independent fresh solvers

For every released dossier, launch many fresh, mutually independent solvers that
inherit no conversation context from this campaign.  Each receives only:

1. the sanitized `DOSSIER.md`;
2. a generic instruction to prove or refute the stated problem from first
   principles in natural language; and
3. one neutral lens, when assigned.

The solver must not inspect the repository, paper, Lean, provenance, source paths,
old candidates, other answers, or incumbent proof; it must not run tools or external
search.  A task with any such exposure is `LEGACY_MIXED_CONTEXT`, is quarantined,
and cannot satisfy Stage-A selection.

Fill all useful agent slots after reserving enough capacity for the coordinator,
dossier auditors, and hostile judges.  Parallelize across `WHOLE`, `CLAIM`, `STEP`,
`ARROW`, and `ROUTE` targets and, within important targets, across neutral lenses:

- unrestricted shortest proof;
- symmetry, invariant, or conservation;
- geometric or variational reasoning;
- elementary analysis, ODE, or linear algebra;
- strengthening and assumption removal;
- adversarial counterexample and boundary audit.

Do not split below a coherent mathematical task.  In particular, each `WHOLE`
solver receives the complete theorem dossier and must prove the whole theorem
without being handed child results, child candidates, an incumbent route, or a
preferred lemma sequence.  Solvers may invent and prove their own intermediate
lemmas inside their answer.  Separate child solvers remain independent and cannot
be cited to complete that answer.

Each solver returns:

- a polished proof of the exact statement or a precise refutation/obstruction;
- its central idea in one sentence;
- a line-by-line obligation and boundary-case audit;
- any natural stronger version and the assumptions it removes;
- auxiliary lemmas, identifying which deserve durable names and which should stay
  local;
- the origin of every non-obvious formula;
- definitions, case splits, or computations eliminated relative to the dossier's
  needs, without speculating about the incumbent; and
- one honest status: `SOLVED`, `PARTIAL`, `FALSE`, or `NO_SIMPLER_ROUTE`.

## 2. Hostile candidate judges

Give every solver response to a fresh hostile judge that sees only the same dossier
and that single response.  It sees neither provenance, paper/Lean sources,
incumbent proof, nor other candidates.  The judge checks every quantifier,
hypothesis, sign, constant, normalization, topology, regularity condition, boundary
case, equality case, and claimed strengthening.  It rejects circularity, hidden
compactness or uniqueness, an assumed desired sign, numerical evidence, or a
conditional reduction presented as a proof.

Score lexicographically:

1. correctness and complete closure;
2. exact scope and boundary coverage;
3. illumination and formula provenance;
4. simplicity, proof length, and shallow auxiliary structure;
5. genuinely useful generality;
6. plausible formalizability without concealing a larger argument.

The per-candidate verdict is `SELECT`, `REPAIR`, `PARTIAL_ONLY`, or `REJECT`.
`REPAIR` returns only to the same solver context and must be re-audited by a fresh
judge.  A candidate enters the selected set only with a final `SELECT`.

## 3. Comparative synthesis without leakage

After independent judgments finish, a repository-aware synthesizer may compare
only the `SELECT` candidates for one target.  This happens after invention and does
not retroactively change blindness.  Preserve mathematically distinct routes and
all minority objections.  Do not choose by vote or prose brevity.

Record one or more selected routes when they differ materially, the strongest exact
formulation, the shortest complete applied proof, reusable cores, remaining
load-bearing calculations, and a recommendation:

- `SELECT_FOR_STAGE_B` for a credible formal replacement;
- `EXPOSITORY_ONLY` for a human-proof improvement not expected to help Lean;
- `KEEP_BASELINE` when no candidate is safer or simpler;
- `OPEN` for a precise missing lemma;
- `FALSE_TARGET_OR_SCOPE_DEFECT` for curator/adjudication review.

Selection remains target-specific.  A selected `WHOLE` route cannot fill a child
coverage cell and selected children cannot assemble into a `WHOLE` success unless a
new independent whole-theorem solver produces and receives judgment on that complete
proof.  Keep every prompt, response, judgment, repair cycle, and lifecycle manifest
physically separate.  Unknown agent/timing fields remain `unknown`; never infer them
from file timestamps or narrative clues.
