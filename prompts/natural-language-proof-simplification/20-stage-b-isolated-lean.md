# Module 20: Stage B isolated, replacement-ready Lean alternatives

Stage B begins only for a frozen Stage-A candidate whose synthesis verdict is
`SELECT_FOR_STAGE_B` and whose independent hostile judgment is `SELECT`.  A
different repository-aware formalizer performs this stage.  Stage-A mathematics is
immutable; Lean convenience cannot rewrite it retroactively.

## 1. Isolation and incumbent prohibition

Create a candidate-specific overlay below the campaign root from the frozen
base revision.  Never edit the live or production Lean tree.  Do not change the
paper, annotations, links, claim ledger, generators, or shared build products.

The formalizer may inspect canonical definitions, the exact target type, public API,
and upstream lemmas needed to express the candidate.  It must not inspect, copy,
invoke, import as a proof edge, or derive through the incumbent target proof, an
alias of it, or any downstream theorem equivalent to or stronger than the target.
Before validation, a repository-aware firewall auditor supplies a sanitized API
packet with the incumbent proof body removed.  Any forbidden edge makes the result
`INCUMBENT_CONTAMINATED`, not a candidate simplification.

## 2. Replacement-ready structure

Implement the candidate in the overlay with this interface:

- a strongest useful reusable core when the Stage-A mathematics genuinely supports
  one;
- explicit semantic bridges for any changed representation, chart, normalization,
  topology, or parameterization;
- a thin public adapter with exactly the frozen paper-facing statement, including
  all quantifiers, binder dependencies, hypotheses, constants, and boundary cases;
- direct consumers or small mirror consumers proving the adapter works at the exact
  locations needed by the paper.

Do not manufacture abstraction for a one-use proof.  A shorter wrapper around a
larger dependency cone is not a simplification.  Preserve distinct centered and
noncentered public endpoints, and preserve exact whole-theorem versus child
granularity even when candidates share an internal core.

## 3. Required validation and comparison

All compilation and analysis runs off the interactive machine under Module 30.  For
each candidate require:

- exact-type and elaboration checks for core, bridges, public adapter, and direct
  consumers;
- an absolute transitive axiom audit rejecting `sorryAx`, admissions, and unapproved
  trusted escapes;
- a proof-edge audit demonstrating zero incumbent, alias, downstream-equivalent, or
  circular dependency;
- source-coherent consumer compilation against the frozen overlay;
- direct imports, transitive physical dependencies, decisive mathematical
  dependencies, bridge length, authored proof lines, proof span, and build impact;
- a clause-by-clause comparison with the frozen paper statement and selected
  Stage-A proof; and
- an adversarial independent review of all boundaries and any claimed strengthening.

Compare correctness and strength first, then explanatory value, physical dependency
cone, proof structure, lines, and maintenance burden.  Record `BETTER`, `PARITY`, or
`WORSE_OR_UNVERIFIED`; never weaken the paper to make an alternative pass.

## 4. Candidate package, not integration

Every candidate package contains the overlay source, a forward patch against the
frozen baseline, an exact inverse patch, expected preimages, changed declarations,
public-type manifest, consumer list, validation commands, logs, per-check receipts,
metrics, risks, and adoption order.  The inverse must restore the frozen baseline in
the same isolated overlay.  Preserve the baseline as fallback; do not delete or
replace it.

End with one status:

- `REPLACEMENT_READY`: exact candidate and inverse patches exist and every required
  isolated validation passed;
- `EXPOSITORY_ONLY`: mathematical proof is useful but no Lean replacement is ready;
- `CANDIDATE_FAILED`: precise formal or dependency gate failed;
- `BLOCKED_COMPUTE`: the required off-machine validation could not run.

These statuses are recommendations for a later, separately authorized rebase and
adoption campaign.  They grant no authority to apply a patch, mutate the live Lean
tree, edit the paper, integrate, commit, push, or publish.
