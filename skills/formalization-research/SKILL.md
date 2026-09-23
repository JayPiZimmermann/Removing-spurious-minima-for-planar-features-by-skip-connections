---
name: formalization-research
description: Explore open mathematical claims in a Lean project through falsification, reproducible experiments, proof-route comparison, and durable evidence. Use for deciding what to try next, not routine compilation.
---

# Turn exploration into a precise result or residual

Start with one exact claim, its place in the theorem dependency graph, the intended Lean declaration, and the cheapest test that could falsify it.

## Separate evidence states

- **Measured:** a sampled or floating-point observation within the instrument's validity range.
- **Certified:** a finite, independently checked enclosure, witness, or cover on a declared domain.
- **Lean specified:** an exact proposition exists but has no verified proof.
- **Lean verified:** the exact declaration passes type and axiom checks; distinguish diagnostic receipts from clean reproducible ones.
- **Integrated:** the intended stable root imports the verified declaration.
- **Published:** the public presentation states the same scope and has a clean evidence closure.

An experiment does not become a certificate by clear prose; a certificate does not become the intended theorem until the formal checker and model bridge are included.

## Choose a discriminating test

- Weigh the claim's importance, search-space coverage, smallest test cost, formalization cost if false, instrument reliability, and reusability. Skip brute-force searches whose feasible coverage cannot change the decision.
- Set a compute and wall-time budget, stopping condition, producer command, seed, precision, domain, and filters before a long run. Launch long jobs with durable logs and inspect exit status before using the result.
- Start with smallest admissible and boundary instances, exact symmetries, and structured families. A generic random search can miss a structured stratum even when it is common within that stratum.
- Treat every filter as a hypothesis. State its parameterization, threshold, and symmetry; inspect excluded candidates, relax each filter, and test an independent structured search before saying a region is empty. If a filtered quantity vanishes inside the claimed domain, a positive cutoff excludes part of that domain regardless of tuning.
- Before calling a computation independent, name the convention it must not share with the first implementation. Use exact symmetry pairs, conservation identities, or a different parameterization as controls. If two instruments disagree, identify which object each measures before combining them.
- State the instrument's noise floor and conditioning range. Recompute borderline signs at higher precision, and check that a perturbation can actually move the object of interest. Reoptimization at a degenerate point may move to another solution rather than refine the stored one.

## Compare proof routes

- Search existing Lean code, current notes, failed-route records, and literature before creating a new residual. A refuted route should be retried only after its recorded reopening condition changes.
- Unfold the key definitions and try a direct identity, symmetry, invariant, positivity or convexity argument, finite-rank calculation, or generic topology lemma before extending a long mechanism.
- Give alternatives the same exact target type and boundary cases. Test the load-bearing step of each against the cheapest counterexample, then compare assumptions, imports, proof cost, reuse, and trust boundary.
- An exact decomposition may be poor for bounds if its large parts cancel. Measure its conditioning before using separate estimates. Cost a proposed proof with the bounds it will consume, not the measured values that inspired it.
- Classify a shortcut as `DIRECT_REPLACE`, `FACTOR_ESSENTIAL`, `KEEP`, or `SUPERSEDE`. A renamed helper that hides the same proof is not a direct replacement. Keep the old verified route until the new one passes the same semantic and no-cheat checks.
- Test conjectures before filing them for a successor, especially at the smallest instance of every mechanism they claim to unify. Check that a proposed intermediate lemma is not the conclusion restated.

## Preserve a usable record

- End with a verified theorem, reproducible refutation, or sharply stated open residual with failed routes. Do not describe the third as a result.
- Keep one current note whose beginning states the live claim, evidence, and next discriminating test. Archive corrected claims beside the claims they replace; search later sections before quoting an old table or verdict.
- Record each failed route's exact statement, assumptions, decisive evidence, reusable pieces, and reopening condition. A timeout or tactic failure is not a mathematical refutation.
- Store decision-relevant drafts, counterexamples, generated candidates, and logs in repository-owned paths with producer information and hashes. Use temporary storage only for reproducible intermediates and verify byte-for-byte migration before relying on a durable copy.
