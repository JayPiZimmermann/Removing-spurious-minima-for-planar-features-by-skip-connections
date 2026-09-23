---
name: formalization-conventions
description: Design and audit Lean definitions and theorem statements for faithful mathematical meaning. Use when changing a public signature or comparing a formal claim with its intended model.
---

# State the intended mathematics exactly

Kernel correctness does not detect a vacuous hypothesis, weakened conclusion, hidden modelling reduction, wrong normalization, or misleading theorem name.

## Before proving or restating

- Search Lean sources, manuscript definitions, work archives, and relevant literature for the object and theorem. Search by defining expression as well as name; names can differ while bodies coincide.
- Read actual definitions, theorem types, implicit variables, imports, and consumers. Do not infer meaning from a docstring or a library name alone. Use `#check @name` on new public declarations to expose accidental auto-bound identifiers.
- State genuine mathematical hypotheses, as weakly as the result allows. Do not add an assumption merely because a tactic or proof order failed. Transform a general hypothesis to a working form inside the proof via a named equivalence.
- Prove each modelling reduction and bridge explicitly. A working characterization must not be silently baked into the definition of the primitive property.
- Check satisfiability when hypotheses could be inconsistent. Supply a concrete witness or a separate nonvacuity theorem, and recheck it after strengthening hypotheses.
- Compare the statement's domain, topology, boundary, orientation, quotient or periodicity, and normalization with the intended model. Name alternative conventions at their definition sites and prove bridges with exact constants or signs.

## Honest names and readable statements

- A name says what a declaration proves. Give reduced, derived, restricted, and conditional forms distinct names. A certificate condition and the final property it certifies are different results.
- Reuse an existing canonical object. If two presentations are genuinely needed, give them distinct names and a public bridge; avoid hidden local copies or private bridges that every consumer must rediscover.
- Turn repeated raw hypothesis blocks into named predicates and proof-dependent conclusions into suitable structures when this improves readability. Keep convenience predicates definitionally equal to the forms they abbreviate when existing proofs rely on that equality.
- Keep useful special-case statements even after a general theorem subsumes their proof. State the special result as a corollary with its original meaning.
- Check whether a purportedly unused hypothesis appears only through a tactic. Delete it provisionally, then compile the theorem and consumers before concluding it is unnecessary.

## Semantic and evidence audit

- For headline refactors, record exact theorem type, unfolded definitions, topology, model bridges, normalization, nonvacuity, and allowed axioms. Compare old and new meanings independently; unchanged type text can hide a changed definition.
- Test every witness against every clause of the theorem's scope. If a report combines extrema or attributes from several objects, record which index or witness attains each value.
- Treat a counterexample as a citation: recompute its inputs from the definitions and check its validity domain and numerical precision. A filtered search establishes only what it searched; persist excluded candidates when they matter to the verdict.
- Independent numerical checks must differ in assumptions or implementation, not merely repeat a shared convention. Use symmetries, invariants, or another formulation as controls. A structural violation in the instrument is a failed self-test.
- A sample, limit, or measured value is not a uniform bound. Check the direction of any inequality, the smallest admissible instance, possible nonmonotonicity, and whether each consumed bound is strong enough in the proof chain.
- A universal claim must be checked against the full quantified set; a sampled maximum underestimates the true supremum. State an instrument's valid domain and check every witness against the goal's scope before reporting it.
- An exact decomposition can be badly conditioned when large pieces cancel. Re-index a sum before deciding whether its terms oscillate; classify the true summand before choosing a pairing, norm bound, or supremum estimate.
- Before promoting a numerical pattern to a mechanism, perturb the alleged cause at a scale the instrument resolves. A flat ratio may reflect shared scaling; exact equality across all trials may reveal an instrument that remeasures the same object.
- Check analysis hypotheses where they matter: open versus closed sets, corners and derivative domains, symmetry quotients, and whether termwise estimates survive summation. Quotient by genuine symmetries before interpreting a mined direction.
- If a proof relies on an exhaustive count or a finite cover, calculate the available slack before formalizing it. Redundant elements can preserve closed-form identities while worsening the inequality that must be proved.
- Public verification also needs exact-type, axiom, import, and consumer checks from `formalization-build`. A clean `#print axioms` alone says nothing about semantic correctness.

Keep unresolved discrepancies explicit. Proof cleanup and faster compilation do not justify changing the claim's scope.
