---
name: formalization-architecture
description: Audit or restructure a multi-module Lean source tree, its import graph, public facade, theorem catalogue, checks, or exploratory area. Use for broad cleanup and proof-architecture changes, not an isolated proof edit.
---

# Preserve the meaning of the theorem tree

An architecture change succeeds only when the intended theorem, definitions, hypotheses, topology, nonvacuity, normalization, and trust boundary survive. Fewer files and faster builds do not compensate for a weaker claim.

## Establish a semantic baseline

- Before broad moves or deletion, keep a recoverable version-control checkpoint. Inventory public import roots, claims advertised to readers, the claim manifest if present, exact theorem types, and direct consumers.
- For each headline claim, record the definitions and model bridges it uses, its topology and boundary conventions, a nonvacuity witness when relevant, normalization identities, and its axiom receipt.
- Compare unfolded meanings as well as printed signatures. A definition can change while a theorem's name and type text remain unchanged. Keep a compatibility definition or prove an explicit equivalence until semantic review passes.
- Have an independent reviewer try to find a weakened hypothesis, changed model, vacuity, missing bridge, or counterexample when a headline result changes.

## Make status and imports explicit

- Paths describe topics; they do not certify trust. Track exploration, candidates, verification, integration, and publication explicitly. Derive reachability and status from the import graph and manifests where possible.
- Keep the public facade small and limited to reviewed headline results. Keep stable secondary results discoverable through a catalogue, with exhaustive integration checks in a checks-only layer when needed.
- Give each metadata field one authority. Extend an existing catalogue or manifest instead of creating a competing registry.
- Production modules must not import audit drivers or regression checks. Scratch work is not a second library: promote reusable Lean declarations to topical modules, programs to scripts, and maintained checks to a checks layer.
- Compare manuscript definitions with Lean definitions before choosing one canonical public form. Preserve explicit bridges for genuinely different presentations; do not merge objects merely because they look similar.

## Simplify proof dependencies

- Map imports, declaration dependencies, consumers, duplicate statements, and expensive closures before refactoring.
- Compare a long proof with at least one genuinely different route: a defining identity, symmetry, invariant, convexity or positivity argument, or reusable topology lemma. Audit each shortcut at boundary and signed counterexamples.
- Prototype alternatives in small leaf modules. Compare semantic strength, assumptions, proof complexity, compile cost, imports, and reuse. Keep the working route until the replacement passes the same semantic and verifier gates.
- Put reusable lemmas low in the import graph. Do not import a specialized consumer merely to reuse one helper.
- Keep special-case statements that readers use, even when a general theorem subsumes their proofs; make them explicit corollaries where appropriate.

## Land bounded changes

- Prefer leaf extraction, import narrowing, and compatibility wrappers before broad moves. Compile changed leaves, direct consumers, relevant roots, and then the public promotion gate when the public closure changes.
- Keep failed routes with their exact claims, assumptions, decisive evidence, useful pieces, and reopening conditions. A tactic failure or timeout does not refute a mathematical claim.
- When work is shared, assign distinct files or worktrees, communicate reusable reductions, and reconcile the shared claim ledger. Never let two writers target the same build artifact.
- Do not delete uncertain material, shared caches, or another worker's files. Commit small reversible units and recheck affected headline claims against the original semantic baseline.
