---
name: formalization-build
description: Build, debug, refactor, and promote Lean 4 modules using targeted compiles, import and consumer checks, and exact theorem verification. Use for Lean source or build changes, not numerical research alone.
---

# Build the exact claim and its consumers

A green build verifies only its compiled import closure. Public verification is tied to a module, declaration, reviewed expected type, and axiom audit.

## Inner loop

1. Search the source tree and library for the statement and definition by both name and expression shape; read candidate declarations in full, including surrounding variables and imports.
2. Edit the smallest leaf module. A member must not import its own aggregator root.
3. Run the exact file or module build with a durable log (`lake env lean Path/File.lean` or `lake build Path.File`). Launch Lean compiles, builds, verifier runs, and consumer checks in the background, record their exit status, and continue independent work while they run.
4. Read the first actual error before following cascades. Rebuild direct consumers and the topical root after the leaf passes. Compile relevant unreached modules by name; a default build may omit them.
5. Run the repository's quick source check at a meaningful checkpoint. Use the full public gate once a coherent source batch is stable.

Avoid concurrent writers to one artifact. If the machine runs out of memory, inspect the active builds and proof size; split heavy generated files or reduce contention. Do not interpret an empty log or missing process match as proof that a build finished: inspect exit markers and the full process command.

## Public promotion gate

- Account for each newly public declaration in the claim manifest, including module, declaration, exact expected Lean type, and stable task identifier. Record a reviewed, content-bound reason for any excluded helper where the repository supports exclusions.
- Build the exact module and affected reverse consumers. Check the declaration's elaborated type and transitive axioms. The usual accepted set is `propext`, `Classical.choice`, and `Quot.sound`; reject `sorryAx` and `Lean.ofReduceBool` for a no-cheat public claim.
- Verify that the intended public root imports the declaration. Declaration-free aggregators still need compilation.
- Preserve the old exact declaration as a compatibility wrapper during a headline refactor until definitions, topology, hypotheses, nonvacuity, normalization, and axioms have passed semantic comparison. Never change an expected type merely to make the gate pass.
- Run direct exact-declaration verification for a theorem not yet in the public manifest. A build, existing `.olean`, source scan, or another worker's report is not an exact-type receipt.
- Distinguish a diagnostic receipt from a clean, reproducible one. At a publication or handoff boundary, verify the relevant manifest target against a committed clean closure.

## Diagnose common failures

- **Imports:** A member importing its root creates a cycle; an aggregator can also expose duplicate names hidden in separate leaves. Check the import graph and full source tree before deleting build products.
- **Stale artifacts:** An import failure can cause unrelated syntax errors below it. Compare source and build state, rebuild the first failed dependency, and distinguish content changes from mtime changes.
- **Moves and renames:** Search all imports and consumers, including sibling roots. Anchor replacements to full identifiers or import lines; inspect the edited imports and remove obsolete artifacts only after confirming the move.
- **Missing names:** Read the whole library declaration rather than a search hit. In new public statements, use `#check @name` to inspect implicit binders: missing imports or namespaces can silently turn an intended constant into a variable.
- **Audit tools:** Compare extracted declaration counts with source declarations. Handle Unicode identifiers and modifiers, skip comments and private names, and inspect residual error output. A clean report cannot prove the extractor omitted nothing.
- **Large arithmetic contexts:** Use `exact` for known facts, prove algebraic identities with `ring_nf` or a suitable normalization tactic, aggregate bounds, and pass only required facts to `linarith only`. `nlinarith only` can still be expensive if product search is unnecessary.
- **Generated files:** Build one complete chunk, including its combiner, before a full generated cover. Split expensive modules in the generator. If a per-file compile in a new folder fails only when writing `.ilean`, create the output directory and retry.
- **Process controls:** Inspect numeric PIDs before killing a job; pattern-based `pkill -f` may match the issuing shell. Keep one owner for each long compile and its log.
- **Negative searches:** Never infer absence from output truncated by `head`; count all matches and search alternative names and statement shapes.
- **Tactic state:** `unfold` processes names in order and a later definition can reintroduce an earlier one. If `omega` silently misses a simple arithmetic fact, normalize the goal or use a direct arithmetic lemma before adding assumptions.
- **Verifier receipts:** An edited aggregator can pass a per-file command that used stale dependencies. Rebuild or verify its actual import closure, then inspect the exact exported declaration.
- **Version control:** Stage explicit paths and inspect the committed file list, especially in a shared tree. A deletion or source edit outside the assigned scope needs investigation before a cleanup is considered complete.

## Preserve evidence

Keep decision-relevant receipts, failed logs, and generated candidates in repository-owned storage with hashes; temporary paths may be cleared. Flag changes to excluded or unbuilt subtrees as unverified and list the rebuild still needed. Commit bounded, recoverable changes, review the exact staged paths, and report verification at the level actually achieved.
