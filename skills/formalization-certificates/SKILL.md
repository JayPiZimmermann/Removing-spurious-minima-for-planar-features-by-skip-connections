---
name: formalization-certificates
description: Design, generate, check, or integrate finite numerical and symbolic certificates for Lean proofs, including interval bounds, covers, and generated source files.
---

# A certificate is data plus an independent checker

Separate the mathematical reduction, finite artifact, generator, and checker. A search proposes evidence; the checker proves the stated finite claim. A checked certificate becomes a theorem only when its verified meaning is connected to the intended Lean statement.

## State the contract

For every promoted certificate, record the exact inequality, root count, enclosure, or cover; the domain and boundary convention; normalization and precision; generator command and input/configuration hashes; checker and trust boundary; decisive margin; and consuming Lean declaration.

- Floating-point samples locate candidates but do not certify signs. Use outward-rounded intervals or another sound finite checker for the final claim.
- Distinguish existence from exclusion. For a cover, prove that every point, including irrational and boundary points, lies in a checked cell. At an exact breakpoint, either split there or use overlapping bounds that cover it.
- Check the original target before designing a cover. Factor out vanishing terms when a nondegenerate core inequality is the real claim; otherwise box counts can explode near a harmless zero.
- A product-box argument must account for cross terms. Estimate their size before committing to a box layout; shrinking boxes does not repair a scale-independent coupling obstruction.
- Tune precision on a representative expression before emission. More recursion or splitting can worsen rounded enclosures and compile cost; choose the cheapest setting that clears the required margin.

## Generate and compile

- Maintain a generator for repetitive Lean source; edit the generator instead of thousands of emitted lines. Record stable inputs and verify deterministic regeneration against committed output.
- Compile representative local cells, then one **complete** small chunk with its combining lemma before generating a large family. Samples test local bounds, not coverage or assembly.
- Split large generated proofs into bounded leaf modules and a thin aggregation module. Diagnose whether time is spent in elaboration, kernel checking, linting, or a large arithmetic tactic before changing numerical precision.
- Prefer term-level identities and small `linarith only [...]` calls over giving an arithmetic tactic a large context. Use `nlinarith` only when multiplication of facts is actually needed.
- Test a second parameter instance when the generator might have silently fixed constants or names for the first one.
- Separate local cell proofs from global aggregation. A top-level assembly can fail from recursion depth or memory even when every cell is correct; split both the cell files and their combining lemmas.

## Preserve reproducibility

- Track canonical manifests, checkers, and artifacts needed by the documented verification command. Use large-file storage for large immutable inputs when appropriate; keep only reproducible logs, locks, and frontier data ignored.
- Before cleanup, enumerate every path referenced by the manifest and ensure each is tracked, downloadable by checksum, or in a documented preservation snapshot. A clean clone must be able to run the ordinary checker without unpacking an unrelated archive.
- Do not present `#eval`, sampling, `native_decide`, or a dirty-source receipt as kernel-level proof of a public theorem. Finish with exact type, axiom, import, and consumer checks from `formalization-build`.
