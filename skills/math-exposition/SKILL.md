---
name: math-exposition
description: Explain mathematical results, proof states, and research conclusions clearly in chat or reader-facing summaries. Use when reporting mathematics; keep source-file formatting conventions separate.
---

# Report mathematics so the scope is visible

Define the objects a message needs, explain the mechanism in plain language, then state hypotheses, conclusion, evidence level, and relevant theorem names. Give internal names a brief gloss. Name the original object before a reduced expression: the operator before its matrix, the measure before an integral, or the domain and basis before certificate coefficients. Say what a computed sign, rank, or bound proves.

## Format for the medium

- In user-facing chat, write readable Unicode mathematics rather than raw TeX commands. If a formula becomes dense, introduce names and split it into smaller equations. Preserve literal Lean terms and exact signatures in code blocks when needed.
- In Markdown source intended for TeX rendering, use the file's TeX conventions rather than replacing them with Unicode symbols. Keep the reader-facing explanation consistent with the rendered result.
- Use one coherent paragraph per idea. Present a finite certificate by its reduction, domain, checking principle, and linked declaration or artifact; include large coefficient tables or verifier traces only when requested.

## Calibrate the claim

- A theorem report states its actual hypotheses and conclusion, and distinguishes machine-checked proof, mathematical argument, finite certificate, and numerical evidence. An isolated compiling body is not necessarily the integrated public result.
- Answer status questions directly. State the live obstruction for incomplete work, and identify whether a result is production-active, staged and Lean-checked, research-only, refuted, or open. A partial reduction or measurement is not a finished theorem.
- Genuine hypotheses belong in the theorem statement. An unproved assumption carrying the main obligation must be described as such; do not report a conditional route as an unconditional result.
- Make retractions plain and correct the source summary where the old claim appears. Before making a universal claim, check every member of the stated set; otherwise quantify only over what was examined.
- Use “no shorter route found among the audited routes” rather than claiming no shorter proof exists. Say what evidence supports the conclusion without turning the report into a log of attempts.

## Keep long-lived summaries current

When corrections accumulate, rewrite the document around the current finding, mechanism, evidence, limitations, and reproducibility instructions. Keep corrections next to the claims they revise. Before quoting an old ledger or README, search for later treatment of the same quantity and verify attributions against source history.
