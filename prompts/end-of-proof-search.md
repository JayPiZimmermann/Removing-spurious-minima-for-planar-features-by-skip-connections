# End a proof-search campaign

Close the current proof-search campaign completely. Work only on agent-owned
lanes and paths. Do not infer ownership merely because a file is modified or
untracked; preserve and leave untouched anything owned by another agent or of
unknown ownership.

## 1. Establish scope and inventory

Record the explicit owned paths and capture `git status --short` before making
changes. Inventory every new, modified, or deleted artifact in those paths and
classify it as one of:

- intended Lean source or maintained support code;
- reusable lemma, proof tool, generator, or certificate checker;
- counterexample, negative evidence, or reproducible experiment;
- maintained documentation or handoff material;
- generated build product, log, lock, checkpoint, cache, or superseded scratch;
- unresolved and requiring review.

Do not finish while an owned artifact is unclassified. Files outside the owned
set are context only: do not edit, delete, stage, restore, or commit them.

## 2. Preserve and consolidate mathematical value

Before deleting or replacing anything, inspect it for remarkable ideas,
counterexamples, exact identities, useful proof fragments, search constraints,
and reproducibility data. Preserve valuable material in a maintained theorem,
focused work note, reusable tool, or compact evidence artifact first. Include
the claim tested, assumptions, producer command, parameters or seed, numerical
precision, and evidence level where applicable.

Extract the strongest reusable lemmas and tools from successful lanes. Search
their consumers and nearby arguments, then recombine them when this yields a
cleaner proof, removes a hypothesis, closes a downstream theorem, or exposes a
more natural public statement. Avoid duplicate aliases and glue theorems that
only rename an existing result.

Before generalizing, run the cheapest meaningful counterexample checks. Test
each assumption and each load-bearing proof step separately when cheap. Do not
launch expensive brute-force searches whose feasible coverage cannot
meaningfully falsify the proposed claim. Record the search budget, stopping
condition, and result as proven, refuted, or open; never promote measured or
sampled evidence to a theorem.

## 3. Integrate and clean

For intended results, update the necessary imports, aggregators, verification
manifests, declaration indexes, and maintained documentation. State exact scope
and normalization. Remove obsolete references rather than leaving contradictory
status prose.

Delete only agent-owned disposable artifacts, and only after preservation and
classification. Resolve exact paths before removing generated files, logs,
locks, caches, or checkpoints. Do not use broad globs or recursive deletion on
an unresolved path. If ownership or recoverability is uncertain, leave the file
in place and report it instead.

## 4. Verify the landed boundary

Validate proportionally to the change:

1. compile each changed Lean leaf and its direct consumers;
2. run the repository's fast regression check;
3. for every promoted or public theorem, run the exact declaration/type and
   no-cheat verification required by the repository's statement verifier and
   its manifest, then run the full public-surface check when the public import
   surface changed;
4. run the relevant generator, certificate replay, or documentation build for
   maintained non-Lean artifacts;
5. inspect the final diff and repeat `git status --short`.

Classify the final mathematical state explicitly:

- **Proven:** exact declaration verified and integrated into its intended root.
- **Refuted:** reproducible counterexample or rigorous contradiction preserved.
- **Open:** exact residual statement, failed routes, and next discriminating test
  recorded without claiming a result.

## 5. Commit only owned work

Stage intended files by explicit path; never use `git add .`, `git add -A`, or a
broad directory that may contain another agent's work. Inspect
`git diff --cached --name-status` and `git diff --cached` before every commit,
and unstage anything outside the owned inventory. Commit all intended owned
source and documentation in cohesive, reviewable commits, including intentional
owned deletions. Never stage or commit another agent's files.

After the commit, rerun each public exact target with the verifier's clean-closure
requirement. A pre-commit diagnostic receipt proves the staged bytes but is not a
commit-reproducible publication receipt. If foreign dirty files lie in the target's
import closure, report that blocker rather than claiming the campaign is published.

At completion, confirm that every retained owned artifact is committed,
including maintained notes for open work, or else safely removed. Do not leave
intended source, evidence, or documented open work merely untracked or
uncommitted; if a required commit is blocked, report the blocker and do not
claim the campaign is closed. Confirm that no unclassified owned file remains.
Report the commits, validation commands and outcomes, proven/refuted/open
classification, preserved evidence, removed disposable artifacts, and untouched
foreign changes. Do not push to a remote unless the user explicitly authorized
the push.
