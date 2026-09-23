# Stop, checkpoint, and prune proof-search lanes

Stop the specified proof-search campaign without losing mathematical value.
This is a controlled checkpoint followed by conservative lane-local cleanup. It
is not permission for a global repository cleanup, a new proof campaign, or
changes outside explicitly owned paths.

Before acting, record:

- the campaign root and lane names;
- each lane's explicitly owned paths;
- the scheduler or controller and its stop mechanism;
- the directory for canonical state notes;
- the time allowed for a productive worker to checkpoint;
- whether staging and commits are authorized for this campaign.

If ownership or stop authority cannot be established, inspect read-only and
report the ambiguity. Do not guess.

## 1. Freeze new work first

1. Disable the scheduler, retry loop, or launcher before stopping workers. Use
   the campaign's supported stop mechanism when one exists.
2. Inventory every campaign process with its exact PID, parent PID, command,
   working directory, start time, lane, output path, and apparent state.
3. Distinguish productive work from retry loops, duplicate jobs, stalled jobs,
   and unrelated processes. Repeated identical infrastructure failures are
   terminal for this freeze; do not keep retrying them.
4. Give a productive owned worker one bounded opportunity to finish or write a
   checkpoint. Record the deadline and the checkpoint produced.
5. Stop only exact, campaign-owned process trees. Prefer a graceful stop. If no
   supported mechanism exists, terminate exact owned PIDs and use a forced stop
   only as a last resort. Never use a fuzzy `pkill`, kill an unknown process, or
   remove a lock to simulate a stop.
6. Confirm that no launcher can restart the lanes. Take two read-only snapshots
   of processes and changing lane outputs. Record anything still writing.

Do not begin cleanup while an owned writer can still modify the lane.

## 2. Inventory each lane before changing it

For every lane, capture scoped `git status --short`, relevant imports and
consumers, and all new, modified, deleted, or generated files. Classify each
owned item as one of:

- result or maintained Lean source;
- reusable lemma, tactic, generator, checker, or proof pattern;
- exact counterexample, no-go theorem, negative experiment, or pruned route;
- promising but incomplete idea or proof fragment;
- reproducible certificate or numerical evidence;
- canonical status or documentation;
- superseded duplicate or dead branch;
- reproducible generated output, log, lock, cache, or checkpoint;
- unresolved and protected pending review.

Nothing may be deleted until every affected item is classified. A modified or
untracked file is not evidence of ownership.

## 3. Write one authoritative state note per lane

Create or refresh a short `<lane>/CURRENT.md`. It is the only lane state file
that future agents must read by default. Use ASCII prose and TeX for mathematics;
do not put Unicode mathematics in Markdown.

Include:

- the exact live claim and, when applicable, its intended Lean declaration
  signature;
- status: `PROVEN`, `REFUTED`, or `OPEN`, with no stronger wording than the
  evidence supports;
- the strongest established facts and their exact file/declaration locations;
- all load-bearing assumptions and known topology, normalization, or boundary
  caveats;
- the best current proof route in dependency order;
- promising ideas and partial arguments that have not yet been tested;
- decisive counterexamples, failed implications, and no-go results;
- the exact current blocker, not a historical list of every obstacle;
- the cheapest next discriminating test, including which assumption or proof
  step it tests;
- compute already spent and a justified compute or wall-time budget for the
  next attempt, with a stopping condition;
- important source, certificate, log, and checkpoint paths, including producer
  command, seed, precision, input hashes, or environment when relevant;
- direct consumers, required imports, and a minimal restart command;
- files that are safe to prune, files that must be promoted, and files whose
  ownership or value remains uncertain.

Keep old chronology out of `CURRENT.md`. Preserve useful history separately;
do not silently rewrite a refutation or make an old failed route look live.

## 4. Preserve remarkable material and dead-route knowledge

Treat a failed route as a first-class research result, not as cleanup residue.
A precise warning can save more search time than a successful local lemma. Do
not reduce failures to "did not work," and do not confuse a timeout, tactic
failure, or missing library lemma with a mathematical refutation.

Before pruning a sunken route, extract anything that could prevent repeated
work or strengthen another proof:

- a minimal counterexample or falsified implication;
- a useful identity, inequality, reduction, or reusable helper;
- an assumption shown necessary or unnecessary;
- a proof-state pattern, elaboration trap, or performance fact;
- a generator, checker, compact certificate, or reproducible test;
- a stronger recombination with an existing maintained lemma;
- a promising untested idea with a precise first test.

Put compact route records in `<lane>/ROUTE_TOMBSTONES.md`. Each record must name
the claim, exact assumptions, route, verdict, decisive evidence, reason for
stopping, reusable pieces and their retained locations, pruned paths, and the
condition that would justify reopening the route. Classify the verdict as one
of:

- `REFUTED`: a mathematical implication or claim is false, with a minimal
  counterexample or rigorous contradiction;
- `BLOCKED`: the route has a precise unresolved mathematical obligation;
- `IMPLEMENTATION_FAILURE`: Lean, tooling, resources, or representation failed,
  but the mathematical route was not disproved;
- `INCONCLUSIVE`: the allocated search or numerical test did not discriminate;
- `SUPERSEDED`: a stronger or cleaner maintained route replaces this one.

For `REFUTED`, state exactly which formulation fails and which nearby weaker
formulations remain possible. For computational evidence, record coverage,
precision, seed or determinism, and why it does or does not establish the
verdict. Preserve a minimal reproducer when prose alone would not prevent the
same mistake. Link large evidence rather than pasting it.

If a result is remarkable but not ready for a canonical source file, keep the
smallest self-contained artifact and mark it `PROMOTE`. Never delete the only
copy of an idea, counterexample, proof fragment, or reproduction recipe.
Future searches must consult the tombstones for the target claim, its key
assumptions, and its proposed proof steps before reopening a route.

## 5. Prune only genuinely sunken lane-owned paths

After the checkpoint and preservation steps, each lane may clean its own dead
paths. A path is a pruning candidate only when it is clearly one of:

- a superseded duplicate with a maintained canonical replacement;
- a refuted or abandoned branch whose decisive evidence and useful parts have
  been preserved;
- an unconsumed experimental alias or wrapper with no independent value;
- a stopped job's reproducible log, lock, checkpoint, or generated shard;
- a build product or cache that is neither shared nor useful for resumption.

Before removing Lean source, use `rg` and the import graph to check declarations,
imports, references, generators, manifests, and downstream consumers. Compile
the canonical replacement and the smallest affected consumer when practical.
Do not delete an open route merely because it did not close quickly.

Prefer a small lane-local archive when recoverability or ownership is uncertain.
Use explicit paths for every move or deletion. Do not use broad globs,
`git clean`, `git reset`, `git stash`, recursive deletion of an unresolved path,
or cleanup commands at the repository root.

Do not touch shared build state, certificates, worktrees, Git locks, generated
publication outputs, shared scratch areas, or another lane's files unless they
are explicitly in the lane's owned scope and independently verified as safe. Fewer files is not by itself a valid cleanup result.

Small mechanical extraction or deduplication is allowed when it is obviously
valuable, stays inside owned paths, and can be checked cheaply. Record larger
generalizations and proof recombinations as follow-up work instead of restarting
the search during shutdown.

## 6. Validate the remaining boundary efficiently

Avoid a full repository rebuild unless a smaller check cannot cover the change.
For each cleaned lane:

1. compile changed canonical Lean leaves and the smallest affected consumers;
2. run the relevant generator or checker for retained artifacts;
3. run the repository's fast regression check;
4. if a file is added to a public import surface, update its reviewed
   verification entry and run the exact declaration/type no-cheat gate plus the
   full public-surface check as required by project policy;
5. inspect scoped status and diff again, and confirm every owned artifact is
   retained, promoted, archived, pruned, or explicitly unresolved.

A cached `.olean`, a generic successful build, or agent prose is not proof of a
claim. If the targeted gate is blocked by unrelated dirty dependencies, record
the blocker and the exact command; do not claim publication readiness.

## 7. Consolidate the campaign handoff

Write a campaign-level `FREEZE_REPORT.md` containing a compact table with one
row per lane:

- lane and owner;
- process state and stop method;
- mathematical status;
- canonical `CURRENT.md` and tombstone paths;
- strongest retained result or idea;
- exact blocker and next test;
- files promoted, archived, pruned, or left unresolved;
- validation commands and outcomes.

Also list infrastructure failures shared by several lanes, any process still
running, every path that remains unsafe to touch, and the exact clean worktree
or command from which each lane can later resume. Historical status files may
be moved out of the default reading path only after the new notes cover their
live information and the move is lane-owned and reversible.

## 8. Git and completion rules

Follow the campaign's declared Git policy. If Git operations are forbidden or
not explicitly authorized, do not stage or commit; report an exact proposed
file list. If commits are authorized, stage only explicit lane-owned paths,
inspect the staged diff, and make cohesive lane-local commits. Never use
`git add .` or `git add -A`, and never push unless separately authorized.

The freeze is complete only when:

- the scheduler cannot launch new work;
- every owned worker is stopped or explicitly documented as still running;
- each lane has a concise authoritative current state;
- remarkable ideas, counterexamples, and route-pruning evidence are retained;
- failed routes are classified with enough evidence to prevent accidental
  repetition or overstatement;
- every pruned path was owned, unconsumed, classified, and recorded;
- every remaining owned artifact has an explicit disposition;
- no foreign or unknown file was modified;
- the campaign report states what can safely resume and what must not be
  repeated.

If any condition cannot be met safely, stop at the checkpointed state, leave the
uncertain material untouched, and report the precise blocker.
