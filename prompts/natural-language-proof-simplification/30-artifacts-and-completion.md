# Module 30: execution boundary, durable artifacts, progress, and terminal states

## 1. Execution boundary

Every heavy job -- Lean or build-system compilation, TeX, scripts, tests,
certificate checkers, symbolic algebra, numerical checks, hashing, and
source/dependency census calculations -- is submitted to the batch system and
never run on the interactive machine.  This campaign does not own the compute
allocation: never start, stop, resize, or cancel it, and never disturb jobs it
did not submit.

The interactive machine may read text, coordinate agents, write campaign
artifacts, inspect already-produced receipts, and atomically submit an
already-authored task.  It may do nothing else that consumes compute.

Prefer the campaign's atomic submission interface when one exists, so that the
task script, its inputs, and its result directory are fixed before the job is
queued.  The task script must live below the campaign root, refuse to run
outside the batch system, use the frozen source or overlay, and write only to
its campaign-owned result directory.  Before the first submission, verify by text
inspection that the submission interface and the result directories exist.  Do
not test for their absence by running the workload locally.  If the interface,
guard, or writable result directory is unavailable, record `HARNESS_UNAVAILABLE`,
leave all compute-dependent candidates pending, and stop; no local fallback is
allowed.

At most one campaign-owned task may be queued or running at any time.  Track
campaign-owned task names and receipts through the durable filesystem interface,
not through scheduler queries.  Wait for a task's terminal exit-status file, log,
and receipt before submitting the next one.  Loop through census and selected
Stage-B validation tasks one at a time while unrelated work retains priority.  Do
not delete, rename, claim, reprioritize, or inspect the contents of another
campaign's tasks.

## 2. Fresh artifact root and immutability

Choose a collision-free root matching:

```text
campaigns/<fresh-campaign-id>/
  natural-language-simplification-<base-rev-short>-<fresh-run-id>/
```

Once chosen, write `RUN_CONFIG.md` with the full base revision, source policy,
artifact root, expected census, non-integration policy, and terminal target.  Keep
private provenance physically separate from solver-visible packets.  Use per-agent
and per-candidate directories so that no parallel writer shares a file.

At minimum retain:

```text
RUN_CONFIG.md
RUN_STATE.md
EVENTS.jsonl
STATUS.md
ETA.md
inventory/{INCLUSION_GRAPH,TARGET_INVENTORY,ALIAS_MAP,PROOF_UNIT_GRAPH,COVERAGE_MATRIX}.*
inventory/CENSUS_RECEIPT.*
targets/<semantic-id>/private/PROVENANCE.md
targets/<semantic-id>/stage-a/DOSSIER.md
targets/<semantic-id>/stage-a/dossier-audit.*
targets/<semantic-id>/stage-a/solvers/<run-id>/{PROMPT,RESULT,RUN_MANIFEST}.*
targets/<semantic-id>/stage-a/judges/<run-id>/{PROMPT,JUDGMENT,RUN_MANIFEST}.*
targets/<semantic-id>/stage-a/SYNTHESIS.*
targets/<semantic-id>/stage-b/<candidate-id>/overlay/
targets/<semantic-id>/stage-b/<candidate-id>/{forward.patch,inverse.patch,METRICS,RECEIPTS,ADOPTION_MANIFEST}.*
jobs/
job-receipts/
FINAL_MANIFEST.json
FINAL_REPORT.md
RESUME.md
```

Every submitted job leaves a durable record: the exact task script, its inputs,
its full log, its exit status, and a receipt naming the source snapshot it ran
against.  A result with no durable log is not evidence.

Promote an artifact only after checking its source snapshot, target, role, scope, and
allowed inputs.  Never overwrite a promoted response or judgment; revisions get new
attempt IDs with lineage.  Record exact observed lifecycle fields, leaving unknown
values `unknown` rather than reconstructing them.

## 3. Progress, ETA, and persistence

Maintain counts derived from the frozen inventory for dossiers curated/audited,
solver attempts returned, hostile judgments complete, target-family coverage,
selected candidates, Stage-B tasks pending/running/passed/failed, and blockers.
Update `STATUS.md` and `ETA.md` at every major wave and every job receipt, and
send concise user-visible updates at regular intervals while the campaign remains
active.  ETAs are ranges based on observed throughput and remaining work, never
promises.

Continue refilling useful Stage-A agent capacity and, serially, the single allowed
compute slot until every inventory-derived target has a terminal Stage-A record and
every selected Stage-B candidate has a terminal isolated validation or a precise
compute blocker.  Unchanged external state is a reason to wait and report, not to
integrate or to move computation onto the interactive machine.

## 4. Terminal states and final manifest

Use exactly one campaign state:

- `INVENTORY_BLOCKED`: baseline, inclusion graph, or required census failed;
- `STAGE_A_IN_PROGRESS`: some required target lacks completed independent attempts
  or hostile judgment;
- `STAGE_A_COMPLETE`: all target coverage closes, with open/false/keep outcomes
  recorded honestly;
- `HARNESS_UNAVAILABLE`: selected candidates require computation but the authorized
  submission path is unavailable;
- `STAGE_B_IN_PROGRESS`: selected alternatives are being validated serially;
- `ADJUDICATION_READY`: all required Stage-A coverage closes and every selected
  Stage-B candidate has a complete isolated package or explicit terminal failure.

`ADJUDICATION_READY` is the maximum.  Never report `INTEGRATED`, paper-final,
release-complete, committed, or pushed.  Open mathematical targets are allowed only
when their exhaustive attempts and exact remaining obstruction are recorded; they
are not mislabeled as solved.

`FINAL_MANIFEST.json` must identify the full base revision and campaign root;
reproduce the dynamic census and alias resolution; enumerate every `WHOLE`, `CLAIM`,
`STEP`, `ARROW`, and `ROUTE` target and its independent coverage; link every dossier,
response, judgment, synthesis, overlay, forward/inverse patch, metric, log, and
receipt; list procedural-blindness exceptions and quarantined runs; state every
failed/open proof obligation; and give candidate-by-candidate adoption recommendations.
It must also certify that no production paper/Lean file was edited and that no
integration, commit, push, allocation-management action, or interactive-machine
computation occurred.

`FINAL_REPORT.md` gives the concise mathematical findings, strongest simplifications,
whole-theorem outcomes, Lean replacement-ready candidates, failed approaches,
remaining blockers, observed throughput, and a later-adoption handoff.  `RESUME.md`
contains the exact safe next action for any nonterminal state.  Rebase onto a newer
paper/Lean tree and live adoption are expressly deferred to a separately authorized
campaign.
