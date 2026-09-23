# Campaign: verify, compress, reconnect, and simplify the Lean tree

You are the principal investigator and integration controller for a multi-day,
massively multi-agent campaign over this repository's Lean development.

This is not merely a file cleanup. Your primary responsibility is the mathematical
correctness, honest scope, auditability, conceptual clarity, and research value of
the Lean development.

## Priority order

Use this order for every decision:

1. Correctness and honest scope of the main results.
2. Exact no-cheat re-verification of every headline and publication-facing theorem.
3. Preservation of proved results, counterexamples, failed-route knowledge, proof
   ideas, and reproducibility data.
4. A coherent architecture with a genuinely narrow headline surface.
5. Shorter, more general, reusable, and searchable proofs.
6. Progress on high-value open frontiers.
7. Reduced repository size, compilation cost, and agent token cost.

Never trade a semantic guarantee for cleaner files or a shorter proof. A plausible
discrepancy in a headline theorem is a stop-the-line event.

## Startup: resume before initializing

First determine whether this campaign already exists. Inspect registered
worktrees, any existing cleanup or integration branch, its latest commits and
status, and the newest final report and handoff under the campaign directory it
names.

If an existing campaign and handoff are present, RESUME them. Use their integration
worktree, ownership records, facade and catalogue architecture, ledgers, migration
map, and current task graph. Do not create another cleanup branch, worktree, campaign
directory, secondary catalogue, or replacement registry. Reconcile the handoff
against Git and running processes, then continue from the latest clean gated commit
plus explicitly classified in-flight work.

Only the absence of a valid existing campaign permits fresh initialization below.
Creation instructions in this prompt are fresh-start-only.

## Immutable rollback baseline

Before any fresh-start edit, establish a preservation ref: commit and push the
complete pre-cleanup state to a dedicated branch, and record its exact commit
hash and subject in the campaign charter. Then:

1. Fetch that branch and require the remote ref to resolve to the recorded commit.
2. Check the integrity of any large-file storage the repository uses.
3. Record the Lean version, build-manifest hash, verifier hash, verification-manifest
   hash, and relevant tool versions.
4. Create a new cleanup integration branch and a dedicated clean worktree from the
   preservation commit.
5. Never amend, rebase, reset, force-push, or otherwise move the preservation ref.
6. Never run this campaign in the original shared workspace.

The preservation ref is a recovery boundary, not permission to delete without
classification.

There may be foreign processes on the machine. Record any process explicitly
classified as unknown and unsafe to stop, and leave it alone. Never kill a process
by fuzzy name. Stop only exact process trees launched and owned by this campaign,
after recording PID, parent, command, working directory, start time, lane, and
outputs.

## Read the operating rules

The controller must read these files completely before delegating:

- `skills/formalization-architecture/SKILL.md`
- `skills/formalization-conventions/SKILL.md`
- `skills/formalization-build/SKILL.md`
- `skills/formalization-research/SKILL.md`
- `skills/formalization-certificates/SKILL.md`
- `skills/math-exposition/SKILL.md`
- `prompts/stop-and-prune-proof-search-lanes.md`
- `prompts/end-of-proof-search.md`

For every frozen lane, read its freeze report, freeze scope or control note, current
state note, and route tombstones before assigning work. Do not reopen a failed route
until its recorded reopening condition is met.

All new Markdown uses ASCII prose and TeX for mathematics. Never put Unicode
mathematical symbols in Markdown. User-facing chat may use Unicode mathematics.

## Multi-agent organization and communication

Use the strongest available agent configuration for every substantive lane,
independent review, adversarial review, integration review, and design RFC. Run every
campaign phase as a many-agent workflow rather than assigning an entire phase to one
agent. Do not silently downgrade a semantic or proof task to a weaker configuration.
If the intended configuration is unavailable, record that fact and pause the affected
lane.

Spawn a broad hierarchy of agents. Use many read-only agents freely, but schedule
memory-heavy Lean builds according to measured resource use. Each editing agent has
one branch or worktree and explicit owned paths. Only the integrator edits shared
aggregators, manifests, publication bindings, and campaign registries.

On a fresh start, create one controller-owned campaign directory with the files
below. On resume, validate and continue the existing directory instead:

- a campaign charter;
- an ownership record;
- a headline ledger;
- a module inventory;
- a classification note for the headline facade;
- a shared-lemma registry;
- a simplification ledger;
- a migration map;
- a work-retention manifest;
- an open-frontiers note;
- a final report.

Workers communicate discoveries to the controller using:

```text
LANE:
KIND: CLAIM | CONFLICT | SHARED_LEMMA | COUNTEREXAMPLE | BLOCKER | PROMOTION
CLAIM:
EVIDENCE:
PATHS_AND_DECLARATIONS:
SEMANTIC_RISK:
PROPOSED_ACTION:
REQUESTED_OWNER:
STATUS:
```

When a lane finds a reusable reduction, the controller immediately sends its exact
statement and likely consumers to the affected teams. Hold regular synthesis passes
whose task is to recombine tools across branches, not merely summarize status.

Appoint one story captain per coherent mathematical story, derived from the actual
theorem families in the tree rather than from a fixed list: one captain per major
result family and its counterexamples, one for the transfer results that connect two
models, one for dynamics and trajectory claims, one for the geometry of the parameter
space, and one for each infrastructure story -- certificates and generated source,
experiments and scripts, and the import graph, build performance, duplicate
declarations, and shared tools.

Each captain may spawn independent semantic reviewers, adversarial falsifiers,
import auditors, proof simplifiers, Lean implementers, and exact verifiers. Register
every child, scope, owned paths, compute budget, and stopping condition. Do not allow
recursive unbounded search.

## Phase I: semantic red-team before architecture changes

Do not move, merge, rename, delete, or simplify a headline theorem until this phase
is complete for that theorem.

Build the candidate headline set from:

- every target in the verifier's statement manifest;
- every claim binding used by public-facing renderings of the results;
- the title, subtitle, and abstract;
- the public facade module and maintained README claims; and
- every theorem called main, unconditional, sharp, complete, all-width, or
  all-dimensional in maintained sources.

Directory membership is not authority. Audit all current manifest targets even if
they are later classified as secondary.

For each target, record:

- exact module, declaration, expected type, and a stable type hash;
- a plain mathematical statement;
- definitions expanded far enough to expose load-bearing modelling choices;
- every hypothesis, quantifier order, and whether it is mathematically natural;
- a nonvacuity witness or a precise reason nonvacuity is automatic;
- ambient space, parameterization, perturbation topology, and boundary convention;
- local minimum versus local minimum on a subset;
- signed, nonnegative, or strictly positive mass assumptions;
- strict versus nonstrict and critical point versus local minimum;
- which objective is meant, including centered versus plain versus joint-skip and
  population versus empirical;
- normalization, periodicity, and quotient conventions;
- exact conclusion and what it does not imply;
- transitive axiom set and clean verifier receipt;
- public claim identifiers and prose depending on the result; and
- independent reviewer verdicts.

Use `GREEN`, `CAVEATED`, `MISSTATED`, `VACUOUS`, `SUPERSEDED`, or `OPEN` as the
semantic status.

### Highest-priority main theorem chain

Begin with the theorem asserted by the title and abstract, and audit its entire
chain: the input law and data model, the structural hypotheses on the teacher, the
sign and width conditions on the student, the class of perturbations the minimality
is taken over, every normalization and coordinate bridge between the stated
objective and the objective actually proved about, and the literal conclusion.

Read and independently rederive the scope of each declaration on that chain, from
the deepest provider to the public statement. Verify that every definition and
bridge supports the interpretation the public prose gives, including degenerate and
boundary cases, and that the prose warns about exactly the restrictions that the
formal statement imposes -- in particular about which parameter topology the
minimality is stated in.

Assign two mathematical reviewers who initially cannot see each other's conclusion
and a third adversarial exact-verification agent. Apply the same pattern to every
headline family.

### Mandatory attacks

For every headline, actively seek:

- inconsistent, unused, or conclusion-encoding hypotheses;
- hidden modelling reductions inside definitions;
- theorem names stronger than their types;
- vacuous pointwise predicates presented as landscape theorems;
- topology changes across coordinate or restriction bridges;
- reduced Hessian results presented as genuine loss-level escape;
- strict/nonstrict, local/global, or critical/local-minimum confusion;
- signed/nonnegative perturbation confusion;
- degenerate-stratum and collision-stratum failures;
- directions modulo a half turn confused with oriented vectors modulo a full turn;
- normalization errors by a factor of a full turn;
- centered and noncentered objectives being interchanged;
- exact fit confused with attaining an internal lower bound;
- finite experiments presented as population mathematics;
- certificate existence confused with checked global coverage;
- one optimization scheme presented as another;
- convergence to a set presented as convergence to one parameter vector; and
- special-case results presented as fully general.

Lean compilation is necessary but not sufficient. Kernel correctness does not
detect weak, vacuous, or misinterpreted statements.

### Stop-the-line rule

If either reviewer finds a plausible semantic discrepancy:

1. Mark the target `RED_TEAM_HOLD`.
2. Freeze refactors in its definition, dependency, and consumer closure.
3. Leave the immutable baseline commit untouched while investigating.
4. Spawn an independent reproducer and definition-tracing agent.
5. Run the cheapest decisive mathematical or numerical test.
6. Report the exact discrepancy and affected public prose.
7. Repair correctness before resuming cleanup.

Do not preserve a false claim merely to keep a test green. Correctness outranks
presentation stability.

## Numerical and symbolic falsification gate

Before a substantial Lean proof or generalization, write a short worksheet:

- exact claim or proof step;
- weakest intended assumptions;
- smallest dimension, width, rank, collision, or boundary case that tests it;
- what observation would refute it;
- expected compute and wall time;
- precision, conditioning, and feasible coverage;
- probability the test changes the route decision;
- expected Lean effort saved if the claim is false;
- reuse value of the witness, generator, or checker; and
- budget and stopping condition.

Choose deliberately between a cheap experiment first, direct Lean proof first, or
deferral. Prefer exact rational or symbolic calculations when possible and outward-
rounded intervals for certification. Floating point is measured evidence only.

A search that finds nothing matters only when its coverage is strong enough to
change credibility. Test assumptions and load-bearing proof steps separately. Use
small dimensions, first overparameterized widths, zero/tiny/equal/unequal masses,
collisions, rank-deficient cases, symmetric controls, asymmetric controls, and
boundary strata.

Every failed route becomes a precise tombstone, not a deleted embarrassment.

## Phase II: map the actual architecture

Generate a fresh import and declaration inventory from the baseline. Do not trust
old hand-maintained counts. For every module record:

- declarations and namespaces;
- direct imports and reverse consumers;
- membership in each public closure;
- manifest and publication consumers;
- evidence and axiom status;
- compile time and peak memory when practical;
- line count and generated/maintained status;
- duplicate, alias, or supersession relationships;
- owning mathematical story; and
- proposed lifecycle classification.

Investigate the usual contradictions rather than assuming their recorded counts:

1. a facade that claims to be headline-only while importing broad catalogues;
2. an aggregator that pulls an entire scratch area into the public closure;
3. public roots consuming modules that live under an experimental directory;
4. large search forests with no clear maintained root;
5. handwritten axiom-audit surfaces overlapping the authoritative verifier manifest;
6. campaign scratch trees that mimic canonical module paths without being library
   source; and
7. generated declaration indexes containing stale and untracked search noise.

Path is topic, not status. Use explicit states such as `PROBE`, `CANDIDATE`,
`VERIFIED`, `INTEGRATED`, `PUBLIC`, `PUBLISHED`, and `RETIRED`.

### Resume from an existing cleanup campaign

Before creating any inventory, registry, facade, or migration record, inspect the
current integration branch and its campaign handoff. Reuse and extend completed
work. In particular, an earlier cleanup run may already provide a narrowed headline
facade, a secondary catalogue of stable non-headline endpoints with a build-coverage
check, a verifier manifest that is the exact-target and reviewed-exclusion authority,
and campaign ledgers for classification, headlines, migration, and shared lemmas.

Such artifacts are the starting point, not permission to trust stale snapshots.
Resolve the latest clean gated integration commit, read its handoff, and confirm each
artifact against the actual import graph and manifest. Never create a parallel
"secondary registry" when the catalogue, the manifest, and the classification ledger
already own that information. Add a new field or one compact companion registry only
when an existing authority genuinely cannot represent it, and record which file owns
each field.

## Canonical definitions from the audited publication model

The publication-facing definitions express the intended public mathematical model.
Treat them as the candidate publication specification, not as unreviewed text to be
copied blindly. Before restructuring dependent proofs, audit each published
definition against the literal loss, parameter domain, topology, normalization, and
current Lean definitions. During stage one, record any error and make only the
smallest truthfulness patch required by the publication invariant below; the
structural and prose rewrite remains frozen for stage two. Once a definition is
approved, make it the unique canonical public Lean definition of that mathematical
object.

Extend the existing catalogue, exact-verification manifest, headline ledger, and
migration map with a machine-readable publication-model view; do not create an
independent competing theorem registry. If a compact companion file is needed for
editorial fields, it references the existing stable task/result identity and is the
sole owner of those fields. For every published definition the joined view records:

- stable publication and result IDs;
- exact mathematical domain, codomain, variables, and quantifier order;
- coordinate model and topology;
- sign, unit-norm, width, dimension, and support conditions;
- normalization and relation to the literal population or empirical loss;
- one canonical Lean declaration;
- every former competing declaration;
- definitional equality, proved equivalence, specialization, or genuine semantic
  distinction;
- consumers and migration status; and
- independent semantic-review and exact-verification evidence.

Enforce one canonical definition per mathematical object. Classify apparent
duplicates before editing:

1. byte-level or elaborated exact duplicates;
2. aliases and compatibility wrappers;
3. equivalent coordinate presentations;
4. specializations of a general definition;
5. genuinely different domains, topologies, quotients, or normalizations; and
6. accidental semantic divergence.

Eliminate category 1 after all consumers migrate. Replace unnecessary category 2
definitions with `abbrev`, notation, re-export, or temporary deprecated aliases.
Represent category 3 by one canonical object plus explicit equivalence,
homeomorphism, chart, or loss-transport theorems. Represent category 4 as a theorem
or thin specialization of the general object. Keep category 5 only when its name
and documentation expose the distinction. Category 6 is a stop-the-line semantic
finding.

Do not erase distinctions that are load-bearing, including:

- the distinct objectives the paper compares;
- mass-angle and mass-unit-direction coordinates;
- signed ambient perturbations and cone-relative perturbations;
- oriented vectors modulo a full turn and projective lines modulo a half turn;
- internal kernel or mass losses and the literal population loss; and
- population, empirical, atomic-measure, and certificate-backed statements.

Place canonical definitions in the smallest stable topical modules with minimal
imports. Reusable proof engines depend on those definitions. The headline facade
contains thin, recognizable publication-facing theorem wrappers whose types match
the natural published theorem shapes. A secondary catalogue contains stable
non-headline endpoints. Compatibility aliases are temporary migration tools, not a
second API.

The publication unit graph and the Lean module graph are related but not identical.
Do not organize Lean internals in chapter order or create one Lean file per prose
fragment. Several published proof units may use one general Lean lemma, and one
published theorem may compose several mathematical modules. What must align exactly
is the public definition/theorem interface, stable result identity, and proved
bridge chain.

Before deleting a competing definition, require:

- a clause-by-clause semantic comparison;
- a proof of equivalence or an explicit correction record when it is not
  definitionally equal;
- migration of every import, theorem, certificate, verifier target, and publication
  binding;
- affected consumer compilation and exact verification; and
- a searchable old-name and old-path migration entry.

At campaign end, every maintained published definition has exactly one canonical
Lean declaration, or a written reason why multiple genuinely different formal
objects are necessary. No headline may depend on an unclassified duplicate.

## Phase III: narrow the headline facade and maintain the secondary catalogue

If the integration branch already contains a narrowed headline facade and a
catalogue layer, treat that implementation as the starting point. Audit its
classification, closure boundaries, exact-target coverage, and naming; then repair or
extend it. Do not recreate the catalogue, move the same files a second time, or
restore demoted modules to the facade merely because an older prompt describes this
phase in the future tense.

Classify every stable declaration or family as:

- `HEADLINE`
- `SECONDARY_STABLE`
- `INTERNAL_SUPPORT`
- `INFRASTRUCTURE`
- `RESEARCH_OPEN`
- `REFUTED_TOMBSTONE`
- `GENERATED_CERTIFICATE`
- `SUPERSEDED_DUPLICATE`

A result belongs in the headline facade only when it changes the central
mathematical story, is the strongest maintained version, has visible scientific
hypotheses, is not merely a bridge/helper/alias, has a maintained public consumer,
and has exact clean verification with an agreed one-sentence scope.

Stable non-headline results remain in topical modules and enter the existing
machine-readable catalogue view with a generated human glossary. Include bridges,
complete classifications, equality cases, sharpness companions, nonvacuity theorems,
conditional reductions, topology companions, specialized examples, and
compatibility declarations. Do not make the catalogue another giant import root.

Compare at least:

1. topical Lean result facades; and
2. a generated exact theorem index backed by manifests without importing every
   result into one closure.

Choose by clarity, dependency size, compilation cost, stable links, and exact
verification coverage. Begin with facade and import changes; do not mechanically
move thousands of files. Declaration names, types, definitions, and file paths may
change when that yields a better architecture or a corrected or stronger result.
Keep the baseline contract recoverable, update every consumer, and use a checked
replacement, equivalence theorem, or temporary compatibility wrapper as
appropriate. Record every old-to-new path and semantic change in the migration map.

Review likely demotions rather than assuming them: broad per-regime catalogues,
vacuous or superseded wrappers, older conditional results that a later theorem
subsumes, internal identities, and manual audit sidecars.

## Target tree and the role of a separate checks root

Aim for:

- a narrow flagship facade;
- stable topical pillars, one per mathematical story;
- a secondary result catalogue and generated glossary;
- explicit research and open-frontier roots outside public closures;
- generated source separated from maintained proofs; and
- archived campaign history outside default agent retrieval.

Use a separate source root and build target for maintained audit and regression
drivers. This does not make checks external to the project. It enforces a one-way
dependency: checks may import the library, while theorem modules can never
accidentally import check drivers. A normal theorem build therefore avoids thousands
of audit commands. Keep the verifier and its statement manifest authoritative, and
generate Lean probes from manifests where useful.

Move publicly consumed results out of directory names that advertise them as scratch
or experimental. Move kernel-clean reusable infrastructure out of experimental areas;
leave demonstrations that rely on forbidden proof escapes in a clearly non-public
experimental area.

## Phase IV: simplify proofs and recombine tools

For each simplification, write a small RFC with:

- baseline theorem types and semantic scope that must remain recoverable, plus any
  proposed correction or strengthening;
- current proof dependencies, line count, and compile cost;
- conceptual mechanism of the replacement;
- falsification attempts and boundary tests;
- reusable abstraction and demonstrated consumers;
- affected import and publication consumers;
- expected reduction in total proof surface; and
- rollback commit.

Accept a replacement only when it preserves or strengthens semantics, keeps the
same or smaller axiom set, passes independent review, and reduces total complexity
rather than merely shortening one file. Keep the old proof until the replacement
and its consumers are green. Report measured build cost before and after: build
efficiency is a co-objective, subordinate to correctness and understandability.

Continuously seek shared tools in:

- residual-potential and kernel calculus;
- criticality as double-zero conditions;
- Green identities and variation-diminishing arguments;
- split, merge, and permutation-quotient geometry;
- local-minimum transport under homeomorphisms, isometries, and restrictions;
- second-variation and trace budgets;
- Gram, zonotope, and rank reductions;
- finite-support and cell geometry;
- certificate schemas and independent checkers; and
- compact nonvacuity and topology witnesses.

Maintain a short list of concrete high-value simplification leads and test them as
hypotheses, not as instructions to force through. Typical leads worth keeping on that
list:

1. replacing a long bespoke expansion by an existing decomposition theorem, applied
   after adding the auxiliary objects that encode the extra degrees of freedom;
2. extracting one generic lemma shared by several instances of the same transport or
   homeomorphism argument;
3. narrowing oversized imports in the largest definition and bridge modules, with
   full consumer closures measured before and after;
4. moving duplicated low-level coordinate, rigidity, continuity, and second-variation
   helpers into demonstrated foundational homes; and
5. making a heavy aggregator opt-in unless a theorem genuinely belongs in the
   headline closure.

Preserve any direct proof that a new route would replace until the replacement and
all of its downstream consequences pass.

### Paired route comparison

When a chain admits two genuinely different routes, run paired independent
investigations rather than letting one team judge its own route. Give each team the
same target and the same boundary obligations, and compare the results on
correctness, boundary coverage, dependency cone, and explanatory value. Seek the
smallest theorem that closes the decisive step, and audit every chart shift and
normalization factor on both sides. Do not delete the losing library merely because
the other route closes one endpoint: retain it if it has independent consumers or
explanatory value.

## Phase V: push high-value open frontiers when simplification creates leverage

Architecture work may reveal proof closures. Pursue them with bounded lanes, but do
not let cleanup become unbounded search. Prioritize frontiers that generalize an
existing theorem along a dimension the paper already discusses, that close a known
gap between a proved special case and the intended general statement, or that become
reachable by a reduction recombined during this campaign.

For each frontier, state the exact model first and do not conflate it with a
neighbouring special case or with a counterexample built from a different input law.
Build one canonical dependency story from the proved special case through the
reductions to the exact residual obstruction. Read all tombstones for a target before
retrying a route.

Keep measured searches separate from proof. A numerically observed sign or rank
condition is not a theorem until the coefficient and realization bridges are proved.

Every lane ends `PROVEN`, `REFUTED`, or `OPEN`. `OPEN` includes the exact residual,
blocker, failed routes, and next discriminating test.

## Phase VI: clean campaign state, experiments, ideas, scripts, and certificates

The campaign state directory is campaign state, not a second source tree. Classify
every moved or deleted path. Promote reusable Lean to its mathematical home, reusable
programs to the maintained scripts or experiments directory, maintained Lean audit
drivers to the checks root, and compact canonical evidence to the certificates
directory.

Merge idea dumps and contradictory status chronologies into a small current
frontier plus searchable tombstones. Archive useful history outside default agent
reading paths. Retain failed routes as warning signs with exact assumptions,
verdict, evidence, nearby valid formulation, reusable pieces, and reopening
condition.

For every campaign-state item choose one disposition:

- promote to maintained source;
- merge into a stronger maintained note;
- retain as canonical current state;
- retain as tombstone or counterexample;
- move to a reproducible experiment;
- archive as historical evidence;
- regenerate from a maintained producer;
- delete as a proved zero-consumer duplicate; or
- unresolved and protected.

Do not delete the only copy of a proof fragment, counterexample, no-go result,
search parameterization, exact identity, checker, seed, precision, producer command,
or environment record. Before deleting Lean, search declarations, imports,
manifests, publication references, generators, and consumers; compile the replacement
and smallest affected consumers.

An artifact is a lifecycle category, not a requirement for a generic top-level
artifacts directory. Keep mathematical certificates in one place with clear
manifests:

- ordinary version control for compact canonical artifacts and manifest dependencies;
- large-file storage for immutable large canonical files and preservation snapshots;
- ignored run storage for reproducible frontier shards, logs, locks, and
  checkpoints after preservation;
- independent checkers and complete boundary coverage; and
- an automated guard preventing ignore patterns from hiding future canonical
  manifest dependencies.

Preservation snapshots of certificates are recovery evidence, not an excuse to make
the ordinary checker require manual archive extraction.

After retained canonical Markdown has been compacted, normalize mathematics to TeX
and upgrade staged checks to scan every retained Markdown file, not merely new lines.
Archive raw history instead of hand-editing disposable dumps.

## Build and compute discipline

Do not run full roots in the ordinary edit loop.

1. Compile the exact changed leaf.
2. Compile its direct or smallest meaningful consumers.
3. Run the repository's fast regression check.
4. Run focused exact verification for touched public targets.
5. At integration milestones run the full public-surface check against the recorded
   preservation baseline.
6. Use staged checks before each integration commit.
7. After committing, rerun affected public targets with the verifier's clean-closure
   requirement.

Measure wall time and peak memory before raising build concurrency, and set
concurrency from those measurements rather than from a fixed rule. Parallelize
read-only graph, semantic, duplication, and counterexample work. Do not run duplicate
compilers for one module or verify against a mutable shared checkout.

At major release milestones, run the complete reviewed manifest in a clean isolated
worktree. Do not treat a generic successful build as the authoritative theorem gate.

## Publication invariant during stage one

The narrative rewrite of the public-facing prose is a later campaign, but its
mathematical contract cannot regress.

Record every baseline claim-to-target binding in the headline ledger. A binding may
change when the replacement is stronger, clearer, or needed for a sound refactor, but
retain the old scope and migration record and exact-verify every affected consumer.
At baseline and each integration milestone:

- run the focused script and publication tests;
- exact-verify every selected published target against a clean closure;
- run citation and reference audits appropriate to moved declarations; and
- run the pure publication check in a disposable validation worktree.

Distinguish a stale-generated-output diagnostic from a theorem-verification
failure. A stale render may be recorded for stage two; a missing, weakened, dirty,
or unexplained and unverified semantic change blocks stage one.

Preserve declaration names with compatibility wrappers where practical, but allow
cleaner checked replacements and synchronized evidence-binding changes. Do not
constrain a sound architecture merely to keep an old path. Record every current or
future prose, proof-architecture, link, and navigation change in the migration map
for the second-stage publication campaign.

If semantic review finds that current prose overstates a theorem, correctness wins:
make the smallest immediate correction needed for honesty and record the broader
rewrite for stage two.

## Git and integration rules

Workers commit coherent lane-local changes and report commit hashes. The integrator
inspects owned paths and diffs, reruns leaf/consumer checks, and integrates only
green commits. Use frequent reversible commits.

Never use `git add .`, `git add -A`, broad recursive staging, `git clean`,
`git reset --hard`, force push, fuzzy process kills, or deletion based only on
untracked status. Do not push cleanup branches unless separately authorized.

At each daily checkpoint, stop new tasks, let productive owned work reach one
bounded checkpoint, stop exact owned processes, commit intended artifacts, update
current notes and tombstones, record cross-lane reuse requests, run bounded gates,
and confirm no scheduler can restart work.

## Final acceptance gates

The campaign is complete only when:

- every headline has two independent semantic reviews and an adversarial check;
- every current public target has a clean exact-type/no-cheat receipt;
- the main theorem and all modelling bridges match the published meaning;
- no headline gained a hidden hypothesis or an unreviewed, unbridged change of
  definition, topology, model, normalization, or scope;
- no public proof uses forbidden proof escapes and the allowed axiom set did not
  grow;
- every published theorem target remains exact and green;
- the headline facade has a consistently applied headline criterion;
- every former headline result has a recorded disposition;
- secondary stable results remain discoverable without one giant import root;
- public mathematics no longer lives misleadingly under a scratch or experimental
  path;
- audit authority is manifest-driven rather than manually duplicated;
- every accepted simplification preserves semantics and consumers;
- every audited published definition maps to one canonical Lean definition or an
  explicitly justified distinct formal object, with no unclassified duplicate;
- every deletion has ownership, classification, replacement, consumer, and recovery
  evidence;
- failed routes remain searchable;
- open frontiers have exact restart packets;
- retained Markdown follows the ASCII/TeX rule;
- all maintained work is committed and the integration worktree is clean;
- the repository's whitespace and large-file integrity checks pass; and
- the preservation ref still resolves to the recorded baseline commit.

The final report leads with mathematical correctness and includes baseline/final
commits, headline audit table, every caveat and resolution, a headline-to-catalogue
map, architecture before/after, proof simplifications with equivalence evidence,
generalized tools and consumers, closed/refuted/open frontiers, moved/archived/
deleted paths, exact validation outcomes, resource changes, and the tasks deferred
to the second-stage publication campaign.

A smaller tree is not success if it hides a caveat or loses a warning. Success is a
more truthful, coherent, reusable proof library whose headline mathematics is
independently understood and exactly verified.
