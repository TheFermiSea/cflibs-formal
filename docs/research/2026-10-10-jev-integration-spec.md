# Jev integration spec for the proof queue, the statement audit and the companion search

**Date:** 2026-10-10. **Status:** exploration spec for the agents that work in this repository.
Nothing here is decided; no decision row is proposed. **Audience:** an agent that has read
`AGENTS.md` and `CONTEXT.md` and is about to pick up one of the experiments in section 8.

Evidence tags used below: `[measured]` was run for this spec (section 9). `[read]` means a file or
page was opened this session. `[claimed]` is a third party's own number, not reproduced.

Disclosure (D23): this repository is public and the companion is private. The companion appears here
by path and symbol only. No host names, absolute paths, costs or backlog ids are used.

## 1. Goal

Find the few places where a fast typed judgment makes the existing search loops cheaper or safer,
and measure each against labels this repository already holds before anything acts on it.

The non-negotiable boundary: **Lean decides truth; the exact gates decide acceptance.** A Jev
answer may reorder work, route it, flag it or ask for a human. It may never accept a proof, clear a
statement audit, raise a scope tag, or lower a gate. Every use below is "ratchet-only": the worst
case of a wrong answer is the behaviour we have today.

## 2. Jev in one paragraph

Jev (TypeSafe's System One model, pinned here as `jev-1.13.0`) is not a chat model. One request,
`POST /v1/systemone`, carries a JSON `state` and a map of typed `questions`: a **Noul** (yes/no with
a probability), a **Choice** (one option from a set, with a distribution and a confidence) or a
**Score** (a position on an ordered scale). Latency is about 200 ms and the price per decision is
very small `[measured]`: 48 requests took a median 180 ms (p90 203 ms), 103,720 input tokens in
total. Known weaknesses: arithmetic, counting and comparing numbers; long irrelevant context;
sensitivity to option order in Choice questions; probabilities returned on a 0.01 grid, so ties are
common. It is useful for typed judgment over unstructured state that code then acts on. It is a bad
fit for anything with an exact checker.

## 3. What already exists here, and what this spec builds on

| Piece | State | Source |
|---|---|---|
| `tools/judgments/judgments.py` | On `main`. Noul-only client, mode-600 key file (never the environment), pinned model, append-only JSONL cache keyed by (set, version, model, text), AUC with a bootstrap interval, `lessons`. The companion vendors it verbatim | `[read]` |
| `tools/judgments/proof_runs.py` | On `main`. Post-mortem of proof-queue runs in two layers kept apart: exact counts (no model) and six judged traits of the planner's final whiteboard | `[read]` |
| Result of that post-mortem | Whiteboard trait "informal proof done" against `PROOF.md` existing: 31 of 32 when yes, 1 of 16 when no. "Ends with an unresolved Lean error" against verified: 1 of 14 when yes, 13 of 22 when no, which the author correctly labels descriptive, not predictive, because a final whiteboard reflects the outcome | commit message of `0b7d612`, PR #20 |
| Companion side | Unmerged companion work reads a kernel's design into nine yes/no traits and uses them as search-archive axes and as "lessons" appended to the proposer's problem statement, all opt-in. Its own finding: a model call per proposal is not worth it, because a rejected candidate costs 2 to 9 seconds at the exact checks. The value found was in describing candidates, not in screening them | companion `tools/cflibs_evo/design_traits.py`, `scripts/evo/design_report.py` |

So Jev work started with **post-hoc description**. This spec moves to **prospective decisions**, and
adds Choice and Score, which `judgments.py` does not speak.

## 4. How the search loops run today (the places a decision could sit)

1. **Statement pipeline.** A frontier item is drafted into `statement.lean` (one `sorry`) plus a
   `dossier.md`; a Mode B statement audit (`.claude/agents/lean-statement-audit.md`, a Claude
   reviewer that emits `verdict`, `edit_class`, `mechanism_class`) must pass before it enters the
   queue. The audit is Gate 5 of `AGENTS.md`: judgment, not automated.
2. **Proof queue** (`tools/openprover/queue/`). A supervisor claims a target, runs OpenProver with a
   planner (Claude under a daily cap, or the local model) and local workers, two attempts per node,
   `max_attempts` per target (default 2), then `verify.py` re-verifies independently (forbidden
   tokens, imports, verbatim definitions, compile, kernel replay, axioms, `pp.all` type). A new
   attempt starts from the previous attempt's furthest-compiled Lean items (carry-forward). Targets
   end in `done`, `parked` or `held`. Search-loop breakers and token caps are rules in the harness.
3. **Landing.** A verified candidate is hand-landed through a PR; docstring, scope tag
   (`docs/scope-tags.tsv`) and theorem card are reviewed; the owner spot-checks EXACT cards (D24).
4. **Oracle and companion.** `oracle/` fixtures and `docs/integration/` certificate mirrors are what
   the companion's evolutionary kernel search is scored and gated against (hard constraints a
   candidate cannot fake). That population lives in the companion, not here.

No loop here is a population search in the evolutionary sense; the nearest thing is two attempts per
target with carry-forward, and the 16-variant red team (a seeded-drift population for the auditor).

## 5. Decision points, ranked

Ranking weighs: value if right, labels already held, how bad a wrong answer is, and whether an exact
rule would do the job instead.

### DP1. Statement-versus-docstring fidelity sweep (rank 1)

- **State Jev sees.** One declaration: its docstring, its printed type and binder names (both are in
  `docs/catalog.jsonl`, 1138 declarations), and its scope-tag row. Not the proof, not the module.
  A few hundred tokens, so the long-context weakness does not apply.
- **Questions** (one request, three questions).
  `outruns` Noul: "Does the docstring claim more than the printed statement proves?"
  `hypothesis_gap` Noul: "Is a hypothesis the docstring names missing from, or weaker in, the
  printed type?"
  `drift` Choice over the repository's closed drift classes
  (`none`, `dropped_positivity`, `totalization_vacuity`, `strict_nonstrict_flip`, `convention_drift`,
  `wrong_reduction_target`, `definition_misalignment`, `narrower_than_docstring`), asked in two
  option orders (section 6).
- **Action.** A ranked worklist for `lean-statement-audit` and for the human reviewer: audit the top
  of the list first, and add a "second look" note on the card. Jev **never clears** a declaration,
  never lowers a finding, never edits a docstring.
- **Replaces.** Nothing. Gate 5 is today a one-off sweep per review round
  (`reviews/`, `docs/research/audit-2026-09-24/`) plus per-target audits. The cardinal rule (a
  docstring must not claim more than its theorem proves) has no standing automation at all.
- **Labels already held.**
  L1: the 16 seeded-drift variants with `edit_class` and `mechanism_class` labels
  (`docs/spec/redteam/2026-09-22/` on the draft spec branch, PR #5; not on `main`, so step 0 of E1
  is moving that corpus onto `main`, consistent with D22).
  L2: the 2026-09-24 audit register, `docs/research/audit-2026-09-24/audits.json`: 147 findings,
  of which 24 `docstring_overclaim`, 23 `faithfulness` (all CONFIRMED), 15 `vacuity`, 9 `scope_tag`,
  each with a `location`. The state must be reconstructed from the audited commit, not from `main`,
  because the P0 batch fixed many of them.
  L3: docstring-only fix commits since (for example the four docstrings qualified after review of
  PR #22): the declaration at the parent commit is a positive.
  L4: negatives are the audited-and-passed declarations of the same modules.
- **Result of the feasibility probe** `[measured]`: section 9.1. In short, 10 of 12 seeded drifts
  flagged and 0 of 4 faithful files flagged at a 0.5 cut, AUC 0.875, misses are the two subtle ones.
  That is weaker than the Claude reviewer (12 of 12 and 4 of 4 in run 3), so Jev is a coverage and
  ordering tool, not a second auditor.

### DP2. Queue target routing and attempt budget (rank 2)

- **State.** `statement.lean`, the head of `dossier.md` (cap about 6000 characters, see the probe's
  truncation lesson), and `target.json`. Never the whiteboard of a running attempt.
- **Questions.** Noul `proof_given` ("the dossier lays out the full chain of steps and names the
  lemmas, so the remaining work is transcription"); Noul `needs_new_theory` ("spectral theory,
  measure theory, asymptotics, long case analysis or auxiliary definitions beyond the statement");
  Noul `elementary_algebra`.
- **Action.** Before any attempt: suggest the attempt budget (`max_attempts`) and whether a planner
  choice is worth its cost (the policy is the owner's, D20; Jev only informs it), or move the target to `held` with the note "dossier needs a proof
  route" instead of spending hours. Advisory first: the note goes in `status.json` and the lead's
  view; nothing is blocked.
- **Replaces.** A uniform `max_attempts = 2` and the lead's manual guess about which dossiers are
  ready. It does not replace `held`/`parked` decisions made on run evidence.
- **Labels.** `supervisor.log` and `verdict.json` give, per target: verified at attempt 1,
  verified later, parked, with hours. `docs/archive/openprover/` holds scrubbed verdicts for 15
  targets. The supervisor log names 70 target ids, 61 of them outside the planner pilots; 36 of those 61
  were verified at attempt 1.
- **Confounds to control.** Planner and worker model changed over the period; many dossiers
  contained a complete proof (the batch-4 PR says so); parked dossiers are longer (13 to 22 KB
  against 5.6 to 18.5 KB for the first-try ones in the probe), so **dossier length is the baseline every trait has to
  beat**.
- **Probe** `[measured]`: section 9.2. Directionally promising on `needs_new_theory`, not proven.

### DP3. Mid-run stall and statement-doubt signal (rank 3)

- **State.** The planner's whiteboard at step k (already produced by OpenProver), not only the final
  one. The existing six traits in `proof_runs.py` are reused unchanged.
- **Questions.** The existing Noul traits `stuck_on_lean_detail`, `statement_doubted`,
  `worker_output_lost`, evaluated at fixed step indices.
- **Action.** `statement_doubted` yes routes the target to the statement-audit agent and a numeric
  counterexample search (the `oracle/` style falsification) before more tokens are spent; a yes on
  `stuck_on_lean_detail` for N consecutive checkpoints can end the attempt early and keep its
  carry-forward items. Both are advisory in shadow.
- **Replaces.** Wall-clock and token caps as the only stop rules (the 9 h wall guard, the token
  budget) and the search-loop breaker, which is a pattern rule.
- **Labels.** The exact layer of `proof_runs.py`: verified or not, empty-worker counts, calls ended at
  the per-call cap. The existing result says the final-board traits describe; this tests whether
  step-k traits **predict** the end state, which is the only version worth acting on.
- **Why rank 3.** Needs the queue running again and many runs; the data for k < final exists in the
  run records but only for completed runs.

### DP4. Claims that outrun the evidence in prose (rank 4)

- **State.** One claim at a time: a sentence from a theorem card's scope narrative, a decision-ledger
  row, a change-log line or a PR body, plus the evidence it cites (the Facts block or the gate list).
  Not a whole document.
- **Questions.** Noul `claim_exceeds_evidence`; Noul `states_status_not_shown` ("says merged, landed,
  green or verified without the named evidence").
- **Action.** A comment-style note on the draft PR or card review. Never blocks.
- **Replaces.** The reviewer's attention for claims in prose; `scripts/check_cards.py` already checks
  structure, anchors and hashes exactly and stays the gate.
- **Labels.** Thin. Known real overclaims fixed after the fact: the spec change-log correction that
  said PR #6 had landed before it was merged; the four docstrings qualified after review of PR #22;
  the card text that wrongly called a landed theorem "parked". Fewer than 30 positives, so this is
  a canary set, not a benchmark.

### DP5. Strategy descriptors for the second queue slot (rank 5, speculative)

- **State.** The first slot's `PROOF.md` or compiled lemma list (not the whole run).
- **Question.** Choice over proof families for a target class (direct computation, monotonicity or
  convexity argument, induction, contraction, case split, counterexample construction).
- **Action.** Tell the second slot's planner which family the first slot already tried, so the two
  attempts per node differ. Companion experience says trait descriptors help a search archive;
  nobody here has shown it for proof attempts.
- **Labels.** Needs dozens of targets with both slots run; today the second slot is the local
  planner by policy, so the comparison is confounded by planner. Do not start before DP1 and DP2.

### DP6. Candidate descriptors for the companion's population (not built here)

The companion's kernel search already uses Jev traits as archive axes and as lessons, opt-in. The
only obligations in this repository are: keep `tools/judgments/judgments.py` byte-stable (the
companion vendors it and checks a digest), and add new capability beside it, not inside it, unless
the vendored copy is bumped in the same step. Fitness in that search stays the exact Lean-twinned
relations and fixtures. A Jev answer is a behaviour descriptor, never a fitness term.

## 6. Where Jev is a bad fit (do not build these)

| Idea | Why not |
|---|---|
| Accepting or scoring a proof | `verify.py` and the kernel exist; the 2026-09-24 audit forged three proofs past a text-only check. Any model verdict is weaker than that. |
| Triage of a failed `lake` build by error category | Lean's message head (`unknown identifier`, `type mismatch`, `unsolved goals`, `failed to synthesize`, `linarith failed`) is already a typed discriminator and a regex reads it for free. Only the `unsolved goals` residual (false goal versus tactic gap) is a judgment, and that is DP3's `statement_doubted`. Not probed, for this reason. |
| Premise or tactic selection | Retrieval over Mathlib, with `exact?`, Loogle and the Lean language server, returns candidates that Lean checks in seconds. Jev has no Mathlib index and degrades on long context. At most a Noul relevance rerank of a retrieved short list, and only after measuring it against the retrieval order. |
| Pre-screening a candidate before `lake env lean` | The companion measured that the exact check is cheaper than a call. Same here: a compile is seconds, kernel replay about 15 s. |
| Numeric comparison against the Python oracle | Arithmetic and number comparison are Jev's stated weaknesses; `oracle/check_fixtures.py` is exact. |
| Choosing which cards the owner spot-checks | D24 is a deterministic rule (relation tag EXACT). A model adds nothing. |
| Scope-tag assignment or promotion | Raising a tag needs an owner decision (`docs/decisions.md`). Jev may flag a tag as too strong; it may not set one. |

## 7. Integration architecture

All of it standard library, no new dependency, no change to the Lean build (non-negotiable 2 is
about Lean imports, but keep the Python equally small).

**Client.** Reuse `JevClient`; add Choice and Score support in a **new module** beside
`judgments.py` (for example `tools/judgments/typed_ask.py`) so the vendored file keeps its digest.
Validate that a Choice answer is one of the offered options and that a Noul lies in [0, 1], as the
rust-daq client does. Pin the model; refuse an answer from another model id (already done). Add a
request-shape rule: **one declaration or one target per request, many questions per request**.
Packing many rows into one `state` drifts rows deep in the batch `[claimed]` (jev-orderby-bench).

**Redaction before sending.** The state leaves the machine. Declarations, statements and dossiers are
public text already. Run whiteboards and run logs can contain node names, addresses and paths: strip
them first (the D23 scrub list is the spec), and never send companion source without an owner
decision on that repository's side.

**Cache.** Keep the JSONL cache keyed by (set, version, model, text). Treat answers inside 0.35 to
0.65 as "no verdict", the existing `UNCERTAIN` band, so run-to-run drift of a few hundredths cannot
flip a decision. Invalidate on a model-id change.

**Option order.** Ask every Choice in two orders (forward and reversed) and act only when both agree;
report the flip rate as a standing metric. Measured here: 15 of 16 stable (section 9.1). Rotation
marginalisation (AnyJev) is the upgrade if questions grow past five options.

**Decision log.** One JSONL record per decision, written outside the repository: decision point id,
question-set version hash, model, a hash of the state (not the state), the answers, the action that
was recommended, the action taken, and later the outcome label joined by target or declaration id.
Bounded size with rotation. Only aggregate reports are committed.

**Kill switch and failure.** A single off switch (`CFLIBS_JEV=off`) and one per decision point; no key
file means off; a circuit breaker opens for a couple of minutes after a failure. Every failure path
returns "no judgment" and the caller does exactly what it does today. The key is read from a mode-600
file only and never printed, cached or logged (existing behaviour; keep the test).

**Shadow, then advisory, then gated.**

| Level | Behaviour | Moves up when |
|---|---|---|
| S0 offline replay | Judge historic items, score against labels, no live effect | E1 passes its gate |
| S1 shadow | Live calls on new items, log the would-be action, nobody sees it | 4 weeks and the criteria in section 10 |
| S2 advisory | The recommendation is shown to the lead or reviewer, with its probability | Reviewers act on it and outcomes still match |
| S3 gated | Only ratchet-safe actions: reorder, hold-for-review, add a note | Never extends to accept, clear or lower |

**Evaluation harness.** Do not invent one; port the shape of the owner's rust-daq `tools/jev-eval`
(draft branch, `jev_eval.py` and `jev_opt.py`): cases are a state plus labelled truth plus **label
provenance** (seeded, mined from history, human, agent); variants are the question text, so one
labelled set scores any wording; train and holdout are split by a **group hash** (group = module for
DP1, target for DP2 and DP3, because attempts at one target are not independent); report accuracy,
Brier and log loss with probabilities floored at 0.005 (the grid is 0.01), ECE next to its noise
floor, reliability bins, a threshold chosen on train and reported on holdout, a Choice
option-reversal check, a replay backend and a disk cache so reruns are free. Put it under
`tools/judgments/` with its own `pytest` tests and no network in tests. Pre-register the acceptance
gate before running (`scripts/prereg.sh`, `docs/preregistrations/`; a frozen pre-registration is
never edited).

**Trivial baselines are part of the harness.** DP1: a regex for strong words in the docstring
("every", "all", "exactly", "iff", "always", "strictly") and docstring length. DP2: dossier length
and statement length. DP3: remaining token budget. A trait that does not beat its baseline is not
promoted.

## 8. Experiments, in order

- **E1 (first; DP1, offline).** Details in section 10.
- **E2 (DP2, offline then shadow).** Extend the probe to all 61 non-pilot target ids with a
  pre-registered question set (questions fixed before reading any answer, unlike the probe), group by
  target family (`FT01`, `FT13`, ...), baseline dossier length, and report era as a covariate.
  Shadow on the next 20 queued targets.
- **E3 (DP3).** After the queue runs again: record whiteboards at fixed steps, test whether step-k
  traits predict the end state, compared to token-budget-remaining.
- **E4 (DP4).** Build a canary set of known prose overclaims from history; run as a shadow comment
  on draft PRs only.
- DP5 and DP6 wait on E1 and E2.

## 9. Feasibility probe `[measured]`

Cap 50 requests; 48 used, no failures, no retries. Model `jev-1.13.0` on every answer. The key was
read at run time from a mode-600 file and never printed. Probe code and raw answers were kept
outside the repository; they are reproducible from the inputs named here. Latency median 180 ms.

### 9.1 DP1 on the 16 red-team variants (32 requests)

State: the variant's `.lean` file (statement plus docstring, about 1 KB). Questions: a `faithful`
Noul and the eight-way `drift` Choice, asked forward and in reversed option order.

| Quantity | Result |
|---|---|
| AUC, mean `faithful` probability, faithful (4) versus drifted (12) | 0.875 |
| Drifted flagged at probability below 0.5 | 10 of 12 |
| Faithful files flagged at 0.5 | 0 of 4 (2 of 4 at 0.65) |
| Missed drifts | `v03` (`Matrix.vecMul` argument order makes the kernel a transpose, probabilities 0.69 and 0.70) and `v14` (`lorentzianG (γ^2)` instead of `lorentzianG γ`, 0.70) |
| Choice equals the labelled edit class, forward and reversed | 12 of 16 and 11 of 16 |
| Choice argmax unchanged when the option order is reversed | 15 of 16 |
| Choice with its own confidence at least 0.5, forward | 11 answered, 10 correct; 5 abstained, of which 3 were wrong |

Reading. The two misses are exactly the ones that need semantic knowledge of a library function
or a convention, which is the weakness Jev is documented to have; the reviewer found both. One
faithful file (`v10`) drew a low-confidence false alarm from the Choice (`definition_misalignment`,
confidence 0.37) while its Noul was 0.58 and 0.47. Confidence below 0.5 tracked most errors, which
supports abstaining on it. n is 16 and the variants are the author's own seeded edits, so this
shows feasibility of the flagging, not a calibrated rate. Seeded edits are also syntactically
unnatural, so real overclaims in prose docstrings may be harder (that is what L2 and L3 test).

### 9.2 DP2 on 16 queue targets (16 requests)

State: `statement.lean` plus the first 6000 characters of `dossier.md`. Labels: 8 targets verified at
attempt 1, 8 targets parked without a verified proof. Three Noul questions in one request.

| Trait | AUC for "verified at attempt 1" (n = 16) |
|---|---|
| `needs_new_theory` (declared direction: yes lowers it) | 0.04, that is 0.96 for "not first try" |
| `proof_given` | 0.83 |
| `elementary_algebra` | 0.75 |
| Baseline: dossier shorter | 0.86 |

Reading, with the caveats that matter:
- The question set was written after seeing which targets were parked and how long their dossiers
  are, so these numbers **describe** and do not test. The question set for E2 must be frozen first.
- n = 16 and attempts at one target family are correlated. No interval is reported because the
  repository's own rule (`MIN_CLASS = 10` per class) calls this not testable.
- The dossier was cut at 6000 characters. Two first-try targets got `proof_given` = 0.04, because
  their proof route sits beyond the cut. That is the long-context weakness showing up, not a
  property of the targets. Summarise first or send the section that holds the route.
- The era confound (different planners and workers) is not controlled.
- `needs_new_theory` did separate the groups better than length, but length is free and nearly as good.
  The honest conclusion is "worth a pre-registered run", nothing more.

### 9.3 Not probed

Lean error triage (regex covers it, section 6), the DP1 sweep on the real catalog (labels need
mapping from the audit register, E1 step 2), DP3 (needs mid-run boards), DP4 (labels too few).

## 10. First experiment E1 and promotion criteria

**E1: offline replay of DP1 on three label sets, nothing live.**

0. Land the red-team corpus on `main` (`labels.json`, the sixteen `.lean` files, `score.py`) under a
   `tools/judgments/cases/` directory, scrubbed per D23. It is currently reachable only through the
   draft spec branch.
1. Write `tools/judgments/fidelity.py`: the DP1 `TraitSet` plus Choice, state builder from a
   `docs/catalog.jsonl` row (or from source at a historic commit), harness from section 7, tests with
   a fake opener (no network).
2. Build L2 and L3: map the 71 docstring-overclaim, faithfulness, vacuity and scope-tag findings of
   `audits.json` (and the post-review docstring-fix commits) to declarations at the audited commit.
   Record the mapping rule and its failures; findings that name a file range instead of a
   declaration are dropped and counted. Negatives are the other declarations of the audited
   modules, sampled, with a note that "not reported" is not "faithful".
3. Pre-register the gate (`scripts/prereg.sh`) before the first call. Split by module group hash.
4. Run: 71 positives plus sampled negatives, each in both option orders, so a few hundred requests. Report
   per label set: AUC with interval, recall at the top 10 and 20 percent of the ranking, order flip
   rate, ECE with noise floor, against the two regex baselines.
5. Report the cases Jev ranked high that no label covers; hand them to the statement-audit agent
   blind to Jev's reasons. If the audit confirms even one new defect that no review found, that is
   the strongest evidence this work can produce.

**Promotion criteria, DP1, S0 to S1** (all pre-registered, none negotiable afterwards):
- On the holdout groups, the lower bound of the AUC interval for `outruns` or `hypothesis_gap` on L2
  is above 0.65 and above both regex baselines' point estimates.
- Recall of confirmed defects in the top 20 percent of the ranking is at least 0.5 with a Wilson
  lower bound reported.
- Choice flip rate under option reversal is at most 10 percent; on L1 at least 10 of 12 flagged and
  at most 1 of 4 faithful flagged (the probe's level, held, not improved).
- Calibration is reported; if ECE is within its noise floor, thresholds use probabilities, otherwise
  ranks only.
- Zero effect on any gate; the kill switch is tested; a fake-opener test proves that with no key or
  with the switch set the pipeline is byte-identical to today.

**S1 to S2:** four weeks of shadow, at least 30 new or changed declarations judged, reviewers
inspecting the top of the list at least once, no loop-safety incident, and at least one reviewer
action that the ranking changed. **S2 to S3:** only reorder and hold-for-review actions are ever
allowed; promotion needs the owner. **DP2 criteria** are analogous: the trait must beat dossier
length on frozen questions over at least 40 targets, grouped by family, and shadow on 20 new targets
must show the recommendation would have changed at least one planner or budget choice for the better.

**Stop conditions.** Stop DP1 if the top-20-percent recall on L2 is not above the best regex
baseline, or if reviewers report the ranking as noise (cf. the published one-week removal below).
Do not tune questions on the holdout; question edits happen on train only.

## 11. What to borrow from the awesome-jev list

Source list: <https://github.com/yibie/awesome-jev>. It has **no entry** for theorem proving, Lean,
proof search or evolutionary search, and its "Scientific Pipelines" category was empty when read
`[read]`. Everything below is a transferable evaluation or safety pattern. Facts were checked with
`gh api` on 2026-10-10; "calls Jev" means the source references the TypeSafe API or SDK.

| Repo | Take | Calls Jev | Tests | License | Caveat |
|---|---|---|---|---|---|
| [sutro-sh/jev-align](https://github.com/sutro-sh/jev-align) | Optimise question components (`instructions`, true and false criteria) with GEPA on labelled rows; pick the next rows to label by ambiguity plus a random audit slice | yes, `src/jev_align/jev.py` | 21 test files | Apache-2.0 | Experimental; its label-free "squash" mode rewards confidence, not correctness: do not copy it |
| [gepa-ai/gepa](https://github.com/gepa-ai/gepa) | The search engine behind the above, if a Pareto search over question wordings is wanted | n/a | yes | MIT | Verify the API with `npx ctx7@latest` and pin the version before use (project rule) |
| [ckorhonen/jev-lint](https://github.com/ckorhonen/jev-lint) | Dev and holdout case files per rule pack; rules expressed as typed questions; honest CIs | yes | 376 test and eval files | MIT | Authors' own rules and tasks |
| [abhixhek/jevcal](https://github.com/abhixhek/jevcal) | Pick a threshold by maximising coverage at a target accuracy with a Wilson lower bound; per-answer accuracy | yes, `src/jevcal/providers/typesafe.py` | 3 test files | MIT | Created and last pushed on one day; port the idea, read the code before reuse |
| [nikkoxgonzales/jev-certify](https://github.com/nikkoxgonzales/jev-certify) | PPI++ and conformal risk control for scarce labels (our n is tens) | not found in the files I sampled (it reports using a gateway) | 5 test files | MIT | One-day scaffold; run its tests in a throwaway directory before vendoring; it reports honestly when a bound is infeasible |
| [nokia-applied-research/AnyJev](https://github.com/nokia-applied-research/AnyJev) | Marginalise a Choice over cyclic rotations of the options to remove order bias | no (open local models) | 64 test files | Apache-2.0 | Technique only; its numbers are for 7 to 8 billion parameter models, not Jev |
| [AnthusAI/Jev-Calibration](https://github.com/AnthusAI/Jev-Calibration) | Isotonic or Platt recalibration, a 0.005 probability floor, several paraphrases in one request | yes, `jev_calibration/jev_client.py` | 1 test-ish file | **none** | No license: re-implement, do not copy; below about 50 labels treat calibrated output as diagnostic |
| [yodablocks/jev-orderby-bench](https://github.com/yodablocks/jev-orderby-bench) | One row per request; tie reports; pre-registered gate | yes, `harness/client.py` | 3 test files | MIT | Small |
| [scienthoon/jev-ood-calibration](https://github.com/scienthoon/jev-ood-calibration) | Floor at half a grid step; ECE beside its noise floor; separate calibration per question type | via a gateway (README) | 0 test files | MIT | Has a published correction to its first release |
| [qkal/Canny](https://github.com/qkal/Canny) | "Facts block, judgments only add notes"; content-hash cache; replay with no network | yes | 89 test-ish files | MIT | Reports no outcome improvement in its own bench |
| [valentynkit/jev-belay](https://github.com/valentynkit/jev-belay) | An exact gate decides whether Jev is asked at all; block caps | yes | 69 test-ish files | MIT | Labels written by a model, 12 positives |
| [Kiln post](https://kiln.tech/blog/auto_optimizing_jev_with_autoresearch) | Method: develop on one half, never read the other, accept only gains above run-to-run noise | n/a (blog) | n/a | n/a | One task; not reproduced |
| [Yifan-Lan/awesome-jev-robustness](https://github.com/Yifan-Lan/awesome-jev-robustness) | Reading list on option order, wording, batching and calibration | n/a | n/a | CC0-1.0 | Every entry is a third party's claim |
| [shimo4228 write-up](https://dev.to/shimo4228/is-there-any-point-to-this-removing-the-jev-plugins-i-added-to-claude-code-after-one-week-49eh) | Negative result: 1,242 decisions, 5 percent followed, plugin removed after one week | n/a | n/a | n/a | `[claimed]`; the reason to measure follow-through (DP2 notes, DP1 worklists) |

Not borrowed: anything that wraps a model gateway in front of inference, and any "open alternative to
Jev" model, because the question here is where a judgment helps, not which model supplies it.

## 12. Risks

- **A green number from a seeded benchmark.** Seeded edits are unnatural. L2 and L3 are real defects
  but are agent-found and agent-verified, and "not reported" is not "faithful". Report metrics by label
  provenance and do not pool them.
- **Leakage between state and label.** Parked dossiers can say they failed; whiteboards report the
  outcome. Strip run-outcome text from every state and test that the strip is applied.
- **Circularity.** Using Jev to tune questions on labels that an agent wrote, then to rank the
  agent's next review. Keep holdout groups untouched until the end, and keep a human-labelled slice.
- **Automation bias.** A ranked list is read as a verdict. Always show the probability, the band, and
  the sentence "Jev never clears". Measure follow-through, as the published removal story warns.
- **Option-order and grid effects.** Order sensitivity on Choice, 0.01-grid ties, a 0.05 drift
  between identical calls. Two orders, a no-verdict band and a content cache address these; the
  logged flip rate says whether they suffice.
- **Long context.** Truncation hid proof routes in the probe. Send the smallest state that carries the
  decision.
- **Data leaving the machine.** Public Lean text is fine; run logs are not until scrubbed; companion
  source is the companion owner's call.
- **Model drift.** The model is pinned, but the pin can be retired. Keep a fixed probe set (the 16
  variants) rerun on a schedule with tolerance comparison, not hashes.
- **Scope creep into acceptance.** The recurring temptation is "if Jev says the statement is
  faithful, skip the audit". Rejected by section 1; a test should fail if any code path maps a Jev
  answer to a pass.
- **Cost of the labels, not the calls.** Calls are nearly free; the human time is reviewing the
  ranking. E1 step 5 is where that time goes, so size it up front.
- **Concurrency.** Other sessions share this repository's checkout and the queue state; run
  experiments from a throwaway worktree and never write run records or caches into the shared tree.

## 13. Open questions for the owner

1. Is moving the red-team corpus from the draft spec branch to `main` (E1 step 0) acceptable under D22?
2. May `judgments.py` gain Choice and Score directly, with a coordinated bump of the companion's
   vendored copy, or must new capability live beside it (this spec assumes beside it)?
3. Is the public repository allowed to hold decision-log aggregates derived from run whiteboards
   once scrubbed per D23?
4. Should DP2 ever be allowed to act on planner choice, which is a D20 decision, or stay advisory
   permanently?
