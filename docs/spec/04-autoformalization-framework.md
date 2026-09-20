# 04 — Autoformalization framework for cflibs-formal

## 1. Position

This repo will **not** adopt Ax-Prover, LeanMarathon, AutoformBot or any prover-specific pipeline as
software. It adopts the **harness pattern** those systems and the 2026 case studies share, because
(a) the repo already runs most of the countermeasures the literature converged on, (b) its scale is one
research theorem at a time, which the cost data put at a few hundred dollars and days per dossier, and
(c) the measured failure mode for applied formalization is statement and definition faithfulness, which
no framework solves and which this repo's gates were built for. Evidence and citations: the review
document of 2026-09-20 (Drive) and its Part B tables; the NotebookLM notebook
`ef9f6127-0ff9-494d-b29c-c0baa803130b`.

The design goal is stated as a falsifiable claim: **an agent run under this harness cannot land a
statement that a seeded-drift red team would have caught, and cannot weaken a preregistered statement
without a recorded Refiner note.** If either happens, the harness has failed, regardless of how many
theorems it closed.

## 2. Tool stack (available today unless marked *to install in Phase 0*)

| Layer | Tool | Role |
|---|---|---|
| Agent | Claude Code (the tool this repo has been developed with) | general coding agent; model-swappable |
| Lean tools | `lean-lsp-mcp` (goals, diagnostics, hover, `leansearch`, `loogle`) and the `lean4-skills` plugin — *to install in Phase 0* (no `.mcp.json` in the repo and no `lean-lsp` server configured as of 2026-09-20; only the `lean@leanprover` plugin is installed); the `lean:lean-proof` plugin skill is already available | the "Prover with Lean tools" pattern of Numina-Lean-Agent / Ax-Prover / Ilin |
| Checking | `lake env lean <file>` only (never `lake build` from a worker); `#print axioms`; `scripts/mutate-check.sh`; `scripts/prereg.sh`; `lake exe axiom-audit`; `lake exe runLinter`; `scripts/stats.sh`; `scripts/kernel-replay.sh` | the gates |
| Review | `.claude/agents/lean-statement-audit.md` (adversarial statement auditor; read-only only after the Phase-0 change that drops its `Write, Edit` tools); `.claude/skills/citation-integrity` | the Target-Reviewer and literature gate |
| Isolation | `git worktree` per worker for *edits*; typechecking runs from the lead checkout (`cd <lead repo root> && lake env lean <absolute path to the worktree file>`), because `.lake` is gitignored and a fresh worktree has no oleans — this is the pattern `scripts/mutate-check.sh` already uses. A worker's new file may import only modules already built in the lead's `.lake` | LeanMarathon/AutoformBot worker isolation |
| Literature | `asta papers`, NotebookLM MCP, arXiv fetch | grounding for `## Literature` |
| Outside closers (optional, gated) | Aristotle, SorryDB participants | lemma closing and, more usefully, **disproving** false lemmas |

## 3. Roles (as skills and prompts, not a scheduler)

1. **Blueprinter.** Input: a dossier section from `03-module-specs.md`. Output: the pre-registration
   file (statement, scope tag, disclosure of prior state), the Lean *statement-only* file with
   `sorry`, and a LaTeX-level proof sketch in the dossier. Never writes tactics.
2. **Target-Reviewer.** The `lean-statement-audit` agent, run **read-only** on the statement-only file
   *before any proof search*. Compares three objects: the dossier statement, the docstring, the Lean
   type. Verdicts use the agent's own vocabulary (`passed` / `gaps_found` / `human_needed`,
   `.claude/agents/lean-statement-audit.md:105–117`), with the drift class named in the report body
   (dropped positivity, totalization vacuity, strict/non-strict flip, convention drift, wrong reduction
   target, definition misalignment, narrower than docstring). `gaps_found` returns the file to the
   Blueprinter. Two Phase-0 fixes to the agent file are required before it can serve: its frontmatter
   currently grants `Write, Edit`, which must be removed so the reviewer is read-only, and its report
   template must carry the drift-class field. This is LeanMarathon's Target-Reviewer with this repo's
   scope-tag vocabulary.
3. **Worker.** One theorem per worktree. May add private lemmas. May **not** add hypotheses to a
   preregistered statement, change a definition, raise `maxHeartbeats`, or touch `docs/`. Stopping rule:
   N failed rounds per theorem, where N = ⌊module round budget / number of statements⌋ with a floor of 3
   (so 9 cascade statements under the 40-round module budget give N = 4), or the module budget.
   Reports the exact `lake env lean` output, never a summary.
4. **Refiner.** May change the blueprint (split a lemma, add a hypothesis) only with a written
   note `docs/preregistrations/<file>.md § Deviations`, which re-triggers the Target-Reviewer.
5. **Lead (human or lead agent).** Runs every gate personally; trusts no self-report; commits.

## 4. Workflow (state machine)

```
DOSSIER ──► PREREG (prereg.sh freeze) ──► STATEMENT FILE (sorry) ──► TARGET-REVIEW
   ▲                                                                  │ gaps_found
   └───────────────────── Refiner note + re-review ◄───────────────────────┘
                                                                           │ passed
                                                                           ▼
                                 WORKER (worktree, lake env lean, budget) ──► green?
                                                                           │ yes
                                                                           ▼
   MUTATE-CHECK ──► AXIOM-AUDIT ──► RUNLINTER ──► STATS ──► ORACLE DIFF ──► SCOPE-TAG ROW
   ──► GEN-DOCS ──► PREREG AUDIT (`prereg.sh audit --results <module>.lean`, reports `PASS  FROZEN`)
   ──► STATEMENT AUDIT (final) ──► COMMIT
```

Any red at any gate returns to the Worker, never skips forward. A statement that only closes after a
Refiner deviation is labelled *exploratory* in the scope-tag citation column until re-frozen.

## 5. The red-team protocol (mandatory before the reviewer is trusted)

The Target-Reviewer is an assertion until it is shown to distinguish. Before the first pilot, run it on
a **seeded-drift set** built from `docs/conventions.md` and the drift classes reported in the
literature. For each of the four headline statements in `03-module-specs.md`, prepare one faithful and
at least four drifted variants:

| Drift class | Seed (example on S3 / L2 / K2 / stoichiometry) | Source of the class |
|---|---|---|
| Dropped positivity | remove `0 < ne`, `0 < γ`, `0 < Ntot` | Ilin (hypothesis creep), Faults paper |
| Totalization vacuity | a ratio that is `0` when the denominator is `0`; `Finset.sum` over an empty range; `ne ^ z` at `ne = 0` | LeanMarathon Target-Reviewer catches |
| Strict/non-strict flip | `StrictAntiOn` → `AntitoneOn`; `<` → `≤` | this repo's mutate-check |
| Convention drift | `log₁₀` for `Real.log` (§1); wrong partition normalization or ground-level reference (§2); `g` folded into `A` (§3); `f` for `A` (§4); thermal-bracket unit mismatch (§6); `λ⁻¹` for `λ⁻³` in the ordinate (§7); `ℕ` exponent where `ℝ` power was meant | `docs/conventions.md` §1–§4, §6, §7 |
| Wrong reduction target | S7 reducing to `sahaEquilibriumNe` instead of `multiElementIonized` | blueprint audit 01 §1.3 |
| Definition misalignment | `ContDiff ℝ ⊤` for `C^∞`; `Real.sqrt` of a possibly negative argument; `Finset.range Z` vs `range (Z+1)` | Ilin, Faults paper |
| Narrower than docstring | docstring says "all stages", statement fixes `Z = 2` | this repo's scope audit |

Blinding: the variants are authored by the lead or by a separate agent, never by the reviewer's own
session; the reviewer receives them unlabeled, in shuffled order, one file each, and its verdicts are
compared with the labels only afterwards. Pass criterion: every drifted variant is flagged with the
correct class and the faithful one is accepted, over two independent runs. Record the run in `docs/spec/redteam/<date>.md`. **If the reviewer fails,
that is the finding; no pilot proceeds.** Repeat the red team whenever the reviewer prompt or model
changes.

## 6. Budgets and metrics

- **Budget per module:** 40 Worker rounds or the dollar equivalent of one LeanMarathon paper run
  (order $300), whichever first. Record actual spend in `06-milestones.md`.
- **Primary metric:** statement faithful under an independent expert read at final audit (binary).
- **Secondary:** mutants killed / mutants seeded; hypotheses added relative to the preregistered
  statement (target 0); Refiner deviations; wall-clock; `lake env lean` rounds; dollars.
- **Report the delta** against the repo's human-directed baseline (751 results), not absolute scores.
- Never report sorry-closure or compile rate as success.

## 7. Boundary-pushing proposals (ordered by value / cost)

### 7.1 A CF-LIBS drift benchmark ("LIBS-DriftBench")
Turn §5 into a permanent artifact: for every physics module, keep a faithful statement and a labelled
set of drifted variants under `docs/spec/driftbench/`. Use it (a) to certify reviewer versions, (b) as
a regression test when models change, and (c) as a contribution to the community: the public drift
benchmarks (DriftBench, ShadowBench) are pure-math; a physics-convention drift set (log base, wavelength
power, Saha bracket sign, units) does not exist. Cost: low; it is the red-team set kept.

### 7.2 Oracle fixtures as shadow theorems
ShadowBench certifies a statement by entailment against auxiliary "shadow" statements checked in Lean.
This repo already has the numerical half: `nonvacuity_*` theorems (`ConditionNumber.lean:349–418`,
`LineSelection.lean:306–340`) and `OracleAnchors.lean` pin concrete instances by `norm_num`. Make it a
rule: **every new headline theorem ships with (i) a `nonvacuity_*` instance theorem and (ii) an oracle
scenario row that instantiates it**, and the statement audit checks that the instance actually exercises
the load-bearing hypothesis (a witness with `E = 0` does not exercise a bound in `E`; the
`EvaluatorSoundness` payoff witness is the recorded example). Cost: low; mostly policy.

### 7.3 Blueprint-attribute parity for `## Literature`
LeanMarathon and LeanArchitect keep a LaTeX statement inside an `@[blueprint …]` attribute on the
declaration and check two-way parity between prose citations and elaborator edges. Adopt the pattern
without the dependency: a repo script `scripts/check-literature-parity.sh` that, for every physics
module, (a) extracts the cited equation names from the `## Literature` paragraph, (b) requires each
headline theorem's docstring to name the equation it encodes, and (c) fails if a theorem cites a
literature item not in `docs/citation-whitelist.tsv`. Later, if physlib adopts LeanArchitect, the
attribute form can be generated from this. Cost: medium (a script), high value for upstreaming.

### 7.4 Vendored vacuity and hazard checker
The Faults-in-Benchmarking paper's checkers (unsatisfiable hypotheses, counterexample search,
ℕ-subtraction and division-by-zero hazards, unused hypotheses) are the mechanical complement to
`mutate-check.sh`. Implement as `scripts/vacuity-check.sh`: for each new theorem, generate a probe file
that (i) tries `exact absurd` / `omega` / `positivity` / `nlinarith` on the hypotheses alone to derive
`False`, (ii) flags `/`, `-` on `ℕ`, `Real.sqrt`, `Real.log` applied to unconstrained arguments, (iii)
runs `lake exe runLinter CflibsFormal.<Module>` and greps the output for `unusedArguments` (the
Batteries `runLinter` takes module names only, not a linter selector; `#lint only unusedArguments` in
a probe file is the alternative). mathlib-only, no new dependency. Cost: medium.

### 7.5 Disprove-first
Ilin's project used Aristotle to *disprove* 28 false conjectures before proving the true ones. Add a
Worker step before proof search: attempt `¬ statement` on small instances (`Fin 2`, `Fin 3`, explicit
numbers) with `decide` / `norm_num` / `nlinarith`. A counterexample is a DRIFT verdict with a witness,
which is worth more than a proof. Optional: submit the negation to an external closer; accept its output
only if it replays under `axiom-audit` locally. Cost: low.

### 7.6 Literature back-translation (MerLean pattern)
After a theorem is green, an agent informalizes it to one sentence of physics prose; the
`citation-integrity` skill compares that sentence to the cited equation in the whitelisted source. A
mismatch is a scope-tag defect (EXACT claimed, REDUCED encoded) or a definition misalignment. Cost: low.

### 7.7 Certificate-gated algorithm search (the verified-search niche)
Already built in the companion (`certificate_gate.py`, PR #408) and confirmed unoccupied in the
literature. The formal side's contribution is C15/C16 and the S8-style **a-posteriori enclosures**: a
certificate that bounds the distance to the true fixed point from a residual the pipeline can compute.
Extend the pattern to the outer loop (`outerLoop_contracts` gate) and to conformal coverage. Cost:
medium; this is where the spec "pays rent."

### 7.8 Agent-driven upstream into PhyslibAlpha (parked by decision D5: not this cycle)
Physlib now has a lighter-review tier that accepts AI-generated contributions and requires tool
independence. The Saha–Eggert seed (`upstream/SahaUpstream.lean`) and, once landed, the cascade are
single-concept PRs of the right shape. Run the harness with Physlib's conventions (unit-aware
`Temperature`, measure-theoretic ensembles) as the target dialect, keeping our discrete core untouched.
Cost: high; value: external validation of the physics by a community that is not us.

### 7.9 A physics-drift dataset contribution
Package 7.1 plus the `docs/conventions.md` hazards as a small public dataset in the DriftBench format.
This is the one place this repo can push the autoformalization literature rather than consume it.

## 8. Pilots (in order)

1. **Reviewer red team** (§5) on S3, L2, K2 and the stoichiometry corollary. Gate for everything below.
2. **Frontier 02/07 dry run** on already-closed theorems: `sahaFactor_strictMonoOn_temp` and
   `equivWidth_lorentzian_sqrt_sharp`. This pilot measures the **Worker** (proof closing within budget),
   not statement faithfulness: the statement is given, and the red team in §5 is the faithfulness test.
   To keep it uncontaminated, give the Worker a *copy* of the module with every proof body replaced by
   `sorry` and the private lemmas removed, typechecked against the lead's built `.lake` (checking out an
   older commit would need a full rebuild, since `.lake` is gitignored); the dossier text may be supplied. Ground truth exists, so
   this is the only pilot with a known answer.
3. **SahaCascade** (03 §1) as the first live module.
4. **ContinuousProfile** (03 §2), then **SpectrometerForward** (03 §3).

## 9. What not to do (from the case studies)
- No `set_option maxHeartbeats` above default without a written reason (Ilin's "excessive heartbeats").
- No hypothesis added by a Worker (Ilin's 42; AutoformBot's "weakening hypotheses").
- No LLM judge as an equivalence oracle (Beyond Compilation); it is a screen, the audit is the verdict.
- No external prover output accepted without local axiom-audit replay (AutoformBot's hidden axioms).
- No proof-side tooling (SMT bridges, CAS packages) as dependencies; `linear_combination`/`polyrith`
  cover the certificate pattern inside mathlib.
- No success claim phrased as CF-LIBS accuracy.
