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
| Orchestrator / Lead / Blueprinter / Target-Reviewer | Claude Code on the owner's subscription (decision D8) | the roles where statement faithfulness is judged; the only paid inference |
| Worker model | **Leanstral 1.5 (119B-A6B, Apache-2.0)** served by llama.cpp on one infer-0x node, Q6_K primary / Q4_K_M speed fallback (decision D6; evidence in §10) | local proof search; zero marginal dollars |
| Worker harness | **OpenProver** (MIT, `pip install openprover`, `--headless --autonomous --lean-project . --lean-theorem <file>`, `lean_verify` = `lake env lean`), patched so a worker alias binds to the local llama-server endpoint (decision D7; §10.4). Comparison arm: Mistral Vibe in programmatic mode (`vibe -p <prompt> --agent lean --yolo --max-turns N --output json`) with a local `api_base`; fallback: Pi agent via RPC | drives the local Worker with Lean tools and reports the exact compiler output |
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
3. **Worker.** The local model (D6) inside the Worker harness (D7); one theorem per worktree. May add private lemmas. May **not** add hypotheses to a
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
compared with the labels only afterwards. Pass criterion: every drifted variant is flagged
(`gaps_found`) with the seeded class as its dominant `drift_class` **or** as a secondary finding, and
every faithful one is accepted (`passed`), over two independent runs. Labels carry **two** classes per
variant, the *edit* (what was changed) and the *mechanism* (why the statement breaks, e.g. Lean's
`x / 0 = 0`), because the two can have different names in the table above and a reviewer that names
the edit and reports the mechanism as a secondary finding, with the refutation executed, has done its
job. (Amended 2026-09-20 after the first run: the original one-label rule scored 10/12 on both models
for that reason; see `docs/spec/redteam/2026-09-20.md`.) Record the run in `docs/spec/redteam/<date>.md`.
**If the reviewer fails, that is the finding; no pilot proceeds.** Repeat the red team whenever the
reviewer prompt or model changes. Ask the reviewer to leave its probe files in place so a verdict can be
replayed.

## 6. Budgets and metrics

- **Budget per module:** 40 Worker rounds or the wall-clock/node-hour cap in `06-milestones.md`,
  whichever first. With a local Worker the marginal dollar cost is near zero; the subscription pays only
  for orchestration and review, so budgets are expressed in rounds, wall-clock hours and node-hours.
  Record actual usage in `06-milestones.md`.
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
   `equivWidth_lorentzian_sqrt_sharp`, run as an A/B: **Leanstral 1.5 (Q6_K, then Q4_K_M)** against the
   **Qwen3.8-27B control** already on the fleet, same harness, same round cap, cache-busted prompts
   (`tools/bench_cachebust.py` discipline: repeated prompts inflate llama.cpp speculation and lie).
   This pilot measures the **Worker** (proof closing within budget),
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

## 10. Local Worker model and harness selection (evidence, 2026-09-20)

Decisions D6–D8 (README) rest on this section. Every row was checked against a primary source on
2026-09-20 (model card, repo README, arXiv abstract/HTML, or a command on the infer nodes); rows from
search-engine summaries only are marked UNVERIFIED.

### 10.1 Hardware and the serving constraints that decide everything

Three VMs `infer-01/02/03`, one **Tesla V100S 32 GB** each (Volta, sm_70: fp16 only, no bf16, no
FlashAttention-2 kernels), 36 vCPU, 251 GB DDR4, 100 Gb/s InfiniBand, 3.6 TB free under `/mnt/models`.
Serving stack is **llama.cpp** (`/opt/llama.cpp-master` build 10326 on all nodes; `/opt/llama.cpp-flashnext`
build 10674 on infer-03), one `llm-server@<model>` unit per node, launch scripts `/usr/local/bin/run-<model>`,
fleet conformance asserted by `/root/verify-node.sh` (must stay byte-identical across nodes; it checks
driver, GPU, IB, `/mnt/models` mount, llama.cpp build flags, vCPU and NUMA counts — it does **not**
inspect `run-*` scripts). The "approved node-spec plan" file a fleet memory note points at no longer
exists on disk; the operative provisioning artifacts are the `run-<model>` launcher template and
`verify-node.sh`. Measured constants that bound any plan (from the fleet memory notes, not re-derived):

- Decode of any model larger than 32 GB is **DRAM-bound at ~92 GB/s** (STREAM Triad, interleaved); a
  6.5B-active MoE at Q4 moves ~4 GB/token, so expect **~20–25 tok/s** single-node; at Q6_K ~15 tok/s.
  `numactl --interleave=all` is mandatory (+35% decode).
- Two-node RPC over IB beats single-node **only when the pooled 64 GB VRAM removes CPU offload**
  (+50–99% measured on a 36 GB model); a 72 GB Q4_K_M does not fit 64 GB, so RPC is a Phase-0
  experiment, not a design input.
- Repeated-prompt benchmarks inflate throughput by feeding llama.cpp's n-gram/MTP speculation; use
  `tools/bench_cachebust.py` (cache-busted) for every measurement.
- Owner's standing constraints: **Q4 is the quantization floor; quality beats tok/s; provision only via
  the node-spec pattern and re-run `verify-node.sh` on all three nodes afterwards.**
- Already on disk: `Qwen3.8-27B` Q6_K (22 GB, the fleet default, ~54 tok/s on novel prompts),
  `DeepSeek-V4-Flash` UD-Q8_K_XL (178 GB, 9.3 tok/s, retired from serving 2026-08-14),
  `Qwen3.8-Flash-Next` (106 GB, rejected 2026-08-28). All four llama.cpp builds on infer-01 already
  contain the `mistral4` architecture (`rg -c mistral4 src/llama-arch.cpp` = 2 in each), which the
  Leanstral GGUF requires.

### 10.2 Candidate Worker models (open weights only)

| Model | Size / active | License | Trained/evaluated against | Headline numbers (own reports) | GGUF for llama.cpp | Verdict for this repo |
|---|---|---|---|---|---|---|
| **Leanstral 1.5** (Mistral, 2026-06-30) | 119B / 6.5B MoE, 256k ctx | Apache-2.0 | agentic code model, RL'd in a multiturn Lean loop + filesystem code-agent mode; tool calls (`lean_run_code`), lean-lsp-mcp recommended | miniF2F saturated; PutnamBench 587/672; FATE-H/X 87%/34% at ~$4/problem via API | Q4_K_M 72 GB, Q6_K 98 GB (GZGavinZhao; arch label `mistral4` fixed; chat template embedded) | **Selected.** Works from compiler feedback, so the repo's Lean 4.33.1 / current mathlib is a nuisance, not a wall |
| Pythagoras-Prover-32B / 4B (2026-06) | dense Qwen3-32B / Qwen3-4B LoRA-SFT+RL | Apache-2.0 | **Lean 4.9.0-rc1**, 8k training context, whole-proof, no self-correction | 32B: 93.0% miniF2F pass@2048, 93/672 Putnam; 4B: 86.1% pass@32 | 32B (mradermacher), 4B Q8 4.7 GB | Reserve: a cheap whole-proof sampler for an APOLLO-style repair loop; 4.9-era mathlib names will be stale here |
| OProver-32B / 8B (m-a-p, 2026-05) | dense, Qwen3 tokenizer | Apache-2.0 | **Lean 4.15.0**; multi-round retrieval + compiler-feedback interface baked into the policy (R = 8–16 rounds, T = 1.0, 20–32k tokens) | 32B: 93.3% miniF2F pass@32, 11.3% PutnamBench; 8B beats Goedel-V2-32B on all five benchmarks | 8B (mradermacher, 5–9 GB) | Reserve: strongest small *iterative* prover; needs its own retrieval memory (OProofs) and prompt serialization |
| Goedel-Prover-V2-32B / 8B (Princeton, 2025-08) | dense | Apache-2.0 | **Lean 4.9** + matching Mathlib; self-correction mode | 32B 88.1% (90.4% w/ self-correction) miniF2F pass@32; 8B 84.6% | both (mradermacher, DevQuasar) | Superseded by the two rows above on every benchmark; oldest mathlib pin |
| DeepSeek-Prover-V2-7B / Kimina-Prover-Distill-8B (2025) | dense | permissive | 2025 mathlib | 75.6% / 77.9% miniF2F pass@32 | yes | Superseded |
| PhysProver (2026-01) | DeepSeek-Prover-V2-7B + 5k RLVR samples on PhysLean | release promised | PhysLean-derived conjectures | +2.4% on physics sub-domains, +1.3% miniF2F | not seen | The only physics-specific prover; too small an effect and too old a base to matter here |
| Qwen3.8-27B (fleet default) | dense 27.8B | open | general coding model | no Lean benchmark | on disk | **Control arm** for the dry run |
| DeepSeek-V4-Flash (on disk, 178 GB Q8) | 284B / 13B MoE | open | general; the **Goedel-Architect backbone** (99.2% miniF2F, 88.8% PutnamBench in that pipeline at ~$0.44/problem via API) | — | on disk | 9.3 tok/s here: a future Blueprinter/Refiner-class option if those roles ever go local, not a Worker |

**Selection rule (record it, not just the outcome):** the discriminating criterion is not a benchmark
score but **coupling to a Mathlib version**. Whole-proof provers memorize the lemma names and tactic
idioms of their training pin (4.9, 4.15, 4.17), while this repo tracks current mathlib (v4.33.1) and its
proofs lean on `positivity`, `gcongr`, `field_simp`, `Real.exp`/`log` lemma names that have moved since.
An agentic model that reads `lake env lean` output and calls tools pays a per-round cost for drift; a
frozen whole-proof model pays it as a hard ceiling. Leanstral 1.5 is the only open-weight model in the
first column that is both SOTA and agentic. Its cost is speed: 20–25 tok/s single-node against ~54 for
the Qwen control, which the dry run will price in rounds and wall-clock.

### 10.3 Frameworks surveyed (including the ones the owner named)

| Framework | What it is | Open? Local backend? | Lean pin / interface | Verdict |
|---|---|---|---|---|
| **OpenProver** (Kripner & Straka, arXiv 2607.09217; `pip install openprover` 1.0.1, MIT) | Planner–Worker–Verifier with whiteboard + repository, inspired by Aletheia; runs on an existing project with sorries; `--headless`, `--autonomous`, `--planner-model`/`--worker-model`, `--provider-url`, `--lean-worker-tools`, `--max-time` | Yes. Planner defaults to the `claude` CLI (the owner's subscription); local workers through an OpenAI-compatible `HFClient`. **Model aliases are hard-coded** (`sonnet`, `opus`, `minimax-m2.5` via vLLM, `leanstral` via Mistral's hosted API) | `lean_verify` = `lake env lean <file>` in the given project — the repo's own rule; MCP server for Claude workers | **Default harness (D7)**, with a ~20-line patch adding a `leanstral-local` alias → `HFClient(base_url=<llama-server>/v1, tool-capable)` and a context-length entry |
| **nanoproof** (Kripner, github Kripner/nanoproof, MIT, 93 stars, last push 2026-05-13; same author as OpenProver) | "Minimal open-source implementation of AlphaProof and HyperTree Proof Search": a from-scratch ~1B-parameter tactic model (nanochat-style, default `--depth 26`) trained by pretrain (Nemotron-CC-Math, ~20B tokens) → midtrain (Lean GitHub) → SFT (LeanTree, ~260k Mathlib transitions) → RL (MCTS self-play on Lean-Workbook/NuminaMath/DeepSeek-Prover statements), with MCTS over tactic states, policy + value heads; best 52.7 % MiniF2F-valid at 512 simulations | Yes / yes (own model; `scripts/prove.py --model-path … --lean-server host:port --theorem …`). **No released checkpoints**: training from scratch is part of the recipe | **Lean v4.27.0** via LeanTree `leanserver` (REPL process pool; `apply?`/`exact?` banned by default); Mathlib pinned to the toolchain | Not a harness for this repo: it is a prover-training framework whose model must be trained, whose Lean pin lags the repo by six minor versions, and whose tactic-level MCTS has no notion of a source statement, docstring, or scope tag. Its `TODO.md` lists nine open "critical" RL defects (policy log-probs unused in UCB, value-target semantics, unbounded replay). Harvest: the LeanTree tactic-state REPL is the cheapest per-goal Lean feedback loop surveyed (candidate for §7.4's tactic-repair sampler) once it supports 4.33; a Mathlib-pinned trained prover could sit behind OpenProver as a `lean_search`-style sub-goal oracle, never as the Worker |
| Mistral Vibe (`vibe --agent lean`) | Leanstral's native harness and RL environment; `~/.vibe/agents/lean.toml` with `api_base` to a local server; lean-lsp-mcp supported | Yes / yes | tool calls; TUI **and a programmatic mode** (verified 2026-09-20 from `vibe --help`: `-p/--prompt`, `--agent`, `--yolo`, `--max-turns`, `--max-price`, `--output {text,json,streaming}`) | Comparison arm: drivable by the Lead one theorem per call; measured in the dry run against the OpenProver arm |
| Pi agent (installed skill) | minimal terminal harness; custom OpenAI-compatible providers per tool; RPC/JSON modes; pi-mcp-adapter | Yes / yes | any, via bash + MCP | Fallback if OpenProver's patch proves awkward |
| **APOLLO** (Ospanov, Farnia, Yousefzadeh; NeurIPS 2025; github aziksh-ospanov/APOLLO, MIT) | model-agnostic repair loop: syntax fixer → sub-lemma isolation via Lean → `linarith`/`norm_num`/`ring`/`field_simp` solvers → low top-K LLM on remaining goals; 84.9% miniF2F for sub-8B models with < 100 samples | Yes / whole-proof prover models | **Lean 4.17.0 REPL bundled**; `ApolloRepair(code, lemma_name, config)` | Right idea (the repo's own tactic stack is its solver set) but pinned to 4.17 and a REPL; harvest the pattern (Phase 5 §7.4/§7.5), do not adopt the code |
| **Hilbert** (Apple, arXiv 2509.22819) | reasoner LLM + prover LLM + retriever + verifier, recursive decomposition | Yes / OpenAI-compatible endpoints for both LLMs | kimina-lean-server | Repo marked "not in active development"; fork at Rose-STL-Lab. Not adopted |
| **Aleph Prover** (Logical Intelligence) | commercial API/CLI (`alephprover` on PyPI); top of PutnamBench leaderboard (668 solved at ~$68/problem, Jan 2026); disproved an Erdős unit-distance conjecture | **No** (hosted only) | API | Not local; excluded by the owner's constraint |
| **LEAP** (Google, arXiv 2606.03303) | blueprint AND–OR DAG + compiler loop + LeanSearch; general LLM only; 12/12 Putnam 2025; Lean-IMO-Bench 70% | Backbone **Gemini-3.1-Pro**; no code, only solutions and the benchmark | compiler feedback | Design lessons only (DAG memoization +10 points; a decomposition reviewer prevents dead ends). Not runnable locally |
| **"Theo"** | **not found** in three searches (arXiv, GitHub, web) as a Lean prover or framework | — | — | UNVERIFIED; owner to supply a pointer |
| Aletheia (Google DeepMind, 2026-04) | Gemini Deep Think research agent with NL verifier; 6/10 FirstProof | No | — | Closed; the architecture OpenProver reproduces |
| A Minimal Agent for ATP / `ax-prover-base` (Axiomatic AI, ICML 2026, AGPL-3.0) | iterative refinement + library search + context management over `lake`; 54.7% PutnamBench pass@1 | Yes / Anthropic, OpenAI, Google API keys only | `lake` build + goals at `sorry` | Closest in spirit to the spec's Worker; API-only backends and AGPL. Not adopted |
| MerLean-Prover (arXiv 2605.26959) | Planning / Check / Lean agents, recursive outer loop; 12/12 Putnam 2025 | Claude models | — | Not adopted (Claude-only) |
| Goedel-Architect (Princeton, arXiv 2606.06468) | blueprint generation + parallel lemma proving + global refinement on DeepSeek-V4-Flash; `sorry_using [...]` skeletons | backbone open, **pipeline code not released** in the paper | `lean_compile` | Its skeleton discipline is what LeanArchitect/this spec already use |
| MechMath (COLM 2026, arXiv 2603.24465) | sorrifier-driven decomposition, isolates failed subgoals into self-contained contexts | not stated | — | Pattern only |
| Discover and Prove (ACL 2026, arXiv 2604.15839) | Hard-Mode answer discovery then rewrite to Easy-Mode for provers | "open-source"; models unstated | — | Not relevant to a spec whose statements are given |
| Numina-Lean-Agent, Ax-Prover, LeanMarathon, AutoformBot | covered in §1 and the review document | Claude/GPT backbones | MCP | Pattern sources for this harness |

### 10.4 Deployment plan for the Worker (Phase 0; do not touch a node before the advisor gate)

1. **Node:** one node only (the GPU is exclusive). Survey of 2026-09-20: `llm-server@qwen38` was
   inactive and the GPU idle on all three nodes, each runs two GitHub Actions runners for the companion,
   RAM in use 26–36 GB of 251. **Worker = infer-02** (7.5 TB free, lowest RAM use); **control = infer-01**
   (start `llm-server@qwen38` there for the dry run); infer-03 untouched.
2. **Weights:** `GZGavinZhao/Leanstral-1.5-119B-A6B-GGUF` → `/mnt/models/Leanstral-1.5/` (Q6_K, 98 GB,
   primary per "quality beats tok/s"; Q4_K_M, 72 GB, speed fallback). Both fit 251 GB RAM. Download at
   the fleet's 11–32 MB/s takes 1–2.5 h per file; verify sha256 against the Hub.
3. **Launcher:** `/usr/local/bin/run-leanstral` in the exact shape of `run-deepseek` (the MoE template):
   `numactl --interleave=all /opt/llama.cpp-master/build/bin/llama-server -m … -ngl 999 -ncmoe <N>
   -fa off -t 36 --no-op-offload -b 4096 -ub 1024 --load-mode mlock -c 65536 --jinja --metrics
   --host 0.0.0.0 --port 8082` (`-fa off` is forced: with `-fa on`, build 10326 loads and then aborts
   at the first compute with `CUDA error: invalid argument` in `ggml_cuda_flash_attn_ext_mma_f16_case`
   on sm_70 for `mistral4`, observed 2026-09-20, log kept as `/var/log/llm-leanstral.log.crash1-fa-on`;
   the other launchers on infer-02, `run-qwen38` and `run-glm53`, use `-fa on` without incident, so
   this was not seen with those models; an MLA-specific cause is plausible but not established),
   `-ncmoe` tuned so that non-expert weights + shared experts + KV fit
   32 GB (overflow fails at context creation, not at load). No speculation flags until measured.
   Chat template comes from the GGUF; tool calls need `--jinja`; `reasoning_content` is the reasoning
   field OpenProver's `HFClient` already reads.
4. **Service:** `systemctl start llm-server@leanstral`; then `/root/verify-node.sh` on all three nodes
   must stay byte-identical (it does not read `run-*`, so the `numactl --interleave=all` prefix is checked
   by eye against the `run-deepseek` template). Before OpenProver, smoke-test one chat completion with a
   `tools` array and a reasoning prompt through `curl`: `tool_calls` must parse and `reasoning_content`
   must be populated under `--jinja` on build 10326; if not, rsync the flashnext worktree build (10674)
   from infer-03 and retry. Start with `-ncmoe` at the full layer count so the server comes up, then lower.
   Thinking mode (verified 2026-09-20): Leanstral 1.5's embedded template accepts only
   `reasoning_effort ∈ {none, high}` and defaults to `none`, under which no `[THINK]` block is emitted
   and `reasoning_content` is null; with `high` the server returns a populated `reasoning_content`
   (3.8 k characters on a one-line `nlinarith` theorem) and the tool-call path works (`finish_reason`
   `tool_calls`, arguments parsed). The launcher therefore passes
   `--chat-template-kwargs '{"reasoning_effort":"high"}'`, because OpenProver's `HFClient` sends no
   per-request template kwargs. The rsync-the-newer-build fallback was not needed.
   Measurements (Q6_K, `tools/bench_cachebust.py`, 400-token answers, `cache_n = 0`, 2026-09-20):

   | `-ncmoe` | VRAM used | decode tok/s | prefill tok/s |
   |---|---|---|---|
   | 36 (all routed experts on CPU) | 12.5 GB | 12.5 | 59 |
   | 30 (six expert layers on the V100S) | 27.7 GB | 10.5 | 70 |

   Moving experts onto the card slowed decode by 16 % and left no KV headroom, so the service runs
   with `-ncmoe 36`; the Q4_K_M comparison is the remaining speed axis. `verify-node.sh` passes on
   infer-01 and infer-02; on infer-03 it reports two pre-existing failures (`run-flashnext` and its
   backup lack `numactl`), not touched by this work. OpenProver writes its scratch directory inside
   `--lean-project` and its run log under `runs/` relative to the cwd; both are pointed at a scratch
   Lean project that symlinks the repo's `lakefile.toml`, `lean-toolchain`, `lake-manifest.json` and
   `.lake` (`tools/openprover/README.md`), so nothing lands in the repository tree.
   Second Worker node (owner go 2026-09-20): infer-03 (10.0.0.28) serves the **Q4_K_M** file on the
   same launcher shape and port, as the quantization comparison arm and to run independent OpenProver
   runs concurrently (one run cannot be split across servers; concurrent slots on one node share its
   DRAM bandwidth, so a second node is the only way two runs proceed at full speed). infer-01 stays
   reserved for the Qwen3.8-27B control. Provenance of both files: Hugging Face
   `GZGavinZhao/Leanstral-1.5-119B-A6B-GGUF`, commit `929d4958`; Q6_K 97,669,011,200 bytes, sha256
   `96d9b908…691c58`; Q4_K_M 72,159,246,080 bytes, sha256 `8d7bdbfa…2b902`; both verified after
   download. Each OpenProver run names its node in `--provider-url`; no load balancer.
   **Shared-node finding (2026-09-20, supersedes the single-number throughput claims above).** Both
   Worker nodes run two GitHub Actions runners for `CF-LIBS-improved` (`/opt/ghrunner/actions-runner`
   and `…-b`, agents `infer-0x`/`infer-0x-b`), whose pytest jobs ran nearly back to back through the
   afternoon (`_diag/Worker_*.log`: 12:38, 12:57, 13:56, 14:45, 15:25, 16:48, 17:30, 17:49, 18:10 UTC).
   Decode is DRAM-bound and the launcher takes all 36 vCPUs, so a co-tenant using one or two cores
   collapses it: with a pytest job running, both nodes measured 1.4–1.7 tok/s (Q6_K on infer-02,
   Q4_K_M on infer-03); with that job paused (`SIGSTOP`, then resumed) infer-02 went to 4.7 tok/s
   while a 98 GB `rsync` was still reading its disk, and to 10.7 tok/s once the copy had finished.
   This, not the quantization or the harness, is why smoke test 2 lost both verifier passes to the
   600 s timeout and why the cumulative decode rate inside OpenProver runs read 2.6 tok/s.
   Same-node comparison on infer-03 with no co-tenant (`bench_cachebust.py`, 150-token answers):

   | file | decode tok/s | prefill tok/s |
   |---|---|---|
   | Q4_K_M (default repack) | 12.9 | 82 |
   | Q4_K_M (`--no-repack`) | 4.2–5.8 (noisy; copy finishing) | 78 |
   | Q6_K | 10.5 | 71 |

   So Q4_K_M is ~20 % faster than Q6_K and the earlier 1.5 tok/s reading on it was entirely the
   co-tenants. Decision: quality > tok/s (owner rule), so **Q6_K stays on both nodes**; Q4_K_M is kept
   on infer-03's disk as `run-leanstral.q4`. Operational rule that follows: a Worker measurement or
   run is valid only if no CI job was active on that node during it (check
   `pgrep -u ghrunner -f pytest`); the CI runners' placement on the Worker nodes is an owner decision
   (options: move the runners, or pin them with a cpuset and leave llama-server thread headroom; the
   `-t 30` headroom experiment is recorded next).
   **Thread-headroom experiment (infer-03, Q6_K, 2026-09-20).** Two pure-CPU hog processes
   (`python3 -c 'while True: pass'`) stand in for a CI job:

   | `-t` | co-tenant | decode tok/s | prefill tok/s |
   |---|---|---|---|
   | 36 | two busy cores | 1.4 | 40 |
   | 30 | two busy cores | 11.4 | 49 |
   | 30 | none | 14.1 | 71 |
   | 36 | none | 10.5 | 71 |

   With every vCPU claimed, one preempted thread stalls llama.cpp's per-token barrier for all the
   others; six threads of headroom removes the cliff and is faster even on an idle node. Both
   launchers now run `-t 30`. The fleet's other launchers (`run-qwen38`, `run-glm53`, `run-frontis`,
   `run-flashnext`) still carry `-t 36` and share the same CI runners; that is the owner's call, but the
   same cliff should be assumed until measured.
   **Answer-reserve finding (smoke tests 2–5, first attempts, 2026-09-20).** With the nodes idle and
   the 1800 s timeout in place, all four remaining smoke tests still ended `not_proved`, and the
   archived worker calls show the same shape every time: `finish_reason: length` at exactly 4096
   completion tokens with empty content and 11–18 k characters of `reasoning_content`. OpenProver's
   `HFClient` sets the per-call `max_tokens` to `--answer-reserve` (default 4096) for OpenAI-style
   backends, and Leanstral's thinking alone uses 3–4.5 k tokens, so the answer never fits; the
   "Phase 2" retry ("your response was cut off") re-thinks and hits the cap again. In the test-2
   rerun the Worker had already produced a correct proof that passed `lean_verify` (re-verified by
   the lead: axiom-clean, statement identical) but could not return it. Fix: `--answer-reserve 12288`
   on every run (no code change); a server-side `--reasoning-budget` is the fallback if thinking
   still overruns. Attempt history per test is kept under the run directory's `old/`.
   **Smoke-test tally (final, 2026-09-20; 45-min caps, `--answer-reserve 12288`, both nodes at
   `-t 30`, nodes idle except where noted).**

   | # | statement | result | evidence |
   |---|---|---|---|
   | 1 | `lorentzianG_pos` (local def) | **proved**, 23.5 min | lead re-check: axiom-clean, statement identical |
   | 2 | `composition_sum_one` (local defs) | **proved**, 36 min, 3rd attempt | lead re-check: axiom-clean, statement identical; attempts 1–2 had a passing `lean_verify` but hit the 600 s / 4096-token caps |
   | 3 | K2 `pixelSignal_injective_iff` (repo defs) | not proved, 93 min over two attempts | 11 failed `lean_verify`; recurring `typeclass instance problem is stuck` in the Worker's rewrites of the `Matrix` setup; `lean_search` found `LinearMap.ker_eq_bot` but the one-line proof was never assembled |
   | 4 | ST `composition_of_preservesStoichiometry` | not proved, 56 min | 11 failed attempts on the target; the two "passed" checks were lemma probes (`div_eq_zero_iff` etc.), not the theorem |
   | 5 | L2 `lorentzianProfile_integral` | not proved, 59 min | Worker never wrote a Lean file: 10 turns re-issuing the same two `lean_search` queries (`integral_add_right_eq_self`, `IsAddRightInvariant volume`), a search loop the harness does not break |

   Reading: the loop closes end to end (planner ↔ Worker ↔ `lean_verify` ↔ verifier ↔ submit) and the
   Worker preserves statements verbatim, but within a 45-minute cap at ~12 tok/s Leanstral closes only
   the algebraic one-liners; the three spec-level targets need either more rounds, a decomposition by
   the planner (none was attempted: every run spawned a single worker), or a loop-breaker on repeated
   tool calls. A CI job was active on infer-03 during the end of test 2 and the start of test 5. Phase
   0's Worker exit criterion ("closes both frozen frontier statements within the round cap") is
   therefore not yet met and the Frontier 02/07 dry run should follow the owner's decision on node
   isolation.
   Smoke test 1/5 (`lorentzianG_pos`, restated with a local def so recall of the repo lemma is not
   available; 2026-09-20): three launches were needed before the loop ran, each a harness defect now
   fixed by `tools/openprover/patch_local_alias.py` (Claude CLI ≥ 2.1 JSON shape; headless TUI
   missing `_sync_step_log_line`; `--provider-url` must be the server root). The successful run:
   `proved` in 23.5 min wall-clock, 4 planner steps (9 Claude CLI calls, 13.1 k output tokens,
   nominal $2.54 on the subscription), one Worker with 3 turns (152 s, 268 s, 369 s; first
   `lean_verify` failed, second passed), verifier pass 345 s. The statement was preserved
   character-for-character and the proof is an explicit `div_pos`/`add_pos_of_nonneg_of_pos`/
   `mul_pos` chain; re-verified by the lead with `lake env lean` and `#print axioms`.
5. **Measure** with `tools/bench_cachebust.py` (cache-busted; written 2026-09-20 because the
   `bench_model_aba.py` this plan first cited does not exist anywhere on the fleet or in the owner's
   repositories, verified by `find` on all three nodes): decode tok/s at Q6_K and Q4_K_M, prefill,
   and a 5-theorem smoke test through OpenProver on sorry'd copies. Record in spec 06. Only then decide
   Q6 vs Q4 and whether the two-node RPC experiment is worth a day.
6. **OpenProver patch:** fork `openprover` 1.0.1 into `tools/openprover/` (MIT; vendored like
   `axiom-audit`), add `leanstral-local` to `model_choices`, `HF_MODEL_MAP`, `VLLM_MODELS` (tool-capable),
   `MODEL_CONTEXT_LENGTHS`, default `--provider-url http://<node>:8082` (server root; the client appends `/v1`)`; keep the planner on `sonnet`/`opus`.
7. **Endpoint isolation:** the base URL is set only in the OpenProver run config and the Worker skill,
   never globally (global rule: per-tool base URLs only; no proxies).
