# cflibs-formal — Development Specification (v0.4.3, 2026-09-23)

This directory is the **working specification** for the next phase of `cflibs-formal`. It replaces the
two Google-Docs drafts ("Lean 4 Scientific Autoformalization", "Revised Architectural Blueprint:
Formalizing CF-LIBS in Lean 4") as the canonical plan; those drafts were audited and their
verified content is folded in here. The repo is the system of record; a Google-Docs copy of this
spec is published for reading only.

## How to read this

| File | Answers | Read when |
|---|---|---|
| `01-blueprint-audit.md` | What in the Revised Blueprint is true, false, already done, or unverifiable | Before touching any module the blueprint proposes |
| `02-architecture.md` | What the repo is today (layers, invariants, namespaces) and the target architecture with the proposed modules placed in it | Before designing a new module |
| `03-module-specs.md` | Per-module dossiers: obstacle, statement, scope tag, literature, mathlib prerequisites, milestone A, acceptance criteria, pre-registration drafts | When starting a module |
| `04-autoformalization-framework.md` | The agent harness this repo will run: roles, tools, gates, the red-team protocol, budgets, and the boundary-pushing proposals | Before running any agent on this repo |
| `05-verification-governance.md` | Gates, CI, scope tags, citation policy, agent policy, review checklists | Before accepting any result |
| `06-milestones.md` | Phased plan with entry/exit criteria, budgets, and what is deferred or refused | For planning and status |

## Status vocabulary (used throughout)

- **VERIFIED** — a primary source was opened (Lean source in this repo, the pinned mathlib checkout,
  an arXiv abstract/HTML page, a GitHub README) and it supports the claim.
- **CORRECTED** — a primary source contradicts the claim as written; the corrected form is given.
- **UNVERIFIED** — only a secondary summary was seen, or nothing was opened. Treat as a lead, not a fact.
- **DONE** — the declaration exists in `CflibsFormal/` today (checked by grep on 2026-09-20).
- Scope tags keep the repo meaning: **EXACT / REDUCED / APPROXIMATION / PURE-MATH** (`docs/scope-tags.tsv`).
- Tractability grades keep the frontier-dossier meaning: **A** (no unmet dependency, mostly
  bookkeeping), **B** (new glue, all mathlib present), **C** (needs absent infrastructure or is refused).

## Non-negotiables (unchanged; restated so this spec cannot drift from AGENTS.md)

1. Axiom-clean: every declaration depends only on `propext`, `Classical.choice`, `Quot.sound`.
2. mathlib-only imports. physlib is an upstream target, not a dependency.
3. Dimensionless `ℝ` core; `Dimensions.lean` is additive and never wired into the core.
4. Honest scoping: the statement is audited, not just the compile. A green proof of the wrong
   statement is worthless.

## How this spec is maintained (it is a living document)

- **Where it lives.** `docs/spec/` on branch `docs/formalization-spec`, tracked by a **draft PR** that
  stays open as the mutable guide. Discussion happens in PR review comments; agreed changes land as
  commits on the branch. The PR is never merged as-is; when a phase completes, the durable parts
  (module docstrings, `docs/frontiers/*` dossiers, `docs/conventions.md`, `CONTEXT.md`) are updated on
  `main` through their own PRs, and the spec's status table is updated here.
- **Versioning.** Bump the version in this file's title and add a line to the change log below whenever
  a statement, tag prediction, budget, or decision changes. Never edit a frozen pre-registration; write a
  deviation note instead (`scripts/prereg.sh` header explains why).
- **Drive copies.** The Google-Docs copies ("cflibs-formal spec 00..06") are read-only snapshots and go
  stale; the branch is canonical. Re-export after a version bump if the Docs copies are being read.
- **What may not change without a decision by the repo owner:** the four non-negotiables; a scope tag
  from REDUCED/APPROXIMATION up to EXACT; adding any dependency; the refusals list in `06-milestones.md`.

### Decisions (made by the repo owner on 2026-09-20)

| # | Decision | Decided | Where it matters |
|---|---|---|---|
| D1 | Instrument model | Abstract kernel with the companion's Gaussian IRF as the first instance | `03` §3.2 |
| D2 | Where the stoichiometry corollaries live | `MatrixEffects.lean` | `03` §4 |
| D3 | Frontier 02/07 dry run before the cascade | Yes, both frontiers | `04` §8, `06` Phase 0 |
| D4 | Budget ceilings per phase | As listed in `06` ($150 / $300 / $200 / $300 / $100) | `06` |
| D5 | Physlib upstream | **Not this cycle.** No PhyslibAlpha submission until the instrument and profile modules exist; Phase 5 item 6 is parked | `04` §7.8, `06` Phase 5, `docs/upstream-physlib-plan.md` |

| D6 | Worker model | **Leanstral 1.5 (119B-A6B, Apache-2.0)** on llama.cpp, Q6_K primary / Q4_K_M speed fallback; Qwen3.8-27B as the dry-run control; whole-proof provers (Pythagoras, OProver) held in reserve as repair-loop samplers. Rule: prefer an agentic model over a Mathlib-pinned one | `04` §10 |
| D7 | Worker harness | **OpenProver** (MIT) with a vendored patch binding a local worker alias to the llama-server endpoint; Claude planner; Mistral Vibe (programmatic `-p` mode, verified) as comparison arm; Pi as fallback | `04` §10.3–10.4 |
| D9 | CI runners on the Worker nodes | **Pin, don't move** (2026-09-21): the two `actions.runner.TheFermiSea-CF-LIBS-improved.*` services on infer-02/03 are pinned to vCPUs 32–35 and `llm-server@` to 0–31 via `systemctl set-property` + a drop-in; launchers at `-t 30` | `04` §10.4 |
| D10 | Dry-run wall-clock cap | **4 hours per frontier statement** (`--max-time 4h`; the cap is soft, budget in wall-clock) | `04` §8.2, `06` Phase 0 |
| D12 | First real Worker target | **`Alt/NeutralityScale.lean` (candidate C3)** ahead of SahaCascade: three EXACT statements (neutrality scale = Fcal; undetected-species charge-fraction bias; closure bias `1/(1−Cu)`), run on Leanstral and the Qwen control after Mode B audit (2026-09-21) | `03` §7 |
| D13 | Red-team output schema | **`edit_class` + `mechanism_class`, standing** (2026-09-22): resolved runs 1–2's two class misses (`v06`, `v11`) as exact hits without a post-hoc rule change; all 16 variants re-run fresh on `sonnet` — 11/12 strict, 12/12 loose | `04` §5, `redteam/2026-09-22.md` |
| D11 | Dry-run A/B order | **Leanstral only first**, one frontier per node; the Qwen3.8-27B control arm follows once a Leanstral result exists | `04` §8.2 |
| D8 | Role split | Local model = Worker only; Claude subscription = Lead, Blueprinter, Target-Reviewer, red team (the roles that judge faithfulness) | `04` §3 |

Also decided: the Phase-0 reviewer-agent change and the tooling install (`.mcp.json` for `lean-lsp-mcp`, the `lean4-skills` plugin) land on this branch; Phase 0's red team is run immediately with Claude as reviewer; the Worker deployment (04 §10.4) proceeds in parallel and is gated by an advisor review before any node is touched. Budgets (D4) are re-expressed in rounds and node-hours because the Worker's marginal dollar cost is near zero.

### Change log

| Version | Date | Change |
|---|---|---|
| v0.1 | 2026-09-20 | Initial seven-file spec; blueprint audit; harness design |
| v0.1.1 | 2026-09-20 | S7 reduction statement: added `0 < ne` (load-bearing); acceptance wording for reductions corrected. (The `0 < S s 0` added at the same time was found unnecessary in v0.2 and removed.) |
| v0.2 | 2026-09-20 | Deep review pass: mathlib lemma names verified and pinned (`LinearMap.ker_eq_bot`, `integral_sub_right_eq_self` via `to_additive`, Chebyshev lemma names), S4 hypotheses stated, S5/S6/S8 binders (incl. `[Nonempty κ]`) and S9 index-type design corrected, S7's unnecessary `S`-positivity removed, `λ` identifiers renamed `lam`, Gershgorin cited for K4, K3 injectivity dropped, L1 weakened to `0 ≤ γ`, G4 Doppler binding added, third stoichiometry theorem dropped, worktree/olean and reviewer-vocabulary/tooling facts corrected, prereg audit scoping and runLinter invocation corrected, red-team blinding and dry-run contamination control added, maintenance and decisions sections added; independently audited (21 findings, all applied); the draft PR that carries this spec was opened with this version |
| v0.2.1 | 2026-09-20 | Consistency: G3/G4 rows in the scope-tag table (05 §3) aligned with 03; S9 grade B in the prereg draft; reviewer-agent row in 04 §2 no longer calls it read-only before the Phase-0 change |
| v0.4.3 | 2026-09-23 | Leanstral matched rerun **3/3** (03 §7.5): Mistral 1.5 chat template (the GGUF's 2603 one 500'd four Worker calls), card sampling, equal reasoning budget, Worker usage summed over turns, equal-token budget; wall-clock 4.5–8.5 h vs Qwen's 20–47 min. Fleet fixes (04 §10.4): infer-01 down after a pve1 reboot (`onboot` now set), infer-03 vCPUs never pinned, infer-02 model split unevenly across NUMA nodes. Mistral Vibe arm started. Correction: PR #6 is open, not merged; v0.4.2 said "landed on `main`" |
| v0.4.2 | 2026-09-22 | First real Worker target landed: `Alt/NeutralityScale.lean` (candidate C3, D12) — Qwen3.8-27B **3/3 proved**, Leanstral **0/3**, both independently re-verified, on `main` via PR #6 (all gates green). Two harness rules added (search-loop breaker, `--reasoning-budget`) and the dry-run Frontier 02/07 diagnosis folded in. Red team **run 3**: reviewer output schema changed to `edit_class`+`mechanism_class` (standing, not an amendment); all sixteen variants re-run fresh on `sonnet` — 4/4 faithful, 12/12 flagged, 11/12 strict two-class, 12/12 loose; both run 1–2 misses now score as exact hits; one labeling gap found (`v03`), not a reviewer defect. `docs/spec/redteam/2026-09-22{.md,/}`. Decision D13 recorded. |
| v0.4.1 | 2026-09-21 | Phase-0 Worker track: second node, shared-node/CI finding and `-t 30`, quant A/B, answer-reserve fix, smoke tally 2/5, nanoproof surveyed; decisions D9–D11 (runner pinning, 4 h dry-run cap, Leanstral-only first) |
| v0.4 | 2026-09-20 | Phase-0 reviewer track complete: blinded red team run twice (default model, `sonnet`) on 16 variants, record and variants in `redteam/2026-09-20{.md,/}`; pass criterion in 04 §5 amended to edit-or-mechanism class with the reason recorded; Mistral Vibe programmatic mode verified (`vibe -p`), D7 and 04 §10.3 corrected; Worker deployed on infer-02 with `-fa off` (sm_70 flash-attention crash recorded in 04 §10.4); Phase 0 status row updated |
| v0.3 | 2026-09-20 | Owner decisions D1–D5 recorded; Worker moved to local models on the infer-0x fleet (D6–D8): model and framework survey with the Mathlib-pin selection rule (04 §10), deployment plan under the node spec, OpenProver as harness, budgets in rounds/node-hours; Phase-0 reviewer agent made read-only with a drift-class field; lean-lsp-mcp and lean4-skills installed |

## Research memos (outside the spec proper)

- `docs/research/first-principles-alternatives.md` — exploration of novel, first-principles composition
  methods beyond CF-LIBS/C-sigma (2026-09-21), with the Asta Paper Finder / Theorizer / AutoDiscovery
  evidence and the reproducible SuperCam feature script beside it.

## One-paragraph summary of the plan

The physics roadmap adds four capabilities the current spec lacks: a **Z-stage ionization cascade**
with a unique charge-neutral electron density (the one genuinely new piece of the blueprint), **continuous
line profiles** (Lorentzian, Gaussian, Voigt-as-convolution) built by reuse of mathlib's Cauchy and
Gaussian densities and this repo's existing `lorentzian`, a **spectrometer kernel** that maps continuous
line emission to pixel sums and certifies when line intensities are recoverable, and two **stoichiometry
corollaries** that fall out of `Closure` and `MatrixEffects` in a few lines. Each lands with a certificate
in `Certificates.lean`, an oracle scenario, and a scope-tag row. The development method is an
**autoformalization harness** rather than an external framework: a general coding agent with Lean LSP
tools, a read-only adversarial statement reviewer that must first pass a seeded-drift red team, preregistered
statements, isolated workers that never run `lake build`, and the existing gates run by the lead. The
boundary-pushing part is the faithfulness tooling: a CF-LIBS drift benchmark derived from
`docs/conventions.md`, oracle fixtures as shadow theorems, blueprint-attribute parity between
`## Literature` prose and declarations, a vendored vacuity checker, a disprove-first step, and an
agent-driven upstream path into PhyslibAlpha.
