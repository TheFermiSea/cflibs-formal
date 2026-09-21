# 06 — Milestones, budgets, deferrals

Budgets are in Worker rounds, wall-clock and node-hours (decision D4 as re-expressed after D6: the
Worker runs on the owner's infer-0x fleet at near-zero marginal cost; the subscription pays only for
orchestration and review). The 2026 literature's $200–$700 per research theorem is the external
reference the round caps were derived from. Each phase has entry and exit criteria; nothing advances
on a self-report.

## Phase 0 — Harness readiness (gate for everything)
- **Entry:** the draft PR carrying this spec is open and the owner has signed off on decisions D1–D5
  in the README table (done 2026-09-20); `lean-lsp-mcp` and `lean4-skills` installed; worktree workflow tested.
- **Work (two parallel tracks):**
  - *Reviewer track (Claude):* `lean-statement-audit` made read-only with the drift-class field (done
    2026-09-20); blinded red team (04 §5) on S3, L2, K2, stoichiometry; record `docs/spec/redteam/<date>.md`.
  - *Worker track (local):* deploy Leanstral 1.5 per 04 §10.4 on one idle infer node (advisor gate before
    touching it); `verify-node.sh` byte-identical on all three; cache-busted throughput at Q6_K and Q4_K_M;
    vendor and patch OpenProver; 5-theorem smoke test on sorry'd copies; then the Frontier 02/07 dry run
    (04 §8.2) as an A/B against the Qwen3.8-27B control.
- **Exit:** reviewer passes two independent red-team runs; the Worker closes both frozen frontier
  statements within the round cap on at least one quant; throughput and closure rate recorded here.
  If the reviewer fails: stop, fix, re-run. Budget: 3 days wall-clock, one node dedicated; subscription
  spend for orchestration only.

## Phase 1 — `SahaCascade.lean` (P0)
- **Entry:** Phase 0 exit; pre-registration frozen (03 §1.7); a new §8 Saha-stage convention added to `docs/conventions.md`.
- **Work:** S1–S9 in grade order (A first: S1, S2, S4, S7; then S3 crux; then S5, S6, S8, S9).
- **Exit:** all acceptance items in 03 §1.6; C15 and Scenario 7(a); scope-tag rows; CONTEXT counts.
- **Deferred inside the phase:** any cascade *iteration* convergence; T-dependence of `ne*`. Both get
  their own dossier later (they compound Frontiers 02–04).
- Budget: 40 Worker rounds per module, 4 days wall-clock, one node.

## Phase 2 — `ContinuousProfile.lean` (P1)
- **Entry:** Phase 1 exit (not a logical dependency, a sequencing choice); pre-registration frozen.
- **Work:** L1–L3, G1–G4, E1 (A); V1–V2 (B). Docstring caveat V3.
- **Exit:** 03 §2.5; `Dimensions.lean` rows for `φ` and `∫ φ`; scope-tag rows.
- **Refused:** Faddeeva / complex error function representation; any Voigt FWHM equality.
- Budget: 40 Worker rounds, 3 days wall-clock, one node.

## Phase 3 — `SpectrometerForward.lean` (P2)
- **Entry:** Phase 2 exit; pre-registration frozen; the companion's `InstrumentModel` parameters read
  and recorded in the dossier (Gaussian σ from resolution or resolving power; top-hat pixels).
- **Work:** K1, K2, K7 (A); K3, K4 (Gershgorin), K5, K6 (B).
- **Exit:** 03 §3.5; C16 and Scenario 7(b–c); `Dimensions.lean` kernel row.
- **Deferred:** condition number of `K` (new frontier dossier, mirrors Frontier 06); self-absorbed
  pixel model (depends on Frontier 09).
- Budget: 40 Worker rounds, 4 days wall-clock, one node.

## Phase 4 — Stoichiometry corollaries, integration, docs (P3–P6)
- **Work:** the two theorems of 03 §4 in `MatrixEffects.lean`; Scenario 7 completed and vendored
  into the companion (manual step, recorded); `docs/module-reference.md` / `theorem-catalog.md`
  regenerated; `CONTEXT.md` architecture paragraph updated; `docs/frontiers/ROADMAP.md` gains rows for
  the deferred items.
- **Exit:** all gates green on `main`; a short `reviews/` note recording the statement audits of
  Phases 1–3.
- Budget: 2 days wall-clock (no Worker rounds; docs and oracle work).

## Phase 5 — Faithfulness tooling and upstream (the boundary-pushing part)
Ordered by value / cost from 04 §7; each is its own PR.
1. LIBS-DriftBench kept as a permanent artifact (04 §7.1) — low cost.
2. Oracle-as-shadow policy enforced (04 §7.2) — policy plus a CI check.
3. `scripts/vacuity-check.sh` (04 §7.4) — medium.
4. `scripts/check-literature-parity.sh` (04 §7.3) — medium.
5. Disprove-first Worker step (04 §7.5) — low.
6. PhyslibAlpha PR for the Saha seed, then the cascade (04 §7.8) — **parked by decision D5: not this
   cycle**; revisit only after the instrument and profile modules exist, with the tool-independence
   framing Physlib requires and a re-read of `docs/upstream-physlib-plan.md` triggers.
7. Public physics-drift dataset (04 §7.9) — after 1 and 3 exist.

## Phase 6 — Integration theorem (the blueprint's Milestone 4), only after Phases 1–3
- Pre-register a composed statement: kernel rank gate ∧ Boltzmann rank gate ∧ cascade neutrality ⇒ the
  recovered composition error is bounded by an explicit expression assembled from `NoiseToComposition`,
  `ConditionNumber`, S8 and K5. Expect REDUCED. Do not attempt before the pieces exist; a single
  "well-posedness" theorem written first invites exactly the retreat the pre-registration gate exists
  to catch.

## Refused (recorded so they are not re-proposed)
- Unit-carrying core types.
- Full Ladenburg–Reiche function (Bessel `I₀`, `I₁` absent from mathlib).
- Voigt FWHM as a theorem about the convolution.
- Any external SMT/CAS/prover package as a dependency.
- Framework adoption (Ax-Prover, LeanMarathon, AutoformBot) as software.

## Status table (update in place)

| Phase | Status | Spend | Notes |
|---|---|---|---|
| 0 | in progress | reviewer track: 32 subagent invocations (~2 M tokens, subscription); Worker track: infer-02 dedicated | Reviewer track **done** 2026-09-20: two blinded runs (default model, `sonnet`), 4/4 faithful accepted, 12/12 drifts flagged, 0 false accepts/rejects, 16/16 cross-run agreement; class criterion amended (edit-or-mechanism), see `redteam/2026-09-20.md`. Worker track: Leanstral 1.5 Q6_K on infer-02 (`llm-server@leanstral`, port 8082, `-fa off` after an sm_70 crash); OpenProver 1.0.1 patched (`tools/openprover/`, three harness defects fixed); smoke tests **2/5 proved** (both algebraic one-liners; statements preserved, axiom-clean on lead re-check), 3/5 not within 45-min caps (K2, ST, L2); second Worker node infer-03 live (Q6_K); **blocker found:** both Worker nodes host the CF-LIBS-improved CI runners, whose jobs cut decode 8× at `-t 36` (now `-t 30`, which holds under contention); OpenProver patched further (1800 s timeout, `--answer-reserve 12288`); runners pinned (D9); Frontier 02/07 dry run (D10 4 h, D11 Leanstral only) **both not proved**: 02 proved all three helper lemmas (lead-verified) and lost the assembly to a thinking overrun + timeouts, 07 never wrote a Lean file (search loop); two harness rules to add before the Qwen arm |
| 1 | not started | — | |
| 2 | not started | — | |
| 3 | not started | — | |
| 4 | not started | — | |
| 5 | not started | — | |
| 6 | not started | — | |
