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
| 0 | in progress | reviewer track: 32+16 subagent invocations (~3 M tokens, subscription); Worker track: infer-01/02/03 all dedicated; first real target landed as PR #6 on `main` | Reviewer track **done** 2026-09-20 (two blinded runs, edit-or-mechanism amendment) and **rerunning** 2026-09-22 with the two-class artifact (`edit_class`/`mechanism_class`, decision from the owner discussion), see `redteam/2026-09-20.md` and `redteam/2026-09-22.md`. Worker track: Leanstral 1.5 Q6_K on infer-02/03, Qwen3.8-27B Q6_K on infer-01 (D11 control arm, now live); OpenProver patched (search-loop breaker, 12-turn cap, `--reasoning-budget 8192` on the launchers); smoke tests 2/5, Frontier 02/07 dry run 0/2 (both not proved; 02 proved 3 helper lemmas, lost the assembly to harness limits fixed after). **First real target, `Alt/NeutralityScale.lean` (D12, candidate C3, §7 above): Qwen 3/3 proved, Leanstral 0/3** — landed on `main` via PR #6 after independent re-verification, the opposite of the owner's expectation entering the test. Runners on all three nodes pinned (D9; one persistence gap found and fixed after two silent SIGKILLs on infer-01). |
| 1 | not started | — | |
| 2 | not started | — | |
| 3 | not started | — | |
| 4 | not started | — | |
| 5 | not started | — | |
| 6 | not started | — | |
