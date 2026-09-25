# Frontier 12 — Runtime certificates: making the verified spec pay rent

*Design dossier. No Lean or pipeline code edited (READ-ONLY on both repos); every current-state claim anchored to a real declaration by `file:line`. This is a bridge design, not a proof frontier — the "obstacle" is an engineering gap, not an open theorem. Scope tags: PURE-MATH / EXACT / REDUCED / APPROXIMATION. Grades A/B/C classify the bridge effort (thin wrapper / new Lean glue / new theory), not the physics.*

> **Status 2026-09-24 (deep audit): corrected, and partly superseded.** This is the 2026-07 design
> for `CflibsFormal/Certificates.lean`. The audit found that several of its claims overstate what
> the landed certificates prove, or attach certificates to loops the pipeline does not run.
> Corrections are made in place and marked **[2026-09-24]**; §0 is the per-certificate ledger.
> In short:
>
> * C10 certifies the fixed-`T` forward charge-neutrality closure at known `Ntot`. It does **not**
>   replace the pipeline's `0.5` damping, which acts on the inverse `(T, n_e)` loop.
> * C12 is `0 ≤ τ` and certifies nothing about the data.
> * C3 is C1 verbatim. C1 and C2 certify a pooled single-intercept design, not the per-element
>   fit the solver runs.
> * C8 and C11 never landed; the C11 product gate cannot pass at realistic parameters.
> * No certificate conjunction, including the `EvaluatorSoundness` bundle, is an informative
>   composition-error bound at realistic parameters.
>
> Audit ids (U-, LF-, INV-, SPC-, PS-, LIT-, RF-, FT-) refer to the 2026-09-24 deep audit
> (`docs/research/audit-2026-09-24/` on the `docs/formalization-spec` branch). Line pins into the
> companion are as of 2026-07 unless marked restamped; prefer the declaration names.

---

## 0. Ledger — what each certificate certifies, and what feeds it [2026-09-24]

Every soundness theorem in `Certificates.lean` is a correct re-export (audit ledger U-04). The
table records what a pass buys. "Feeder" describes the companion CF-LIBS-improved at `b142ae25`:
`certificates_wiring.py` (`CERTIFICATE_WIRING_STATUS`) for the inversion, and the evolution gate
`certificate_gate.py`, whose `HARD_CERTIFICATES_DEFAULT` is C1, C2, C3, C4, C7, C9, C10, C12, C13
and whose never-HARD set (`REPORTED_CERTIFICATES`) is C5, C6, C14.

| # | Lean def | Certifies (proved) | Does not certify | Feeder |
|---|---|---|---|---|
| C1 | `energySpreadCert` | the pooled single-intercept `[1\|E]` normal matrix is nonsingular (iff) | the accuracy of `T`; the rank of the per-element-intercept fit the solver runs, whose condition is a positive within-element spread. Passes for any 2 distinct energies, and on pooled designs that fit cannot identify (SPC-01, INV-04) | inversion: auto, pooled energies; evolution gate: HARD |
| C2 | `jointRankCert` | the pooled `[1\|E\|s]` design is identifiable (iff) | the same two limits: Al I only + Ti II only passes while `[x\|dummies\|s]` is rank-deficient (INV-04) | auto when ≥ 2 stages; HARD |
| C3 | `conditioningCert` | `κ ≥ 1`, and the scaled design is orthonormal | nothing beyond C1: same predicate, and the conclusion holds for every design with `SSₑ > 0` (U-07). `1/SSₑ` carries units, so it is not scale-free | auto; HARD |
| C4 | `slopeBudgetCert` | `\|Δβ\| ≤ τ_β`, given `\|ŷₖ − yₖ\| ≤ ε` on every line | that `ε` bounds every line: `1/SNR` is a 1σ scale, and all `n` lines fall within it with probability `0.683ⁿ` when all sit at the minimum SNR (U-03) | inversion: skip (no target); evolution gate: HARD with `ε = 1/min SNR` |
| C5 | `tempBudgetCert` | `\|T̂ − T\|/T ≤ τ_T`, given a slope-error bound `B` (exact identity) | `B` itself; no C4→C5 composite theorem exists | skip; never HARD |
| C6 | `compBudgetCert` | every `\|ΔCₛ\| ≤ τ_C`, given `\|N̂ₛ − Nₛ\| ≤ δ` for all `s` | `δ` itself; abundance-blind (one absolute `δ` and `τ_C` for all species), so loose for minor species (LIT-05) | skip; never HARD |
| C7 | `mcWhirterCert` | `ΔE ≤ E*` (iff) | LTE: McWhirter is necessary, not sufficient; circular at the recovered `(T̂, n̂_e)` (R3); `C = 1.6·10¹²` presumes `n_e` in cm⁻³, `T` in K, `ΔE` in eV (PS-11) | auto at the reported `(T, n_e)`; HARD |
| C8 | — | not implemented | the named theorem `stark_saha_lte_consistent` needs exact Stark = Saha equality, so it cannot back a tolerance predicate (U-11, PS-09) | — |
| C9 | `sahaIterCert` | convergence of the single-element forward Saha iteration to its closed-form root | anything about the inverse loop; it needs the absolute `Ntot` | skip: `(S, Ntot, b)` never materialized; HARD in the evolution gate |
| C10 | `dampedIterCert` | convergence of the fixed-`T` forward multi-element closure at known `Ntot` to a given fixed point `r` | the inverse `(T, n_e)` loop and its `0.5` damping (U-02, INV-05) | skip: absolute `Ntot` not materialized; HARD in the evolution gate |
| C11 | — | not implemented | the proposed `L₁·L₂ < 1` gate evaluates to 6·10³–5·10⁴ at realistic parameters, so it cannot pass (INV-03) | — |
| C12 | `knownTauCert` | `0 ≤ τ`, and the model left-inverse identity `I_thin = (I_thin·SA(τ))/SA(τ)` | that `τ` is known or correct; anything about the data (LF-11, U-05, SPC-03) | auto with the estimated optical depth when SA is applied; HARD |
| C13 | `saDistinctCert` | the flat-kernel pair ratio is injective for opacity coefficients `0 < w₂ < w₁` | injectivity for a profile-resolved (Voigt) curve of growth; the shared source term and shared lower level, which the Prop does not encode (U-06, LF-04, LF-08) | skip: not materialized; HARD |
| C14 | `aliasBudgetCert` | `\|N̂ − N\| ≤ N·δ/(1 − δ)`, given the assumed response-factor bound | `δ` itself (R2); the predicate is only `0 ≤ δ < 1` | skip; never HARD |

**No composition guarantee.** The only composed chain,
`EvaluatorSoundness.hardGateBundle_composition_error_le` via
`NoiseToComposition.noise_to_composition`, gives composition bounds of 26 to 1.4·10³ at 0.5–5 %
noise on NIST Fe/Cr/Ni level lists, where a fraction error is at most 1. It falls below 1 only
when the level lists are truncated at 1 eV (U-01, re-run by the verifier). The loose leg is the
partition-function channel. Do not score or advertise the evaluator bundle as a certified
composition bound. The fixes are a log-derivative `U` leg (RF-18) and a relative,
abundance-aware closure bound (RF-23).

**Current priority.** Keep C1–C3 and C12 out of every HARD path until the within-element design
certificates (C1g/C2g, RF-16 / FT-04) and the `τ`-error lemma (FT-13) land. Certify the loop the
pipeline runs (RF-17 / FT-01) instead of C10/C11.

---

## 1. The obstacle

The pipeline **already trusts unverified heuristics at points where the spec has a proven gate.** Three anchored instances:

1. **The iteration damping is a hard-coded `0.5`, with only a-posteriori convergence detection.** `IterativeCFLIBSSolver` (`iterative.py:968`) sets `T_K = 0.5*T_prev + 0.5*T_new` (`iterative.py:2454`) and `n_e = 0.5*ne_prev + 0.5*ne_new` (`iterative.py:2531`); the JAX `lax.while` mirror does the same "50/50 damping" (`iterative.py:908,937`). Convergence is only *detected* after the fact by `|ΔT| < tol` (`iterative.py:2551`; JAX `:945`). *[2026-09-24: pins restamped to companion `b142ae25`; they were `:929`, `:1965`, `:2022`, `:853,890`, `:2039`.]*

   **[2026-09-24] Withdrawn.** This item used to say that the spec proves "an unconditional convergence certificate the solver ignores": that `dampedMultiElementIter_contraction` gives "a provably-convergent damping the pipeline could compute from its own `S`, `Ntot` instead of guessing `0.5`". That is false (U-02, INV-05, SPC-04). The theorem itself stands: the canonical relaxation `lam = 1/(1 + ∑ₛ Ntotₛ/Sₛ)` contracts the fixed-`T` forward charge-neutrality map `x ↦ ∑ₛ Ntotₛ·Sₛ/(x + Sₛ)` at rate `1 − lam < 1` with no smallness hypothesis on `S`, `Ntot`. But that map needs the absolute element totals `Ntot`, which the inverse solver does not know and does not iterate. The `0.5` damps the outer `(T, n_e)` loop, whose `n_e` update comes from the SB offset, Stark widths or pressure balance. **C10 certifies the forward closure at known `Ntot` (`anderson_solver.py` territory, not wired into a shipped pipeline); it says nothing about the inverse `(T, n_e)` loop or its `0.5` damping.** A certificate for the loop the pipeline runs is RF-17 / FT-01. The JAX route's `n_e` leg (`iterative.py:929-937`) is a closure at fixed *pressure*, not at fixed `Ntot`, so C10 does not apply there either; a pressure-balance closure certificate is a possible frontier idea.

   Likewise `outerLoop_contracts` (`OuterLoopModelB`) gives the outer `T`↔`n_e` sweep an `L₁·L₂ < 1` gate; nothing in `iterative.py` evaluates it. **[2026-09-24]** That gate evaluates to 6·10³–5·10⁴ at realistic LIBS parameters (INV-03), and Model B freezes the Saha offset at a reference `T` (RF-11), so it is not a usable runtime certificate either.

2. **Identifiability is gated qualitatively where the spec proves a quantitative determinant gate.** `temperature_identifiable` (`identifiability.py:84`) counts "≥2 distinct upper-level energies"; the spec's `designNormalMatrix_det_ne_zero_iff` (`OLS.lean:220`) proves the exact rank condition `det M ≠ 0 ↔ 0 < ∑ₖ(Eₖ−Ē)²`, and its scale-free conditioning is settled by `centeredScaledDesign_orthonormal` (`OLS.lean:471`, `κ_scaled = 1`). The joint Saha–Boltzmann fit's identifiability is the full biconditional `jointDesign_det_pos_iff` (`OLS.lean:683`) — with no runtime evaluator in the pipeline. *[2026-09-24: both theorems are about single-intercept designs. The solver fits one intercept per element, whose rank condition is a positive within-element spread, so C1/C2 can pass where that fit is rank-deficient (SPC-01, INV-04). The grouped certificates C1g/C2g are RF-16 / FT-04.]*

3. **The bridge already exists for three theorem families — and stops exactly at the iteration/contraction wall.** `derived_thresholds.py` mirrors `ErrorBudget.lean` verbatim and is conformance-pinned to the oracle (`derived_thresholds.py:1-25`, `tests/oracle/test_derived_thresholds.py`); `reliability.py` mirrors `twoLineBeta_stable_sharp`, `composition_dist_vector_le`, `mcWhirterBound`, `stark_saha_lte_consistent`; `identifiability.py:12` states each guard "mirrors a PROVEN identifiability theorem in the companion Lean spec." So the pattern is proven-viable — but it is **prose-cited, not type-linked**: nothing guarantees the Python predicate is the same Prop the theorem discharges, and the highest-value gates (§1.1) have no mirror at all. *[2026-09-24: the overhaul review (G2) found `identifiability.py` and `reliability.py` dead in production, imported only by scripts and tests (U-14); and the §1.1 gates do not certify the loop the pipeline runs.]*

The repo's own ledger already frames the target: `docs/SOLVER_FORMALIZATION_GAPS.md:191` — *"Tier 3 — the hypothesis IS the runtime check (wire it; no Lean fix required)"* — and `OuterLoopModelB.lean:71` calls `L₁·L₂ < 1` "the runtime-checkable convergence certificate the solver flag gates on." This dossier turns that scattered intent into **one typed bridge**: a `CflibsFormal/Certificates.lean` where each certificate is a `Prop` of pure float arithmetic paired with a soundness theorem `certificate → guarantee`, plus a reference Python checker mirroring those exact defs — extending the existing `oracle/` + `check_fixtures.py` mechanism, not inventing a new one.

**What "paying rent" means:** when a certificate predicate evaluates `True` on the pipeline's actual floats, a theorem — not a heuristic — guarantees the corresponding well-posedness / convergence / error property. When it evaluates `False`, the honest action (`refuse_to_report`, `identifiability.py:265`; the M8 per-element flags, `quality.py:656`) is already wired; the certificate names which proven precondition failed. *[2026-09-24: the guarantee holds for the model the wrapped theorem is stated over, and only under the soundness theorem's remaining hypotheses, several of which are assumed rather than measured; §0 says what each certificate buys. "Already wired" does not hold for `refuse_to_report`: the overhaul review found `identifiability.py` dead in production (U-14).]*

---

## 2. The certificate map

Each row: certificate → data inputs → checkable predicate (floats) → Lean guarantee theorem → pipeline attach point → grade. `SSₑ := ∑ₖ(Eₖ−Ē)²`, `SSₛ`, `S_Es := ∑ₖ(Eₖ−Ē)(sₖ−s̄)`; `Ŝ := ∑ₛN̂ₛ`; `card` = species count.

*[2026-09-24: this is the 2026-07 design map. Rows C3 and C8–C13 carry corrections; §0 is the authoritative ledger of what each landed certificate certifies. Some Lean line pins below have drifted since 2026-07; the declaration names are authoritative.]*

| # | Certificate | Data inputs | Checkable predicate | Lean guarantee theorem | Pipeline attach point | Grade |
|---|---|---|---|---|---|---|
| C1 | Energy-spread rank / T-identifiable | line energies `E` | `0 < SSₑ` | `OLS.designNormalMatrix_det_ne_zero_iff` (`OLS.lean:220`) ⇒ normal matrix nonsingular ⇒ slope→T recoverable | `identifiability.py:temperature_identifiable:84`; `boltzmann.py:BoltzmannPlotFitter.fit:154` | A |
| C2 | Joint Saha–Boltzmann rank | `E`, ion indicator `s` | `0 < SSₑ·SSₛ − S_Es²` | `OLS.jointDesign_det_pos_iff` (`OLS.lean:683`) ⇒ joint (T,n_e) fit identifiable (E,s not collinear) | `closed_form.py:_build_design_matrix:255`/`_solve_wls:305`; `joint_optimizer.py:optimize:495` | A |
| C3 | Boltzmann-plot conditioning | `E`, `card` | `0 < SSₑ` (⇒ scaled design orthonormal, κ=1) | `OLS.boltzmannConditionNumber_ge_one` (`OLS.lean:341`) + `centeredScaledDesign_orthonormal` (`OLS.lean:471`) ⇒ only genuine sensitivity is `1/SSₑ` **[2026-09-24: same predicate as C1, and the conclusion holds for every design with `SSₑ > 0`, so C3 adds nothing to C1 (U-07); `1/SSₑ` carries units, so it is not scale-free]** | `reliability.py:temperature_conditioning:48` | A |
| C4 | Slope / energy-spread budget | est. per-line err `ε`, target `τ_β`, `card`, `SSₑ` | `ε²·card ≤ τ_β²·SSₑ` | `ErrorBudget.maxPerLineError_sufficient` (`:244`)/`requiredEnergySpread_sufficient` (`:227`) ⇒ `\|Δβ\| ≤ τ_β` | `derived_thresholds.py:max_per_line_error:48`/`required_energy_spread:42` | A |
| C5 | Temperature-error budget | `k_B`, `T̂`, slope bound `B`, `τ_T` | `k_B·T̂·B ≤ τ_T` (identity `\|ΔT\|/T=k_B·T̂·\|Δβ\|`) | `ErrorBudget.temp_rel_error_le` (`:215`)/`temp_rel_error_eq` (`:199`) ⇒ `\|T̂−T\|/T ≤ τ_T` | `derived_thresholds.py:slope_target_from_temp_rel:65`; `error_budget.py:temp_rel_error_bound:145` | A |
| C6 | Composition budget | per-species err `δ`, `τ_C`, `Ŝ`, `card` | `(card+1)·δ ≤ τ_C·Ŝ` | `ErrorBudget.composition_target_sufficient` (`:325`) ⇒ `\|ΔCₛ\| ≤ τ_C` ∀s | `derived_thresholds.py:density_budget_from_composition:71`; `reliability.py:composition_error_bound:138` | A |
| C7 | McWhirter LTE admissibility | `T`, gap `ΔE`, `n_e`, `C=1.6e12` | `C·√T·ΔE³ ≤ n_e` | `PartialLTE.mcwhirter_iff_thermalizationLimit` (`PartialLTE.lean:87`) ⇒ `ΔE ≤ E*` | `reliability.py:mcwhirter_min_ne:173`; `lte_validator.py:check_mcwhirter:115` | A |
| C8 | Stark↔Saha LTE self-consistency | `n_e^Stark`, `n_e^Saha`, `T`, `ΔE` | `\|Δn_e\|/mean ≤ rtol` ∧ `mean ≥ C·√T·ΔE³` | `StarkBroadening.stark_saha_lte_consistent` (`StarkBroadening.lean:189`) ⇒ two independent diagnostics agree + clear McWhirter **[2026-09-24: not implemented. The named theorem needs exact equality `hagree` of the two estimates, so it does not cover the `rtol` predicate (U-11, PS-09). An error-bar C8 is RF-20 / FT-06]** | `reliability.py:stark_saha_lte_gate:205`; `stark_ne.py:measure_stark_ne:394` | ~~A~~ not landed |
| C9 | Inner Saha-iteration contraction | `S`, `Ntot`, ceiling `b` | `b<Ntot ∧ sahaEquilibriumNe S Ntot ≤ b ∧ √S/(2√(Ntot−b))<1 ∧ √(S·Ntot)≤b` | `SahaEquilibrium.sahaIter_contraction` (`:485`)+`sahaIter_mapsTo` (`:542`)+`sahaIter_tendsto` (`:593`) ⇒ geometric convergence **[2026-09-24: a forward solver at fixed `T` and known absolute `Ntot`; the inversion never forms its `(S, Ntot, b)` inputs]** | `saha_boltzmann.py:solve_ionization_balance:164`/`solve_species_states:502` | A |
| C10 | Damped multi-element closure contraction (no smallness condition; forward model at known `Ntot`) | `S,Ntot:ι→ℝ` (>0) | none — set `lam=1/(1+∑Ntotₛ/Sₛ)`; rate `1−lam<1` unconditional | `SahaEquilibrium.dampedMultiElementIter_contraction` (`:778`)+`_tendsto` (`:869`); direct loop `multiElementIonized_iter_tendsto` (`:946`) ⇒ convergence of the fixed-`T` forward charge-neutrality closure | `anderson_solver.py:picard_solve`/`anderson_solve` (forward closure; not wired into a shipped pipeline). **[2026-09-24] Does not replace the `0.5` damping** (`iterative.py:2454,2531`; JAX `:908,937`), which acts on the inverse `(T, n_e)` loop (U-02, INV-05) | A |
| C11 | Outer T↔n_e loop product gate | `L₁=sahaFactorLipConst/R₀`, `L₂=(\|S_Es\|/SSₑ)/(k_B·smin²·nemin)`, box, floor `smin` | `L₁·L₂ < 1` ∧ box-invariance ∧ `smin ≤ slope` | `OuterLoopModelB.outerLoop_contracts`; spine `outerContraction_box` (`SahaEquilibrium.lean:1269`); 2-D `jointOuterMap_contraction` (`:1426`) ⇒ ∃! fixed point + convergence | `iterative.py:IterativeCFLIBSSolver`/`_run_lax_while_loop` **[2026-09-24: not runtime-checkable in practice: the gate evaluates to 6·10³–5·10⁴ at realistic parameters (INV-03). Do not wire it; the replacement is RF-17 / FT-01]** | ~~B~~ not landed |
| C12 | Self-absorption model left-inverse (`0 ≤ τ`) — **non-informative [2026-09-24]** | an estimated `τ` | designed as `tau_known ∧ 0 ≤ τ`; **landed as `0 ≤ τ` alone**, with no "known" clause | `lineIntensity_eq_selfAbsorbedIntensity_div` ⇒ the model identity `I_thin = (I_thin·SA(τ))/SA(τ)`, true for every `τ ≥ 0` including a wrong estimate, so nothing about the data (LF-11, U-05, SPC-03); bias `selfAbsorbedIntensity_le_lineIntensity` | `self_absorption.py:_escape_factor:169`/`correct_with_cog:919` | A (thin), but non-informative; the FT-13 replacement is a refusal-grade lemma, not a certificate |
| C13 | Self-absorption identifiability (N,τ) alias (flat kernel) | `n_lines`, `tau_known`, `n_distinct` | `tau_known ∨ (n≥2 ∧ n_distinct≥2)`; **landed as `0 < w₂ < w₁` on opacity coefficients** (`τ = w·n`, not widths) | `selfAbsorption_breaks_identifiability` / `CurveOfGrowth.cogRatio_injOn` (`:254`) ⇒ (N,τ) resolvable **[2026-09-24: flat kernel `1 − e^{−wn}` only; assumes the two lines share one source term and one lower-level column, which the Prop does not encode; the `tau_known` branch is C12, which is non-informative (U-06, LF-04, LF-08)]** | `identifiability.py:self_absorption_identifiable:195` | A |
| C14 | Atomic-data aliasing error budget | assumed rel. err `δ` (`0≤δ<1`) | `δ < 1` ⇒ `\|N̂−N\| ≤ N·δ/(1−δ)` | `AtomicDataPerturbation.classicDensity_aliasing_error` (`:213`); OLS `Alt.olsDensity_aliasing_A_error` (`OLSAtomicDataPerturbation.lean:206`); `olsComposition_atomicData_error` (`:284`) | `quality.py:per_element_reliability_from_uncertainty:656` | A* (§5) |

**Reading the map.** C4–C8, C13 already have Python mirrors (`derived_thresholds.py`, `reliability.py`, `identifiability.py`) — M1 makes them *sound* (type-linked, not just prose-cited) and adds non-vacuity witnesses. C1–C3 *upgrade* the qualitative guards to the proven quantitative determinant/conditioning gates. *[2026-09-24: C8 never landed in Lean, so it has no type link; and several landed witnesses sit at zero-error corners (C4, C6, C14), so they show the soundness theorem applies without exercising a nonzero error.]*

**[2026-09-24] Withdrawn.** This paragraph called C9–C11 "the untapped core — the convergence certificates that turn guessed `0.5` damping and post-hoc `|ΔT|<tol` into an a-priori theorem", and C10 "the headline rent-payer: no gate at all, only a change of the relaxation constant to the proven-convergent `1/(1+∑Ntot/S)`". C9 and C10 certify forward closures at known absolute `Ntot`; they do not touch the `0.5` damping or the `|ΔT| < tol` stop of the inverse loop (§1.1). C11 cannot pass at realistic parameters (INV-03). The convergence certificate for the loop the pipeline runs is RF-17 / FT-01.

---

## 3. Inventory — thin wrappers vs new glue vs new theory

### Grade A — thin wrappers over an existing theorem (implement now)

The Lean theorem's hypothesis is already a pure arithmetic Prop over the exact inputs the pipeline holds; its conclusion *is* the guarantee. Soundness is a one-line re-export.

- **C1, C2, C3** — `designNormalMatrix_det_ne_zero_iff`, `jointDesign_det_pos_iff`, `boltzmannConditionNumber_ge_one`/`centeredScaledDesign_orthonormal` are already biconditionals/inequalities over `SSₑ`, `SSₑ·SSₛ−S_Es²`. Witnesses exist in-repo (`OLS.lean:237,716`). *[2026-09-24: C1 and C2 are single-intercept designs, not the per-element fit the solver runs (SPC-01, INV-04); C3 adds nothing to C1 (U-07).]*
- **C4, C5, C6** — `maxPerLineError_sufficient`, `temp_rel_error_le`, `composition_target_sufficient` take exactly `(ε,τ_β,card,SSₑ)`, `(k_B,T̂,B)`, `(δ,τ_C,Ŝ,card)`. The predicate *is* the theorem's hypothesis. Float mirrors already in `derived_thresholds.py`, oracle-conformance-tested. *[2026-09-24: the predicate is the theorem's arithmetic hypothesis; the epistemic hypotheses (`∀k |ŷₖ−yₖ|≤ε`, the slope bound `B`, `∀s |N̂ₛ−Nₛ|≤δ`) stay outside it, and that is where the content is (§5 R1).]*
- **C7** — `mcwhirter_iff_thermalizationLimit` is a clean biconditional; predicate = its LHS. *[2026-09-24: McWhirter is necessary for LTE, not sufficient; `C = 1.6·10¹²` presumes `n_e` in cm⁻³, `T` in K, `ΔE` in eV (PS-11).]*
- **C9** — `sahaIter_contraction`+`sahaIter_mapsTo`+`sahaIter_tendsto` exist; bundle their float hypotheses into one Prop, re-export `tendsto`. (Note: the predicate references `sahaEquilibriumNe S Ntot`, the closed-form fixed point, which is computable from `S,Ntot`.)
- **C10** — `dampedMultiElementIter_contraction`/`_tendsto` are *unconditional* for the canonical `lam` (only positivity `∀s, 0<Sₛ ∧ 0<Ntotₛ` required; verified: rate `1−lam<1` with no smallness hypothesis). The "certificate" is trivially true and the guarantee is geometric convergence. Strongest wrapper: essentially no gate. *[2026-09-24: the convergence is of the fixed-`T` forward charge-neutrality closure at known absolute `Ntot`, not of the inverse loop (§1.1). The landed soundness theorem also takes the fixed point `r` as a hypothesis; `dampedMultiElementIter_converges_to_equilibrium` (`SahaContraction`) removes it.]*
- **C12** — `lineIntensity_eq_selfAbsorbedIntensity_div` holds for all `τ≥0`; the only "certificate" is that `τ` is known. **[2026-09-24] Retracted from "implement now".** "Known" is not arithmetic, so the landed predicate is `0 ≤ τ` alone, and the identity holds for every `τ ≥ 0`, including a wrong estimate: C12 certifies nothing about the data (LF-11, U-05, SPC-03). The self-absorption model is also approximate (flat line-centre escape factor applied to integrated intensities; LF-01). The replacement (FT-13) is a ½-Lipschitz bound on `log SA` plus a `τ`-error propagation lemma whose content sits in an assumed `|τ̂ − τ| ≤ Δ`: a refusal-grade lemma (§5 R7), not a checkable certificate.
- **C13** — the disjunction is exactly `self_absorption_identifiable`'s shape. Note the pairing is looser than a clean biconditional: `selfAbsorption_breaks_identifiability` (`SelfAbsorptionInverse`) proves the failure direction and `cogRatio_injOn` (`CurveOfGrowth.lean:254`) the injectivity/recovery direction; the wrapper stitches both. *[2026-09-24: the landed C13 is `0 < w₂ < w₁` on per-line opacity coefficients (`τ = w·n`), not widths; the `tau_known` branch is C12, which is non-informative. Injectivity holds for the flat kernel `1 − e^{−wn}` with a shared source term and lower-level column; for Stark-broadened Voigt lines (`γ/σ ≳ 0.1`) the pair ratio is non-monotone within `τ ≤ 30` (U-06, LF-04, LF-08).]*
- **C14** — `classicDensity_aliasing_error` gives `|N̂−N|≤N·δ/(1−δ)` from `δ<1`. Thin, **but `δ` is not runtime-knowable** (§5) — grade-A math, refusal-grade epistemics (A*).

### Grade B — needs new Lean glue

- **C11 (outer-loop product gate)** — `outerLoop_contracts` exists, but `L₁ = sahaFactorLipConst kB Tmin Tmax me h chi …/R₀` is a defined constant needing a Float mirror, and `hmapsNe`/`hmapsT`/`hslopeFloor` are side conditions (confirmed in the signature at `OuterLoopModelB.lean:75-98`). A grade-B certificate packages the **product gate `L₁·L₂<1` as a bare float predicate** (the abstract `outerContraction_box` already accepts `L₁,L₂` as reals) and records the box/floor conditions as runtime-observable side certificates. Glue: (i) a computable `sahaFactorLipConstFloat`; (ii) a soundness lemma stitching the float gate to `outerContraction_box`'s `hq`. The 2-D `jointOuterMap_contraction` (row-sum `max(a+b,c+d)<1`) is the analogous glue. **[2026-09-24] Do not implement.** With `sahaFactorLipConst` as proved, the gate evaluates to 6·10³–5·10⁴ at realistic LIBS parameters, so it cannot pass (INV-03); Model B also freezes the Saha offset at a reference `T` (RF-11). The replacement is a gain / residual-stop certificate for the loop the pipeline runs (RF-17 / FT-01).
- **A unified `refuseToReportCertificate`** — one Prop = C1 ∧ C6 ∧ (C7∨C8) mirroring `refuse_to_report` (`identifiability.py:265`), with a single soundness theorem. Glue over C1/C6/C7, not new theory.

### Grade C — needs new theory (out of M1 scope; recorded)

- **A-priori box-invariance for C11.** `neLeg_mapsTo` (`SahaEquilibrium.lean:1326`) discharges `hmapsNe` only given Saha-factor box bounds `[Slo,Shi]` from the partition floor/ceiling of `SahaStability`. An a-priori certificate that the plasma stays in the box needs a proven `S(T)`-range over `[Tmin,Tmax]` (attainable via frontier-02 `sahaFactor_strictMonoOn_temp` + partition floor/ceiling) — a real theorem chain, not a wrapper. Until then C11's box conditions are a-posteriori observable, not a-priori certified (§5 R4). *[2026-09-24: `outerLoop_contracts_apriori` (`SahaRangeEnclosure`) now derives the `n_e` box invariance from two endpoint containments and the level-truncation premise `hEχ`, via `electronDensityFromRatio_mem_Icc` (FM-04); `hmapsT` and `hslopeFloor` remain a-posteriori. The product gate itself still cannot pass (INV-03).]*
- **A certificate that estimated ε/δ are genuine bounds** — not a spec gap; a fundamental epistemic limit (§5 R1/R2). No Lean work fixes it.

---

## 4. Milestone ladder

### M1 — `CflibsFormal/Certificates.lean` (the typed bridge) · grade A

A new leaf module (imports `OLS`, `ErrorBudget`, `SahaEquilibrium`, `PartialLTE`, `SelfAbsorption`, `AtomicDataPerturbation`, `SelfAbsorptionInverse`, `CurveOfGrowth`, `StarkBroadening`; add to `CflibsFormal.lean` root; one `docs/scope-tags.tsv` row per result or docs-sync CI fails). Each certificate is (1) a `def …Certificate (… : ℝ) : Prop` — pure arithmetic over runtime inputs (what the Python checker mirrors); (2) a `theorem …Certificate_sound : …Certificate … → <guarantee>` — a thin re-export; (3) a non-vacuity witness in the house style (`OLS.lean:237`, `SahaEquilibrium.lean:1372`).

A-grade list (inputs → predicate → guarantee theorem): C1 energySpreadCert, C2 jointRankCert, C3 conditioningCert, C4 slopeBudgetCert, C5 tempBudgetCert, C6 compBudgetCert, C7 mcWhirterCert, C9 sahaIterCert, C10 dampedIterCert, C12 knownTauCert, C13 saDistinctCert, C14 aliasBudgetCert (with a `-- REFUSAL: δ assumed, not measured` docstring). See the `milestonesA` field for each spelled out. Best first target: **C10** (highest rent, unconditional, trivial wrapper), then C1/C4/C7 (Python mirrors already exist). *[2026-09-24: M1 landed. C10's "highest rent" rested on the withdrawn damping claim (§1.1): it certifies the forward closure only. C12 landed as `0 ≤ τ` and is non-informative. The landed witnesses for C4, C6 and C14 sit at zero-error corners.]*

### M2 — reference Python checker `cflibs_certificates.py` · grade A (design only; PROPOSED, not installed)

A stdlib-only module in the style of `oracle/check_fixtures.py`, mirroring each M1 `def` as a `…_certificate(inputs) -> (bool, theorem_name, value)`. Consolidates the three existing partial mirrors (`derived_thresholds.py`, `reliability.py`, `identifiability.py`) behind one certificate protocol so every gate returns the theorem it activated. Attach map: C1/C3→`boltzmann.py:fit`+`reliability.py:temperature_conditioning`; C2→`closed_form.py:_build_design_matrix`/`joint_optimizer.py:optimize`; C4/C5/C6→`derived_thresholds.py`→`line_selection.py`; C7/C8→`lte_validator.py:check_mcwhirter`/`reliability.py:stark_saha_lte_gate`; C9→`saha_boltzmann.py:solve_species_states`; C10→`anderson_solver.py:picard_solve` only *[2026-09-24: not the `0.5` damping of the inverse loop, §1.1]*; C11→`iterative.py` outer loop (log `L₁·L₂` verdict beside `converged`) *[2026-09-24: do not wire; the gate cannot pass at realistic parameters, INV-03 / RF-11]*; C12/C13→`self_absorption.py`/`identifiability.py`; C14→`quality.py:per_element_reliability_from_uncertainty`.

### M3 — oracle fixture extension · grade A (extends existing mechanism)

Add a `certificates` scenario array to `oracle/fixtures.json`, emitted by a Float mirror in `oracle/Generate.lean` (same pattern as the existing `error-budget` scenario). Each entry: certificate name, inputs, expected verdict, `theorem` tag. The pipeline's `tests/oracle/` harness (already has `test_derived_thresholds.py`, `test_spec_regression.py`, consumes `fixtures.json`) gains `test_certificates_conformance.py` so a Python↔Lean drift fails CI.

### M4+ — Rust-side + strict-mode CI wiring · design only

`native/` crate mirrors the hot certificates (C1, C4, C7, C10) for the real-time path, conformance-checked against the same `fixtures.json`. Strict mode `CFLIBS_NO_FALLBACK` (`docs/SOLVER_FORMALIZATION_GAPS.md:222`) already gates solves on proven preconditions and refuses; wire each certificate verdict into that decision and into the M8 per-element reliability flags (`quality.py:downgrade_quality_flag:708`) so a failed certificate names its theorem.

---

## 5. Refusals — hypotheses NOT runtime-checkable (the core value)

- **R1 — ε (C4) and δ (C6) are distances to an unknown truth.** `maxPerLineError_sufficient` guarantees `|Δβ|≤τ_β` *given* `∀k |ŷₖ−yₖ|≤ε`, but `yₖ` is the *true* log-intensity; runtime has only an SNR *estimate* of ε. The predicate is checkable; soundness is conditional on the noise model. Report "conditional on SNR model," never "proven." *[2026-09-24: worse, an `ε = 1/SNR` is a one-sigma scale, not a bound; with Gaussian noise of that size on every line the `∀k` premise holds with probability `0.683ⁿ`, about 0.02 at `n = 10` (U-03). A statistical slope certificate is FT-12. Any atomic-data error in the ordinates must also be inside `ε`.]*
- **R2 — atomic-data δ (C14) is unknowable in principle.** You use tabulated data *because* you don't know truth. Only a literature-uncertainty δ (e.g. NIST grade) can be plugged; the bound is as honest as that catalog claim. This is the A* mark. Aligns with the repo's "aliasing = worst-case BIAS not variance" refusal (`frontiers/ROADMAP.md`).
- **R3 — LTE validity (C7) is evaluated at the *recovered* n_e, T → self-referential.** A single-diagnostic pass certifies internal consistency, not physical LTE — which is exactly why C8 (`stark_saha_lte_gate`) requires *two independent* diagnostics (Stark width vs Saha ratio) to agree before clearing McWhirter. Refuse C7-alone as an LTE certificate; require C8. *[2026-09-24: C8 does not exist yet (§0); its designated theorem needs exact Stark = Saha equality. Even two agreeing diagnostics clearing McWhirter give a necessary condition for LTE, not a sufficient one (`PartialLTE`).]*
- **R4 — outer-loop box-invariance + slope-floor (C11) are a-posteriori, not a-priori.** `outerLoop_contracts` needs `hmapsNe`/`hmapsT` (iterates stay in the box) and `hslopeFloor`; whether the plasma stays in box needs a proven `S(T)`-range not yet a runtime input (grade C). The `L₁·L₂<1` gate *is* checkable; the box conditions can only be observed after a run. Do not report C11 as an a-priori convergence proof until the frontier-02→04 Saha-box chain lands. *[2026-09-24: the `n_e` box leg has landed (`outerLoop_contracts_apriori`, §3 grade C), but the `L₁·L₂<1` gate evaluates to 6·10³–5·10⁴ at realistic parameters (INV-03), so C11 is not a usable certificate either way.]*
- **R5 — completeness / missing-mass m is not runtime-checkable at all.** Absolute composition is provably inflated by `1/(1−m)` (`docs/SOLVER_FORMALIZATION_GAPS.md:201`), but m depends on *undetected* sub-threshold species. No certificate can bound it from the observed spectrum. Disposition (already the pipeline's): report absolute fractions as upper bounds, prefer ratios/deltas, flag non-reliable unless completeness is externally certified. No certificate proposed.
- **R6 — Float ≠ ℝ near a threshold.** All predicates are exact-ℝ; checkers are IEEE-754. Near a boundary (`SSₑ≈0`, `L₁·L₂≈1`, `δ≈1`) the float verdict may disagree with the proven ℝ verdict (`docs/SOLVER_FORMALIZATION_GAPS.md:205`). Every threshold certificate carries an interval margin; the oracle's `rtol=1e-6` is ample for O(1)-separated cases but honest about the boundary.
- **R7 — the optical depth τ (C12) is an estimate [2026-09-24].** `0 ≤ τ` says nothing about how far the estimate `τ̂` is from the plasma's optical depth. A `τ`-error bound `|τ̂ − τ| ≤ Δ` is a distance to an unknown truth, R1-type. The FT-13 lemma would turn an assumed `Δ` into a `Δ/2` bound on the log error of the corrected intensity; report that as "conditional on the assumed `τ` error", never as a certificate. The flat-kernel `SA` model adds its own error for peaked profiles (LF-01).

---

## 6. Recommendation

**[2026-09-24] Superseded.** The 2026-07 recommendation was "Attack C10 first, then the already-mirrored A-set (C1, C4, C7)", on the grounds that C10 "pays the most rent for the least work: unconditional theorem, trivial wrapper, and it replaces a *guessed* `0.5` damping (`iterative.py:2022`) with a *proven-convergent* `lam = 1/(1+∑Ntot/S)`". That rationale is withdrawn: C10 certifies the fixed-`T` forward charge-neutrality closure at known `Ntot` and says nothing about the inverse `(T, n_e)` loop or its `0.5` damping (§1.1). M1 has landed as `CflibsFormal/Certificates.lean`, and the parts of the original plan that still hold are these: C1/C4/C7 have Python mirrors, so the Lean wrapper was the missing half; the typed bridge replaces scattered "mirrors a proven theorem" prose (`identifiability.py:12`, `reliability.py:1`, `derived_thresholds.py:1`) and extends the existing `oracle/` + `check_fixtures.py` + `tests/oracle/` mechanism rather than inventing a new bridge; and every wrapped theorem is proven, so the honesty of the bridge lives in §0 and §5.

Current priorities, from the audit:

1. Keep C1–C3 and C12 out of every HARD path until the within-element design certificates (C1g/C2g, RF-16 / FT-04) and the `τ`-error lemma (FT-13) land. C3 adds nothing to C1; C12 adds nothing at all.
2. Certify the loop the pipeline runs: exact reduced-map gain, a damped-Picard window and an a-posteriori residual stop (RF-17 / FT-01). This, not C10 or C11, is what can speak to the `0.5` damping.
3. Replace the zero-error witnesses of C4, C6 and C14 with witnesses at a nonzero error, and do not advertise the `EvaluatorSoundness` bundle as a composition guarantee until the log-derivative `U` leg (RF-18) and a relative closure bound (RF-23) make it informative (§0).
4. Land C8 on error bars (RF-20 / FT-06) and the statistical C4σ (FT-12), each with a refusal note for its assumed inputs.
