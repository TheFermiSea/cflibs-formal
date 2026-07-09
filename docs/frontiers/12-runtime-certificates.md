# Frontier 12 — Runtime certificates: making the verified spec pay rent

*Design dossier. No Lean or pipeline code edited (READ-ONLY on both repos); every current-state claim anchored to a real declaration by `file:line`. This is a bridge design, not a proof frontier — the "obstacle" is an engineering gap, not an open theorem. Scope tags: PURE-MATH / EXACT / REDUCED / APPROXIMATION. Grades A/B/C classify the bridge effort (thin wrapper / new Lean glue / new theory), not the physics.*

---

## 1. The obstacle

The pipeline **already trusts unverified heuristics at points where the spec has a proven gate.** Three anchored instances:

1. **The iteration damping is a hard-coded `0.5`, with only a-posteriori convergence detection.** `IterativeCFLIBSSolver` (`iterative.py:929`) sets `T_K = 0.5*T_prev + 0.5*T_new` (`iterative.py:1965`) and `n_e = 0.5*ne_prev + 0.5*ne_new` (`iterative.py:2022`); the JAX `lax.while` mirror does the same "50/50 damping" (`iterative.py:853,890`). Convergence is only *detected* after the fact by `|ΔT| < tol` (`iterative.py:2039`). **The spec proves an unconditional convergence certificate the solver ignores:** `dampedMultiElementIter_contraction` (`SahaEquilibrium.lean:778`) shows the canonical relaxation `lam = 1/(1 + ∑ₛ Ntotₛ/Sₛ)` contracts at rate `1 − lam < 1` **with no smallness hypothesis on S, Ntot** — a provably-convergent damping the pipeline could compute from its own `S`, `Ntot` instead of guessing `0.5`. Likewise `outerLoop_contracts` (`OuterLoopModelB.lean:75`) gives the outer `T`↔`n_e` sweep a runtime-checkable `L₁·L₂ < 1` gate (`OuterLoopModelB.lean:90-92`); nothing in `iterative.py` evaluates it.

2. **Identifiability is gated qualitatively where the spec proves a quantitative determinant gate.** `temperature_identifiable` (`identifiability.py:84`) counts "≥2 distinct upper-level energies"; the spec's `designNormalMatrix_det_ne_zero_iff` (`OLS.lean:220`) proves the exact rank condition `det M ≠ 0 ↔ 0 < ∑ₖ(Eₖ−Ē)²`, and its scale-free conditioning is settled by `centeredScaledDesign_orthonormal` (`OLS.lean:471`, `κ_scaled = 1`). The joint Saha–Boltzmann fit's identifiability is the full biconditional `jointDesign_det_pos_iff` (`OLS.lean:683`) — with no runtime evaluator in the pipeline.

3. **The bridge already exists for three theorem families — and stops exactly at the iteration/contraction wall.** `derived_thresholds.py` mirrors `ErrorBudget.lean` verbatim and is conformance-pinned to the oracle (`derived_thresholds.py:1-25`, `tests/oracle/test_derived_thresholds.py`); `reliability.py` mirrors `twoLineBeta_stable_sharp`, `composition_dist_vector_le`, `mcWhirterBound`, `stark_saha_lte_consistent`; `identifiability.py:12` states each guard "mirrors a PROVEN identifiability theorem in the companion Lean spec." So the pattern is proven-viable — but it is **prose-cited, not type-linked**: nothing guarantees the Python predicate is the same Prop the theorem discharges, and the highest-value gates (§1.1) have no mirror at all.

The repo's own ledger already frames the target: `docs/SOLVER_FORMALIZATION_GAPS.md:191` — *"Tier 3 — the hypothesis IS the runtime check (wire it; no Lean fix required)"* — and `OuterLoopModelB.lean:71` calls `L₁·L₂ < 1` "the runtime-checkable convergence certificate the solver flag gates on." This dossier turns that scattered intent into **one typed bridge**: a `CflibsFormal/Certificates.lean` where each certificate is a `Prop` of pure float arithmetic paired with a soundness theorem `certificate → guarantee`, plus a reference Python checker mirroring those exact defs — extending the existing `oracle/` + `check_fixtures.py` mechanism, not inventing a new one.

**What "paying rent" means:** when a certificate predicate evaluates `True` on the pipeline's actual floats, a theorem — not a heuristic — guarantees the corresponding well-posedness / convergence / error property. When it evaluates `False`, the honest action (`refuse_to_report`, `identifiability.py:265`; the M8 per-element flags, `quality.py:656`) is already wired; the certificate names which proven precondition failed.

---

## 2. The certificate map

Each row: certificate → data inputs → checkable predicate (floats) → Lean guarantee theorem → pipeline attach point → grade. `SSₑ := ∑ₖ(Eₖ−Ē)²`, `SSₛ`, `S_Es := ∑ₖ(Eₖ−Ē)(sₖ−s̄)`; `Ŝ := ∑ₛN̂ₛ`; `card` = species count.

| # | Certificate | Data inputs | Checkable predicate | Lean guarantee theorem | Pipeline attach point | Grade |
|---|---|---|---|---|---|---|
| C1 | Energy-spread rank / T-identifiable | line energies `E` | `0 < SSₑ` | `OLS.designNormalMatrix_det_ne_zero_iff` (`OLS.lean:220`) ⇒ normal matrix nonsingular ⇒ slope→T recoverable | `identifiability.py:temperature_identifiable:84`; `boltzmann.py:BoltzmannPlotFitter.fit:154` | A |
| C2 | Joint Saha–Boltzmann rank | `E`, ion indicator `s` | `0 < SSₑ·SSₛ − S_Es²` | `OLS.jointDesign_det_pos_iff` (`OLS.lean:683`) ⇒ joint (T,n_e) fit identifiable (E,s not collinear) | `closed_form.py:_build_design_matrix:255`/`_solve_wls:305`; `joint_optimizer.py:optimize:495` | A |
| C3 | Boltzmann-plot conditioning | `E`, `card` | `0 < SSₑ` (⇒ scaled design orthonormal, κ=1) | `OLS.boltzmannConditionNumber_ge_one` (`OLS.lean:341`) + `centeredScaledDesign_orthonormal` (`OLS.lean:471`) ⇒ only genuine sensitivity is `1/SSₑ` | `reliability.py:temperature_conditioning:48` | A |
| C4 | Slope / energy-spread budget | est. per-line err `ε`, target `τ_β`, `card`, `SSₑ` | `ε²·card ≤ τ_β²·SSₑ` | `ErrorBudget.maxPerLineError_sufficient` (`:244`)/`requiredEnergySpread_sufficient` (`:227`) ⇒ `|Δβ| ≤ τ_β` | `derived_thresholds.py:max_per_line_error:48`/`required_energy_spread:42` | A |
| C5 | Temperature-error budget | `k_B`, `T̂`, slope bound `B`, `τ_T` | `k_B·T̂·B ≤ τ_T` (identity `|ΔT|/T=k_B·T̂·|Δβ|`) | `ErrorBudget.temp_rel_error_le` (`:215`)/`temp_rel_error_eq` (`:199`) ⇒ `|T̂−T|/T ≤ τ_T` | `derived_thresholds.py:slope_target_from_temp_rel:65`; `error_budget.py:temp_rel_error_bound:145` | A |
| C6 | Composition budget | per-species err `δ`, `τ_C`, `Ŝ`, `card` | `(card+1)·δ ≤ τ_C·Ŝ` | `ErrorBudget.composition_target_sufficient` (`:325`) ⇒ `|ΔCₛ| ≤ τ_C` ∀s | `derived_thresholds.py:density_budget_from_composition:71`; `reliability.py:composition_error_bound:138` | A |
| C7 | McWhirter LTE admissibility | `T`, gap `ΔE`, `n_e`, `C=1.6e12` | `C·√T·ΔE³ ≤ n_e` | `PartialLTE.mcwhirter_iff_thermalizationLimit` (`PartialLTE.lean:87`) ⇒ `ΔE ≤ E*` | `reliability.py:mcwhirter_min_ne:173`; `lte_validator.py:check_mcwhirter:115` | A |
| C8 | Stark↔Saha LTE self-consistency | `n_e^Stark`, `n_e^Saha`, `T`, `ΔE` | `|Δn_e|/mean ≤ rtol` ∧ `mean ≥ C·√T·ΔE³` | `StarkBroadening.stark_saha_lte_consistent` (`StarkBroadening.lean:189`) ⇒ two independent diagnostics agree + clear McWhirter | `reliability.py:stark_saha_lte_gate:205`; `stark_ne.py:measure_stark_ne:394` | A |
| C9 | Inner Saha-iteration contraction | `S`, `Ntot`, ceiling `b` | `b<Ntot ∧ sahaEquilibriumNe S Ntot ≤ b ∧ √S/(2√(Ntot−b))<1 ∧ √(S·Ntot)≤b` | `SahaEquilibrium.sahaIter_contraction` (`:485`)+`sahaIter_mapsTo` (`:542`)+`sahaIter_tendsto` (`:593`) ⇒ geometric convergence | `saha_boltzmann.py:solve_ionization_balance:164`/`solve_species_states:502` | A |
| C10 | Damped multi-element contraction (UNCONDITIONAL) | `S,Ntot:ι→ℝ` (>0) | none — set `lam=1/(1+∑Ntotₛ/Sₛ)`; rate `1−lam<1` unconditional | `SahaEquilibrium.dampedMultiElementIter_contraction` (`:778`)+`_tendsto` (`:869`); direct loop `multiElementIonized_iter_tendsto` (`:946`) | `anderson_solver.py:picard_solve:646`/`anderson_solve:582`; replaces `0.5` at `iterative.py:2022` | A |
| C11 | Outer T↔n_e loop product gate | `L₁=sahaFactorLipConst/R₀`, `L₂=(|S_Es|/SSₑ)/(k_B·smin²·nemin)`, box, floor `smin` | `L₁·L₂ < 1` ∧ box-invariance ∧ `smin ≤ slope` | `OuterLoopModelB.outerLoop_contracts` (`:75`); spine `outerContraction_box` (`SahaEquilibrium.lean:1269`); 2-D `jointOuterMap_contraction` (`:1426`) ⇒ ∃! fixed point + convergence | `iterative.py:IterativeCFLIBSSolver:929`/`_run_lax_while_loop:775` | B |
| C12 | Self-absorption exact correction (known τ) | `τ ≥ 0` known flag | `tau_known ∧ 0 ≤ τ` (divide by `SA(τ)`) | `SelfAbsorption.lineIntensity_eq_selfAbsorbedIntensity_div` (`:237`) ⇒ exact thin recovery; bias `selfAbsorbedIntensity_le_lineIntensity` (`:152`) | `self_absorption.py:_escape_factor:169`/`correct_with_cog:919` | A |
| C13 | Self-absorption identifiability (N,τ) alias | `n_lines`, `tau_known`, `n_distinct` | `tau_known ∨ (n≥2 ∧ n_distinct≥2)` | `SelfAbsorptionInverse.selfAbsorption_breaks_identifiability` (`:144`)/`CurveOfGrowth.cogRatio_injOn` (`:254`) ⇒ (N,τ) resolvable | `identifiability.py:self_absorption_identifiable:195` | A |
| C14 | Atomic-data aliasing error budget | assumed rel. err `δ` (`0≤δ<1`) | `δ < 1` ⇒ `|N̂−N| ≤ N·δ/(1−δ)` | `AtomicDataPerturbation.classicDensity_aliasing_error` (`:213`); OLS `Alt.olsDensity_aliasing_A_error` (`OLSAtomicDataPerturbation.lean:206`); `olsComposition_atomicData_error` (`:284`) | `quality.py:per_element_reliability_from_uncertainty:656` | A* (§5) |

**Reading the map.** C4–C8, C13 already have Python mirrors (`derived_thresholds.py`, `reliability.py`, `identifiability.py`) — M1 makes them *sound* (type-linked, not just prose-cited) and adds non-vacuity witnesses. C1–C3 *upgrade* the qualitative guards to the proven quantitative determinant/conditioning gates. **C9–C11 are the untapped core** — the convergence certificates that turn guessed `0.5` damping and post-hoc `|ΔT|<tol` into an a-priori theorem. C10 is the headline rent-payer: no gate at all, only a change of the relaxation constant to the proven-convergent `1/(1+∑Ntot/S)`.

---

## 3. Inventory — thin wrappers vs new glue vs new theory

### Grade A — thin wrappers over an existing theorem (implement now)

The Lean theorem's hypothesis is already a pure arithmetic Prop over the exact inputs the pipeline holds; its conclusion *is* the guarantee. Soundness is a one-line re-export.

- **C1, C2, C3** — `designNormalMatrix_det_ne_zero_iff`, `jointDesign_det_pos_iff`, `boltzmannConditionNumber_ge_one`/`centeredScaledDesign_orthonormal` are already biconditionals/inequalities over `SSₑ`, `SSₑ·SSₛ−S_Es²`. Witnesses exist in-repo (`OLS.lean:237,716`).
- **C4, C5, C6** — `maxPerLineError_sufficient`, `temp_rel_error_le`, `composition_target_sufficient` take exactly `(ε,τ_β,card,SSₑ)`, `(k_B,T̂,B)`, `(δ,τ_C,Ŝ,card)`. The predicate *is* the theorem's hypothesis. Float mirrors already in `derived_thresholds.py`, oracle-conformance-tested.
- **C7** — `mcwhirter_iff_thermalizationLimit` is a clean biconditional; predicate = its LHS.
- **C9** — `sahaIter_contraction`+`sahaIter_mapsTo`+`sahaIter_tendsto` exist; bundle their float hypotheses into one Prop, re-export `tendsto`. (Note: the predicate references `sahaEquilibriumNe S Ntot`, the closed-form fixed point, which is computable from `S,Ntot`.)
- **C10** — `dampedMultiElementIter_contraction`/`_tendsto` are *unconditional* for the canonical `lam` (only positivity `∀s, 0<Sₛ ∧ 0<Ntotₛ` required; verified: rate `1−lam<1` with no smallness hypothesis). The "certificate" is trivially true and the guarantee is geometric convergence. Strongest wrapper: essentially no gate.
- **C12** — `lineIntensity_eq_selfAbsorbedIntensity_div` holds for all `τ≥0`; the only "certificate" is that `τ` is known.
- **C13** — the disjunction is exactly `self_absorption_identifiable`'s shape. Note the pairing is looser than a clean biconditional: `selfAbsorption_breaks_identifiability` (`SelfAbsorptionInverse.lean:144`) proves the failure direction and `cogRatio_injOn` (`CurveOfGrowth.lean:254`) the injectivity/recovery direction; the wrapper stitches both.
- **C14** — `classicDensity_aliasing_error` gives `|N̂−N|≤N·δ/(1−δ)` from `δ<1`. Thin, **but `δ` is not runtime-knowable** (§5) — grade-A math, refusal-grade epistemics (A*).

### Grade B — needs new Lean glue

- **C11 (outer-loop product gate)** — `outerLoop_contracts` exists, but `L₁ = sahaFactorLipConst kB Tmin Tmax me h chi …/R₀` is a defined constant needing a Float mirror, and `hmapsNe`/`hmapsT`/`hslopeFloor` are side conditions (confirmed in the signature at `OuterLoopModelB.lean:75-98`). A grade-B certificate packages the **product gate `L₁·L₂<1` as a bare float predicate** (the abstract `outerContraction_box` already accepts `L₁,L₂` as reals) and records the box/floor conditions as runtime-observable side certificates. Glue: (i) a computable `sahaFactorLipConstFloat`; (ii) a soundness lemma stitching the float gate to `outerContraction_box`'s `hq`. The 2-D `jointOuterMap_contraction` (row-sum `max(a+b,c+d)<1`) is the analogous glue.
- **A unified `refuseToReportCertificate`** — one Prop = C1 ∧ C6 ∧ (C7∨C8) mirroring `refuse_to_report` (`identifiability.py:265`), with a single soundness theorem. Glue over C1/C6/C7, not new theory.

### Grade C — needs new theory (out of M1 scope; recorded)

- **A-priori box-invariance for C11.** `neLeg_mapsTo` (`SahaEquilibrium.lean:1326`) discharges `hmapsNe` only given Saha-factor box bounds `[Slo,Shi]` from the partition floor/ceiling of `SahaStability`. An a-priori certificate that the plasma stays in the box needs a proven `S(T)`-range over `[Tmin,Tmax]` (attainable via frontier-02 `sahaFactor_strictMonoOn_temp` + partition floor/ceiling) — a real theorem chain, not a wrapper. Until then C11's box conditions are a-posteriori observable, not a-priori certified (§5 R4).
- **A certificate that estimated ε/δ are genuine bounds** — not a spec gap; a fundamental epistemic limit (§5 R1/R2). No Lean work fixes it.

---

## 4. Milestone ladder

### M1 — `CflibsFormal/Certificates.lean` (the typed bridge) · grade A

A new leaf module (imports `OLS`, `ErrorBudget`, `SahaEquilibrium`, `PartialLTE`, `SelfAbsorption`, `AtomicDataPerturbation`, `SelfAbsorptionInverse`, `CurveOfGrowth`, `StarkBroadening`; add to `CflibsFormal.lean` root; one `docs/scope-tags.tsv` row per result or docs-sync CI fails). Each certificate is (1) a `def …Certificate (… : ℝ) : Prop` — pure arithmetic over runtime inputs (what the Python checker mirrors); (2) a `theorem …Certificate_sound : …Certificate … → <guarantee>` — a thin re-export; (3) a non-vacuity witness in the house style (`OLS.lean:237`, `SahaEquilibrium.lean:1372`).

A-grade list (inputs → predicate → guarantee theorem): C1 energySpreadCert, C2 jointRankCert, C3 conditioningCert, C4 slopeBudgetCert, C5 tempBudgetCert, C6 compBudgetCert, C7 mcWhirterCert, C9 sahaIterCert, C10 dampedIterCert, C12 knownTauCert, C13 saDistinctCert, C14 aliasBudgetCert (with a `-- REFUSAL: δ assumed, not measured` docstring). See the `milestonesA` field for each spelled out. Best first target: **C10** (highest rent, unconditional, trivial wrapper), then C1/C4/C7 (Python mirrors already exist).

### M2 — reference Python checker `cflibs_certificates.py` · grade A (design only; PROPOSED, not installed)

A stdlib-only module in the style of `oracle/check_fixtures.py`, mirroring each M1 `def` as a `…_certificate(inputs) -> (bool, theorem_name, value)`. Consolidates the three existing partial mirrors (`derived_thresholds.py`, `reliability.py`, `identifiability.py`) behind one certificate protocol so every gate returns the theorem it activated. Attach map: C1/C3→`boltzmann.py:fit`+`reliability.py:temperature_conditioning`; C2→`closed_form.py:_build_design_matrix`/`joint_optimizer.py:optimize`; C4/C5/C6→`derived_thresholds.py`→`line_selection.py`; C7/C8→`lte_validator.py:check_mcwhirter`/`reliability.py:stark_saha_lte_gate`; C9→`saha_boltzmann.py:solve_species_states`; **C10→`anderson_solver.py:picard_solve` and the `0.5` at `iterative.py:2022`**; C11→`iterative.py` outer loop (log `L₁·L₂` verdict beside `converged`); C12/C13→`self_absorption.py`/`identifiability.py`; C14→`quality.py:per_element_reliability_from_uncertainty`.

### M3 — oracle fixture extension · grade A (extends existing mechanism)

Add a `certificates` scenario array to `oracle/fixtures.json`, emitted by a Float mirror in `oracle/Generate.lean` (same pattern as the existing `error-budget` scenario). Each entry: certificate name, inputs, expected verdict, `theorem` tag. The pipeline's `tests/oracle/` harness (already has `test_derived_thresholds.py`, `test_spec_regression.py`, consumes `fixtures.json`) gains `test_certificates_conformance.py` so a Python↔Lean drift fails CI.

### M4+ — Rust-side + strict-mode CI wiring · design only

`native/` crate mirrors the hot certificates (C1, C4, C7, C10) for the real-time path, conformance-checked against the same `fixtures.json`. Strict mode `CFLIBS_NO_FALLBACK` (`docs/SOLVER_FORMALIZATION_GAPS.md:222`) already gates solves on proven preconditions and refuses; wire each certificate verdict into that decision and into the M8 per-element reliability flags (`quality.py:downgrade_quality_flag:708`) so a failed certificate names its theorem.

---

## 5. Refusals — hypotheses NOT runtime-checkable (the core value)

- **R1 — ε (C4) and δ (C6) are distances to an unknown truth.** `maxPerLineError_sufficient` guarantees `|Δβ|≤τ_β` *given* `∀k |ŷₖ−yₖ|≤ε`, but `yₖ` is the *true* log-intensity; runtime has only an SNR *estimate* of ε. The predicate is checkable; soundness is conditional on the noise model. Report "conditional on SNR model," never "proven."
- **R2 — atomic-data δ (C14) is unknowable in principle.** You use tabulated data *because* you don't know truth. Only a literature-uncertainty δ (e.g. NIST grade) can be plugged; the bound is as honest as that catalog claim. This is the A* mark. Aligns with the repo's "aliasing = worst-case BIAS not variance" refusal (`frontiers/ROADMAP.md`).
- **R3 — LTE validity (C7) is evaluated at the *recovered* n_e, T → self-referential.** A single-diagnostic pass certifies internal consistency, not physical LTE — which is exactly why C8 (`stark_saha_lte_gate`) requires *two independent* diagnostics (Stark width vs Saha ratio) to agree before clearing McWhirter. Refuse C7-alone as an LTE certificate; require C8.
- **R4 — outer-loop box-invariance + slope-floor (C11) are a-posteriori, not a-priori.** `outerLoop_contracts` needs `hmapsNe`/`hmapsT` (iterates stay in the box) and `hslopeFloor`; whether the plasma stays in box needs a proven `S(T)`-range not yet a runtime input (grade C). The `L₁·L₂<1` gate *is* checkable; the box conditions can only be observed after a run. Do not report C11 as an a-priori convergence proof until the frontier-02→04 Saha-box chain lands.
- **R5 — completeness / missing-mass m is not runtime-checkable at all.** Absolute composition is provably inflated by `1/(1−m)` (`docs/SOLVER_FORMALIZATION_GAPS.md:201`), but m depends on *undetected* sub-threshold species. No certificate can bound it from the observed spectrum. Disposition (already the pipeline's): report absolute fractions as upper bounds, prefer ratios/deltas, flag non-reliable unless completeness is externally certified. No certificate proposed.
- **R6 — Float ≠ ℝ near a threshold.** All predicates are exact-ℝ; checkers are IEEE-754. Near a boundary (`SSₑ≈0`, `L₁·L₂≈1`, `δ≈1`) the float verdict may disagree with the proven ℝ verdict (`docs/SOLVER_FORMALIZATION_GAPS.md:205`). Every threshold certificate carries an interval margin; the oracle's `rtol=1e-6` is ample for O(1)-separated cases but honest about the boundary.

---

## 6. Recommendation

**Attack C10 first, then the already-mirrored A-set (C1, C4, C7).** C10 pays the most rent for the least work: unconditional theorem, trivial wrapper, and it replaces a *guessed* `0.5` damping (`iterative.py:2022`) with a *proven-convergent* `lam = 1/(1+∑Ntot/S)`. C1/C4/C7 already have conformance-pinned Python mirrors, so the Lean wrapper is the only missing half. This converts scattered "mirrors a proven theorem" prose (`identifiability.py:12`, `reliability.py:1`, `derived_thresholds.py:1`) into a single type-linked `Certificates.lean` and extends the existing `oracle/` + `check_fixtures.py` + `tests/oracle/` mechanism rather than inventing a new bridge. Effort for M1 (all grade-A): **S–M** (one focused session for C1–C10 wrappers + witnesses; C11 glue a short follow-up; C14 needs only its refusal docstring). The frontier is favourable because every guarantee theorem is already proven — this is a wiring frontier, and its honesty lives in §5.