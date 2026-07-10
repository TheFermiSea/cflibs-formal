# CF-LIBS numerical regression oracle

Turns the **verified** `CflibsFormal` spec into an executable regression oracle for the
companion numerical pipeline (CF-LIBS-improved): fixtures (`fixtures.json`) that a numerical
implementation must reproduce, where **each check instantiates a proven theorem.**

The fixtures exercise the **multi-element** problem that is the whole point of CF-LIBS (several
chemically distinct elements, each with its own atomic data and partition function `U_s`, tied
together by the closure), across the classic algorithm **and the alternative estimators** the
spec proves sound/equivalent. Six scenarios:

1. **ternary alloy** — 3 chemically-distinct elements, 4 lines each, distinct optical depths:
   checked with the classic inversion, the multi-line **OLS** Boltzmann-plot estimator, the
   **self-absorption** correction (optically-thick input + known `τ`), per-element **temperature**
   recovery, closure, and calibration-free invariance.
2. **two-stage Saha–Boltzmann** — one element in its neutral + ion stages: recover `T` and the
   **electron density `n_e`** from the two stages.
3. **error-budget thresholds** — the empirical `min_energy_spread` / `min_snr` knobs (and the
   temperature/composition budgets) **derived** from the proven error-propagation chain
   (`ErrorBudget.lean`), with self-consistency invariants that witness the derived thresholds.
4. **energy/wavelength ordinate** — one element through the energy forward map
   `lineIntensityEnergy` with **distinct, `E_k`-correlated per-line `λ`** (never `λ=1`): proves
   the wavelength ordinate `ln(I·λ/(gA))` (the companion pipeline's standard form) and the
   photon-rate ordinate `ln(I/(gA))` are the **same** Boltzmann plot (`ForwardMapEnergy.lean`).
5. **Stark broadening + McWhirter** — the Griem linear-width electron-density inverse
   `n_e = nRef·width/(2w)` (`StarkBroadening.starkDensity_recovers`), its forward round trip, and
   the `√T·ΔE³` McWhirter LTE-bound shape (`mcWhirterBound`). Kept dimensionless so the physical
   `REF_NE`/`1.6e12` constants stay out of the lossless formatter; the Python checker applies them.
6. **runtime certificates** — the **typed bridge** (`CflibsFormal/Certificates.lean`, dossier 12
   M3): the **12 certificate predicates** (C1–C7, C9, C10, C12–C14), each a pure-arithmetic `Prop`
   whose truth activates a **proven soundness theorem** (well-posedness / convergence / error
   guarantee). Each is emitted on its **non-vacuity witness** (the exact inputs of the Lean
   `example`s), with the concrete inputs, expected boolean verdict, decisive value (determinant /
   contraction rate / budget margin), and guarantee theorem — plus the reference mirror's **four
   rejection tests** (`docs/integration/cflibs_certificates.py`). The Float mirror is 1:1 with each
   `def …Cert` (**same inequalities, same strictness**); the checker re-derives verdict + value and
   requires agreement.

## Files

| file | role |
| --- | --- |
| `Generate.lean` | a computable **`Float` mirror** of the verified forward map, classic inversion, OLS / self-absorbed / Saha estimators; emits `fixtures.json`. Built as `lake exe oracle-fixtures`. |
| `fixtures.json` | a `scenarios` array; each scenario has a `kind`, its data, and `checks` tagged with the theorem each instantiates. |
| `check_fixtures.py` | reference checker (pure stdlib). Self-checks the fixtures; **swap the `IMPL` block for calls into your pipeline** to regression-test it. |

## Regenerate / run

```bash
lake exe oracle-fixtures > oracle/fixtures.json   # regenerate from the Lean mirror
python3 oracle/check_fixtures.py                   # check (exit 0 = pass, 1 = fail)
```

## What is and isn't verified (read this)

The definitions in `CflibsFormal/` are **`noncomputable` and ℝ-valued** (ℝ is not computable),
so they cannot be `#eval`'d. `Generate.lean` re-implements the **same formulas over `Float`**.

- **Verified:** the *formula structure* (each `Float` def matches a proven ℝ def) and the
  *invariants* (the checks below are proven theorems).
- **Not verified:** the IEEE-754 numerical evaluation (`Float ≠ ℝ`). Checks are
  **tolerance-based** (`rtol = 1e-6`) — ample for catching formula/sign/factor/inversion bugs
  (which differ by ≫ that), not a bit-exact comparison.

Inputs are **dimensionless** (matching the spec; `kB = T = 1`, `E` in units of `kB·T`). Feed
your pipeline these exact inputs. Atomic data is synthetic but **distinct per element**; swap in
NIST values (and your unit convention) freely.

## Fixture ↔ theorem map

**Scenario 1 — ternary alloy:**

| check | asserts | proven by |
| --- | --- | --- |
| `forward` | `lineIntensity` with each element's own `(g,E,A)` reproduces its lines (and `U_s` per element) | `ForwardMap.lineIntensity` + `boltzmann_plot_intensity` |
| `round_trip` | `classicDensity(lineIntensity(N)) == N` per element (own `U_s`) | `Classic.classicDensity_recovers` / `classic_sound` |
| `temperature` | 2-line Boltzmann-plot slope recovers `T`, per element | `Classic.classic_temperature_correct` |
| `ols` | OLS regression over **all** lines recovers `N` per element; OLS composition `==` classic/true | `Alt.olsDensity_recovers` / `leastSquares_sound` / `leastSquares_agrees_classic` |
| `self_absorbed` | from optically-thick intensities (`thin·SA(τ)`) + known `τ`, the corrected estimator recovers the true composition | `Alt.selfAbsorbed_sound` |
| `closure` | recovered composition `== N_s/ΣN` and sums to 1, across heterogeneous elements | `Closure.composition_sum_one` / `classic_sound` |
| `calibration_free` | scaling `Fcal` leaves composition unchanged | `Classic.classic_calibration_free` |

**Scenario 2 — two-stage Saha–Boltzmann:**

| check | asserts | proven by |
| --- | --- | --- |
| `temperature` | neutral 2-line slope recovers `T` | `Classic.classic_temperature_correct` |
| `saha` | recover `N_z`, `N_{z+1}` from the two stages; `R = N_{z+1}/N_z`; `n_e = S(T)/R == ` true `n_e`; and `R·n_e == S(T)` | `Saha.electronDensityFromRatio` / `saha_relation` / `electronDensity_antitone` / `SahaInverse.saha_joint_identifiability` |

**Scenario 3 — error-budget thresholds:**

The `thresholds` are the DERIVED magic numbers (Float mirrors of the `ErrorBudget.lean` formulas);
each `checks` entry is a self-consistency invariant of a proven theorem.

| check | asserts | proven by |
| --- | --- | --- |
| `energy_spread_tight` | `slopeErrorBound(snr, n, requiredEnergySpread(τ_β,snr,n)) == τ_β` — the derived `min_energy_spread` is exactly tight | `ErrorBudget.requiredEnergySpread_sufficient` (+ `olsSlope_stable_l2`) |
| `snr_tight` | `slopeErrorBound(maxPerLineError(τ_β,n,ssE), n, ssE) == τ_β` — the derived `min_snr` is exactly tight | `ErrorBudget.maxPerLineError_sufficient` (+ `olsSlope_stable_l2`) |
| `noise_gain` | `noiseGain == 1/ssE` — the Gauss–Markov slope-variance multiplier (kernel of the statistical line-count law) | `ErrorBudget.olsSlope_noise_gain` |
| `temp_rel` | `slopeTargetFromTempRel(relTtarget,kB,T)·(kB·T) == relTtarget` — exact `σ_T/T` ↔ `σ_β` conversion | `ErrorBudget.temp_rel_error_eq` |
| `composition_budget` | `(card+1)·densityBudgetFromComposition(τ_C,Ŝ,card) == τ_C·Ŝ` — composition target ↦ per-species density budget | `ErrorBudget.composition_target_sufficient` (+ `composition_abs_sub_le`) |

Note `requiredMinLinesStat` is the **statistical** (Gauss–Markov) line-count law: the deterministic
worst-case bounds (`olsSlope_stable_l1`/`_l2`) show energy spread and SNR dominate, but do not give
a line-count threshold — only `olsSlope_noise_gain` (the `1/ssE` kernel under independent noise)
does. See the `ErrorBudget.lean` module docstring.

**Scenario 4 — energy/wavelength ordinate:**

One element fed through `lineIntensityEnergy` with **distinct, `E_k`-correlated per-line `λ`**
(`element.lambda`, never `λ=1`). Demonstrates that the wavelength ordinate `ln(I·λ/(gA))` and the
photon-rate ordinate `ln(I/(gA))` are the same Boltzmann plot.

| check | asserts | proven by |
| --- | --- | --- |
| `forward` | `lineIntensityEnergy(hc,4π,N,Fgeo, g,E,A,λ, k) == element.intensities[k]` | `ForwardMapEnergy.lineIntensityEnergy` |
| `reduction` | `lineIntensityEnergy[k] == lineIntensity` with the **per-line** `Fcal = hc·Fgeo/(4π·λ_k)` | `ForwardMapEnergy.lineIntensityEnergy_eq_lineIntensity` |
| `mul_lam` | `lineIntensityEnergy[k]·λ_k == lineIntensity` with the **λ-free** `Fcal = hc·Fgeo/(4π)` (λ cancels the `1/λ` photon-energy factor) | `ForwardMapEnergy.lineIntensityEnergy_mul_lam` |
| `temperature` | the 2-line slope of `ln(I·λ/(gA))` vs `E` recovers `T` exactly (λ cancels; distinct per-line λ) | `ForwardMapEnergy.temperature_from_two_lines_wavelength` |

Why **distinct** per-line λ matters: a `λ=1` fixture is blind to every λ-bug (they cancel
uniformly). A λ-drop bug (pipeline omits the `1/λ` factor) **tilts the slope** because λ
correlates with `E_k` → wrong `T`. The negative test (drop `1/λ` in `line_intensity_energy`)
fails 13 checks including the temperature recovery (`T → 0.893` vs `1.0`).

**Scenario 6 — runtime certificates (the typed bridge):**

The `certificates` array carries one entry per predicate in `CflibsFormal/Certificates.lean`
(dossier 12 M3), each on its **non-vacuity witness** (the exact inputs of the module's Lean
`example`s). Every entry is `{id, name, theorem, predicate, inputs, verdict, value}`: the Float
mirror emits the expected boolean `verdict` and the decisive `value` (the number the predicate
compares — a determinant, contraction rate, or budget margin); the checker re-derives both from
`inputs` and requires agreement (the value only where `verdict` holds — a margin/rate is
meaningful only on the accept side). Each `…Cert` mirror is 1:1 with its Lean `def`: **same
inequalities, same strictness**. A certificate is **SUFFICIENT** for its guarantee, generally not
necessary; a `False` verdict names which proven precondition failed, it does not disprove the
guarantee. `value`s use the same formulas as the reference mirror `docs/integration/cflibs_certificates.py`.

| id | predicate (verdict) · decisive value | guarantee theorem (soundness re-export) |
| --- | --- | --- |
| `C1` energy_spread | `0 < SSₑ` · `SSₑ` | `OLS.designNormalMatrix_det_ne_zero_iff` — Boltzmann normal matrix nonsingular ⇒ T-identifiable |
| `C2` joint_rank | `0 < SSₑ·SSₛ − S_Es²` · joint Gram det | `OLS.jointDesign_det_pos_iff` — centered `E`,`s` not collinear ⇒ joint (T,nₑ) identifiable |
| `C3` conditioning | `0 < SSₑ` · `SSₑ` | `OLS.boltzmannConditionNumber_ge_one` (+ `centeredScaledDesign_orthonormal`) — κ≥1, scaled design orthonormal |
| `C4` slope_budget | `ε²·n ≤ τ_β²·SSₑ` · slack `rhs−lhs` | `ErrorBudget.maxPerLineError_sufficient` — `\|Δβ\| ≤ τ_β` (ε epistemic, R1) |
| `C5` temp_budget | `k_B·T̂·B ≤ τ_T` · slack `τ_T−lhs` | `ErrorBudget.temp_rel_error_le` — `\|ΔT\|/T ≤ τ_T` (B epistemic, R1) |
| `C6` comp_budget | `(n+1)·δ ≤ τ_C·Ŝ` · slack `rhs−lhs` | `ErrorBudget.composition_target_sufficient` — `\|ΔCₛ\| ≤ τ_C` ∀s (δ epistemic, R1) |
| `C7` mcwhirter | `C·√T·ΔE³ ≤ nₑ` · margin `nₑ−lhs` | `PartialLTE.mcwhirter_iff_thermalizationLimit` — `ΔE ≤ E*` (internal consistency only, R3) |
| `C9` saha_iter | `b<Ntot ∧ root≤b ∧ √S/(2√(Ntot−b))<1 ∧ √(S·Ntot)≤b` · rate | `SahaEquilibrium.sahaIter_tendsto` — geometric convergence to `sahaEquilibriumNe S Ntot` |
| `C10` damped_iter | `∀s Sₛ>0 ∧ Ntotₛ>0` · rate `1−lam` | `SahaEquilibrium.dampedMultiElementIter_tendsto` — **UNCONDITIONAL** convergence at `1−lam<1`, canonical `lam=1/(1+∑Ntot/S)` |
| `C12` known_tau | `0 ≤ τ` · `τ` | `SelfAbsorption.lineIntensity_eq_selfAbsorbedIntensity_div` — exact thin recovery `I_thin=I_meas/SA(τ)` |
| `C13` sa_distinct | `0 < w₂ ∧ w₂ < w₁` · gap `w₁−w₂` | `CurveOfGrowth.cogRatio_injOn` — curve-of-growth ratio injective ⇒ N resolved without source scale |
| `C14` alias_budget | `0 ≤ δ ∧ δ < 1` · amp `δ/(1−δ)` | `AtomicDataPerturbation.classicDensity_aliasing_error` — `\|N̂−N\| ≤ N·δ/(1−δ)` (**A\***: δ ASSUMED, not measured, R2) |

**Four rejection tests** (mirroring `docs/integration/cflibs_certificates.py`, honest-refusal side):
`C1` flat energies `E=[1,1]` (`SSₑ=0`); `C2` collinear `E=[0,1]`, `s=[0,2]` (det `=0`); `C10`
nonpositive Saha factor `S=[0,1]` (fails `0<Sₛ`); `C14` `δ=1` (fails `δ<1`). Each has
`verdict:false`; the checker recomputes `false` and would flag any predicate that wrongly accepts.
Verified non-vacuous: tampering any positive/negative verdict or a decisive value fails the checker.

## Why multi-element (and why a single family is insufficient)

CF-LIBS recovers the composition of *different* elements; each has a distinct partition function
`U_s(T)`, and the de-normalization `N_s = I·U_s/(Fcal·A·g·bf)` uses a **different `U_s` per
element**. A fixture that gave every element the **same** `(g,E,A)` would miss this: dropping or
sharing `U_s` still gives the right composition because the common `U` cancels in
`(N_s/U)/Σ(N_t/U) = N_s/ΣN`. With **distinct** `U_s` it does not cancel — so the multi-element
fixtures catch exactly the bugs the single-family case cannot. (Verified: dropping the
per-element `U_s` fails `round_trip` and corrupts `closure`, whereas it would pass under a single
family.)

**Why forward AND invariant checks:** a *consistent* formula error (e.g. a flipped Boltzmann sign
in BOTH the forward and inverse) cancels in the round-trip/closure checks — only the `forward`
check, comparing to the verified-spec ground truth, catches it. The invariant checks catch
inversion/closure/calibration/`n_e` bugs the forward check cannot. You need both. (Verified: a
wrong thermal-bracket power in the Saha factor fails the `saha` `n_e` check.)
