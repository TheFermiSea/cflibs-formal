/-
Copyright (c) 2026 Brian Squires. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Squires
-/
import Mathlib
import CflibsFormal.OLS
import CflibsFormal.ErrorBudget
import CflibsFormal.PartialLTE
import CflibsFormal.SahaEquilibrium
import CflibsFormal.SelfAbsorption
import CflibsFormal.CurveOfGrowth
import CflibsFormal.AtomicDataPerturbation

/-!
# CF-LIBS formalization — runtime certificates (the typed bridge)

This module is the **typed bridge** between the verified spec and a floating-point pipeline.
Each *certificate* is a `def …Cert (… : ℝ) : Prop` whose body is **pure arithmetic** over the
runtime inputs the pipeline already holds (comparisons, `+ − · /`, `max`, `Real.sqrt`) — exactly
the predicate a float checker can evaluate. Paired with each certificate is a **soundness
theorem** `…_certificate_sound : …Cert … → <guarantee>` that is a *thin re-export* of an existing
`CflibsFormal` theorem (named in each docstring): when the arithmetic predicate holds on the
pipeline's actual floats, a proven theorem — not a heuristic — guarantees the corresponding
well-posedness / convergence / error property. Every certificate carries a concrete non-vacuity
witness that both satisfies the predicate and exercises the guarantee.

## Honest scope

* A certificate is **SUFFICIENT** for its guarantee, and (except where the wrapped theorem is a
  biconditional, C1/C2/C7) **generally not necessary**. A `False` verdict names which proven
  precondition failed; it does not prove the guarantee false.
* **Only runtime-checkable arithmetic lives in a certificate.** Hypotheses that reference an
  *unknown truth* stay OUT of the `Cert` and remain explicit hypotheses of the soundness theorem
  (the dossier §5 refusals): the per-line error bound `ε` (C4) and per-species density error `δ`
  (C6) are distances to the true intensities/densities (R1); the atomic-data aliasing `δ` (C14) is
  unknowable in principle (R2, the A* mark — see the `-- REFUSAL` note there); the fixed-point
  data `r`, the slope-error bound `B`, and all positivity of *true* quantities are epistemic
  inputs, never part of the checkable predicate.
* **C10 is unconditional.** Unlike the scalar Saha leg (C9), the damped multi-element iteration
  converges at rate `1 − lam < 1` with *no* smallness/contraction side condition — the certificate
  is just positivity of the (physically always positive) Saha factors and total densities.
* **Float ≠ ℝ near a threshold (R6).** All predicates are exact-ℝ; a float checker is IEEE-754, so
  near a boundary (`SS_E ≈ 0`, `δ ≈ 1`) the float verdict may disagree with the proven ℝ verdict.
  The companion checker carries an interval margin.

The reference Python mirror is `docs/integration/cflibs_certificates.py` (one function per
certificate, 1:1 with these defs).

## Literature

The wrapped theorems (and hence these certificates) inherit their physics citations: the
Boltzmann-plot rank / conditioning gates (C1–C3) from Tognoni et al. 2010 and Aguilera & Aragón
2007; the deterministic error budget (C4–C6) from Tognoni et al. 2010; the McWhirter LTE criterion
(C7) from R. W. P. McWhirter (1965) via G. Cristoforetti et al., *Spectrochim. Acta B* **65**
(2010) 86–95; the Saha–Eggert closure iterations (C9, C10) from H. R. Griem, *Principles of Plasma
Spectroscopy* (1997); the self-absorption / curve-of-growth recovery (C12, C13) from I. B.
Gornushkin et al. 1999 and Cristoforetti & Tognoni 2013; and the atomic-data aliasing floor (C14)
from Tognoni et al. 2010. This module adds **no new mathematics** — it only re-exports.
-/

namespace CflibsFormal

variable {ι : Type*} [Fintype ι]

/-! ## C1 — Energy-spread rank gate (T-identifiability)

Wraps `OLS.designNormalMatrix_det_ne_zero_iff` (`OLS.lean:220`). Predicate: positive energy
spread. Guarantee: the Boltzmann-plot normal matrix is nonsingular, so the slope→T fit is
well-posed. -/

/-- **C1 certificate.** Positive energy spread `SS_E = ∑ₖ (Eₖ − Ē)² > 0` — the runtime rank gate
mirrored by the pipeline's `temperature_identifiable` guard. -/
def energySpreadCert (E : ι → ℝ) : Prop := 0 < ∑ k, (E k - mean E) ^ 2

/-- **C1 soundness** (thin re-export of `designNormalMatrix_det_ne_zero_iff`, `OLS.lean:220`). A
positive energy spread certifies the Boltzmann-plot normal matrix is nonsingular. -/
theorem energySpread_certificate_sound [Nonempty ι] (E : ι → ℝ)
    (hcert : energySpreadCert E) : (designNormalMatrix E).det ≠ 0 :=
  (designNormalMatrix_det_ne_zero_iff E).mpr hcert

-- Non-vacuity: two lines at distinct energies `E = (0, 1)` (`SS_E = 1/2 > 0`) certify a
-- nonsingular design (`det = 1 ≠ 0`).
example : (designNormalMatrix (ι := Fin 2) ![0, 1]).det ≠ 0 :=
  energySpread_certificate_sound ![0, 1]
    (by norm_num [energySpreadCert, mean, Fin.sum_univ_two])

/-! ## C2 — Joint Saha–Boltzmann rank gate

Wraps `OLS.jointDesign_det_pos_iff` (`OLS.lean:683`) via `det_jointDesignNormalMatrix`. Predicate:
`SS_E·SS_s − S_Es² > 0`. Guarantee: the centered energies and ion-stage indicator are not
proportional, so the joint (T, nₑ) fit is identifiable. -/

/-- **C2 certificate.** Positive joint Gram determinant per line-count,
`SS_E·SS_s − S_Es² > 0`, with `S_Es = ∑ₖ (Eₖ − Ē)(sₖ − s̄)` — the runtime identifiability gate for
the three-column `[1 | E | s]` design. -/
def jointRankCert (E s : ι → ℝ) : Prop :=
  0 < (∑ k, (E k - mean E) ^ 2) * (∑ k, (s k - mean s) ^ 2)
        - (∑ k, (E k - mean E) * (s k - mean s)) ^ 2

/-- **C2 soundness** (thin re-export of `jointDesign_det_pos_iff`, `OLS.lean:683`). A positive
joint Gram determinant certifies the centered energies and ion indicator are not collinear, i.e.
the joint (T, nₑ) fit is identifiable. -/
theorem jointRank_certificate_sound [Nonempty ι] (E s : ι → ℝ)
    (hcert : jointRankCert E s) : ¬ jointDesignCenteredProportional E s := by
  apply (jointDesign_det_pos_iff E s).mp
  rw [det_jointDesignNormalMatrix]
  exact mul_pos (by exact_mod_cast Fintype.card_pos) hcert

-- Non-vacuity: `E = (0,1,2)`, `s = (0,0,1)` (two neutral, one ionized line) gives
-- `SS_E·SS_s − S_Es² = 2·(2/3) − 1 = 1/3 > 0`, so the joint fit is identifiable.
example : ¬ jointDesignCenteredProportional (ι := Fin 3) ![0, 1, 2] ![0, 0, 1] :=
  jointRank_certificate_sound ![0, 1, 2] ![0, 0, 1]
    (by unfold jointRankCert mean; simp [Fin.sum_univ_three]; norm_num)

/-! ## C3 — Boltzmann-plot conditioning

Wraps `OLS.boltzmannConditionNumber_ge_one` (`OLS.lean:341`) and
`OLS.centeredScaledDesign_orthonormal` (`OLS.lean:471`). Same predicate as C1. Guarantee: the raw
condition number is `≥ 1`, and the *scaled* design is orthonormal (`κ_scaled = 1`), so the only
genuine, scale-free sensitivity is the slope noise gain `1/SS_E`. -/

/-- **C3 certificate.** Positive energy spread — identical to `energySpreadCert`, restated because
it gates a distinct guarantee (conditioning rather than rank). -/
def conditioningCert (E : ι → ℝ) : Prop := 0 < ∑ k, (E k - mean E) ^ 2

/-- **C3 soundness** (thin re-export of `boltzmannConditionNumber_ge_one` +
`centeredScaledDesign_orthonormal`, `OLS.lean:341,471`). Positive spread certifies `κ ≥ 1` and the
scaled centered design is orthonormal (`κ_scaled = 1`): no residual matrix-conditioning content
beyond the scale-free slope gain `1/SS_E`. -/
theorem conditioning_certificate_sound [Nonempty ι] (E : ι → ℝ)
    (hcert : conditioningCert E) :
    1 ≤ boltzmannConditionNumber E
      ∧ (∑ k, ((E k - mean E) / Real.sqrt (∑ k, (E k - mean E) ^ 2)) ^ 2 = 1)
      ∧ (∑ _k : ι, (1 / Real.sqrt (Fintype.card ι : ℝ)) ^ 2 = (1 : ℝ))
      ∧ (∑ k, ((E k - mean E) / Real.sqrt (∑ k, (E k - mean E) ^ 2))
            * (1 / Real.sqrt (Fintype.card ι : ℝ)) = 0) :=
  ⟨boltzmannConditionNumber_ge_one E hcert, centeredScaledDesign_orthonormal E hcert⟩

-- Non-vacuity: `E = (0,1)` has `κ = max(1/2, 2)/min(1/2, 2) = 4 ≥ 1` (a genuine `κ > 1`).
example : 1 ≤ boltzmannConditionNumber (ι := Fin 2) ![0, 1] :=
  (conditioning_certificate_sound ![0, 1]
    (by norm_num [conditioningCert, mean, Fin.sum_univ_two])).1

/-! ## C4 — Slope / energy-spread error budget

Wraps `ErrorBudget.maxPerLineError_sufficient` (`ErrorBudget.lean:244`). Predicate:
`ε²·card ≤ τ_β²·SS_E`. Guarantee: the OLS slope (inverse-temperature) error is within `τ_β`.
`ε` is a distance to the *true* ordinates and stays out of the certificate (R1). -/

/-- **C4 certificate.** The per-line error / energy-spread budget `ε²·n ≤ τ_β²·SS_E` (`n` = line
count). Runtime-checkable given the SNR estimate `ε`, the target slope error `τ_β`, and the design
quantities `n`, `SS_E`. -/
def slopeBudgetCert (eps tauBeta SSe : ℝ) (n : ℕ) : Prop :=
  eps ^ 2 * (n : ℝ) ≤ tauBeta ^ 2 * SSe

/-- **C4 soundness** (thin re-export of `maxPerLineError_sufficient`, `ErrorBudget.lean:244`). If
the per-line error is bounded by `ε` (an epistemic input, R1) and the budget certificate holds,
the OLS slope error is `≤ τ_β`. -/
theorem slopeBudget_certificate_sound [Nonempty ι] {E y yHat : ι → ℝ} {eps tauBeta : ℝ}
    (htau : 0 < tauBeta) (hvar : 0 < ∑ k, (E k - mean E) ^ 2)
    (hδ : ∀ k, |yHat k - y k| ≤ eps)
    (hcert : slopeBudgetCert eps tauBeta (∑ k, (E k - mean E) ^ 2) (Fintype.card ι)) :
    |olsSlope E yHat - olsSlope E y| ≤ tauBeta :=
  maxPerLineError_sufficient htau hvar hδ hcert

-- Non-vacuity: `E = (0,1)` (`SS_E = 1/2`), `ε = 1`, `τ_β = 2`: the budget `1²·2 ≤ 2²·(1/2)` is
-- tight (`2 ≤ 2`), certifying the slope error stays `≤ 2` (exercised at the noise-free `ŷ = y`).
example : |olsSlope (ι := Fin 2) ![0, 1] ![0, 0] - olsSlope ![0, 1] ![0, 0]| ≤ 2 :=
  slopeBudget_certificate_sound (eps := 1) (by norm_num)
    (by norm_num [mean, Fin.sum_univ_two]) (fun k => by norm_num)
    (by norm_num [slopeBudgetCert, mean, Fin.sum_univ_two])

/-! ## C5 — Temperature-error budget

Wraps `ErrorBudget.temp_rel_error_le` (`ErrorBudget.lean:215`, exact identity `temp_rel_error_eq`).
Predicate: `k_B·T̂·B ≤ τ_T`. Guarantee: the relative temperature error is within `τ_T`. `B` (a
slope-error bound) is an epistemic input (R1). -/

/-- **C5 certificate.** The temperature budget `k_B·T̂·B ≤ τ_T`, where `B` bounds the
inverse-temperature (slope) error. Uses the exact identity `|ΔT|/T = k_B·T̂·|Δβ|`. -/
def tempBudgetCert (kB THat B tauT : ℝ) : Prop := kB * THat * B ≤ tauT

/-- **C5 soundness** (thin re-export of `temp_rel_error_le`, `ErrorBudget.lean:215`). Given a
slope-error bound `B` (epistemic, R1) and the temperature budget, the relative temperature error is
`≤ τ_T`. -/
theorem tempBudget_certificate_sound {kB T THat B tauT : ℝ}
    (hkB : 0 < kB) (hT : 0 < T) (hTHat : 0 < THat)
    (hB : |1 / (kB * THat) - 1 / (kB * T)| ≤ B)
    (hcert : tempBudgetCert kB THat B tauT) :
    |THat - T| / T ≤ tauT :=
  le_trans (temp_rel_error_le hkB hT hTHat hB) hcert

-- Non-vacuity: `k_B = 1`, `T = 1`, `T̂ = 2`, `B = 1/2`, `τ_T = 1`: the budget `1·2·(1/2) ≤ 1` is
-- tight, certifying the relative error `|2 − 1|/1 = 1 ≤ 1` (a genuine, nonzero, tight bound).
example : |(2 : ℝ) - 1| / 1 ≤ 1 :=
  tempBudget_certificate_sound (kB := 1) (T := 1) (THat := 2) (B := 1 / 2) (tauT := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [tempBudgetCert])

/-! ## C6 — Composition error budget

Wraps `ErrorBudget.composition_target_sufficient` (`ErrorBudget.lean:325`). Predicate:
`(card + 1)·δ ≤ τ_C·Ŝ`. Guarantee: each composition fraction is within `τ_C`. `δ` (per-species
density error) is a distance to the truth and stays out of the certificate (R1). -/

/-- **C6 certificate.** The composition budget `(m + 1)·δ ≤ τ_C·Ŝ` (`m` = species count,
`Ŝ = ∑ₛ N̂ₛ`), with `δ` the per-species absolute density error. -/
def compBudgetCert (delta tauC Shat : ℝ) (n : ℕ) : Prop :=
  ((n : ℝ) + 1) * delta ≤ tauC * Shat

/-- **C6 soundness** (thin re-export of `composition_target_sufficient`, `ErrorBudget.lean:325`).
Given a per-species density error bounded by `δ` (epistemic, R1) and the composition budget, every
composition fraction error is `≤ τ_C`. -/
theorem compBudget_certificate_sound {κ : Type*} [Fintype κ] {N Nhat : κ → ℝ} {delta tauC : ℝ}
    (hN : ∀ s, 0 ≤ N s) (hS : 0 < totalDensity N) (hShat : 0 < totalDensity Nhat)
    (hdelta : ∀ s, |Nhat s - N s| ≤ delta)
    (hcert : compBudgetCert delta tauC (totalDensity Nhat) (Fintype.card κ)) (s : κ) :
    |composition Nhat s - composition N s| ≤ tauC :=
  composition_target_sufficient hN hS hShat hdelta hcert s

-- Non-vacuity: two species `N = N̂ = (1, 1)` (`Ŝ = 2`), `δ = 1`, `τ_C = 2`: the budget
-- `(2 + 1)·1 ≤ 2·2` holds non-trivially (`3 ≤ 4`), certifying each fraction error `≤ 2`.
example : |composition (κ := Fin 2) ![1, 1] 0 - composition ![1, 1] 0| ≤ 2 :=
  compBudget_certificate_sound (N := ![1, 1]) (Nhat := ![1, 1]) (delta := 1) (tauC := 2)
    (fun s => by fin_cases s <;> norm_num)
    (by simp [totalDensity, Fin.sum_univ_two])
    (by simp [totalDensity, Fin.sum_univ_two])
    (fun s => by fin_cases s <;> norm_num)
    (by simp [compBudgetCert, totalDensity, Fin.sum_univ_two]; norm_num) 0

/-! ## C7 — McWhirter LTE admissibility

Wraps `PartialLTE.mcwhirter_iff_thermalizationLimit` (`PartialLTE.lean:87`), a biconditional.
Predicate: `C·√T·ΔE³ ≤ nₑ`. Guarantee: the transition gap is within the thermalization limit
(collisionally LTE-admissible). See R3: a single diagnostic certifies *internal consistency*, not
physical LTE. -/

/-- **C7 certificate.** The McWhirter density condition `C·√T·ΔE³ ≤ nₑ` (`C = 1.6·10¹²` in CGS). -/
def mcWhirterCert (C T dE ne : ℝ) : Prop := C * Real.sqrt T * dE ^ 3 ≤ ne

/-- **C7 soundness** (thin re-export of `mcwhirter_iff_thermalizationLimit`, `PartialLTE.lean:87`).
The McWhirter density condition certifies the transition gap `ΔE` is within the thermalization
limit `E*`. -/
theorem mcWhirter_certificate_sound {C T dE ne : ℝ}
    (hC : 0 < C) (hT : 0 < T) (hdE : 0 ≤ dE) (hne : 0 ≤ ne)
    (hcert : mcWhirterCert C T dE ne) :
    dE ≤ thermalizationLimit C T ne :=
  (mcwhirter_iff_thermalizationLimit hC hT hdE hne).mp hcert

-- Non-vacuity: `C = 1`, `T = 1`, `ΔE = 1`, `nₑ = 2`: `1·√1·1³ = 1 ≤ 2` certifies
-- `ΔE = 1 ≤ E* = 2^(1/3) ≈ 1.26` (a genuine strict admissibility margin).
example : (1 : ℝ) ≤ thermalizationLimit 1 1 2 :=
  mcWhirter_certificate_sound (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [mcWhirterCert, Real.sqrt_one])

/-! ## C9 — Inner Saha-iteration contraction

Wraps `SahaEquilibrium.sahaIter_tendsto` (`SahaEquilibrium.lean:593`, via `_contraction` /
`_mapsTo`). Predicate: the four interval/contraction clauses. Guarantee: the fixed-point iteration
converges geometrically to the closed-form root `sahaEquilibriumNe S Ntot`. -/

/-- **C9 certificate.** The four runtime clauses for the single-element two-stage Saha iteration:
`b < Ntot`, the closed-form root `sahaEquilibriumNe S Ntot ≤ b`, the contraction rate
`√S/(2·√(Ntot − b)) < 1`, and the interval-invariance bound `√(S·Ntot) ≤ b`. -/
def sahaIterCert (S Ntot b : ℝ) : Prop :=
  b < Ntot
    ∧ sahaEquilibriumNe S Ntot ≤ b
    ∧ Real.sqrt S / (2 * Real.sqrt (Ntot - b)) < 1
    ∧ Real.sqrt (S * Ntot) ≤ b

/-- **C9 soundness** (thin re-export of `sahaIter_tendsto`, `SahaEquilibrium.lean:593`). The four
clauses, with positivity of `S`, `Ntot` and a start `x₀ ∈ [0, b]`, certify geometric convergence
of the iterates to the closed-form electron density. -/
theorem sahaIter_certificate_sound {S Ntot b x0 : ℝ} (hS : 0 < S) (hN : 0 < Ntot)
    (hx0 : 0 ≤ x0) (hx0b : x0 ≤ b) (hcert : sahaIterCert S Ntot b) :
    Filter.Tendsto (fun n => (sahaIter S Ntot)^[n] x0) Filter.atTop
      (nhds (sahaEquilibriumNe S Ntot)) :=
  sahaIter_tendsto hS hN hcert.1 hcert.2.1 hcert.2.2.2 hcert.2.2.1 hx0 hx0b

-- Non-vacuity: `S = 1`, `Ntot = 3`, `b = 2`, start `x₀ = 0`. All four clauses hold
-- (`2 < 3`; root `(−1+√13)/2 ≈ 1.30 ≤ 2`; rate `√1/(2√1) = 1/2 < 1`; `√3 ≈ 1.73 ≤ 2`), certifying
-- convergence to `sahaEquilibriumNe 1 3`.
example : Filter.Tendsto (fun n => (sahaIter 1 3)^[n] 0) Filter.atTop
    (nhds (sahaEquilibriumNe 1 3)) :=
  sahaIter_certificate_sound (S := 1) (Ntot := 3) (b := 2) (x0 := 0)
    (by norm_num) (by norm_num) le_rfl (by norm_num)
    ⟨by norm_num,
     by have h : Real.sqrt ((1 : ℝ) ^ 2 + 4 * 1 * 3) ≤ 5 := by
          rw [show (5 : ℝ) = Real.sqrt 25 by
            rw [show (25 : ℝ) = 5 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
          exact Real.sqrt_le_sqrt (by norm_num)
        unfold sahaEquilibriumNe
        rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
        linarith,
     by rw [show (3 : ℝ) - 2 = 1 by norm_num]; simp only [Real.sqrt_one]; norm_num,
     by rw [show (2 : ℝ) = Real.sqrt 4 by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
        exact Real.sqrt_le_sqrt (by norm_num)⟩

/-! ## C10 — Damped multi-element contraction (UNCONDITIONAL) · the headline

Wraps `SahaEquilibrium.dampedMultiElementIter_tendsto` (`SahaEquilibrium.lean:869`). With the
canonical relaxation `lam = 1/(1 + ∑ₛ Ntotₛ/Sₛ)` the averaged iteration converges at rate
`1 − lam < 1` **with no smallness hypothesis** — the certificate is just positivity. This replaces
the pipeline's guessed `0.5` damping with a proven-convergent relaxation. -/

/-- **C10 certificate.** Positivity of every Saha factor `Sₛ` and total density `Ntotₛ` — the only
runtime-checkable content the unconditional convergence needs. There is deliberately **no**
contraction-rate clause: the canonical `lam = 1/(1 + ∑ Ntotₛ/Sₛ)` makes `1 − lam < 1` automatic. -/
def dampedIterCert (S Ntot : ι → ℝ) : Prop := (∀ s, 0 < S s) ∧ (∀ s, 0 < Ntot s)

/-- **C10 soundness** (thin re-export of `dampedMultiElementIter_tendsto`,
`SahaEquilibrium.lean:869`). Positivity, the canonical `lam`, and any nonnegative start certify
unconditional convergence of the damped multi-element closure iteration to the coupled fixed
point `r`. -/
theorem dampedIter_certificate_sound (S Ntot : ι → ℝ) {lam r x0 : ℝ}
    (hcert : dampedIterCert S Ntot)
    (hlamval : lam = 1 / (1 + ∑ s, Ntot s / S s))
    (hr : 0 ≤ r) (hfix : r = multiElementIonized S Ntot r) (hx0 : 0 ≤ x0) :
    Filter.Tendsto (fun n => (dampedMultiElementIter S Ntot lam)^[n] x0) Filter.atTop
      (nhds r) :=
  dampedMultiElementIter_tendsto S Ntot hcert.1 hcert.2 hlamval hr hfix hx0

-- Non-vacuity: two species `S = Ntot = (1, 1)`, canonical `lam = 1/(1 + 2) = 1/3`, fixed point
-- `r = 1` (`G 1 = 2/(1+1) = 1`), start `x₀ = 0`. Certifies convergence of the damped iteration
-- to `1`.
example : Filter.Tendsto
    (fun n => (dampedMultiElementIter (ι := Fin 2) ![1, 1] ![1, 1] (1 / 3))^[n] 0)
    Filter.atTop (nhds 1) :=
  dampedIter_certificate_sound ![1, 1] ![1, 1]
    ⟨fun s => by fin_cases s <;> norm_num, fun s => by fin_cases s <;> norm_num⟩
    (by simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]; norm_num)
    (by norm_num)
    (by simp only [multiElementIonized, Fin.sum_univ_two, Matrix.cons_val_zero,
          Matrix.cons_val_one]; norm_num)
    le_rfl

/-! ## C12 — Self-absorption exact correction (known τ)

Wraps `SelfAbsorption.lineIntensity_eq_selfAbsorbedIntensity_div` (`SelfAbsorption.lean:237`), which
holds for every `τ ≥ 0`. Predicate: `τ` is a known nonnegative optical depth. Guarantee: dividing
the measured intensity by `SA(τ)` recovers the optically-thin intensity exactly. -/

/-- **C12 certificate.** The optical depth is a known nonnegative value, `0 ≤ τ`. -/
def knownTauCert (tau : ℝ) : Prop := 0 ≤ tau

/-- **C12 soundness** (thin re-export of `lineIntensity_eq_selfAbsorbedIntensity_div`,
`SelfAbsorption.lean:237`). A known `τ ≥ 0` certifies exact optically-thin recovery
`I_thin = I_meas / SA(τ)`. -/
theorem knownTau_certificate_sound {kB T N Fcal : ℝ} {g E A : ι → ℝ} (k : ι) {tau : ℝ}
    (hcert : knownTauCert tau) :
    lineIntensity kB T N Fcal g E A k
      = selfAbsorbedIntensity kB T N Fcal g E A k tau / selfAbsorptionFactor tau :=
  lineIntensity_eq_selfAbsorbedIntensity_div k hcert

-- Non-vacuity: `τ = 1` (`SA(1) = 1 − e⁻¹ ≠ 1`, a genuine correction) certifies exact recovery.
example {kB T N Fcal : ℝ} {g E A : Fin 1 → ℝ} :
    lineIntensity kB T N Fcal g E A 0
      = selfAbsorbedIntensity kB T N Fcal g E A 0 1 / selfAbsorptionFactor 1 :=
  knownTau_certificate_sound 0 zero_le_one

/-! ## C13 — Self-absorption identifiability (multi-line, unknown scale)

Wraps `CurveOfGrowth.cogRatio_injOn` (`CurveOfGrowth.lean:254`) — the positive recovery direction.
Predicate: two lines with distinct positive curve-of-growth widths. Guarantee: the source-free
curve-of-growth ratio is injective in the column density, so `N` is resolved from the ratio alone.
The `τ`-known branch of the dossier's C13 disjunction is exactly C12 (`knownTauCert`); the failure
mode without distinct data is `SelfAbsorptionInverse.selfAbsorption_breaks_identifiability`. -/

/-- **C13 certificate.** Two lines with distinct positive widths `0 < w₂ < w₁` — the
runtime "≥ 2 distinct widths" content that breaks the single-line (N, τ) alias. -/
def saDistinctCert (w₁ w₂ : ℝ) : Prop := 0 < w₂ ∧ w₂ < w₁

/-- **C13 soundness** (thin re-export of `cogRatio_injOn`, `CurveOfGrowth.lean:254`). Distinct
positive widths certify the curve-of-growth ratio is injective on `(0, ∞)`, i.e. the column density
(hence relative composition) is recovered without knowing the common source scale. -/
theorem saDistinct_certificate_sound {w₁ w₂ : ℝ} (hcert : saDistinctCert w₁ w₂) :
    Set.InjOn (fun n => cogRatio w₁ w₂ n) (Set.Ioi 0) :=
  cogRatio_injOn hcert.2 hcert.1

-- Non-vacuity: widths `w₁ = 2`, `w₂ = 1` (`0 < 1 < 2`) certify an injective, hence invertible,
-- ratio observable.
example : Set.InjOn (fun n => cogRatio 2 1 n) (Set.Ioi 0) :=
  saDistinct_certificate_sound ⟨by norm_num, by norm_num⟩

/-! ## C14 — Atomic-data aliasing error budget (A* — refusal-flagged)

Wraps `AtomicDataPerturbation.classicDensity_aliasing_error` (`AtomicDataPerturbation.lean:213`).
Predicate: `0 ≤ δ < 1`. Guarantee: `|N̂ − N| ≤ N·δ/(1 − δ)`.

REFUSAL (R2): `δ` is the relative atomic-data error — a distance to an *unknown* truth (you use
tabulated data precisely because truth is unknown). Only a literature-uncertainty `δ` (e.g. a NIST
grade) can be plugged; the bound is exactly as honest as that catalog claim. The predicate is
runtime-*evaluable* but its input is ASSUMED, not MEASURED — report "conditional on the atomic-data
uncertainty," never "proven." -/

/-- **C14 certificate.** The atomic-data aliasing budget `0 ≤ δ < 1`.
    REFUSAL: `δ` is assumed (a catalog uncertainty), not measured — see the section note (R2). -/
def aliasBudgetCert (delta : ℝ) : Prop := 0 ≤ delta ∧ delta < 1

/-- **C14 soundness** (thin re-export of `classicDensity_aliasing_error`,
`AtomicDataPerturbation.lean:213`). Given an assumed relative atomic-data error bound `δ` (R2) and
`δ < 1`, the recovered density obeys `|N̂ − N| ≤ N·δ/(1 − δ)`. -/
theorem aliasBudget_certificate_sound [Nonempty ι] {kB T N Fcal delta : ℝ}
    {g E A g' E' A' : ι → ℝ} (hg : ∀ k, 0 < g k) (hg' : ∀ k, 0 < g' k) (hFcal : 0 < Fcal) (u : ι)
    (hA : 0 < A u) (hA' : 0 < A' u) (hN : 0 < N)
    (hpert : |responseFactor kB T g' E' A' u - responseFactor kB T g E A u|
              ≤ delta * responseFactor kB T g E A u)
    (hcert : aliasBudgetCert delta) :
    |Classic.classicDensity kB T Fcal g' E' A' u (lineIntensity kB T N Fcal g E A u) - N|
      ≤ N * (delta / (1 - delta)) :=
  classicDensity_aliasing_error hg hg' hFcal u hA hA' hN hcert.1 hcert.2 hpert

-- Non-vacuity (certificate satisfiable at a genuine interior `δ`): `δ = 1/2 ∈ [0, 1)`.
example : aliasBudgetCert (1 / 2) := ⟨by norm_num, by norm_num⟩

-- Non-vacuity (guarantee exercised): with correct atomic data (`g' = g`, `E' = E`, `A' = A`) and
-- `δ = 0`, the aliasing bound is `≤ N·(0/1) = 0` — the exact-recovery corner.
example {kB T N Fcal : ℝ} {g E A : Fin 1 → ℝ}
    (hg : ∀ k, 0 < g k) (hFcal : 0 < Fcal) (hA : 0 < A 0) (hN : 0 < N) :
    |Classic.classicDensity kB T Fcal g E A 0 (lineIntensity kB T N Fcal g E A 0) - N|
      ≤ N * ((0 : ℝ) / (1 - 0)) :=
  aliasBudget_certificate_sound (delta := 0) (g' := g) (E' := E) (A' := A)
    hg hg hFcal 0 hA hA hN (by simp) ⟨le_rfl, by norm_num⟩

end CflibsFormal
