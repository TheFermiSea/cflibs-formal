/-
Copyright (c) 2026 Brian Squires. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Squires
-/
import Mathlib
import CflibsFormal.ForwardMap
import CflibsFormal.Boltzmann

/-!
# Saha–Boltzmann formalization — self-absorption / optical-thickness-aware forward map

The optically-thin `lineIntensity` (`ForwardMap.lean`) is the `τ → 0` limit of the true,
optically-thick line emission. At finite optical depth `τ` the **measured** intensity is

  `I_meas = I_thin · SA(τ)`,   `SA(τ) = (1 - exp(-τ)) / τ`   (`τ > 0`),

the curve-of-growth self-absorption factor, with continuous extension `SA 0 := 1`. This is
the dominant reliability failure mode for concentrated alloy / high-entropy-alloy lines.

We prove:

* `selfAbsorptionFactor_pos` / `selfAbsorptionFactor_le_one` — `SA(τ) ∈ (0, 1]` for
  `τ ≥ 0`: lines are dimmed, never brightened or extinguished.
* `selfAbsorptionFactor_tendsto_one` — `SA(τ) → 1` as `τ → 0⁺`, so the thick model
  recovers `ForwardMap` in the optically-thin limit (a strict generalization).
* `selfAbsorbedIntensity_le_lineIntensity` / `selfAbsorbedIntensity_lt_lineIntensity` —
  the **bias-direction theorem**: a self-absorbed line is measured below its thin value,
  so neglecting self-absorption biases the inferred upper-level population and hence the
  CF-LIBS composition DOWNWARD.
* `slabIntensity_eq_thin_mul_SA` — the **derivation** of `SA(τ)` from first principles:
  the radiative-transfer slab intensity `S·(1-exp(-τ))` (defined independently of `SA`)
  factors as the optically-thin emission `S·τ` times `SA(τ)`. With `slabIntensity_le_thin`
  and `selfAbsorbedIntensity_eq_slab` this shows the multiplicative model used here is
  exactly the radiative-transfer slab solution — `SA` is derived, not presupposed.
* `lineIntensity_eq_selfAbsorbedIntensity_div` — the **exact curve-of-growth correction**:
  with a known `τ`, dividing the measured intensity by `SA(τ)` recovers the optically-thin
  intensity exactly, which feeds the existing Boltzmann-plot inversion unchanged.
-/

namespace CflibsFormal

open Finset Real
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- **Curve-of-growth self-absorption factor** `SA(τ)`. For optical depth `τ > 0` the
measured line is dimmed by `SA(τ) = (1 - exp(-τ)) / τ ∈ (0, 1]`; the optically-thin
limit `τ → 0⁺` gives `SA → 1`, recovering the `ForwardMap` model. We take the
continuous extension `SA 0 := 1` so the function is total. -/
noncomputable def selfAbsorptionFactor (tau : ℝ) : ℝ :=
  if tau = 0 then 1 else (1 - Real.exp (-tau)) / tau

/-- **Optically-thick (self-absorbed) line intensity.** The measured intensity is the
optically-thin `lineIntensity` (reused verbatim from `ForwardMap.lean`) multiplied by
the curve-of-growth factor `SA(τ)`: `I_meas = I_thin · SA(τ)`. At `τ = 0` this equals
`lineIntensity` exactly. -/
noncomputable def selfAbsorbedIntensity (kB T N Fcal : ℝ) (g E A : ι → ℝ) (k : ι)
    (tau : ℝ) : ℝ :=
  lineIntensity kB T N Fcal g E A k * selfAbsorptionFactor tau

/-- **Positivity of the self-absorption factor.** At finite optical depth the line is
never fully extinguished: `SA(τ) > 0` for `τ ≥ 0`, so `selfAbsorbedIntensity` stays a
positive observable and `Real.log` of it is defined — the precondition for any
Boltzmann-plot inversion on self-absorbed data. -/
theorem selfAbsorptionFactor_pos {tau : ℝ} (htau : 0 ≤ tau) :
    0 < selfAbsorptionFactor tau := by
  unfold selfAbsorptionFactor
  rcases htau.eq_or_lt with h | h
  · rw [← h, if_pos rfl]; exact one_pos
  · rw [if_neg h.ne']
    apply div_pos _ h
    have : Real.exp (-tau) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    linarith

/-- **Self-absorption only dims.** `SA(τ) ≤ 1` for `τ ≥ 0`: optically-thick lines are
dimmed relative to the thin model, never brightened. Together with positivity this pins
`SA(τ) ∈ (0, 1]`. -/
theorem selfAbsorptionFactor_le_one {tau : ℝ} (htau : 0 ≤ tau) :
    selfAbsorptionFactor tau ≤ 1 := by
  unfold selfAbsorptionFactor
  rcases htau.eq_or_lt with h | h
  · rw [← h, if_pos rfl]
  · rw [if_neg h.ne', div_le_one h]
    have := Real.one_sub_le_exp_neg tau
    linarith

/-- **Thin limit.** `SA(τ) → 1` as `τ → 0⁺`: the self-absorption-aware forward model
continuously reduces to the optically-thin `ForwardMap` as `τ → 0`. The thick model is a
strict generalization, not a different model, so all thin-limit CF-LIBS identities remain
the correct asymptotics. -/
theorem selfAbsorptionFactor_tendsto_one :
    Filter.Tendsto selfAbsorptionFactor (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  have hexp : HasDerivAt (fun t : ℝ => Real.exp (-t)) (Real.exp (-(0:ℝ)) * -1) 0 :=
    (Real.hasDerivAt_exp (-(0:ℝ))).comp 0 ((hasDerivAt_id (0:ℝ)).neg)
  have hd : HasDerivAt (fun t : ℝ => -Real.exp (-t)) 1 0 := by
    have h := hexp.neg
    simp only [neg_zero, Real.exp_zero, mul_neg, mul_one, neg_neg] at h
    exact h
  have h2 := hd.tendsto_slope_zero_right
  refine h2.congr' ?_
  have hmem : Set.Ioi (0 : ℝ) ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) := self_mem_nhdsWithin
  filter_upwards [hmem] with t ht
  rw [selfAbsorptionFactor, if_neg ht.ne']
  simp only [smul_eq_mul, zero_add, neg_zero, Real.exp_zero]
  rw [sub_neg_eq_add]
  ring

/-- **Bias-direction theorem (non-strict).** A self-absorbed line is measured at or below
its optically-thin value: `I_meas ≤ I_thin`. Hence neglecting self-absorption
underestimates the inferred upper-level population and therefore biases the extracted
CF-LIBS composition DOWNWARD — the dominant failure mode for concentrated alloy /
high-entropy-alloy lines. -/
theorem selfAbsorbedIntensity_le_lineIntensity [Nonempty ι] {kB T N Fcal : ℝ}
    {g E A : ι → ℝ} (hg : ∀ k, 0 < g k) (hN : 0 < N) (hFcal : 0 < Fcal)
    (hA : ∀ k, 0 < A k) (k : ι) {tau : ℝ} (htau : 0 ≤ tau) :
    selfAbsorbedIntensity kB T N Fcal g E A k tau ≤ lineIntensity kB T N Fcal g E A k := by
  unfold selfAbsorbedIntensity
  have hI : 0 < lineIntensity kB T N Fcal g E A k := lineIntensity_pos hg hN hFcal hA k
  exact mul_le_of_le_one_right hI.le (selfAbsorptionFactor_le_one htau)

/-- **Bias-direction theorem (strict).** For any *actually* optically-thick line
(`τ > 0`) the downward bias is strict: `I_meas < I_thin`. Self-absorption is never
benign — it always reduces the measured intensity and must be corrected. -/
theorem selfAbsorbedIntensity_lt_lineIntensity [Nonempty ι] {kB T N Fcal : ℝ}
    {g E A : ι → ℝ} (hg : ∀ k, 0 < g k) (hN : 0 < N) (hFcal : 0 < Fcal)
    (hA : ∀ k, 0 < A k) (k : ι) {tau : ℝ} (htau : 0 < tau) :
    selfAbsorbedIntensity kB T N Fcal g E A k tau < lineIntensity kB T N Fcal g E A k := by
  unfold selfAbsorbedIntensity
  have hI : 0 < lineIntensity kB T N Fcal g E A k := lineIntensity_pos hg hN hFcal hA k
  have hSA : selfAbsorptionFactor tau < 1 := by
    unfold selfAbsorptionFactor
    rw [if_neg htau.ne', div_lt_one htau]
    have := Real.one_sub_lt_exp_neg htau.ne'
    linarith
  exact mul_lt_of_lt_one_right hI hSA

/-- **Radiative-transfer slab intensity.** The emergent intensity from a uniform LTE
slab with (frequency-integrated) source strength `S` and line optical depth `τ`, from
the formal solution of radiative transfer for a homogeneous layer:
  `I_slab = S · (1 - exp(-τ))`.
This is defined from radiative transfer ALONE — independently of `selfAbsorptionFactor` —
so the curve-of-growth identity below is a *derived* fact, not a definitional one. In the
optically-thin limit `τ → 0` it reduces to the first-order emission `S · τ`, the quantity
identified with `lineIntensity`. -/
noncomputable def slabIntensity (S tau : ℝ) : ℝ :=
  S * (1 - Real.exp (-tau))

/-- **Radiative-transfer dimming, derived.** The emergent slab intensity never exceeds
the optically-thin first-order emission `S · τ`: `I_slab ≤ S · τ` for `S ≥ 0`, `τ ≥ 0`.
Obtained directly from `1 - exp(-τ) ≤ τ` — it does NOT route through
`selfAbsorptionFactor`, so it independently confirms the curve-of-growth saturation. -/
theorem slabIntensity_le_thin {S tau : ℝ} (hS : 0 ≤ S) (_htau : 0 ≤ tau) :
    slabIntensity S tau ≤ S * tau := by
  unfold slabIntensity
  have h : 1 - Real.exp (-tau) ≤ tau := by
    have := Real.one_sub_le_exp_neg tau
    linarith
  exact mul_le_mul_of_nonneg_left h hS

/-- **Curve-of-growth identity (DERIVED, not definitional).** For `τ > 0` the
radiative-transfer slab intensity factors as the optically-thin emission `S · τ` times
the self-absorption factor:
  `I_slab = (S · τ) · SA(τ)`.
This DERIVES `selfAbsorptionFactor` as the genuine ratio of the emergent (thick) slab
intensity to the optically-thin emission — the physical justification for the model
`selfAbsorbedIntensity = lineIntensity · SA(τ)`. The proof is a real cancellation
(`slabIntensity` is built from `exp`, never from `SA`), not `rfl`. -/
theorem slabIntensity_eq_thin_mul_SA {S tau : ℝ} (htau : 0 < tau) :
    slabIntensity S tau = (S * tau) * selfAbsorptionFactor tau := by
  unfold slabIntensity selfAbsorptionFactor
  rw [if_neg htau.ne']
  field_simp

/-- **The model intensity IS a radiative-transfer slab intensity.** For `τ > 0`, the
self-absorbed line `selfAbsorbedIntensity = lineIntensity · SA(τ)` equals the emergent
slab intensity `slabIntensity` whose optically-thin emission `S · τ` is the thin line
`lineIntensity` (effective source strength `S = lineIntensity / τ`). This closes the loop:
the multiplicative model used here is exactly the radiative-transfer slab solution, so
`SA` is derived, not assumed. -/
theorem selfAbsorbedIntensity_eq_slab {kB T N Fcal : ℝ} {g E A : ι → ℝ} (k : ι)
    {tau : ℝ} (htau : 0 < tau) :
    selfAbsorbedIntensity kB T N Fcal g E A k tau
      = slabIntensity (lineIntensity kB T N Fcal g E A k / tau) tau := by
  have hτ : tau ≠ 0 := htau.ne'
  unfold selfAbsorbedIntensity
  rw [slabIntensity_eq_thin_mul_SA htau]
  field_simp

/-- **Exact curve-of-growth correction (model left-inverse).** Dividing the self-absorbed
measurement by the known `SA(τ)` recovers the optically-thin intensity exactly:
`I_thin = I_meas / SA(τ)`. This is the left-inverse of the model
`selfAbsorbedIntensity = lineIntensity · SA(τ)` — itself the genuine radiative-transfer
slab solution (`slabIntensity_eq_thin_mul_SA` / `selfAbsorbedIntensity_eq_slab`), so the
correction is physically derived, not merely definitional. It feeds the existing
`boltzmann_plot_intensity` / `temperature_from_two_lines` inversion unchanged:
self-absorption is exactly invertible given a known optical depth. Holds for all `τ ≥ 0`
(at `τ = 0`, `SA = 1` and the correction is the identity). -/
theorem lineIntensity_eq_selfAbsorbedIntensity_div {kB T N Fcal : ℝ}
    {g E A : ι → ℝ} (k : ι) {tau : ℝ} (htau : 0 ≤ tau) :
    lineIntensity kB T N Fcal g E A k
      = selfAbsorbedIntensity kB T N Fcal g E A k tau / selfAbsorptionFactor tau := by
  have hSA : selfAbsorptionFactor tau ≠ 0 := (selfAbsorptionFactor_pos htau).ne'
  unfold selfAbsorbedIntensity
  rw [mul_div_cancel_right₀ _ hSA]

end CflibsFormal
