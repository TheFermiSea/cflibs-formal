/-
Copyright (c) 2026 Brian Squires. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Squires
-/
import Mathlib
import CflibsFormal.Analysis
import CflibsFormal.ForwardMap
import CflibsFormal.Boltzmann

/-!
# Saha–Boltzmann formalization — self-absorption / optical-thickness-aware forward map

The optically-thin `lineIntensity` (`ForwardMap.lean`) is the `τ → 0` limit of self-absorbed
line emission. This module models the **measured** intensity at optical depth `τ` as

  `I_meas = I_thin · SA(τ)`,   `SA(τ) = (1 - exp(-τ)) / τ`   (`τ > 0`),

the flat-profile (line-centre) self-absorption factor, with continuous extension
`SA 0 := 1`. This is the dominant reliability failure mode for concentrated alloy /
high-entropy-alloy lines.

We prove:

* `selfAbsorptionFactor_pos` / `selfAbsorptionFactor_le_one` — `SA(τ) ∈ (0, 1]` for
  `τ ≥ 0`: lines are dimmed, never brightened or extinguished.
* `selfAbsorptionFactor_tendsto_one` — `SA(τ) → 1` as `τ → 0⁺`, so the thick model
  recovers `ForwardMap` in the optically-thin limit (a strict generalization).
* `selfAbsorbedIntensity_le_lineIntensity` / `selfAbsorbedIntensity_lt_lineIntensity` —
  the **bias-direction theorem**: a self-absorbed line is measured below its thin value,
  so neglecting self-absorption biases the inferred upper-level population DOWNWARD — and
  hence the extracted composition of any *differentially* self-absorbed species DOWNWARD
  (a self-absorption factor common to ALL species cancels in the scale-invariant closure;
  see `SelfAbsorptionInverse`). The direction holds for any nonnegative integrable profile
  (`EquivalentWidth.equivWidth_le_thin`); the size `SA(τ)` of the shortfall is the
  flat-profile value.
* `slabIntensity_eq_thin_mul_SA` — the **derivation** of `SA(τ)` for one optical depth: the
  radiative-transfer slab intensity `S·(1-exp(-τ))` (defined independently of `SA`) factors as
  the optically-thin emission `S·τ` times `SA(τ)`. With `slabIntensity_le_thin` and
  `selfAbsorbedIntensity_eq_slab` this shows the multiplicative model is the slab solution
  applied to the whole line with a single `τ`. `SA` is derived, not presupposed — for a
  rectangular profile or per frequency, not for the integrated intensity of a peaked line.
* `lineIntensity_eq_selfAbsorbedIntensity_div` — the **model left-inverse**: dividing the
  model's output at `τ` by `SA(τ)` returns the optically-thin `lineIntensity`, for every
  `τ ≥ 0`. It is algebra on the model; it does not check that a given `τ` is the true optical
  depth.

## Scope — flat profile / line-centre escape factor (read before using)

* **What is exact.** `slabIntensity S τ = S·(1 − exp(−τ))` is the formal solution of radiative
  transfer for a homogeneous slab at ONE frequency, with `τ` the optical depth and `S` the
  source function at that frequency. Integrated over a line it is exact only when `τ` is the
  same at every frequency of the line, i.e. for a rectangular profile
  (`EquivalentWidth.equivWidth_rectangular`).
* **What is approximate.** `selfAbsorbedIntensity` multiplies the frequency-INTEGRATED
  `lineIntensity` by `SA(τ)`. For a peaked profile `ψ` (peak `1`) with line-centre optical depth
  `τ₀`, the integrated emergent intensity is `S·∫(1 − exp(−τ₀·ψ(x))) dx`, and its ratio to the
  thin value `S·τ₀·∫ψ` is not `SA(τ₀)`. In the numerical probes of
  `docs/research/audit-2026-09-24` (finding LF-01, reproduced by its verifier; scipy, not a
  theorem of this repo) that ratio is larger, so dividing by `SA(τ₀)` over-corrects: by 1.41×
  (Gaussian) and 1.85× (Lorentzian) at `τ₀ = 3`, and by 1.87× and 3.48× at `τ₀ = 10`. For a
  Lorentzian the integrated deficit does not saturate at all
  (`EquivalentWidth.equivWidth_lorentzian_sqrt_sharp`: `W(τ)/√τ → 2`), whereas the slab kernel
  saturates at `S`.
* **Tags.** `selfAbsorptionFactor` and `selfAbsorbedIntensity` carry the model tag
  APPROXIMATION in `docs/scope-tags.tsv`. A theorem's own tag says how exactly it holds for
  this model; its published tag is the weaker of the two (`docs/conventions.md` §8), so every
  physics result stated over these definitions publishes APPROXIMATION. PURE-MATH rows (pure
  algebra or analysis, with no physics claim) are exempt.
* **`τ` is a free real.** Nothing here ties `τ` to the plasma state (`OpticalDepth` does), and
  no bound is proved for the error of a correction made with an estimated `τ̂ ≠ τ`.

## Literature

Gornushkin, Anzano, King, Smith, Omenetto, Winefordner, "Curve of growth methodology applied
to laser-induced plasma emission spectroscopy", *Spectrochimica Acta Part B* **54** (1999)
491–503 — the homogeneous-slab curve-of-growth relation `I = S·(1 − exp(−τ))` from which the
escape factor `SA(τ) = (1 − exp(−τ))/τ`, its `SA ∈ (0, 1]` dimming bound, and the
bias-direction theorem here are derived.
-/

namespace CflibsFormal

open Finset Real
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- **Flat-profile (line-centre) self-absorption factor** `SA(τ)`. For optical depth `τ > 0`,
`SA(τ) = (1 - exp(-τ)) / τ ∈ (0, 1]` is the escaping fraction of a homogeneous slab with the
SAME optical depth `τ` at every frequency of the line (a rectangular profile) — equivalently,
the ratio of emergent to optically-thin intensity at a single frequency. The optically-thin
limit `τ → 0⁺` gives `SA → 1`, recovering the `ForwardMap` model. We take the continuous
extension `SA 0 := 1` so the function is total.

Model tag APPROXIMATION: applied to the integrated intensity of a peaked profile with
line-centre depth `τ`, it understates the escaping fraction (module scope block). -/
noncomputable def selfAbsorptionFactor (tau : ℝ) : ℝ :=
  if tau = 0 then 1 else (1 - Real.exp (-tau)) / tau

/-- **Optically-thick (self-absorbed) line intensity — flat-profile model.** The measured
intensity is modelled as the frequency-integrated optically-thin `lineIntensity` (reused
verbatim from `ForwardMap.lean`) multiplied by the flat-profile factor `SA(τ)`:
`I_meas = I_thin · SA(τ)`. At `τ = 0` this equals `lineIntensity` exactly.

Model tag APPROXIMATION: the whole line is treated as one optical depth `τ`, which for a
peaked profile overstates the dimming (module scope block). -/
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

/-- **Strict monotonicity of the escape factor.** `SA(τ) = (1 − exp(−τ))/τ` is STRICTLY
DECREASING in the optical depth `τ > 0`: a more optically-thick line escapes a strictly smaller
fraction of its photons (`SA` runs monotonically from `1` at `τ → 0⁺` down toward `0`). Proof:
`strictAntiOn_of_deriv_neg` on the clean branch `(1 − exp(−x))/x`, whose derivative numerator
`exp(−x)·(x + 1) − 1 < 0` (from `Real.add_one_lt_exp`, `x + 1 < exp x`, scaled by `exp(−x) > 0`),
transferred across the `if` of `selfAbsorptionFactor` by `StrictAntiOn.congr`. -/
theorem selfAbsorptionFactor_strictAntiOn :
    StrictAntiOn selfAbsorptionFactor (Set.Ioi 0) := by
  have hclean : StrictAntiOn (fun t : ℝ => (1 - Real.exp (-t)) / t) (Set.Ioi 0) := by
    apply strictAntiOn_div_of_deriv_num_neg
      (f := fun t => 1 - Real.exp (-t)) (g := fun t => t)
      (f' := fun t => Real.exp (-t)) (g' := fun _ => 1)
    · intro x hx
      exact Set.mem_Ioi.mp hx
    · intro x _
      have he : HasDerivAt (fun t : ℝ => Real.exp (-t)) (Real.exp (-x) * -1) x :=
        (Real.hasDerivAt_exp (-x)).comp x ((hasDerivAt_id x).neg)
      simpa using he.const_sub 1
    · intro x _
      exact hasDerivAt_id x
    · intro x hx
      have hxne : x ≠ 0 := (Set.mem_Ioi.mp hx).ne'
      have hkey : Real.exp (-x) * (x + 1) < 1 := by
        have h1 : x + 1 < Real.exp x := Real.add_one_lt_exp hxne
        have h2 : Real.exp (-x) * (x + 1) < Real.exp (-x) * Real.exp x :=
          mul_lt_mul_of_pos_left h1 (Real.exp_pos _)
        rwa [← Real.exp_add, neg_add_cancel, Real.exp_zero] at h2
      nlinarith [hkey]
  have heqon : Set.EqOn (fun t : ℝ => (1 - Real.exp (-t)) / t) selfAbsorptionFactor
      (Set.Ioi 0) := by
    intro t ht
    rw [selfAbsorptionFactor, if_neg (Set.mem_Ioi.mp ht).ne']
  exact hclean.congr heqon

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
its optically-thin value: `I_meas ≤ I_thin`. Hence neglecting self-absorption biases the
inferred upper-level population DOWNWARD, and hence the extracted composition of any
*differentially* self-absorbed species (a factor common to all species cancels in the
scale-invariant closure) — the dominant failure mode for concentrated alloy /
high-entropy-alloy lines. The direction holds for any nonnegative integrable profile
(`EquivalentWidth.equivWidth_le_thin`); the size of the shortfall, `SA(τ)`, is the
flat-profile value. -/
theorem selfAbsorbedIntensity_le_lineIntensity [Nonempty ι] {kB T N Fcal : ℝ}
    {g E A : ι → ℝ} (hg : ∀ k, 0 < g k) (hN : 0 < N) (hFcal : 0 < Fcal)
    (hA : ∀ k, 0 < A k) (k : ι) {tau : ℝ} (htau : 0 ≤ tau) :
    selfAbsorbedIntensity kB T N Fcal g E A k tau ≤ lineIntensity kB T N Fcal g E A k := by
  unfold selfAbsorbedIntensity
  have hI : 0 < lineIntensity kB T N Fcal g E A k := lineIntensity_pos hg hN hFcal hA k
  exact mul_le_of_le_one_right hI.le (selfAbsorptionFactor_le_one htau)

/-- **Bias-direction theorem (strict).** For any *actually* optically-thick line
(`τ > 0`) the downward bias is strict: `I_meas < I_thin`. Self-absorption is never
benign — it always reduces the measured intensity and must be corrected, biasing the
inferred upper-level population DOWNWARD, and hence the extracted composition of any
*differentially* self-absorbed species (a factor common to all species cancels in the
scale-invariant closure). -/
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

/-- **Radiative-transfer slab intensity at one frequency.** The emergent intensity, at a
frequency where a uniform LTE slab has source function `S` and optical depth `τ`, from the
formal solution of radiative transfer for a homogeneous layer:
  `I_slab = S · (1 - exp(-τ))`.
Integrated over a line this is the line intensity only for a rectangular profile, where `τ` is
the same at every frequency (`EquivalentWidth.equivWidth_rectangular`). It is defined from
radiative transfer ALONE — independently of `selfAbsorptionFactor` — so the curve-of-growth
identity below is a *derived* fact, not a definitional one. In the optically-thin limit
`τ → 0` it reduces to the first-order emission `S · τ`, the quantity identified with
`lineIntensity`. -/
noncomputable def slabIntensity (S tau : ℝ) : ℝ :=
  S * (1 - Real.exp (-tau))

/-- **Radiative-transfer dimming, derived.** The emergent slab intensity never exceeds
the optically-thin first-order emission `S · τ`: `I_slab ≤ S · τ` for `S ≥ 0`, `τ ≥ 0`.
Obtained directly from `1 - exp(-τ) ≤ τ` — it does NOT route through
`selfAbsorptionFactor`, so it independently confirms the curve-of-growth saturation (per
frequency, or for a rectangular profile). -/
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
This DERIVES `selfAbsorptionFactor` as the ratio of the emergent (thick) slab intensity to
the optically-thin emission at ONE optical depth — per frequency, or for a rectangular
profile. That is the justification for the model `selfAbsorbedIntensity = lineIntensity · SA(τ)`
in that case only: for the integrated intensity of a peaked profile the ratio is a different
escape factor, which the audit probes find larger (module scope block). The proof is a real
cancellation (`slabIntensity` is built from `exp`, never from `SA`), not `rfl`. -/
theorem slabIntensity_eq_thin_mul_SA {S tau : ℝ} (htau : 0 < tau) :
    slabIntensity S tau = (S * tau) * selfAbsorptionFactor tau := by
  unfold slabIntensity selfAbsorptionFactor
  rw [if_neg htau.ne']
  field_simp

/-- **The model intensity is a slab intensity at a single optical depth.** For `τ > 0`, the
self-absorbed line `selfAbsorbedIntensity = lineIntensity · SA(τ)` equals the emergent
slab intensity `slabIntensity` whose optically-thin emission `S · τ` is the thin line
`lineIntensity` (effective source strength `S = lineIntensity / τ`). So the multiplicative
model is the slab solution applied to the whole line with one optical depth `τ`: exact per
frequency or for a rectangular profile, and the flat-profile approximation for the integrated
intensity of a real, peaked line (module scope block). `SA` is derived for that case, not
assumed; the identity says nothing about the profile. -/
theorem selfAbsorbedIntensity_eq_slab {kB T N Fcal : ℝ} {g E A : ι → ℝ} (k : ι)
    {tau : ℝ} (htau : 0 < tau) :
    selfAbsorbedIntensity kB T N Fcal g E A k tau
      = slabIntensity (lineIntensity kB T N Fcal g E A k / tau) tau := by
  have hτ : tau ≠ 0 := htau.ne'
  unfold selfAbsorbedIntensity
  rw [slabIntensity_eq_thin_mul_SA htau]
  field_simp

/-- **Model left-inverse of the flat-profile correction.** For every `τ ≥ 0`, dividing the
model output `selfAbsorbedIntensity … τ` by `SA(τ)` returns `lineIntensity`:
`I_thin = I_meas / SA(τ)`, with `I_meas` this model's value at the same `τ` (at `τ = 0`,
`SA = 1` and the division is the identity). The proof is `mul_div_cancel_right₀` on the
definition, so the statement is algebra on the model. Because it holds for EVERY `τ ≥ 0`, it
does not certify that a given `τ` is the true optical depth: data corrected with an estimated
`τ̂` return the thin intensity only if they were produced by this model at `τ̂`, and no error
bound for `τ̂ ≠ τ` is proved here. On a real peaked line the correction also inherits the
flat-profile over-correction (module scope block). Its output feeds the
`boltzmann_plot_intensity` / `temperature_from_two_lines` inversion unchanged. Consumers:
`Alt.selfAbsorbed_sound`, and the C12 certificate `Certificates.knownTau_certificate_sound`,
whose predicate `knownTauCert τ := 0 ≤ τ` checks only nonnegativity. -/
theorem lineIntensity_eq_selfAbsorbedIntensity_div {kB T N Fcal : ℝ}
    {g E A : ι → ℝ} (k : ι) {tau : ℝ} (htau : 0 ≤ tau) :
    lineIntensity kB T N Fcal g E A k
      = selfAbsorbedIntensity kB T N Fcal g E A k tau / selfAbsorptionFactor tau := by
  have hSA : selfAbsorptionFactor tau ≠ 0 := (selfAbsorptionFactor_pos htau).ne'
  unfold selfAbsorbedIntensity
  rw [mul_div_cancel_right₀ _ hSA]

end CflibsFormal
