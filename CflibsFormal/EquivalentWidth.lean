/-
Copyright (c) 2026 Brian Squires. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Squires
-/
import Mathlib

/-!
# Saha–Boltzmann formalization — the equivalent-width curve of growth

`CurveOfGrowth.lean` models the *line-center intensity* `I = S·(1 - exp(-τ))` of a self-absorbed
line. The classical **curve of growth** is the companion *integrated* observable: the
**equivalent width**

  `W(τ) = ∫ (1 - exp(-(τ · φ x))) dx`,

the line's total deficit relative to the continuum, as a function of the central optical-depth
scale `τ` and the line **profile** `φ` (a nonnegative, integrable shape with area `∫φ`). This is
the diagnostic whose log–log slope distinguishes the optical-thickness regimes.

We prove the **weak-line / saturation** structure of the curve of growth, profile-agnostically:

* `equivWidth_nonneg` — `0 ≤ W(τ)` (a line only removes flux).
* `equivWidth_le_thin` — **the linear-regime upper bound** `W(τ) ≤ τ · ∫φ`: the equivalent width
  never exceeds the optically-thin value `τ·∫φ` (the slope-1 line on the curve of growth). The line
  *saturates* — the curve bends below the linear asymptote — because `1 - exp(-y) ≤ y`.
* `equivWidth_mono` — `W` is increasing in `τ`: more column density ⇒ larger equivalent width.
* `equivWidth_weakLine` — **the linear regime is exact at small `τ`:** `W(τ)/τ → ∫φ` as `τ → 0⁺`, so
  the curve of growth is asymptotically tangent to the slope-1 line `τ·∫φ` at the origin and (with
  `equivWidth_le_thin`) bends strictly below it as `τ` grows.
* `equivWidth_rectangular` — for a **flat (rectangular) profile** of unit area the equivalent width
  is exactly the slab deficit `W(τ) = 1 - exp(-τ)`, tying the integrated curve of growth back to the
  `SelfAbsorption.slabIntensity` / escape-factor kernel and witnessing the results are non-vacuous.

## Honest scope

* **EXACT, within the model.** `W(τ) = ∫(1 - exp(-τφ))` is the standard equivalent-width definition
  (absorption / self-absorption deficit). The bound `W ≤ τ·∫φ`, monotonicity, and the rectangular
  identity are exact under the stated hypotheses (`φ ≥ 0`, `Integrable φ`, `τ ≥ 0`).
* **Only the LINEAR regime and saturation onset — the slope-½ damping wing is OUT OF SCOPE.** The
  curve of growth has three regimes: linear (`W ∝ τ`, slope 1), flat/Doppler saturation
  (`W ∝ √(ln τ)`), and the square-root damping wing (`W ∝ √τ`, slope ½, from the Lorentzian wings).
  We prove the slope-1 *upper bound* (`equivWidth_le_thin`), the exact slope-1 *tangency* at small
  `τ` (`equivWidth_weakLine`), and monotonicity — but NOT the saturated asymptotics: the slope-½
  Lorentz-wing growth needs a profile-specific improper-integral asymptotic (Ladenburg–Reiche /
  Bessel-function form) beyond the profile-agnostic results here.
* **Profile-agnostic.** No specific profile (Gaussian/Doppler, Lorentzian, Voigt) is assumed; the
  results hold for any nonnegative integrable `φ`. The rectangular witness is the one concrete
  instance, chosen because it closes in elementary form and recovers the audited slab kernel.
* **Physics is in the profile, not the Lean statement.** `τ` lumps the oscillator strength / lower-
  level column density (`τ = w·n` of `CurveOfGrowth.cogIntensity`); `∫φ` is the profile area. No
  physical constant enters any statement.

## Literature

The equivalent width `W = ∫(1 - e^{-τ_ν}) dν` and its curve of growth (linear, flat, and
square-root regimes) are standard radiative transfer — e.g. D. Mihalas, *Stellar Atmospheres*,
2nd ed., W. H. Freeman (1978), the curve-of-growth treatment. In the calibration-free LIBS
setting the curve of growth `I = S·(1 - exp(-τ))` is Gornushkin, I. B.; Anzano, J. M.; King,
L. A.; Smith, B. W.; Omenetto, N.; Winefordner, J. D. "Curve of growth methodology applied to
laser-induced plasma emission analysis," *Spectrochimica Acta Part B* **54** (1999) 491–503
(the `cogIntensity` kernel of `CurveOfGrowth.lean`); the multi-line / Cσ curve-of-growth
correction is formalized in the sibling `Alt/CSigmaCurveOfGrowth` (Aragón & Aguilera). The
slope-½ damping-wing branch deferred here is governed by the classical Ladenburg–Reiche
curve-of-growth function for a Lorentzian profile.
-/

namespace CflibsFormal

open MeasureTheory Real

/-- **Equivalent width (curve of growth).** For a line of central optical-depth scale `τ` and
nonnegative profile `φ` (area `∫φ`), the equivalent width is the integrated line deficit
`W(τ) = ∫ (1 - exp(-(τ · φ x))) dx`. The optically-thin value is `τ·∫φ`; `W` saturates below it. -/
noncomputable def equivWidth (φ : ℝ → ℝ) (τ : ℝ) : ℝ :=
  ∫ x, (1 - Real.exp (-(τ * φ x)))

/-- The equivalent-width integrand `1 - exp(-(τφ))` is integrable: it is sandwiched
`0 ≤ 1 - exp(-(τφ)) ≤ τφ` (from `1 - exp(-y) ≤ y`) by the integrable dominating profile `τ·φ`. -/
theorem equivWidth_integrand_integrable {φ : ℝ → ℝ} {τ : ℝ} (hτ : 0 ≤ τ)
    (hφnn : 0 ≤ φ) (hφ : Integrable φ) :
    Integrable (fun x => 1 - Real.exp (-(τ * φ x))) := by
  refine Integrable.mono' (hφ.const_mul τ) ?_ ?_
  · exact (aestronglyMeasurable_const.sub
      (Real.continuous_exp.comp_aestronglyMeasurable
        ((hφ.aestronglyMeasurable.const_mul τ).neg)))
  · filter_upwards with x
    have hx : 0 ≤ τ * φ x := mul_nonneg hτ (hφnn x)
    have hnn : 0 ≤ 1 - Real.exp (-(τ * φ x)) := by
      have : Real.exp (-(τ * φ x)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      linarith
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    linarith [Real.one_sub_le_exp_neg (τ * φ x)]

/-- **A line only removes flux:** the equivalent width is nonnegative for `τ ≥ 0`, `φ ≥ 0`. -/
theorem equivWidth_nonneg {φ : ℝ → ℝ} {τ : ℝ} (hτ : 0 ≤ τ) (hφnn : 0 ≤ φ) :
    0 ≤ equivWidth φ τ := by
  refine integral_nonneg (fun x => ?_)
  simp only [Pi.zero_apply]
  have : Real.exp (-(τ * φ x)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by have := mul_nonneg hτ (hφnn x); linarith)
  linarith

/-- **The linear-regime upper bound (saturation).** `W(τ) ≤ τ · ∫φ`: the equivalent width never
exceeds the optically-thin value `τ·∫φ` (the slope-1 asymptote of the curve of growth). The curve
bends below the linear line because `1 - exp(-y) ≤ y` pointwise — the onset of saturation. -/
theorem equivWidth_le_thin {φ : ℝ → ℝ} {τ : ℝ} (hτ : 0 ≤ τ) (hφnn : 0 ≤ φ) (hφ : Integrable φ) :
    equivWidth φ τ ≤ τ * ∫ x, φ x := by
  rw [equivWidth, ← integral_const_mul]
  refine integral_mono (equivWidth_integrand_integrable hτ hφnn hφ) (hφ.const_mul τ) (fun x => ?_)
  linarith [Real.one_sub_le_exp_neg (τ * φ x)]

/-- **The curve of growth is increasing.** For `0 ≤ τ₁ ≤ τ₂` the equivalent width grows:
`W(τ₁) ≤ W(τ₂)`. More lower-level column density (larger `τ`) removes strictly more flux. -/
theorem equivWidth_mono {φ : ℝ → ℝ} {τ₁ τ₂ : ℝ} (hτ₁ : 0 ≤ τ₁) (hτ : τ₁ ≤ τ₂)
    (hφnn : 0 ≤ φ) (hφ : Integrable φ) :
    equivWidth φ τ₁ ≤ equivWidth φ τ₂ := by
  refine integral_mono (equivWidth_integrand_integrable hτ₁ hφnn hφ)
    (equivWidth_integrand_integrable (hτ₁.trans hτ) hφnn hφ) (fun x => ?_)
  have hmul : τ₁ * φ x ≤ τ₂ * φ x := mul_le_mul_of_nonneg_right hτ (hφnn x)
  have hexp : Real.exp (-(τ₂ * φ x)) ≤ Real.exp (-(τ₁ * φ x)) :=
    Real.exp_le_exp.mpr (by linarith)
  linarith

/-- **The flat-profile curve of growth recovers the slab deficit.** For a rectangular profile of
unit area — the indicator of `[0,1]` — the equivalent width is exactly `W(τ) = 1 - exp(-τ)`, the
self-absorption deficit of `SelfAbsorption.slabIntensity` (`I = S·(1 - exp(-τ))`). This pins the
integrated curve of growth to the audited slab kernel and certifies the results are non-vacuous
(`τ·∫φ = τ`, and `1 - exp(-τ) ≤ τ` consistent with `equivWidth_le_thin`). -/
theorem equivWidth_rectangular (τ : ℝ) :
    equivWidth (Set.indicator (Set.Icc 0 1) (fun _ => 1)) τ = 1 - Real.exp (-τ) := by
  have hrw : (fun x => 1 - Real.exp (-(τ * Set.indicator (Set.Icc (0:ℝ) 1) (fun _ => 1) x)))
      = Set.indicator (Set.Icc 0 1) (fun _ => 1 - Real.exp (-τ)) := by
    funext x
    by_cases hx : x ∈ Set.Icc (0:ℝ) 1
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]; norm_num
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]; norm_num
  rw [equivWidth, hrw, integral_indicator_const _ measurableSet_Icc, measureReal_def,
    Real.volume_Icc]
  simp

/-- **The weak-line (linear) limit of the curve of growth.** `W(τ)/τ → ∫φ` as `τ → 0⁺`: at small
optical depth the equivalent width is asymptotically the optically-thin value `τ·∫φ` (slope 1 on the
log–log curve of growth). With `equivWidth_le_thin` (`W ≤ τ·∫φ`) this *pins the linear regime*: the
curve starts tangent to the slope-1 line and bends strictly below it as `τ` grows — the onset of
saturation. Dominated convergence with the integrable bound `φ`; the pointwise quotient
`(1 - exp(-τφ))/τ → φ` is the derivative of `τ ↦ 1 - exp(-τφ)` at `0`
(`HasDerivAt.tendsto_slope_zero_right`). -/
theorem equivWidth_weakLine {φ : ℝ → ℝ} (hφnn : 0 ≤ φ) (hφ : Integrable φ) :
    Filter.Tendsto (fun τ => equivWidth φ τ / τ)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (∫ x, φ x)) := by
  have hEq : (fun τ : ℝ => equivWidth φ τ / τ)
      = (fun τ : ℝ => ∫ x, (1 - Real.exp (-(τ * φ x))) / τ) := by
    funext τ; rw [equivWidth, integral_div]
  rw [hEq]
  apply tendsto_integral_filter_of_dominated_convergence φ
  · -- each `F τ` is a.e.-strongly measurable
    filter_upwards [self_mem_nhdsWithin] with τ _
    exact (continuous_id.div_const τ).comp_aestronglyMeasurable
      (aestronglyMeasurable_const.sub
        (Real.continuous_exp.comp_aestronglyMeasurable
          ((hφ.aestronglyMeasurable.const_mul τ).neg)))
  · -- domination `‖(1 - exp(-τφ))/τ‖ ≤ φ` for `τ > 0`
    filter_upwards [self_mem_nhdsWithin] with τ (hτ : (0:ℝ) < τ)
    filter_upwards with x
    have hx : 0 ≤ τ * φ x := mul_nonneg hτ.le (hφnn x)
    have hnn : 0 ≤ 1 - Real.exp (-(τ * φ x)) := by
      have : Real.exp (-(τ * φ x)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hnn hτ.le), div_le_iff₀ hτ]
    nlinarith [Real.one_sub_le_exp_neg (τ * φ x)]
  · exact hφ
  · -- pointwise limit: the slope of `τ ↦ 1 - exp(-τφ x)` at `0` is `φ x`
    refine ae_of_all _ (fun x => ?_)
    have hmul : HasDerivAt (fun τ : ℝ => τ * φ x) (φ x) 0 := by
      simpa using (hasDerivAt_id (0:ℝ)).mul_const (φ x)
    have hexp : HasDerivAt (fun τ : ℝ => Real.exp (-(τ * φ x))) (-(φ x)) 0 := by
      simpa using hmul.neg.exp
    have hd : HasDerivAt (fun τ : ℝ => 1 - Real.exp (-(τ * φ x))) (φ x) 0 := by
      simpa using hexp.const_sub 1
    refine hd.tendsto_slope_zero_right.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t _
    simp only [zero_add, smul_eq_mul, zero_mul, neg_zero, Real.exp_zero]
    ring

end CflibsFormal
