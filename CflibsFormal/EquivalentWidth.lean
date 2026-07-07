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

/-- **Saturation kills forward sensitivity (EXACT).** For `τ₁ ≤ τ₂` the slab curve of growth
`g(τ) = 1 - exp(-τ)` — the rectangular equivalent width `W = 1 - e^{-τ}` of
`equivWidth_rectangular` — obeys `|g(τ₂) - g(τ₁)| ≤ e^{-τ₁} · (τ₂ - τ₁)`: the forward response
decays like `e^{-τ}`, so deep in saturation the observable stops moving with `τ`. Proof:
`e^{-τ₁} - e^{-τ₂} = e^{-τ₁}(1 - e^{-(τ₂-τ₁)}) ≤ e^{-τ₁}(τ₂-τ₁)` via `Real.one_sub_le_exp_neg`. The
thick-regime √τ damping-wing growth stays out of scope (see the module honest-scope note). -/
theorem slabCurve_forward_lipschitz {τ₁ τ₂ : ℝ} (hτ : τ₁ ≤ τ₂) :
    |(1 - Real.exp (-τ₂)) - (1 - Real.exp (-τ₁))| ≤ Real.exp (-τ₁) * (τ₂ - τ₁) := by
  have hle : Real.exp (-τ₂) ≤ Real.exp (-τ₁) := Real.exp_le_exp.mpr (by linarith)
  have hprod : Real.exp (-τ₁) * Real.exp (-(τ₂ - τ₁)) = Real.exp (-τ₂) := by
    rw [← Real.exp_add]; congr 1; ring
  have hval : (1 - Real.exp (-τ₂)) - (1 - Real.exp (-τ₁))
      = Real.exp (-τ₁) - Real.exp (-τ₂) := by ring
  rw [hval, abs_of_nonneg (by linarith)]
  have hcalc : Real.exp (-τ₁) * (1 - Real.exp (-(τ₂ - τ₁)))
      = Real.exp (-τ₁) - Real.exp (-τ₂) := by rw [mul_sub, mul_one, hprod]
  have ha : (0:ℝ) ≤ Real.exp (-τ₁) := (Real.exp_pos _).le
  have hkey : Real.exp (-τ₁) * (1 - Real.exp (-(τ₂ - τ₁)))
      ≤ Real.exp (-τ₁) * (τ₂ - τ₁) :=
    mul_le_mul_of_nonneg_left (by linarith [Real.one_sub_le_exp_neg (τ₂ - τ₁)]) ha
  linarith [hkey, hcalc]

/-- **Inverse ill-conditioning — the condition number of the equivalent-width inversion (EXACT).**
On the unsaturated region `W₁, W₂ ≤ Wmax` with `Wmax < 1` (nonnegativity of the widths is not
even needed), the inverse `τ = -log(1 - W)` is Lipschitz with constant `1/(1 - Wmax)`:
`|log(1-W₁) - log(1-W₂)| ≤ |W₁ - W₂| / (1 - Wmax)`. The condition number `1/(1 - Wmax)` blows up as
`Wmax → 1`, quantifying why the inversion is unusable in saturation — the explicit bound that
licenses the runtime saturation gate ("refuse when saturated"). Proof: `log a - log b ≤ (a-b)/b`
(from `Real.log_le_sub_one_of_pos`) two-sidedly, then `1 - W ≥ 1 - Wmax > 0`. -/
theorem slabCurve_inverse_lipschitz {W₁ W₂ Wmax : ℝ} (hWmax : Wmax < 1)
    (hW₁ : W₁ ≤ Wmax) (hW₂ : W₂ ≤ Wmax) :
    |Real.log (1 - W₁) - Real.log (1 - W₂)| ≤ |W₁ - W₂| / (1 - Wmax) := by
  have hc : (0:ℝ) < 1 - Wmax := by linarith
  have hupos : (0:ℝ) < 1 - W₁ := by linarith
  have hvpos : (0:ℝ) < 1 - W₂ := by linarith
  have hcv : 1 - Wmax ≤ 1 - W₂ := by linarith
  have hcu : 1 - Wmax ≤ 1 - W₁ := by linarith
  have hMnn : (0:ℝ) ≤ |W₁ - W₂| := abs_nonneg _
  have hlog : ∀ a b : ℝ, 0 < a → 0 < b → Real.log a - Real.log b ≤ (a - b) / b := by
    intro a b ha hb
    have h := Real.log_le_sub_one_of_pos (div_pos ha hb)
    rw [Real.log_div ha.ne' hb.ne'] at h
    have heq : (a - b) / b = a / b - 1 := by rw [sub_div, div_self hb.ne']
    linarith
  have hf : Real.log (1 - W₁) - Real.log (1 - W₂) ≤ |W₁ - W₂| / (1 - Wmax) := by
    have h1 := hlog (1 - W₁) (1 - W₂) hupos hvpos
    have heqs : (1 - W₁) - (1 - W₂) = W₂ - W₁ := by ring
    have hle : (1 - W₁) - (1 - W₂) ≤ |W₁ - W₂| := by
      rw [heqs, abs_sub_comm]; exact le_abs_self _
    have h2 : ((1 - W₁) - (1 - W₂)) / (1 - W₂) ≤ |W₁ - W₂| / (1 - Wmax) := by
      rw [div_le_div_iff₀ hvpos hc]
      nlinarith [mul_nonneg hMnn (by linarith : (0:ℝ) ≤ (1 - W₂) - (1 - Wmax)),
        mul_nonneg (by linarith [hle] : (0:ℝ) ≤ |W₁ - W₂| - ((1 - W₁) - (1 - W₂))) hc.le]
    linarith [h1, h2]
  have hr : Real.log (1 - W₂) - Real.log (1 - W₁) ≤ |W₁ - W₂| / (1 - Wmax) := by
    have h1 := hlog (1 - W₂) (1 - W₁) hvpos hupos
    have heqs : (1 - W₂) - (1 - W₁) = W₁ - W₂ := by ring
    have hle : (1 - W₂) - (1 - W₁) ≤ |W₁ - W₂| := by
      rw [heqs]; exact le_abs_self _
    have h2 : ((1 - W₂) - (1 - W₁)) / (1 - W₁) ≤ |W₁ - W₂| / (1 - Wmax) := by
      rw [div_le_div_iff₀ hupos hc]
      nlinarith [mul_nonneg hMnn (by linarith : (0:ℝ) ≤ (1 - W₁) - (1 - Wmax)),
        mul_nonneg (by linarith [hle] : (0:ℝ) ≤ |W₁ - W₂| - ((1 - W₂) - (1 - W₁))) hc.le]
    linarith [h1, h2]
  exact abs_sub_le_iff.mpr ⟨hf, hr⟩

/-- **Round-trip inverse-Lipschitz bound in τ (EXACT).** For `0 ≤ τ₁, τ₂ ≤ τmax`,
`|τ₁ - τ₂| ≤ |g(τ₁) - g(τ₂)| · e^{τmax}` with `g(τ) = 1 - exp(-τ)`: the inverse-Lipschitz constant
`e^{τmax}` equals `1/(1 - Wmax)` for `Wmax = g(τmax)`, the same blow-up as
`slabCurve_inverse_lipschitz` phrased via a τ-bound instead of a `W`-bound. Proof: for `a ≤ b`,
`e^{-a} - e^{-b} = e^{-b}(e^{b-a} - 1) ≥ e^{-τmax}(b - a)` via `Real.add_one_le_exp`, then multiply
by `e^{τmax}`. The thick-regime √τ damping wing stays out of scope (module honest-scope note). -/
theorem slabCurve_roundTrip_lipschitz {τ₁ τ₂ τmax : ℝ}
    (hτ₁ : 0 ≤ τ₁) (hτ₂ : 0 ≤ τ₂) (h₁ : τ₁ ≤ τmax) (h₂ : τ₂ ≤ τmax) :
    |τ₁ - τ₂| ≤ |(1 - Real.exp (-τ₁)) - (1 - Real.exp (-τ₂))| * Real.exp τmax := by
  have key : ∀ a b : ℝ, 0 ≤ a → b ≤ τmax → a ≤ b →
      b - a ≤ (Real.exp (-a) - Real.exp (-b)) * Real.exp τmax := by
    intro a b ha hbmax hab
    have hb1 : (0:ℝ) ≤ Real.exp (-b) := (Real.exp_pos _).le
    have hmul : Real.exp (-b) * Real.exp (b - a) = Real.exp (-a) := by
      rw [← Real.exp_add]; congr 1; ring
    have hfac : Real.exp (-a) - Real.exp (-b)
        = Real.exp (-b) * (Real.exp (b - a) - 1) := by rw [mul_sub, mul_one, hmul]
    have hlow : Real.exp (-b) * (b - a) ≤ Real.exp (-a) - Real.exp (-b) := by
      rw [hfac]
      exact mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (b - a)]) hb1
    have hba : (0:ℝ) ≤ b - a := by linarith
    have hbb : Real.exp (-τmax) ≤ Real.exp (-b) := Real.exp_le_exp.mpr (by linarith)
    have hlow2 : Real.exp (-τmax) * (b - a) ≤ Real.exp (-a) - Real.exp (-b) :=
      le_trans (mul_le_mul_of_nonneg_right hbb hba) hlow
    have hexpmax : (0:ℝ) < Real.exp τmax := Real.exp_pos _
    have hcancel : Real.exp (-τmax) * Real.exp τmax = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    have hLHS : Real.exp (-τmax) * (b - a) * Real.exp τmax = b - a := by
      rw [mul_right_comm, hcancel, one_mul]
    have hfin := mul_le_mul_of_nonneg_right hlow2 hexpmax.le
    rw [hLHS] at hfin
    exact hfin
  rcases le_total τ₁ τ₂ with h | h
  · have habs1 : |τ₁ - τ₂| = τ₂ - τ₁ := by
      rw [abs_sub_comm]; exact abs_of_nonneg (by linarith)
    have hsgn : (1 - Real.exp (-τ₁)) - (1 - Real.exp (-τ₂))
        = -(Real.exp (-τ₁) - Real.exp (-τ₂)) := by ring
    have hexple : Real.exp (-τ₂) ≤ Real.exp (-τ₁) := Real.exp_le_exp.mpr (by linarith)
    have habs2 : |(1 - Real.exp (-τ₁)) - (1 - Real.exp (-τ₂))|
        = Real.exp (-τ₁) - Real.exp (-τ₂) := by
      rw [hsgn, abs_neg, abs_of_nonneg (by linarith)]
    rw [habs1, habs2]
    exact key τ₁ τ₂ hτ₁ h₂ h
  · have habs1 : |τ₁ - τ₂| = τ₁ - τ₂ := abs_of_nonneg (by linarith)
    have hsgn : (1 - Real.exp (-τ₁)) - (1 - Real.exp (-τ₂))
        = Real.exp (-τ₂) - Real.exp (-τ₁) := by ring
    have hexple : Real.exp (-τ₁) ≤ Real.exp (-τ₂) := Real.exp_le_exp.mpr (by linarith)
    have habs2 : |(1 - Real.exp (-τ₁)) - (1 - Real.exp (-τ₂))|
        = Real.exp (-τ₂) - Real.exp (-τ₁) := by
      rw [hsgn, abs_of_nonneg (by linarith)]
    rw [habs1, habs2]
    exact key τ₂ τ₁ hτ₂ h₁ h

/-- Rectangular-profile witness (unit-area indicator of `[0,1]`) for the inverse map. -/
private noncomputable def nvCogRectProfile : ℝ → ℝ :=
  Set.indicator (Set.Icc 0 1) (fun _ => 1)

/-- Non-vacuity: for the rectangular equivalent width `W = 1 - e^{-τ}` (`equivWidth_rectangular`)
the inverse `τ = -log(1 - W)` recovers `τ` exactly, so the forward/inverse pair of the slab curve
is a genuine bijection off saturation and the conditioning bounds above act on a real inversion. -/
example (τ : ℝ) : -Real.log (1 - equivWidth nvCogRectProfile τ) = τ := by
  unfold nvCogRectProfile
  rw [equivWidth_rectangular]
  have h : (1:ℝ) - (1 - Real.exp (-τ)) = Real.exp (-τ) := by ring
  rw [h, Real.log_exp, neg_neg]

-- Non-vacuity: the forward-sensitivity bound is a real inequality on concrete depths `τ ∈ {1, 2}`.
example : |(1 - Real.exp (-(2:ℝ))) - (1 - Real.exp (-(1:ℝ)))| ≤ Real.exp (-(1:ℝ)) * (2 - 1) :=
  slabCurve_forward_lipschitz (by norm_num)

-- Non-vacuity: the inverse ill-conditioning bound instantiates on `[0, 1/2]` (`Wmax = 1/2`).
example : |Real.log (1 - (0:ℝ)) - Real.log (1 - (1/2:ℝ))| ≤ |(0:ℝ) - 1/2| / (1 - 1/2) :=
  slabCurve_inverse_lipschitz (by norm_num) (by norm_num) (by norm_num)

-- Non-vacuity: the round-trip inverse-Lipschitz bound instantiates on `τ ≤ 2`.
example : |(1:ℝ) - 2| ≤ |(1 - Real.exp (-(1:ℝ))) - (1 - Real.exp (-(2:ℝ)))| * Real.exp 2 :=
  slabCurve_roundTrip_lipschitz (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-! ## The Lorentzian damping wing — bringing the √τ scaling into scope as a lower bound -/

/-- **The (normalized) Lorentzian profile** `L(x) = (1/π)·1/(1+x²)` — the natural / pressure-
broadening line shape, a unit-area probability density (`∫L = 1`, `lorentzian_integral`) with
heavy `∼1/x²` wings. The slow wing decay is exactly what makes the equivalent-width curve of growth
grow without bound (the √τ damping-wing regime), in contrast to the rectangular / slab profile whose
equivalent width saturates at `1` (`equivWidth_rectangular`). -/
noncomputable def lorentzian (x : ℝ) : ℝ := (1 / Real.pi) * (1 / (1 + x ^ 2))

/-- The Lorentzian profile is strictly positive. -/
theorem lorentzian_pos (x : ℝ) : 0 < lorentzian x := by
  unfold lorentzian
  exact mul_pos (div_pos one_pos Real.pi_pos) (div_pos one_pos (by positivity))

/-- The Lorentzian profile is integrable: `(1 + x²)⁻¹` is (`integrable_inv_one_add_sq`) and `L` is a
constant multiple of it. -/
theorem lorentzian_integrable : Integrable lorentzian := by
  have h : lorentzian = fun x => (Real.pi)⁻¹ * (1 + x ^ 2)⁻¹ := by
    funext x; unfold lorentzian; simp only [one_div]
  rw [h]
  exact integrable_inv_one_add_sq.const_mul _

/-- **The Lorentzian is a unit-area profile:** `∫ L = 1` (since `∫ (1 + x²)⁻¹ = π`). Hence
`equivWidth_le_thin` reads `W(τ) ≤ τ` for `L`, and the √τ lower bound below sits genuinely under
the slope-1 line for large `τ` — the curve of growth grows like `√τ`, strictly slower than `τ`. -/
theorem lorentzian_integral : ∫ x, lorentzian x = 1 := by
  have h : ∀ x, lorentzian x = (Real.pi)⁻¹ * (1 + x ^ 2)⁻¹ := by
    intro x; unfold lorentzian; simp only [one_div]
  simp only [h]
  rw [integral_const_mul, integral_univ_inv_one_add_sq, inv_mul_cancel₀ Real.pi_ne_zero]

/-- On the core plateau `1 ≤ x ≤ √(τ/2π)` the Lorentzian optical depth exceeds one: `1 ≤ τ·L(x)`.
From `1 + x² ≤ 2x²` (`x ≥ 1`, so `x² ≥ 1`) and `x² ≤ τ/2π` (`x ≤ √(τ/2π)`) we get
`π(1+x²) ≤ 2πx² ≤ τ`, whence `τ·L = τ/(π(1+x²)) ≥ 1`. -/
private theorem lorentzian_tau_ge_one {τ x : ℝ} (hτ : 0 ≤ τ)
    (hx1 : 1 ≤ x) (hx2 : x ≤ Real.sqrt (τ / (2 * Real.pi))) :
    1 ≤ τ * lorentzian x := by
  have hpi := Real.pi_pos
  have hx0 : (0:ℝ) ≤ x := le_trans zero_le_one hx1
  have hs_nn : (0:ℝ) ≤ τ / (2 * Real.pi) := by positivity
  have hx2sq : x ^ 2 ≤ τ / (2 * Real.pi) := (Real.le_sqrt hx0 hs_nn).mp hx2
  have h2pi : (0:ℝ) < 2 * Real.pi := by positivity
  have h2 : x ^ 2 * (2 * Real.pi) ≤ τ := (le_div_iff₀ h2pi).mp hx2sq
  have hxsq1 : (1:ℝ) ≤ x ^ 2 := by nlinarith [hx1, hx0]
  have hden_pos : (0:ℝ) < Real.pi * (1 + x ^ 2) := by positivity
  have hle : Real.pi * (1 + x ^ 2) ≤ τ := by nlinarith [h2, hxsq1, hpi]
  have heq : τ * lorentzian x = τ / (Real.pi * (1 + x ^ 2)) := by
    unfold lorentzian
    rw [div_mul_div_comm, mul_one, mul_one_div]
  rw [heq, one_le_div₀ hden_pos]
  exact hle

/-- **The √τ damping-wing lower bound (EXACT, within the model).** For the Lorentzian profile the
equivalent width grows at least like `√τ`: with the explicit positive constant
`c = (1 - e⁻¹)/(2√(2π))`, for every `τ ≥ 8π`,

  `c · √τ ≤ W(τ) = equivWidth lorentzian τ`.

**Contrast with the slab / rectangular profile.** There the equivalent width *saturates* —
`W = 1 - e^{-τ} ≤ 1` (`equivWidth_rectangular`), so an optically-thick slab line carries no more
integrated information than a fully black one; the inversion also becomes ill-conditioned
(`slabCurve_inverse_lipschitz`). The Lorentzian curve of growth instead *keeps growing*: its heavy
`∼1/x²` wings never go fully black, so `W → ∞` as `√τ`. This is exactly why the optically-thick
regime remains informative but must be modelled with the Lorentz-wing profile rather than the
saturating slab kernel.

**Scope.** This is a genuine **lower bound**, NOT the Ladenburg–Reiche asymptotic *equality* (the
slope-½ `W ∼ 2√(τ·⟨width⟩)` curve-of-growth function): the sharp constant and matching upper bound
need the profile-specific improper-integral asymptotics that stay OUT of scope (module honest-scope
note). Construction: on `A = [1, √(τ/2π)]` the integrand `1 - e^{-τL} ≥ 1 - e⁻¹` (since `τ·L ≥ 1`
there, `lorentzian_tau_ge_one`); lower-bounding `W` by the constant `1 - e⁻¹` on `A` via
`integral_mono` against its indicator (mirroring `equivWidth_rectangular`) gives
`W ≥ (1 - e⁻¹)(√(τ/2π) - 1) ≥ (1 - e⁻¹)·½√(τ/2π) = c·√τ`, using `τ ≥ 8π ⇒ √(τ/2π) ≥ 2`. Only the
right half-line `x ≥ 1` is used; the mirror `x ≤ -1` would double `c` but is unnecessary. -/
theorem equivWidth_lorentzian_sqrt_lower {τ : ℝ} (hτ : 8 * Real.pi ≤ τ) :
    (1 - Real.exp (-1)) / (2 * Real.sqrt (2 * Real.pi)) * Real.sqrt τ
      ≤ equivWidth lorentzian τ := by
  have hpi := Real.pi_pos
  have hτ0 : (0:ℝ) ≤ τ := le_trans (by positivity) hτ
  set s := Real.sqrt (τ / (2 * Real.pi)) with hs
  have hs_nn : (0:ℝ) ≤ τ / (2 * Real.pi) := by positivity
  have hfrac4 : (4:ℝ) ≤ τ / (2 * Real.pi) := by
    rw [le_div_iff₀ (by positivity : (0:ℝ) < 2 * Real.pi)]; nlinarith [hτ]
  have hs2 : (2:ℝ) ≤ s := by
    rw [hs, Real.le_sqrt (by norm_num) hs_nn]; nlinarith [hfrac4]
  have hexp1 : (0:ℝ) < 1 - Real.exp (-1) := by
    have : Real.exp (-1) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
    linarith
  have hp_pos : (0:ℝ) < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have hpne : Real.sqrt (2 * Real.pi) ≠ 0 := hp_pos.ne'
  have hsdiv : s = Real.sqrt τ / Real.sqrt (2 * Real.pi) := by
    rw [hs, Real.sqrt_div' τ (by positivity)]
  have hlor_nn : (0 : ℝ → ℝ) ≤ lorentzian := fun x => (lorentzian_pos x).le
  have hintegrand_int :=
    equivWidth_integrand_integrable hτ0 hlor_nn lorentzian_integrable
  have hAfin : volume (Set.Icc (1:ℝ) s) < ⊤ := measure_Icc_lt_top
  have hind_int : Integrable ((Set.Icc (1:ℝ) s).indicator (fun _ => 1 - Real.exp (-1))) :=
    (integrableOn_const (hs := hAfin.ne)).integrable_indicator measurableSet_Icc
  have hpt : ∀ x, (Set.Icc (1:ℝ) s).indicator (fun _ => 1 - Real.exp (-1)) x
      ≤ 1 - Real.exp (-(τ * lorentzian x)) := by
    intro x
    by_cases hx : x ∈ Set.Icc (1:ℝ) s
    · rw [Set.indicator_of_mem hx]
      have h1 : 1 ≤ τ * lorentzian x := lorentzian_tau_ge_one hτ0 hx.1 (hs ▸ hx.2)
      have hexp : Real.exp (-(τ * lorentzian x)) ≤ Real.exp (-1) :=
        Real.exp_le_exp.mpr (by linarith)
      linarith
    · rw [Set.indicator_of_notMem hx]
      have hnn : 0 ≤ τ * lorentzian x := mul_nonneg hτ0 (lorentzian_pos x).le
      have : Real.exp (-(τ * lorentzian x)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      linarith
  have hval : ∫ x, (Set.Icc (1:ℝ) s).indicator (fun _ => 1 - Real.exp (-1)) x
      = (s - 1) * (1 - Real.exp (-1)) := by
    rw [integral_indicator_const _ measurableSet_Icc, measureReal_def, Real.volume_Icc,
      ENNReal.toReal_ofReal (by linarith [hs2] : (0:ℝ) ≤ s - 1), smul_eq_mul]
  calc (1 - Real.exp (-1)) / (2 * Real.sqrt (2 * Real.pi)) * Real.sqrt τ
      = s / 2 * (1 - Real.exp (-1)) := by rw [hsdiv]; field_simp
    _ ≤ (s - 1) * (1 - Real.exp (-1)) :=
        mul_le_mul_of_nonneg_right (by linarith [hs2]) hexp1.le
    _ = ∫ x, (Set.Icc (1:ℝ) s).indicator (fun _ => 1 - Real.exp (-1)) x := hval.symm
    _ ≤ equivWidth lorentzian τ := by
        rw [equivWidth]; exact integral_mono hind_int hintegrand_int hpt

/-- Non-vacuity: the √τ lower bound fires at the threshold `τ = 8π` (hypothesis `8π ≤ 8π`), so the
constant `c = (1 - e⁻¹)/(2√(2π))` gives a genuine lower bound on the Lorentzian equivalent width. -/
theorem nvLz_sqrt_lower_at_threshold :
    (1 - Real.exp (-1)) / (2 * Real.sqrt (2 * Real.pi)) * Real.sqrt (8 * Real.pi)
      ≤ equivWidth lorentzian (8 * Real.pi) :=
  equivWidth_lorentzian_sqrt_lower le_rfl

/-- For `t ≥ 0` the arctangent lies below the diagonal: `arctan t ≤ t`. The graph of `arctan` is
concave on `[0, ∞)` with unit slope at the origin; here from `Real.lt_tan` on `arctan t ∈ [0, π/2)`
together with `tan (arctan t) = t`. (PURE-MATH.) -/
private theorem nvLzu_arctan_le_self {t : ℝ} (ht : 0 ≤ t) : Real.arctan t ≤ t := by
  rcases eq_or_lt_of_le ht with h | h
  · subst h; simp
  · have hlt := Real.lt_tan (Real.arctan_pos.mpr h) (Real.arctan_lt_pi_div_two t)
    rw [Real.tan_arctan] at hlt
    exact hlt.le

/-- **The √τ damping-wing UPPER bound (EXACT, within the model).** Matching
`equivWidth_lorentzian_sqrt_lower`: for the Lorentzian profile the equivalent width grows *at most*
like `√τ`, with the explicit constant `C = 4/√π`, for every `τ ≥ 0`:

  `W(τ) = equivWidth lorentzian τ ≤ (4/√π) · √τ`.

**Construction (split at `a = √(τ/π)`).** Decompose `ℝ = [-a, a] ∪ [-a, a]ᶜ`
(`integral_add_compl`). On the core `[-a, a]` the integrand `1 - e^{-τL} ≤ 1`, so the inner part is
`≤ vol [-a, a] = 2a`. On the tails `1 - e^{-τL} ≤ τ·L` (`Real.one_sub_le_exp_neg`), and the
Lorentzian tail mass is `∫_{[-a,a]ᶜ} L = 1 - (2/π)·arctan a = (2/π)·arctan(1/a) ≤ (2/π)/a`
(`arctan_inv_of_pos`, `nvLzu_arctan_le_self`); since `τ = π·a²` the outer part is
`≤ τ·(2/π)/a = 2a`. Total `W ≤ 4a = 4√(τ/π) = (4/√π)·√τ`.

**Scope.** A genuine **upper bound**; the constant `4/√π ≈ 2.257` is NOT sharp (the split is
deliberately crude). With the lower bound this pins the `√τ` *regime* up to constants — but the
Ladenburg–Reiche sharp-constant asymptotic *equality* stays OUT of scope (module honest-scope
note). Gornushkin 1999. -/
theorem equivWidth_lorentzian_sqrt_upper {τ : ℝ} (hτ : 0 ≤ τ) :
    equivWidth lorentzian τ ≤ 4 / Real.sqrt Real.pi * Real.sqrt τ := by
  have hπpos := Real.pi_pos
  have hπne : Real.pi ≠ 0 := Real.pi_ne_zero
  have hlor_nn : (0 : ℝ → ℝ) ≤ lorentzian := fun x => (lorentzian_pos x).le
  rcases eq_or_lt_of_le hτ with hz | hτpos
  · rw [← hz]; simp [equivWidth]
  · have hτ0 : (0:ℝ) ≤ τ := hτpos.le
    set a := Real.sqrt (τ / Real.pi) with ha_def
    have ha_pos : 0 < a := Real.sqrt_pos.mpr (div_pos hτpos hπpos)
    have hane : a ≠ 0 := ha_pos.ne'
    have hasq : a ^ 2 = τ / Real.pi := Real.sq_sqrt (div_nonneg hτ0 hπpos.le)
    have hπa2 : Real.pi * a ^ 2 = τ := by rw [hasq]; field_simp
    set f := fun x => 1 - Real.exp (-(τ * lorentzian x))
    have hf_int : Integrable f :=
      equivWidth_integrand_integrable hτ0 hlor_nn lorentzian_integrable
    have hvol : ∫ _ in Set.Icc (-a) a, (1:ℝ) = 2 * a := by
      rw [setIntegral_const, smul_eq_mul, mul_one, measureReal_def, Real.volume_Icc,
        ENNReal.toReal_ofReal (by linarith : (0:ℝ) ≤ a - -a)]
      ring
    have hinner : ∫ x in Set.Icc (-a) a, f x ≤ 2 * a := by
      have hci : IntegrableOn (fun _ : ℝ => (1:ℝ)) (Set.Icc (-a) a) :=
        integrableOn_const (hs := measure_Icc_lt_top.ne)
      have hle : ∫ x in Set.Icc (-a) a, f x ≤ ∫ _ in Set.Icc (-a) a, (1:ℝ) := by
        refine setIntegral_mono_on hf_int.integrableOn hci measurableSet_Icc (fun x _ => ?_)
        change (1:ℝ) - Real.exp (-(τ * lorentzian x)) ≤ 1
        linarith [Real.exp_pos (-(τ * lorentzian x))]
      exact hle.trans_eq hvol
    have hLs : ∫ x in Set.Icc (-a) a, lorentzian x = 2 / Real.pi * Real.arctan a := by
      have hL : ∀ x, lorentzian x = (Real.pi)⁻¹ * (1 + x ^ 2)⁻¹ := by
        intro x; unfold lorentzian; simp only [one_div]
      simp only [hL]
      rw [integral_const_mul, integral_Icc_eq_integral_Ioc,
        intervalIntegral.integral_of_le (by linarith : (-a:ℝ) ≤ a) |>.symm,
        integral_inv_one_add_sq, Real.arctan_neg]
      ring
    have hcompl : ∫ x in (Set.Icc (-a) a)ᶜ, lorentzian x
        = 1 - 2 / Real.pi * Real.arctan a := by
      rw [setIntegral_compl₀ measurableSet_Icc.nullMeasurableSet lorentzian_integrable,
        lorentzian_integral, hLs]
    have hinv : Real.arctan a⁻¹ = Real.pi / 2 - Real.arctan a := Real.arctan_inv_of_pos ha_pos
    have hinv' : Real.arctan a = Real.pi / 2 - Real.arctan a⁻¹ := by linarith [hinv]
    have harc : Real.arctan a⁻¹ ≤ a⁻¹ := nvLzu_arctan_le_self (inv_pos.mpr ha_pos).le
    have hstep : ∫ x in (Set.Icc (-a) a)ᶜ, f x
        ≤ τ * ∫ x in (Set.Icc (-a) a)ᶜ, lorentzian x := by
      rw [← integral_const_mul]
      refine setIntegral_mono_on hf_int.integrableOn
        (lorentzian_integrable.const_mul τ).integrableOn measurableSet_Icc.compl (fun x _ => ?_)
      change (1:ℝ) - Real.exp (-(τ * lorentzian x)) ≤ τ * lorentzian x
      linarith [Real.one_sub_le_exp_neg (τ * lorentzian x)]
    rw [hcompl] at hstep
    have hkey : τ * (1 - 2 / Real.pi * Real.arctan a) = 2 * a ^ 2 * Real.arctan a⁻¹ := by
      rw [← hπa2, hinv']; field_simp; ring
    have hfin2 : 2 * a ^ 2 * Real.arctan a⁻¹ ≤ 2 * a := by
      have h1 : 2 * a ^ 2 * Real.arctan a⁻¹ ≤ 2 * a ^ 2 * a⁻¹ :=
        mul_le_mul_of_nonneg_left harc (by positivity)
      have h2 : 2 * a ^ 2 * a⁻¹ = 2 * a := by field_simp
      linarith [h1, h2]
    have houter : ∫ x in (Set.Icc (-a) a)ᶜ, f x ≤ 2 * a :=
      hstep.trans (hkey.le.trans hfin2)
    calc equivWidth lorentzian τ
        = (∫ x in Set.Icc (-a) a, f x) + (∫ x in (Set.Icc (-a) a)ᶜ, f x) := by
          rw [equivWidth]; exact (integral_add_compl measurableSet_Icc hf_int).symm
      _ ≤ 2 * a + 2 * a := add_le_add hinner houter
      _ = 4 * a := by ring
      _ = 4 / Real.sqrt Real.pi * Real.sqrt τ := by rw [ha_def, Real.sqrt_div hτ0]; ring

/-- **The √τ damping-wing REGIME, pinned up to constants (EXACT, within the model).** Combining
`equivWidth_lorentzian_sqrt_lower` with `equivWidth_lorentzian_sqrt_upper`: for `τ ≥ 8π` the
Lorentzian equivalent width is trapped between two explicit `√τ` lines,

  `(1 - e⁻¹)/(2√(2π)) · √τ ≤ W(τ) ≤ (4/√π) · √τ`.

So the curve of growth grows *exactly* on the order of `√τ` — the slope-½ damping wing — with the
two explicit constants (`≈ 0.126` and `≈ 2.257`) bracketing it. **The sharp Ladenburg–Reiche
asymptotic EQUALITY (the exact slope-½ constant `W ∼ 2√(τ·⟨width⟩)`) stays OUT of scope:** it needs
the profile-specific improper-integral asymptotics, not merely the two-sided envelope proved here.
Gornushkin 1999. -/
theorem equivWidth_lorentzian_sqrt_two_sided {τ : ℝ} (hτ : 8 * Real.pi ≤ τ) :
    (1 - Real.exp (-1)) / (2 * Real.sqrt (2 * Real.pi)) * Real.sqrt τ
        ≤ equivWidth lorentzian τ
    ∧ equivWidth lorentzian τ ≤ 4 / Real.sqrt Real.pi * Real.sqrt τ :=
  ⟨equivWidth_lorentzian_sqrt_lower hτ,
    equivWidth_lorentzian_sqrt_upper (le_trans (by positivity) hτ)⟩

/-- Non-vacuity: the two-sided √τ envelope fires at the threshold `τ = 8π`, trapping the Lorentzian
equivalent width between the two explicit constants at a concrete optical depth. -/
example :
    (1 - Real.exp (-1)) / (2 * Real.sqrt (2 * Real.pi)) * Real.sqrt (8 * Real.pi)
        ≤ equivWidth lorentzian (8 * Real.pi)
    ∧ equivWidth lorentzian (8 * Real.pi)
        ≤ 4 / Real.sqrt Real.pi * Real.sqrt (8 * Real.pi) :=
  equivWidth_lorentzian_sqrt_two_sided le_rfl

/-! ### Lorentzian width-scaling identity (Frontier 07, Phase 1) -/
/-- **The Lorentzian equivalent-width rescaling identity (EXACT, within the model).**
For width scale `τ > 0`, the equivalent width of the (unit-width) Lorentzian profile
`equivWidth lorentzian τ = ∫ x, (1 - exp(-(τ · lorentzian x)))` equals `√(τ/π)` times the
same equivalent-width integral evaluated at the *rescaled* unit profile with optical depth
`β/(1+β·u²)` where `β = τ/π`. This is the substitution `x = √(τ/π) · u` (Jacobian `√(τ/π)`)
that trades the `τ`-dependent Lorentzian width for a `τ`-dependent optical depth on a
fixed (unit) profile — the algebraic core of the Ladenburg–Reiche sharp-constant ladder
(`docs/frontiers/07-ladenburg-reiche.md`, milestone M1).

**Proof.** With `a := √(τ/π) > 0`, `a² = τ/π`, and `g x := 1 - exp(-(τ·lorentzian x))`:
pointwise `g (a * u) = 1 - exp(-((τ/π)/(1 + (τ/π)·u²)))` (pure algebra, since
`τ · lorentzian (a·u) = τ/(π·(1+(a u)²)) = (τ/π)/(1+(τ/π)u²)` using `(au)² = a²u² = (τ/π)u²`).
Mathlib's full-line linear change of variables
`MeasureTheory.Measure.integral_comp_mul_left g a : ∫ x, g (a*x) = |a⁻¹| • ∫ y, g y`
then gives `∫ y, g y = a * ∫ u, g (a*u)` (since `a > 0`), i.e. exactly the claimed identity. -/
theorem equivWidth_lorentzian_scaled (τ : ℝ) (hτ : 0 < τ) :
    equivWidth lorentzian τ
      = Real.sqrt (τ / Real.pi) *
          ∫ u, (1 - Real.exp (-((τ / Real.pi) / (1 + (τ / Real.pi) * u ^ 2)))) := by
  have hπpos := Real.pi_pos
  set a := Real.sqrt (τ / Real.pi)
  have ha_pos : 0 < a := Real.sqrt_pos.mpr (div_pos hτ hπpos)
  have ha2 : a ^ 2 = τ / Real.pi := Real.sq_sqrt (div_pos hτ hπpos).le
  set g : ℝ → ℝ := fun x => 1 - Real.exp (-(τ * lorentzian x))
  have hpt : ∀ u : ℝ,
      g (a * u) = 1 - Real.exp (-((τ / Real.pi) / (1 + (τ / Real.pi) * u ^ 2))) := by
    intro u
    have hau2 : (a * u) ^ 2 = (τ / Real.pi) * u ^ 2 := by rw [mul_pow, ha2]
    have hkey : τ * lorentzian (a * u) = (τ / Real.pi) / (1 + (τ / Real.pi) * u ^ 2) := by
      unfold lorentzian
      rw [hau2]
      have hd1 : (1 : ℝ) + a ^ 2 * u ^ 2 ≠ 0 := by
        rw [ha2]; positivity
      have hd2 : (1 : ℝ) + τ / Real.pi * u ^ 2 ≠ 0 := by positivity
      field_simp
    change (1 : ℝ) - Real.exp (-(τ * lorentzian (a * u)))
        = 1 - Real.exp (-((τ / Real.pi) / (1 + (τ / Real.pi) * u ^ 2)))
    rw [hkey]
  have hlem := MeasureTheory.Measure.integral_comp_mul_left g a
  have habs : |a⁻¹| = a⁻¹ := abs_of_pos (inv_pos.mpr ha_pos)
  rw [habs, smul_eq_mul] at hlem
  have hane : a ≠ 0 := ha_pos.ne'
  have hval : (∫ y, g y) = a * ∫ u, g (a * u) := by
    have hmul : a * ∫ x, g (a * x) = a * (a⁻¹ * ∫ y, g y) := congrArg (fun z => a * z) hlem
    rw [← mul_assoc, mul_inv_cancel₀ hane, one_mul] at hmul
    exact hmul.symm
  have hcongr : (∫ u, g (a * u))
      = ∫ u, (1 - Real.exp (-((τ / Real.pi) / (1 + (τ / Real.pi) * u ^ 2)))) := by
    congr 1
    funext u
    exact hpt u
  change (∫ y, g y) = a * ∫ u, (1 - Real.exp (-((τ / Real.pi) / (1 + (τ / Real.pi) * u ^ 2))))
  rw [hval, hcongr]

/-- Non-vacuity: `equivWidth_lorentzian_scaled` instantiates at a concrete depth `τ = π`
(so `τ/π = 1`), giving a genuine rescaling identity between the Lorentzian equivalent width
at `τ = π` and the unit-optical-depth Cauchy-kernel integral `∫ u, (1 - exp(-1/(1+u²)))`. -/
example :
    equivWidth lorentzian Real.pi
      = Real.sqrt (Real.pi / Real.pi) *
          ∫ u, (1 - Real.exp (-((Real.pi / Real.pi) / (1 + (Real.pi / Real.pi) * u ^ 2)))) :=
  equivWidth_lorentzian_scaled Real.pi Real.pi_pos


end CflibsFormal
