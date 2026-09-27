/-
Copyright (c) 2026 Brian Squires. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Squires
-/
import Mathlib
import CflibsFormal.SelfAbsorption
import CflibsFormal.EquivalentWidth
import CflibsFormal.CurveOfGrowth

/-!
# Profile escape factor versus the flat-slab self-absorption factor

`SelfAbsorption.selfAbsorptionFactor` is the flat-profile escape factor
`SA(τ) = (1 − exp(−τ))/τ`: one optical depth for the whole line. A real line has a profile
`ψ`, and its integrated self-absorbed strength is the equivalent width
`W(ψ, τ₀) = ∫ (1 − exp(−τ₀ ψ(x))) dx` (`EquivalentWidth.equivWidth`), whose optically thin
value is `τ₀ ∫ ψ`. This module compares the two.

## Main results

* `escape_ge_slab`: for a profile with `0 ≤ ψ ≤ 1` (so `τ₀` is at least the depth at every
  frequency; `τ₀` is the line-centre depth when `ψ` peaks at `1`), integrable, and `τ₀ > 0`,
  `SA(τ₀) · (τ₀ ∫ ψ) ≤ W(ψ, τ₀)`. The profile-integrated escape factor `W/(τ₀ ∫ ψ)` is at
  least the flat-slab factor at the line-centre depth. Equality holds for a rectangular profile
  (`equivWidth_rectangular`). Proof: the chord inequality of the convex `exp` applied pointwise
  at `t = ψ(x) ∈ [0, 1]`, then `integral_mono`.
* `inv_sub_inv_exp_sub_one_mem`: `0 < 1/τ − 1/(exp τ − 1) < 1/2` for `τ > 0`. Since
  `d/dτ log SA(τ) = 1/(exp τ − 1) − 1/τ` (a calculus fact not formalized here), this is the
  statement that `log SA` has slope in `(−1/2, 0)`. Both bounds are sharp in the limits.

Both results are pure mathematics about the defined functions. No statement here says which
profile a real line has, or how well either factor corrects a measured intensity.

## Literature

Gornushkin, Anzano, King, Smith, Omenetto, Winefordner, "Curve of growth methodology applied
to laser-induced plasma emission spectroscopy", *Spectrochimica Acta Part B* **54** (1999) 491
— the curve of growth, its equivalent width and the slab escape factor; Bulajic, Corsi,
Cristoforetti, Legnaioli, Palleschi, Salvetti, Tognoni, "A procedure for correcting
self-absorption in calibration-free LIBS", *Spectrochimica Acta Part B* **57** (2002) 339 — the
self-absorption correction that uses `SA`.
-/

namespace CflibsFormal

open MeasureTheory

/-- Derivative of `exp t · (t − 2) + t + 2`. -/
private theorem hasDerivAt_exp_mul_sub_two_add (t : ℝ) :
    HasDerivAt (fun t => Real.exp t * (t - 2) + t + 2)
      (Real.exp t * (t - 2) + Real.exp t * 1 + 1) t :=
  (((Real.hasDerivAt_exp t).mul ((hasDerivAt_id t).sub_const 2)).add (hasDerivAt_id t)).add_const 2

/-- Positivity of `exp t · (t − 2) + t + 2` on `t > 0`: it vanishes at `0` and its derivative
`exp t · (t − 1) + 1` is positive there by `exp_mul_one_sub_lt_one`. -/
private theorem exp_mul_sub_two_add_pos {τ : ℝ} (hτ : 0 < τ) :
    0 < Real.exp τ * (τ - 2) + τ + 2 := by
  have hmono : StrictMonoOn (fun t => Real.exp t * (t - 2) + t + 2) (Set.Ici (0:ℝ)) := by
    refine strictMonoOn_of_hasDerivWithinAt_pos (convex_Ici (0:ℝ)) ?_
      (fun x _ => (hasDerivAt_exp_mul_sub_two_add x).hasDerivWithinAt) ?_
    · fun_prop
    · intro x hx
      rw [interior_Ici] at hx
      have hx' : 0 < x := hx
      nlinarith [exp_mul_one_sub_lt_one hx', Real.exp_pos x]
  have h0 : (0:ℝ) ∈ Set.Ici (0:ℝ) := Set.mem_Ici.mpr le_rfl
  have hτ' : τ ∈ Set.Ici (0:ℝ) := Set.mem_Ici.mpr hτ.le
  have := hmono h0 hτ' hτ
  simp at this
  linarith

/-- **The log slab self-absorption factor has slope in `(−1/2, 0)`.** For `τ > 0`,
`0 < 1/τ − 1/(exp τ − 1) < 1/2`. The middle expression is minus the derivative of
`log SA(τ) = log ((1 − exp(−τ))/τ)`. That identity is context, not part of this statement;
with it, `log SA` is strictly decreasing and `1/2`-Lipschitz on `τ > 0`. Both bounds are strict
and sharp in the limits (`→ 1/2` as `τ → 0⁺`, `→ 0` as `τ → ∞`), so the proof goes through the
exact inequality `exp τ · (τ − 2) + τ + 2 > 0`, not a numerical estimate.

Hypothesis `hτ` is needed: at `τ = 0` Lean's `1/0 = 0` makes the middle expression `0`, and at
`τ = −1` it is `≈ 0.58 > 1/2`. Scope: PURE-MATH. -/
theorem inv_sub_inv_exp_sub_one_mem {τ : ℝ} (hτ : 0 < τ) :
    0 < 1 / τ - 1 / (Real.exp τ - 1) ∧ 1 / τ - 1 / (Real.exp τ - 1) < 1 / 2 := by
  constructor
  · have hlt : τ < Real.exp τ - 1 := by linarith [Real.add_one_lt_exp hτ.ne']
    have := one_div_lt_one_div_of_lt hτ hlt
    linarith
  · have hE : 0 < Real.exp τ - 1 := by linarith [Real.add_one_lt_exp hτ.ne']
    have hf := exp_mul_sub_two_add_pos hτ
    rw [div_sub_div _ _ hτ.ne' hE.ne', div_lt_div_iff₀ (mul_pos hτ hE) (by norm_num : (0:ℝ) < 2)]
    nlinarith [hf, Real.exp_pos τ]

/-- Chord inequality of the convex `exp`: `(1 − exp(−τ)) · t ≤ 1 − exp(−τ t)` for
`t ∈ [0, 1]`. -/
private theorem slab_chord_le {τ t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 - Real.exp (-τ)) * t ≤ 1 - Real.exp (-(τ * t)) := by
  have hc := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (-τ))
    (by linarith : (0 : ℝ) ≤ 1 - t) ht0 (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at hc
  have : t * -τ = -(τ * t) := by ring
  rw [this] at hc
  nlinarith [hc]

/-- **The profile escape factor bounds the flat-slab factor from above.** For a profile `ψ`
with `0 ≤ ψ ≤ 1`, integrable, and a depth `τ₀ > 0`,
`selfAbsorptionFactor τ₀ · (τ₀ · ∫ ψ) ≤ equivWidth ψ τ₀`.

Reading: `τ₀ ∫ ψ` is the optically thin equivalent width and `W/(τ₀ ∫ ψ)` the profile-integrated
escape factor, so (when `∫ ψ > 0`) that escape factor is at least the flat-slab factor `SA(τ₀)`.
With `ψ ≤ 1`, `τ₀` bounds the depth at every frequency; it is the line-centre depth when `ψ`
peaks at `1`. The wings are less absorbed than the centre, which is the whole mechanism: the
chord inequality `(1 − exp(−τ₀)) t ≤ 1 − exp(−τ₀ t)` for `t = ψ(x) ∈ [0, 1]`, integrated.
Equality holds for the rectangular profile (`equivWidth_rectangular`).

Hypotheses: `hψ1` and `hψ0` are load-bearing (the chord inequality reverses outside `[0, 1]`;
numerically, `ψ = 2` on `[0, 1]` with `τ₀ = 1` gives `1.26 > 0.86`, and `ψ = −1` on `[0, 1]`
gives `−0.63 > −1.72`); `hint` supplies the integrability that `integral_mono` needs
(`equivWidth_integrand_integrable`); `hτ` is the physical domain and selects the non-totalized
branch of `selfAbsorptionFactor`; it is not claimed to be logically necessary.

Scope: PURE-MATH (an inequality between the defined functions). It does not say which profile
a real line has, and it models no inhomogeneity. Literature: Gornushkin 1999 (curve of growth,
escape factor). -/
theorem escape_ge_slab {ψ : ℝ → ℝ} {τ0 : ℝ} (hψ0 : 0 ≤ ψ) (hψ1 : ∀ x, ψ x ≤ 1)
    (hint : Integrable ψ) (hτ : 0 < τ0) :
    selfAbsorptionFactor τ0 * (τ0 * ∫ x, ψ x) ≤ equivWidth ψ τ0 := by
  have hL : selfAbsorptionFactor τ0 * (τ0 * ∫ x, ψ x) = ∫ x, (1 - Real.exp (-τ0)) * ψ x := by
    rw [selfAbsorptionFactor, if_neg hτ.ne']
    field_simp [hτ.ne']
    rw [integral_const_mul]
  rw [hL, equivWidth]
  exact integral_mono (hint.const_mul (1 - Real.exp (-τ0)))
    (equivWidth_integrand_integrable hτ.le hψ0 hint)
    (fun x => slab_chord_le (hψ0 x) (hψ1 x))

end CflibsFormal
