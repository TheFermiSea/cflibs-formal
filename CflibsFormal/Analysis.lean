/-
Copyright (c) 2026 Brian Squires. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Squires
-/
import Mathlib

/-!
# Shared analysis scaffolding

A small, function-agnostic real-analysis helper reused across the curve-of-growth /
escape-factor monotonicity proofs. The physics-specific content (the sign of each
derivative numerator) stays in the originating modules; only the generic
`strictAntiOn_of_deriv_neg` + quotient-rule plumbing lives here.
-/

namespace CflibsFormal

open Set

/-- **Quotient strictly antitone from a negative derivative numerator.** On `(0, ∞)`, if `g > 0`
and `f`, `g` are differentiable with `f'·g − f·g' < 0`, then `x ↦ f x / g x` is strictly antitone.
The shared scaffold behind the curve-of-growth / escape-factor monotonicity proofs
(`strictAntiOn_of_deriv_neg` + the quotient rule). -/
theorem strictAntiOn_div_of_deriv_num_neg {f g f' g' : ℝ → ℝ}
    (hg : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < g x)
    (hf : ∀ x ∈ Set.Ioi (0 : ℝ), HasDerivAt f (f' x) x)
    (hg' : ∀ x ∈ Set.Ioi (0 : ℝ), HasDerivAt g (g' x) x)
    (hnum : ∀ x ∈ Set.Ioi (0 : ℝ), f' x * g x - f x * g' x < 0) :
    StrictAntiOn (fun x => f x / g x) (Set.Ioi 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioi 0)
  · intro x hx
    exact (((hf x hx).continuousAt.continuousWithinAt).div
      ((hg' x hx).continuousAt.continuousWithinAt) (hg x hx).ne')
  · intro x hx
    rw [interior_Ioi] at hx
    have hd : HasDerivAt (fun x => f x / g x)
        ((f' x * g x - f x * g' x) / g x ^ 2) x :=
      (hf x hx).div (hg' x hx) (hg x hx).ne'
    rw [hd.deriv]
    exact div_neg_of_neg_of_pos (hnum x hx) (pow_pos (hg x hx) 2)

/-! ### Exponential Lipschitz-below bound (temperature metric stability) -/

/-- One-directional exponential mean-value bound: for `y ≤ x`,
    `exp y * (x - y) ≤ exp x - exp y`.  Follows from `x - y + 1 ≤ exp (x - y)`.
    (The hypothesis `_h` is unused: the bound in fact holds for all reals.) -/
private lemma exp_sub_ge {x y : ℝ} (_h : y ≤ x) :
    Real.exp y * (x - y) ≤ Real.exp x - Real.exp y := by
  have hpos := Real.exp_pos y
  have key : (x - y) + 1 ≤ Real.exp (x - y) := Real.add_one_le_exp (x - y)
  have step : Real.exp y * (x - y) ≤ Real.exp y * (Real.exp (x - y) - 1) :=
    mul_le_mul_of_nonneg_left (by linarith) hpos.le
  have harg : y + (x - y) = x := by ring
  have eqn : Real.exp y * (Real.exp (x - y) - 1) = Real.exp x - Real.exp y := by
    rw [mul_sub, mul_one, ← Real.exp_add, harg]
  linarith [step, eqn]

/-- General exponential Lipschitz-below bound:
    `exp (min x y) * |x - y| ≤ |exp x - exp y|` for all reals. -/
private lemma exp_diff_lower (x y : ℝ) :
    Real.exp (min x y) * |x - y| ≤ |Real.exp x - Real.exp y| := by
  rcases le_total y x with h | h
  · -- `y ≤ x`, so `min x y = y`
    rw [min_eq_right h]
    have hd : |x - y| = x - y := abs_of_nonneg (by linarith)
    have hsub : Real.exp y * (x - y) ≤ Real.exp x - Real.exp y := exp_sub_ge h
    have hge : 0 ≤ Real.exp x - Real.exp y := by
      nlinarith [hsub, mul_nonneg (Real.exp_pos y).le (show (0:ℝ) ≤ x - y by linarith)]
    rw [hd, abs_of_nonneg hge]; exact hsub
  · -- `x ≤ y`, so `min x y = x`
    rw [min_eq_left h]
    have hd : |x - y| = y - x := by rw [abs_of_nonpos (by linarith)]; ring
    have hsub : Real.exp x * (y - x) ≤ Real.exp y - Real.exp x := exp_sub_ge h
    have hle : Real.exp x - Real.exp y ≤ 0 := by
      nlinarith [hsub, mul_nonneg (Real.exp_pos x).le (show (0:ℝ) ≤ y - x by linarith)]
    rw [hd, abs_of_nonpos hle]; linarith [hsub]

/-- On a temperature box `[Tmin,Tmax]` (`0 < Tmin`), the map `T ↦ exp (D / T)` is
    Lipschitz-below in `T`, with explicit positive constant
    `exp (-(|D| / Tmin)) * (|D| / Tmax ^ 2)`. -/
lemma temp_exp_diff_lower {D Tmin Tmax T T0 : ℝ}
    (hTmin : 0 < Tmin) (hT : Tmin ≤ T) (hTM : T ≤ Tmax)
    (hT0 : Tmin ≤ T0) (hT0M : T0 ≤ Tmax) :
    Real.exp (-(|D| / Tmin)) * (|D| / Tmax ^ 2) * |T - T0|
      ≤ |Real.exp (D / T) - Real.exp (D / T0)| := by
  have hTpos : 0 < T := lt_of_lt_of_le hTmin hT
  have hT0pos : 0 < T0 := lt_of_lt_of_le hTmin hT0
  have hTmaxpos : 0 < Tmax := lt_of_lt_of_le hTpos hTM
  -- Step 2: lower bound the arguments, hence `min`.
  have hDT : -(|D| / Tmin) ≤ D / T :=
    neg_le_of_abs_le (by rw [abs_div, abs_of_pos hTpos]; gcongr)
  have hDT0 : -(|D| / Tmin) ≤ D / T0 :=
    neg_le_of_abs_le (by rw [abs_div, abs_of_pos hT0pos]; gcongr)
  have hmin : -(|D| / Tmin) ≤ min (D / T) (D / T0) := le_min hDT hDT0
  have ha : Real.exp (-(|D| / Tmin)) ≤ Real.exp (min (D / T) (D / T0)) :=
    Real.exp_le_exp.mpr hmin
  -- Step 3: lower bound the argument gap.
  have hTT0 : T * T0 ≤ Tmax ^ 2 := by
    rw [sq]; exact mul_le_mul hTM hT0M hT0pos.le (le_trans hT0pos.le hT0M)
  have heq : |D / T - D / T0| = |D| * |T - T0| / (T * T0) := by
    have hb1 : D / T - D / T0 = D * (T0 - T) / (T * T0) := by
      rw [div_sub_div D D (ne_of_gt hTpos) (ne_of_gt hT0pos)]; ring
    rw [hb1, abs_div, abs_mul, abs_of_pos (mul_pos hTpos hT0pos), abs_sub_comm T0 T]
  have hb : |D| / Tmax ^ 2 * |T - T0| ≤ |D / T - D / T0| := by
    rw [heq, div_mul_eq_mul_div]
    gcongr
  -- Combine the two factors, then chain with the general bound.
  have hA2 : (0:ℝ) ≤ |D| / Tmax ^ 2 * |T - T0| := by positivity
  have hcomb :
      Real.exp (-(|D| / Tmin)) * (|D| / Tmax ^ 2 * |T - T0|)
        ≤ Real.exp (min (D / T) (D / T0)) * |D / T - D / T0| :=
    mul_le_mul ha hb hA2 (Real.exp_pos _).le
  calc Real.exp (-(|D| / Tmin)) * (|D| / Tmax ^ 2) * |T - T0|
      = Real.exp (-(|D| / Tmin)) * (|D| / Tmax ^ 2 * |T - T0|) := by ring
    _ ≤ Real.exp (min (D / T) (D / T0)) * |D / T - D / T0| := hcomb
    _ ≤ |Real.exp (D / T) - Real.exp (D / T0)| := exp_diff_lower (D / T) (D / T0)

end CflibsFormal
