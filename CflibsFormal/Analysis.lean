/-
Copyright (c) 2026 Brian Squires. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Squires
-/
import Mathlib

/-!
# Shared analysis scaffolding

Small, function-agnostic real-analysis helpers reused across the proofs. The
physics-specific content stays in the originating modules; only generic facts live here:

* `strictAntiOn_div_of_deriv_num_neg` — quotient strictly antitone from a negative
  derivative numerator (curve-of-growth / escape-factor monotonicity scaffold).
* `exp_sub_le_mul` / `abs_exp_sub_le` — the one-sided and two-point exponential slope
  bounds (`exp a − exp b ≤ exp a·(a−b)`, `|exp a − exp b| ≤ max(exp a, exp b)·|a−b|`),
  the kernel of every temperature-sensitivity bound.
* `abs_exp_sub_one_le` — the exponential perturbation bound `|x| ≤ η ⇒ |exp x − 1| ≤ exp η − 1`
  (log-domain error ⇒ relative error).
* `inv_kT_sub_le` — the inverse-temperature gap bound
  `|1/(k_B T₁) − 1/(k_B T₂)| ≤ |T₁ − T₂|/(k_B·Tmin²)` on a temperature floor.

Formerly, isolated per-module `private` copies of the exponential and inverse-temperature
lemmas lived in `Identifiability`, `PartitionLipschitz`, `SahaStability`, `ErrorBudget`, and
`AtomicDataPerturbation`; this module is their single public home.
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

/-- **Elementary exponential slope bound.** For all reals `a, b`,
`exp a − exp b ≤ exp a · (a − b)` (from `Real.add_one_le_exp (b − a)`). No ordering
hypothesis is needed. Pure real analysis. -/
theorem exp_sub_le_mul (a b : ℝ) :
    Real.exp a - Real.exp b ≤ Real.exp a * (a - b) := by
  have hstep : b - a + 1 ≤ Real.exp (b - a) := Real.add_one_le_exp (b - a)
  have hle : Real.exp a * (1 - Real.exp (b - a)) ≤ Real.exp a * (a - b) :=
    mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos a).le
  have hrw : Real.exp a * (1 - Real.exp (b - a)) = Real.exp a - Real.exp b := by
    have hab : a + (b - a) = b := by ring
    rw [mul_sub, mul_one, ← Real.exp_add, hab]
  rwa [hrw] at hle

/-- **Two-point Lipschitz-type bound for `exp`.** `|exp a − exp b| ≤ max(exp a, exp b)·|a − b|`:
the slope is controlled by the larger endpoint value. Symmetrising `exp_sub_le_mul` over
`le_total b a`. The kernel of every temperature-sensitivity bound in the spec. -/
theorem abs_exp_sub_le (a b : ℝ) :
    |Real.exp a - Real.exp b| ≤ max (Real.exp a) (Real.exp b) * |a - b| := by
  rcases le_total b a with h | h
  · rw [max_eq_left (Real.exp_le_exp.mpr h),
      abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr h)),
      abs_of_nonneg (sub_nonneg.mpr h)]
    exact exp_sub_le_mul a b
  · rw [max_eq_right (Real.exp_le_exp.mpr h),
      abs_sub_comm (Real.exp a) (Real.exp b), abs_sub_comm a b,
      abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr h)),
      abs_of_nonneg (sub_nonneg.mpr h)]
    exact exp_sub_le_mul b a

/-- **Exponential perturbation bound.** `|exp x − 1| ≤ exp η − 1` whenever `|x| ≤ η`. The
kernel of "log-domain error ⇒ relative error": a bounded additive error on a log-quantity (an
intercept, a temperature) maps to a bounded relative error. Exact (no linearization); the
leading term is `η`, since `exp η − 1 → η` as `η → 0`. -/
theorem abs_exp_sub_one_le {x eta : ℝ} (hx : |x| ≤ eta) :
    |Real.exp x - 1| ≤ Real.exp eta - 1 := by
  have h := abs_le.mp hx
  have hup : Real.exp x ≤ Real.exp eta := Real.exp_le_exp.mpr h.2
  have hlo : Real.exp (-eta) ≤ Real.exp x := Real.exp_le_exp.mpr h.1
  have hsum : (2 : ℝ) ≤ Real.exp eta + Real.exp (-eta) := by
    have a := Real.add_one_le_exp eta
    have b := Real.add_one_le_exp (-eta)
    linarith
  rw [abs_le]
  exact ⟨by nlinarith [hlo, hsum], by linarith [hup]⟩

/-- **Inverse-temperature gap bound.** On a floor `Tmin ≤ T₁, T₂` (`0 < Tmin`, `0 < k_B`),
`|1/(k_B T₁) − 1/(k_B T₂)| ≤ |T₁ − T₂|/(k_B·Tmin²)`, since the difference equals
`(T₂ − T₁)/(k_B T₁ T₂)` and `T₁ T₂ ≥ Tmin²`. Pure real algebra; the bridge from a
temperature error to an inverse-temperature (Boltzmann-exponent) error. -/
theorem inv_kT_sub_le {kB Tmin T1 T2 : ℝ}
    (hkB : 0 < kB) (hTmin : 0 < Tmin) (hT1 : Tmin ≤ T1) (hT2 : Tmin ≤ T2) :
    |1 / (kB * T1) - 1 / (kB * T2)| ≤ |T1 - T2| / (kB * Tmin ^ 2) := by
  have hT1pos : 0 < T1 := lt_of_lt_of_le hTmin hT1
  have hT2pos : 0 < T2 := lt_of_lt_of_le hTmin hT2
  have hbig : 0 < kB * T1 * T2 := mul_pos (mul_pos hkB hT1pos) hT2pos
  have hsmall : 0 < kB * Tmin ^ 2 := mul_pos hkB (pow_pos hTmin 2)
  have heq : 1 / (kB * T1) - 1 / (kB * T2) = (T2 - T1) / (kB * T1 * T2) := by
    field_simp
  rw [heq, abs_div, abs_of_pos hbig, abs_sub_comm T2 T1, div_le_div_iff₀ hbig hsmall]
  have hTsq : Tmin ^ 2 ≤ T1 * T2 := by
    rw [sq]; exact mul_le_mul hT1 hT2 hTmin.le hT1pos.le
  have hden : kB * Tmin ^ 2 ≤ kB * T1 * T2 := by
    calc kB * Tmin ^ 2 ≤ kB * (T1 * T2) := mul_le_mul_of_nonneg_left hTsq hkB.le
      _ = kB * T1 * T2 := by ring
  exact mul_le_mul_of_nonneg_left hden (abs_nonneg _)

end CflibsFormal

