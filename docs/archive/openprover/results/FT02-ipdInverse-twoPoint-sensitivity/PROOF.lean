-- Summary: Complete Lean 4 proof of FT02 two-point log-sensitivity bracket for ipdLogMap.
import Mathlib

/-!
# FT-02 (item 7): two-point log-sensitivity bracket for the IPD-aware Saha inverse
-/

open Filter Topology

namespace Plan.FT02

/-- **Log-coordinate IPD-aware Saha inverse map** `F(ℓ) = log a + b·exp(ℓ/2)`. -/
noncomputable def ipdLogMap (a b ℓ : ℝ) : ℝ := Real.log a + b * Real.exp (ℓ / 2)

/-- Chord below the tangent at the right end (from `Real.add_one_le_exp`): for all reals,
`exp(y/2) − exp(x/2) ≤ exp(y/2)/2 · (y − x)`. -/
lemma exp_half_sub_le (x y : ℝ) :
    Real.exp (y / 2) - Real.exp (x / 2) ≤ Real.exp (y / 2) / 2 * (y - x) := by
  have h1 := Real.add_one_le_exp ((x - y) / 2)
  have h2 : Real.exp (x / 2) = Real.exp (y / 2) * Real.exp ((x - y) / 2) := by
    rw [← Real.exp_add]; ring_nf
  have hy := Real.exp_pos (y / 2)
  rw [h2]
  nlinarith [mul_le_mul_of_nonneg_left h1 hy.le]

/-- `exp(·/2)` is monotone. -/
lemma exp_half_mono {x y : ℝ} (h : x ≤ y) : Real.exp (x / 2) ≤ Real.exp (y / 2) :=
  Real.exp_le_exp.mpr (by linarith)

/-- The fixed-point equation rearranged: `ℓ − b·exp(ℓ/2) = log a`. -/
lemma ipdLogMap_fixed_iff {a b ℓ : ℝ} :
    ipdLogMap a b ℓ = ℓ ↔ ℓ - b * Real.exp (ℓ / 2) = Real.log a := by
  unfold ipdLogMap; constructor <;> intro h <;> linarith

/-- **Two-point log-sensitivity bracket for the IPD-aware inverse (FT-02 item 7).** -/
theorem ipdInverse_twoPoint_sensitivity {a1 a2 b l1 l2 q : ℝ} (ha1 : 0 < a1) (hb : 0 ≤ b)
    (hq : q < 1) (h1 : ipdLogMap a1 b l1 = l1) (h2 : ipdLogMap a2 b l2 = l2) (ha : a1 ≤ a2)
    (hreg : b * Real.exp (max l1 l2 / 2) / 2 ≤ q) :
    Real.log a2 - Real.log a1 ≤ l2 - l1 ∧ l2 - l1 ≤ (Real.log a2 - Real.log a1) / (1 - q) := by
  have ha2 : 0 < a2 := lt_of_lt_of_le ha1 ha
  have hΔ : 0 ≤ Real.log a2 - Real.log a1 := sub_nonneg.mpr (Real.log_le_log ha1 ha)
  have e1 := ipdLogMap_fixed_iff.mp h1   -- l1 - b * exp (l1/2) = log a1
  have e2 := ipdLogMap_fixed_iff.mp h2   -- l2 - b * exp (l2/2) = log a2
  have hle : l1 ≤ l2 := by
    by_contra hlt
    push Not at hlt                        -- hlt : l2 < l1
    rw [max_eq_left hlt.le] at hreg
    have c := mul_le_mul_of_nonneg_left (exp_half_sub_le l2 l1) hb
    nlinarith [c, mul_le_mul_of_nonneg_right hreg (sub_pos.mpr hlt).le,
      mul_pos (sub_pos.mpr hq) (sub_pos.mpr hlt), e1, e2, hΔ]
  rw [max_eq_right hle] at hreg
  have c := mul_le_mul_of_nonneg_left (exp_half_sub_le l1 l2) hb
  have m := mul_nonneg hb (sub_nonneg.mpr (exp_half_mono hle))
  refine ⟨by linarith [m, e1, e2], ?_⟩
  rw [le_div_iff₀ (by linarith)]
  nlinarith [c, mul_le_mul_of_nonneg_right hreg (sub_nonneg.mpr hle), e1, e2]

end Plan.FT02
