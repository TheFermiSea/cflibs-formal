import Mathlib

open Filter Topology

namespace Plan.FT02

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

/-- `ipdLogMap a b` is `q`-Lipschitz on `Iic ℓ1` when `b·exp(ℓ1/2)/2 ≤ q`, `0 ≤ b`. -/
lemma ipdLogMap_lipschitz_Iic {a b ℓ1 q : ℝ} (hb : 0 ≤ b) (hq : b * Real.exp (ℓ1 / 2) / 2 ≤ q)
    {x y : ℝ} (hx : x ≤ ℓ1) (hy : y ≤ ℓ1) :
    |ipdLogMap a b x - ipdLogMap a b y| ≤ q * |x - y| := by
  have key : ∀ u v : ℝ, u ≤ v → v ≤ ℓ1 →
      |ipdLogMap a b u - ipdLogMap a b v| ≤ q * |u - v| := by
    intro u v huv hv
    have h0 : 0 ≤ Real.exp (v / 2) - Real.exp (u / 2) := sub_nonneg.mpr (exp_half_mono huv)
    have h1 := exp_half_sub_le u v
    have h2 : Real.exp (v / 2) ≤ Real.exp (ℓ1 / 2) := exp_half_mono hv
    have hdiff : ipdLogMap a b u - ipdLogMap a b v
        = -(b * (Real.exp (v / 2) - Real.exp (u / 2))) := by
      unfold ipdLogMap; ring
    rw [hdiff, abs_neg, abs_of_nonneg (mul_nonneg hb h0),
      abs_of_nonpos (by linarith : u - v ≤ 0)]
    calc b * (Real.exp (v / 2) - Real.exp (u / 2))
        ≤ b * (Real.exp (v / 2) / 2 * (v - u)) := mul_le_mul_of_nonneg_left h1 hb
      _ = (b * Real.exp (v / 2) / 2) * (v - u) := by ring
      _ ≤ q * (v - u) := by
          apply mul_le_mul_of_nonneg_right _ (by linarith)
          nlinarith [mul_le_mul_of_nonneg_left h2 hb]
      _ = q * -(u - v) := by ring
  rcases le_total x y with hxy | hxy
  · exact key x y hxy hy
  · rw [abs_sub_comm, abs_sub_comm x y]; exact key y x hxy hx

end Plan.FT02
