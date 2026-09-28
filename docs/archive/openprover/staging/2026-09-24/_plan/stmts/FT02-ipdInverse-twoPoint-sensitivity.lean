import Mathlib

open Filter Topology

namespace Plan.FT02


/-- Log-coordinate IPD-aware Saha inverse map, `ℓ = log n_e`, with the lowering term
`b·e^{ℓ/2}` (coefficient `b` abstract). -/
noncomputable def ipdLogMap (a b ℓ : ℝ) : ℝ := Real.log a + b * Real.exp (ℓ / 2)

theorem ipdInverse_twoPoint_sensitivity {a1 a2 b l1 l2 q : ℝ} (ha1 : 0 < a1) (hb : 0 ≤ b)
    (hq : q < 1) (h1 : ipdLogMap a1 b l1 = l1) (h2 : ipdLogMap a2 b l2 = l2) (ha : a1 ≤ a2)
    (hreg : b * Real.exp (max l1 l2 / 2) / 2 ≤ q) :
    Real.log a2 - Real.log a1 ≤ l2 - l1 ∧ l2 - l1 ≤ (Real.log a2 - Real.log a1) / (1 - q) := by
  sorry

end Plan.FT02
