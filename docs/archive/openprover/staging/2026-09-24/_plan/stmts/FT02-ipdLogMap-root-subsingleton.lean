import Mathlib

open Filter Topology

namespace Plan.FT02


/-- Log-coordinate IPD-aware Saha inverse map, `ℓ = log n_e`, with the lowering term
`b·e^{ℓ/2}` (coefficient `b` abstract). -/
noncomputable def ipdLogMap (a b ℓ : ℝ) : ℝ := Real.log a + b * Real.exp (ℓ / 2)

theorem ipdLogMap_root_subsingleton {a b : ℝ} (hb : 0 < b) :
    {ℓ | ipdLogMap a b ℓ = ℓ ∧ b * Real.exp (ℓ / 2) < 2}.Subsingleton := by
  sorry

end Plan.FT02
