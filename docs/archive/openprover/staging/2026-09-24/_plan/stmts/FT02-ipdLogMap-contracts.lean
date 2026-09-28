import Mathlib

open Filter Topology

namespace Plan.FT02


/-- Log-coordinate IPD-aware Saha inverse map, `ℓ = log n_e`, with the lowering term
`b·e^{ℓ/2}` (coefficient `b` abstract). -/
noncomputable def ipdLogMap (a b ℓ : ℝ) : ℝ := Real.log a + b * Real.exp (ℓ / 2)

theorem ipdLogMap_contracts {a b ℓ1 q : ℝ} (hb : 0 ≤ b)
    (hq : b * Real.exp (ℓ1 / 2) / 2 ≤ q) (hq1 : q < 1)
    (hmaps : Set.MapsTo (ipdLogMap a b) (Set.Iic ℓ1) (Set.Iic ℓ1)) :
    ∃ ℓs ∈ Set.Iic ℓ1, ipdLogMap a b ℓs = ℓs ∧
      (∀ ℓ ∈ Set.Iic ℓ1, ipdLogMap a b ℓ = ℓ → ℓ = ℓs) ∧
      ∀ ℓ0 ∈ Set.Iic ℓ1, Tendsto (fun n => (ipdLogMap a b)^[n] ℓ0) atTop (𝓝 ℓs) := by
  sorry

end Plan.FT02
