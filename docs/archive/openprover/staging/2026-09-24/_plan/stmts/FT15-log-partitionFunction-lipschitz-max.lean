import Mathlib
import CflibsFormal.Boltzmann

open Finset CflibsFormal

namespace Plan.FT15

variable {ι : Type*} [Fintype ι]

/-- Boltzmann-weighted mean excitation energy `⟨E⟩_T = ∑ g E e^{-E/kT} / U(T)`. -/
noncomputable def meanExcitation (kB T : ℝ) (g E : ι → ℝ) : ℝ :=
  (∑ k, g k * E k * boltzmannFactor kB T (E k)) / partitionFunction kB T g E

theorem log_partitionFunction_lipschitz_max [Nonempty ι] {kB T1 T2 : ℝ} {g E : ι → ℝ}
    (hkB : 0 < kB) (hT1 : 0 < T1) (hT2 : 0 < T2) (hg : ∀ k, 0 < g k) (hE : ∀ k, 0 ≤ E k) :
    |Real.log (partitionFunction kB T1 g E) - Real.log (partitionFunction kB T2 g E)|
      ≤ meanExcitation kB (max T1 T2) g E * |1 / (kB * T1) - 1 / (kB * T2)| := by
  sorry

end Plan.FT15
