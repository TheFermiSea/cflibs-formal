import Mathlib
import CflibsFormal.Boltzmann

open Finset CflibsFormal

namespace Plan.FT15

variable {ι : Type*} [Fintype ι]

/-- Boltzmann-weighted mean excitation energy `⟨E⟩_T = ∑ g E e^{-E/kT} / U(T)`. -/
noncomputable def meanExcitation (kB T : ℝ) (g E : ι → ℝ) : ℝ :=
  (∑ k, g k * E k * boltzmannFactor kB T (E k)) / partitionFunction kB T g E

theorem meanExcitation_monotoneOn_temp [Nonempty ι] {kB : ℝ} {g E : ι → ℝ} (hkB : 0 < kB)
    (hg : ∀ k, 0 < g k) :
    MonotoneOn (fun T => meanExcitation kB T g E) (Set.Ioi 0) := by
  sorry

end Plan.FT15
