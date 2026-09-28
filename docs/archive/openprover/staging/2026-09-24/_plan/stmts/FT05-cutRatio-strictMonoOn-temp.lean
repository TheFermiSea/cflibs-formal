import Mathlib
import CflibsFormal.Boltzmann

open Finset CflibsFormal

namespace Plan.FT05


variable {ι : Type*} [Fintype ι]

/-- Partition function truncated to the levels strictly below the cutoff energy `cut`. -/
noncomputable def partitionFunctionCut (kB T cut : ℝ) (g E : ι → ℝ) : ℝ :=
  ∑ k ∈ univ.filter (fun k => E k < cut), g k * boltzmannFactor kB T (E k)

theorem cutRatio_strictMonoOn_temp {kB cut : ℝ} {g E : ι → ℝ} (hkB : 0 < kB)
    (hg : ∀ k, 0 < g k) (hkeep : ∃ k, E k < cut) (hdrop : ∃ k, cut ≤ E k) :
    StrictMonoOn (fun T => partitionFunction kB T g E / partitionFunctionCut kB T cut g E)
      (Set.Ioi 0) := by
  sorry

end Plan.FT05
