import Mathlib
import CflibsFormal.OLS
import CflibsFormal.SelfAbsorption

open Finset CflibsFormal

namespace Plan.FT18


variable {ι : Type*} [Fintype ι]

theorem olsSlope_selfAbsorbed_ge [Nonempty ι] {E y τ : ι → ℝ} (hτ : ∀ k, 0 < τ k)
    (hanti : ∀ i j, E i < E j → τ j ≤ τ i) :
    olsSlope E y ≤ olsSlope E (fun k => y k + Real.log (selfAbsorptionFactor (τ k))) := by
  sorry

end Plan.FT18
