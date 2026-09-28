import Mathlib
import CflibsFormal.Alt.StochasticBudget

open Finset CflibsFormal MeasureTheory ProbabilityTheory

namespace Plan.FT12


variable {ι : Type*} [Fintype ι] {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ]

theorem olsSlope_subGaussian_tail_hetero [Nonempty ι] (E : ι → ℝ) (α β : ℝ) (ε : ι → Ω → ℝ)
    {c : ι → NNReal} {δ : ℝ} (hvar : 0 < ∑ k, (E k - mean E) ^ 2) (hδ : 0 ≤ δ)
    (hindep : iIndepFun ε μ) (hsubG : ∀ k, HasSubgaussianMGF (ε k) (c k) μ) :
    μ.real {ω | δ ≤ |Alt.betaHat E α β ε ω - β|}
      ≤ 2 * Real.exp (-(δ ^ 2) / (2 * ∑ k, olsWeight E k ^ 2 * (c k : ℝ))) := by
  sorry

end Plan.FT12
