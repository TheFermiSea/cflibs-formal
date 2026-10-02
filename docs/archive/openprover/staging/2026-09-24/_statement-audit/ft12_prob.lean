import Mathlib
import CflibsFormal.Alt.StochasticBudget

open Finset CflibsFormal MeasureTheory ProbabilityTheory

variable {ι : Type*} [Fintype ι] {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

-- The statement's `hindep` alone forces a probability measure, so omitting
-- `[IsProbabilityMeasure μ]` does not generalise the statement.
example (ε : ι → Ω → ℝ) (hindep : iIndepFun ε μ) : IsProbabilityMeasure μ :=
  hindep.isProbabilityMeasure

-- RHS is a non-trivial bound (< 1) at E = (0,1,2), per-line proxies (1,2,3), δ = 3.
example : 2 * Real.exp (-((3:ℝ) ^ 2) /
    (2 * ∑ k, olsWeight (![0, 1, 2] : Fin 3 → ℝ) k ^ 2 * ((![1, 2, 3] : Fin 3 → NNReal) k : ℝ)))
      < 1 := by
  have hw : ∑ k, olsWeight (![0, 1, 2] : Fin 3 → ℝ) k ^ 2 * ((![1, 2, 3] : Fin 3 → NNReal) k : ℝ)
      = 1 := by
    simp [olsWeight, mean, Fin.sum_univ_three]; norm_num
  rw [hw, show -((3:ℝ) ^ 2) / (2 * 1) = -(9/2) by norm_num, Real.exp_neg]
  have h2 : Real.exp (9/2) > 2 := by
    have := Real.add_one_le_exp (9/2 : ℝ); linarith
  have : (Real.exp (9/2))⁻¹ < 1/2 := by
    rw [inv_lt_comm₀ (Real.exp_pos _) (by norm_num)]; linarith
  linarith

-- Satisfiability of hsubG with a positive per-line proxy (zero noise on a probability space).
example (c : NNReal) : HasSubgaussianMGF (fun _ : Unit => (0:ℝ)) c (Measure.dirac ()) := by
  refine ⟨fun t => by simp, fun t => ?_⟩
  simp [mgf]
  positivity
