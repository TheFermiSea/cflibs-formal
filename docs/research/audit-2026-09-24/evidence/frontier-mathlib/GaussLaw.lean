import Mathlib
import CflibsFormal.Alt.OLSVariance

open MeasureTheory ProbabilityTheory
open CflibsFormal CflibsFormal.Alt

#check @ProbabilityTheory.iIndepFun.hasGaussianLaw_fun_sum
#check @ProbabilityTheory.HasGaussianLaw.map_eq_gaussianReal
#check @ProbabilityTheory.IsGaussian.hasGaussianLaw
#check @ProbabilityTheory.HasGaussianLaw.map_fun
#check @ProbabilityTheory.iIndepFun.comp
#check @ProbabilityTheory.memLp_id_gaussianReal

variable {ι Ω : Type*} [Fintype ι] {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- Statement sketch: exact Gaussian law of the OLS Boltzmann-plot slope. -/
theorem betaHat_law_gaussian [Nonempty ι] [IsProbabilityMeasure P] (E : ι → ℝ) (α β : ℝ)
    (v : NNReal) (ε : ι → Ω → ℝ)
    (hvar : 0 < ∑ k, (E k - mean E) ^ 2)
    (hind : iIndepFun ε P) (hlaw : ∀ k, P.map (ε k) = gaussianReal 0 v) :
    P.map (betaHat E α β ε) =
      gaussianReal β (v * ⟨1 / ∑ k, (E k - mean E) ^ 2, by positivity⟩) := by
  sorry

end
