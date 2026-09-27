import Mathlib
import CflibsFormal.LineBroadening
open MeasureTheory ProbabilityTheory

theorem gaussianPDFReal_convolution (m₁ m₂ : ℝ) (v₁ v₂ : NNReal) (h₁ : v₁ ≠ 0) (h₂ : v₂ ≠ 0) :
    convolution (gaussianPDFReal m₁ v₁) (gaussianPDFReal m₂ v₂)
      (ContinuousLinearMap.lsmul ℝ ℝ) volume = gaussianPDFReal (m₁ + m₂) (v₁ + v₂) := by
  sorry

/-- Half-maximum of the mathlib Gaussian density at `m ± √(2 ln 2 · v)`. -/
theorem gaussianPDFReal_half_max (m : ℝ) (v : NNReal) :
    gaussianPDFReal m v (m + Real.sqrt (2 * Real.log 2 * v)) = gaussianPDFReal m v m / 2 := by
  sorry

example (w₁ w₂ : ℝ) : CflibsFormal.gaussQuadrature w₁ w₂ = Real.sqrt (w₁ ^ 2 + w₂ ^ 2) := rfl
