import Mathlib
import CflibsFormal.LineBroadening

namespace AuditQuad
open CflibsFormal MeasureTheory ProbabilityTheory
open scoped NNReal

noncomputable def gaussFWHM (v : ℝ≥0) : ℝ := 2 * Real.sqrt (2 * Real.log 2 * v)

theorem gaussFWHM_conv (v₁ v₂ : ℝ≥0) :
    gaussFWHM (v₁ + v₂) = gaussQuadrature (gaussFWHM v₁) (gaussFWHM v₂) := by
  have hl : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have h1 : (0:ℝ) ≤ 2 * Real.log 2 * (v₁ : ℝ) := by positivity
  have h2 : (0:ℝ) ≤ 2 * Real.log 2 * (v₂ : ℝ) := by positivity
  unfold gaussFWHM gaussQuadrature
  rw [mul_pow, mul_pow, Real.sq_sqrt h1, Real.sq_sqrt h2, NNReal.coe_add]
  rw [show (2:ℝ) ^ 2 * (2 * Real.log 2 * v₁) + 2 ^ 2 * (2 * Real.log 2 * v₂)
      = 2 ^ 2 * (2 * Real.log 2 * (v₁ + v₂)) by ring]
  have h12 : (0:ℝ) ≤ 2 * Real.log 2 * (↑v₁ + ↑v₂) := by positivity
  rw [Real.sqrt_mul' ((2:ℝ) ^ 2) h12, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]

theorem gaussianPDFReal_halfMax (μ₀ : ℝ) (v : ℝ≥0) (hv : v ≠ 0) :
    gaussianPDFReal μ₀ v (μ₀ + gaussFWHM v / 2) = gaussianPDFReal μ₀ v μ₀ / 2 := by
  have hvpos : (0:ℝ) < v := by positivity
  have hl : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hsq : Real.sqrt (2 * Real.log 2 * v) ^ 2 = 2 * Real.log 2 * v :=
    Real.sq_sqrt (by positivity)
  simp only [gaussianPDFReal, gaussFWHM]
  have : -(μ₀ + 2 * Real.sqrt (2 * Real.log 2 * ↑v) / 2 - μ₀) ^ 2 / (2 * (v:ℝ))
      = -Real.log 2 := by
    rw [show μ₀ + 2 * Real.sqrt (2 * Real.log 2 * ↑v) / 2 - μ₀
        = Real.sqrt (2 * Real.log 2 * ↑v) by ring, hsq]
    field_simp
  rw [this, Real.exp_neg, Real.exp_log (by norm_num)]
  simp
  ring

end AuditQuad
#print axioms AuditQuad.gaussFWHM_conv
#print axioms AuditQuad.gaussianPDFReal_halfMax
