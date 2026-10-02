import Mathlib

open Finset

namespace Plan.FT10

variable {ι : Type*} [Fintype ι]

/-- Weighted mean `Ē_w = ∑ w E / ∑ w`. -/
noncomputable def wMean (w E : ι → ℝ) : ℝ := (∑ k, w k * E k) / ∑ k, w k

/-- Weighted centred sum of squares `∑ w (E − Ē_w)²`. -/
noncomputable def wSS (w E : ι → ℝ) : ℝ := ∑ k, w k * (E k - wMean w E) ^ 2

/-- Weighted-least-squares slope weight `w_k (E_k − Ē_w) / wSS`. -/
noncomputable def wlsWeight (w E : ι → ℝ) (k : ι) : ℝ := w k * (E k - wMean w E) / wSS w E

theorem wls_min_noiseGain {w E a : ι → ℝ} (hw : ∀ k, 0 < w k) (hSS : 0 < wSS w E)
    (ha0 : ∑ k, a k = 0) (ha1 : ∑ k, a k * E k = 1) :
    ∑ k, wlsWeight w E k ^ 2 / w k = 1 / wSS w E ∧ 1 / wSS w E ≤ ∑ k, a k ^ 2 / w k := by
  sorry

end Plan.FT10
