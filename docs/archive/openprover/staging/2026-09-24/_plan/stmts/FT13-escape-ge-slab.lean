import Mathlib
import CflibsFormal.SelfAbsorption
import CflibsFormal.EquivalentWidth

open CflibsFormal MeasureTheory

namespace Plan.FT13


theorem escape_ge_slab {ψ : ℝ → ℝ} {τ0 : ℝ} (hψ0 : 0 ≤ ψ) (hψ1 : ∀ x, ψ x ≤ 1)
    (hint : Integrable ψ) (hτ : 0 < τ0) :
    selfAbsorptionFactor τ0 * (τ0 * ∫ x, ψ x) ≤ equivWidth ψ τ0 := by
  sorry

end Plan.FT13
