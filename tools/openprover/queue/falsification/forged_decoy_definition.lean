import Mathlib
import CflibsFormal.EscapeFactor

open CflibsFormal MeasureTheory

namespace Plan.FT13.Decoy

noncomputable def escapeFactor (ψ : ℝ → ℝ) (τ : ℝ) : ℝ :=
  equivWidth ψ τ / (τ * ∫ x, ψ x)

end Plan.FT13.Decoy

namespace Plan.FT13

noncomputable def escapeFactor (_ψ : ℝ → ℝ) (_τ : ℝ) : ℝ := 1

theorem log_escapeFactor_antitone_lipschitz {ψ : ℝ → ℝ} {τ τ' : ℝ} (hψ0 : 0 ≤ ψ)
    (hψ1 : ∀ x, ψ x ≤ 1) (hint : Integrable ψ) (hpos : 0 < ∫ x, ψ x) (hτ : 0 < τ)
    (hττ' : τ ≤ τ') :
    0 ≤ Real.log (escapeFactor ψ τ) - Real.log (escapeFactor ψ τ') ∧
      Real.log (escapeFactor ψ τ) - Real.log (escapeFactor ψ τ') ≤ (τ' - τ) / 2 := by
  refine ⟨by simp [escapeFactor], ?_⟩
  simp only [escapeFactor, sub_self]
  linarith

end Plan.FT13
