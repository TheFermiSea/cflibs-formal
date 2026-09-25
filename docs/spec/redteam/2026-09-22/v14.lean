import Mathlib
import CflibsFormal.LadenburgReiche
open MeasureTheory
namespace RedTeam
/-- The Lorentzian of half-width `γ` centred at `lam₀`. -/
noncomputable def lorentzianProfile (γ lam₀ x : ℝ) : ℝ := CflibsFormal.lorentzianG (γ ^ 2) (x - lam₀)
/-- **Shifted Lorentzian normalization (L2).** The Lorentzian line profile of half-width `γ > 0`
centred at `lam₀`, `L(x) = (γ/π) / ((x − lam₀)² + γ²)`, is a unit-area profile over the whole real
line: `∫ x, lorentzianProfile γ lam₀ x = 1`. -/
theorem lorentzianProfile_integral {γ lam₀ : ℝ} (hγ : 0 < γ) :
    ∫ x, lorentzianProfile γ lam₀ x = 1 := by
  sorry
end RedTeam
