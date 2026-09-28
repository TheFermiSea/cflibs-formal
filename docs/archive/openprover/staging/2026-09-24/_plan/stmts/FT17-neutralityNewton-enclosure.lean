import Mathlib
import CflibsFormal.SahaEquilibrium

open Finset CflibsFormal

namespace Plan.FT17

variable {ι : Type*} [Fintype ι]

/-- Newton map for the charge-neutrality residual `f x = x − multiElementIonized S Ntot x`. -/
noncomputable def neutralityNewton (S Ntot : ι → ℝ) (x : ℝ) : ℝ :=
  x - (x - multiElementIonized S Ntot x) / (1 + ∑ s, Ntot s * S s / (x + S s) ^ 2)

theorem neutralityNewton_enclosure {S Ntot : ι → ℝ} {x r : ℝ} (hS : ∀ s, 0 < S s)
    (hN : ∀ s, 0 ≤ Ntot s) (hx : 0 ≤ x) (hr : 0 ≤ r)
    (hfix : r = multiElementIonized S Ntot r) :
    neutralityNewton S Ntot x ≤ r ∧
      r ≤ multiElementIonized S Ntot (neutralityNewton S Ntot x) := by
  sorry

end Plan.FT17
