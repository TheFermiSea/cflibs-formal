import Mathlib
import CflibsFormal.SahaEquilibrium
open Finset
namespace RedTeam
/-- `Π_{j<z} S j`: the neutral-to-stage-`z` Saha product. -/
noncomputable def sahaStageProduct (S : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1
  | z + 1 => sahaStageProduct S z * S z
/-- Fraction of a species in stage `z` at electron density `ne`. -/
noncomputable def stageFraction (Z : ℕ) (S : ℕ → ℝ) (ne : ℝ) (z : ℕ) : ℝ :=
  (sahaStageProduct S z / ne ^ z) / ∑ k ∈ range (Z + 1), sahaStageProduct S k / ne ^ k
/-- Free electrons liberated by one species of total density `Ntot`. -/
noncomputable def speciesCharge (Z : ℕ) (S : ℕ → ℝ) (Ntot ne : ℝ) : ℝ :=
  Ntot * ∑ z ∈ range (Z + 1), (z : ℝ) * stageFraction Z S ne z
/-- **Cascade antitonicity (S3).** For a species with `Z ≥ 1` ionization stages, positive total
density `Ntot`, and positive Saha factors `S z` for every stage `z < Z`, the liberated charge
`speciesCharge Z S Ntot ne` is *strictly decreasing* in the electron density `ne` on `(0, ∞)`:
raising `n_e` drives every stage toward recombination (monotone likelihood ratio in `z`). -/
theorem speciesCharge_strictAntiOn (Z : ℕ) (S : ℕ → ℝ) (Ntot : ℝ) (hZ : 1 ≤ Z) (hN : 0 < Ntot)
    (hS : ∀ z < Z, 0 < S z) :
    StrictAntiOn (speciesCharge Z S Ntot) (Set.Ioi (0 : ℝ)) := by
  sorry
end RedTeam
