import Mathlib
import CflibsFormal.SahaStability
import CflibsFormal.SahaEquilibrium

open CflibsFormal

namespace Plan.F02M6


variable {ι : Type*} [Fintype ι] {κ : Type*} [Fintype κ]

theorem sahaEquilibriumNe_strictMonoOn_temp [Nonempty ι] [Nonempty κ]
    {kB me h chi Ntot : ℝ} {gZ EZ : ι → ℝ} {gZ1 EZ1 : κ → ℝ}
    (hkB : 0 < kB) (hme : 0 < me) (hh : 0 < h) (_hchi : 0 ≤ chi)
    (hgZ : ∀ k, 0 < gZ k) (_hEZ : ∀ k, 0 ≤ EZ k)
    (hgZ1 : ∀ k, 0 < gZ1 k) (hEZ1 : ∀ k, 0 ≤ EZ1 k)
    (hEχ : ∀ k, EZ k ≤ chi) (hN : 0 < Ntot) :
    StrictMonoOn (fun T => sahaEquilibriumNe (sahaFactor kB T me h chi gZ EZ gZ1 EZ1) Ntot)
      (Set.Ioi 0) := by
  sorry

end Plan.F02M6
