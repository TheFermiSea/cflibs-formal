import CflibsFormal

open Finset Real CflibsFormal

namespace AdvV2b

/-- FT-19: with Saha-coupled ion column `NII z = NI z * S(T z) / ne`, the ion zone weight is the
neutral zone weight times `2·θ^{3/2}·exp(-χ/kT)/ne` — the partition functions cancel, so the
reweighting factor is NOT `S/ne`. -/
theorem ion_zoneWeight_eq {ζ ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty ι] [Nonempty κ]
    {kB Fcal me h chi ne : ℝ} {T NI NII : ζ → ℝ} {gZ EZ : ι → ℝ} {gZ1 EZ1 : κ → ℝ}
    (hgZ : ∀ k, 0 < gZ k) (hgZ1 : ∀ k, 0 < gZ1 k)
    (hNII : ∀ z, NII z = NI z * sahaFactor kB (T z) me h chi gZ EZ gZ1 EZ1 / ne) (z : ζ) :
    zoneWeight kB Fcal T NII gZ1 EZ1 z
      = zoneWeight kB Fcal T NI gZ EZ z
        * (2 * thermalBracket kB (T z) me h ^ (3 / 2 : ℝ) * Real.exp (-chi / (kB * T z)) / ne) := by
  have hU0 : partitionFunction kB (T z) gZ EZ ≠ 0 := (partitionFunction_pos hgZ).ne'
  have hU1 : partitionFunction kB (T z) gZ1 EZ1 ≠ 0 := (partitionFunction_pos hgZ1).ne'
  simp only [zoneWeight, hNII, sahaFactor]
  field_simp

/-- FT-14 (iv) sketch with no hypotheses is false: at `N = 0` the LHS is `0/0 = 0`. -/
theorem perLine_tauRatio_unguarded_false :
    ¬ (∀ (kB T N s1 s2 ell : ℝ) (g E : Fin 2 → ℝ),
        opticalDepth kB T N s1 ell g E 0 / opticalDepth kB T N s2 ell g E 1
          = s1 * g 0 * boltzmannFactor kB T (E 0) / (s2 * g 1 * boltzmannFactor kB T (E 1))) := by
  intro h
  have := h 1 1 0 1 1 1 ![1, 1] ![0, 0]
  simp [opticalDepth, population, boltzmannFactor] at this

end AdvV2b
#print axioms AdvV2b.ion_zoneWeight_eq
#print axioms AdvV2b.perLine_tauRatio_unguarded_false
