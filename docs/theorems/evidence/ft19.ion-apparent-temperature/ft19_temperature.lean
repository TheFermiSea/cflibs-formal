import CflibsFormal
open CflibsFormal
namespace ScratchFT19T
/-- Temperature form of the landed FT-19 result: both apparent temperatures are finite and
positive and the ion one is at least the neutral one. Scratch only (card-A evidence). -/
theorem ion_apparentT_ge_neutral {ζ ι κ : Type*} [Fintype ζ] [Fintype ι] [Fintype κ]
    [Nonempty ζ] [Nonempty ι] [Nonempty κ]
    {kB Fcal me h chi ne : ℝ} {T NI NII : ζ → ℝ}
    {gZ EZ AI : ι → ℝ} {gZ1 EZ1 AII : κ → ℝ}
    (hkB : 0 < kB) (hme : 0 < me) (hh : 0 < h) (hchi : 0 ≤ chi) (hne : 0 < ne)
    (hFcal : 0 < Fcal) (hT : ∀ z, 0 < T z) (hNI : ∀ z, 0 < NI z)
    (hgZ : ∀ k, 0 < gZ k) (hgZ1 : ∀ k, 0 < gZ1 k)
    (hAI : ∀ k, 0 < AI k) (hAII : ∀ k, 0 < AII k)
    (hNII : ∀ z, NII z = NI z * sahaFactor kB (T z) me h chi gZ EZ gZ1 EZ1 / ne)
    (i j : ι) (hij : EZ i < EZ j) (i' j' : κ) (hij' : EZ1 i' < EZ1 j')
    (hanchor : EZ j ≤ EZ1 i') :
    let βI := apparentBeta (EZ i)
        (Real.log (mixedLineIntensity kB T NI Fcal gZ EZ AI i / (gZ i * AI i))) (EZ j)
        (Real.log (mixedLineIntensity kB T NI Fcal gZ EZ AI j / (gZ j * AI j)))
    let βII := apparentBeta (EZ1 i')
        (Real.log (mixedLineIntensity kB T NII Fcal gZ1 EZ1 AII i' / (gZ1 i' * AII i')))
        (EZ1 j')
        (Real.log (mixedLineIntensity kB T NII Fcal gZ1 EZ1 AII j' / (gZ1 j' * AII j')))
    0 < βII ∧ 0 < βI ∧ 1 / (kB * βI) ≤ 1 / (kB * βII) := by
  intro βI βII
  have hmain : βII ≤ βI := mixed_ion_apparentBeta_le_neutral hkB hme hh hchi hne hFcal hT hNI
    hgZ hgZ1 hAI hAII hNII i j hij i' j' hij' hanchor
  have hNIIpos : ∀ z, 0 < NII z := by
    intro z; rw [hNII z]
    exact div_pos (mul_pos (hNI z) (sahaFactor_pos hkB (hT z) hme hh hgZ hgZ1)) hne
  have hb0 : ∀ z, 0 < zoneBeta kB T z := fun z => by
    simp only [zoneBeta]; exact one_div_pos.mpr (mul_pos hkB (hT z))
  have hII : 0 < βII := by
    simp only [βII]
    rw [mixed_boltzmann_ordinate (N := NII) (Fcal := Fcal) hkB hT hgZ1 hAII i',
      mixed_boltzmann_ordinate (N := NII) (Fcal := Fcal) hkB hT hgZ1 hAII j']
    exact pairSlope_pos (fun z => zoneWeight_pos (T := T) (kB := kB) (E := EZ1) hgZ1 hNIIpos
      hFcal z) hb0 hij'
  exact ⟨hII, lt_of_lt_of_le hII hmain, apparentTemperature_ge hkB hII hmain⟩
end ScratchFT19T
#print axioms ScratchFT19T.ion_apparentT_ge_neutral
