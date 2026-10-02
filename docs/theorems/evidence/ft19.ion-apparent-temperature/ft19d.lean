import CflibsFormal

/-!
Scratch (card-A evidence, NOT library code): the FT-19d weaker-anchor variant of
`CflibsFormal.mixed_ion_apparentBeta_le_neutral` recorded in staging FOLLOWUPS.md.
Anchor `EZ j ≤ EZ1 i' + chi` instead of `EZ j ≤ EZ1 i'`; `hchi : 0 ≤ chi` dropped.
Corollary: the anchor holds whenever the neutral upper level is bound (`EZ j ≤ chi`) and the
ion lower-line energy is nonnegative.
-/

open CflibsFormal

namespace ScratchFT19d

/-- Shifting both abscissae by `c` leaves a two-point slope unchanged. -/
lemma apparentBeta_shift (E₁ y₁ E₂ y₂ c : ℝ) :
    apparentBeta E₁ y₁ E₂ y₂ = apparentBeta (E₁ + c) y₁ (E₂ + c) y₂ := by
  unfold apparentBeta; congr 1; ring

/-- The `e^{-chi b}` factor of the reweight is an abscissa shift of the log-mixture. -/
lemma logMixture_shift {ζ : Type*} [Fintype ζ] {kB me h chi ne : ℝ} {T : ζ → ℝ} (w : ζ → ℝ)
    (hkB : 0 < kB) (hT : ∀ z, 0 < T z) (E : ℝ) :
    logMixture (fun z => w z * ionReweight kB me h chi ne (T z)) (zoneBeta kB T) E
      = logMixture (fun z => w z * ionReweight kB me h 0 ne (T z)) (zoneBeta kB T) (E + chi) := by
  unfold logMixture mixture
  congr 1
  apply Finset.sum_congr rfl
  intro z _
  have hkT : kB * T z ≠ 0 := (mul_pos hkB (hT z)).ne'
  simp only [ionReweight, zoneBeta, neg_zero, zero_div, Real.exp_zero, mul_one]
  have : Real.exp (-chi / (kB * T z)) * Real.exp (-(E * (1 / (kB * T z))))
      = Real.exp (-((E + chi) * (1 / (kB * T z)))) := by
    rw [← Real.exp_add]; congr 1; field_simp; ring
  calc w z * (2 * thermalBracket kB (T z) me h ^ (3 / 2 : ℝ) * Real.exp (-chi / (kB * T z)) / ne)
        * Real.exp (-(E * (1 / (kB * T z))))
      = w z * (2 * thermalBracket kB (T z) me h ^ (3 / 2 : ℝ) / ne)
        * (Real.exp (-chi / (kB * T z)) * Real.exp (-(E * (1 / (kB * T z))))) := by ring
    _ = _ := by rw [this]

theorem mixed_ion_apparentBeta_le_neutral_shift {ζ ι κ : Type*} [Fintype ζ] [Fintype ι]
    [Fintype κ] [Nonempty ζ] [Nonempty ι] [Nonempty κ]
    {kB Fcal me h chi ne : ℝ} {T NI NII : ζ → ℝ}
    {gZ EZ AI : ι → ℝ} {gZ1 EZ1 AII : κ → ℝ}
    (hkB : 0 < kB) (hme : 0 < me) (hh : 0 < h) (hne : 0 < ne)
    (hFcal : 0 < Fcal) (hT : ∀ z, 0 < T z) (hNI : ∀ z, 0 < NI z)
    (hgZ : ∀ k, 0 < gZ k) (hgZ1 : ∀ k, 0 < gZ1 k)
    (hAI : ∀ k, 0 < AI k) (hAII : ∀ k, 0 < AII k)
    (hNII : ∀ z, NII z = NI z * sahaFactor kB (T z) me h chi gZ EZ gZ1 EZ1 / ne)
    (i j : ι) (hij : EZ i < EZ j) (i' j' : κ) (hij' : EZ1 i' < EZ1 j')
    (hanchor : EZ j ≤ EZ1 i' + chi) :
    apparentBeta (EZ1 i')
        (Real.log (mixedLineIntensity kB T NII Fcal gZ1 EZ1 AII i' / (gZ1 i' * AII i')))
        (EZ1 j')
        (Real.log (mixedLineIntensity kB T NII Fcal gZ1 EZ1 AII j' / (gZ1 j' * AII j')))
      ≤ apparentBeta (EZ i)
        (Real.log (mixedLineIntensity kB T NI Fcal gZ EZ AI i / (gZ i * AI i)))
        (EZ j)
        (Real.log (mixedLineIntensity kB T NI Fcal gZ EZ AI j / (gZ j * AI j))) := by
  set w : ζ → ℝ := zoneWeight kB Fcal T NI gZ EZ with hw_def
  set b : ζ → ℝ := zoneBeta kB T with hb_def
  set ρ0 : ζ → ℝ := fun z => ionReweight kB me h 0 ne (T z) with hρ0_def
  have hw : ∀ z, 0 < w z := fun z => zoneWeight_pos (T := T) (kB := kB) (E := EZ) hgZ hNI hFcal z
  have hρ0 : ∀ z, 0 < ρ0 z := by
    intro z
    have := thermalBracket_pos hkB (hT z) hme hh
    simp only [hρ0_def, ionReweight]; positivity
  have hanti : ∀ x y, b x < b y → ρ0 y ≤ ρ0 x := by
    intro x y hxy
    simp only [hb_def, zoneBeta] at hxy
    have hlt : kB * T y < kB * T x :=
      (one_div_lt_one_div (mul_pos hkB (hT x)) (mul_pos hkB (hT y))).mp hxy
    have hltT : T y < T x := lt_of_mul_lt_mul_left hlt hkB.le
    exact ((ionReweight_strictMonoOn hkB hme hh le_rfl hne) (hT y) (hT x) hltT).le
  have hwρ : ∀ z, 0 < w z * ρ0 z := fun z => mul_pos (hw z) (hρ0 z)
  -- ion ordinates as a shifted log-mixture with the chi-free reweight
  have hion : ∀ k : κ,
      Real.log (mixedLineIntensity kB T NII Fcal gZ1 EZ1 AII k / (gZ1 k * AII k))
        = logMixture (fun z => w z * ρ0 z) b (EZ1 k + chi) := by
    intro k
    rw [mixed_boltzmann_ordinate (N := NII) (Fcal := Fcal) hkB hT hgZ1 hAII k,
      ion_zoneWeight_eq (Fcal := Fcal) hne hgZ hgZ1 hNII]
    exact logMixture_shift (chi := chi) w hkB hT (EZ1 k)
  rw [hion i', hion j',
    mixed_boltzmann_ordinate (N := NI) (Fcal := Fcal) hkB hT hgZ hAI i,
    mixed_boltzmann_ordinate (N := NI) (Fcal := Fcal) hkB hT hgZ hAI j,
    apparentBeta_shift (EZ1 i') _ (EZ1 j') _ chi]
  have hf : EZ1 i' + chi < EZ1 j' + chi := by linarith
  have h3 : tiltMean w b (EZ1 i' + chi) ≤ tiltMean w b (EZ j) := by
    rcases hanchor.lt_or_eq with h | h
    · exact (tiltMean_le_pairSlope hw h).trans (pairSlope_le_tiltMean hw h)
    · exact h ▸ le_rfl
  calc _ ≤ tiltMean (fun z => w z * ρ0 z) b (EZ1 i' + chi) := pairSlope_le_tiltMean hwρ hf
    _ ≤ tiltMean w b (EZ1 i' + chi) := tiltMean_reweight_le hw hρ0 hanti _
    _ ≤ tiltMean w b (EZ j) := h3
    _ ≤ _ := tiltMean_le_pairSlope hw hij

/-- Bound-level corollary: a bound neutral upper level (`EZ j ≤ chi`) and a nonnegative ion
lower-line energy discharge the anchor. -/
theorem mixed_ion_apparentBeta_le_neutral_bound {ζ ι κ : Type*} [Fintype ζ] [Fintype ι]
    [Fintype κ] [Nonempty ζ] [Nonempty ι] [Nonempty κ]
    {kB Fcal me h chi ne : ℝ} {T NI NII : ζ → ℝ}
    {gZ EZ AI : ι → ℝ} {gZ1 EZ1 AII : κ → ℝ}
    (hkB : 0 < kB) (hme : 0 < me) (hh : 0 < h) (hne : 0 < ne)
    (hFcal : 0 < Fcal) (hT : ∀ z, 0 < T z) (hNI : ∀ z, 0 < NI z)
    (hgZ : ∀ k, 0 < gZ k) (hgZ1 : ∀ k, 0 < gZ1 k)
    (hAI : ∀ k, 0 < AI k) (hAII : ∀ k, 0 < AII k)
    (hNII : ∀ z, NII z = NI z * sahaFactor kB (T z) me h chi gZ EZ gZ1 EZ1 / ne)
    (i j : ι) (hij : EZ i < EZ j) (i' j' : κ) (hij' : EZ1 i' < EZ1 j')
    (hbound : EZ j ≤ chi) (hion0 : 0 ≤ EZ1 i') :
    apparentBeta (EZ1 i')
        (Real.log (mixedLineIntensity kB T NII Fcal gZ1 EZ1 AII i' / (gZ1 i' * AII i')))
        (EZ1 j')
        (Real.log (mixedLineIntensity kB T NII Fcal gZ1 EZ1 AII j' / (gZ1 j' * AII j')))
      ≤ apparentBeta (EZ i)
        (Real.log (mixedLineIntensity kB T NI Fcal gZ EZ AI i / (gZ i * AI i)))
        (EZ j)
        (Real.log (mixedLineIntensity kB T NI Fcal gZ EZ AI j / (gZ j * AI j))) :=
  mixed_ion_apparentBeta_le_neutral_shift hkB hme hh hne hFcal hT hNI hgZ hgZ1 hAI hAII hNII
    i j hij i' j' hij' (by linarith)

end ScratchFT19d

#print axioms ScratchFT19d.mixed_ion_apparentBeta_le_neutral_shift
#print axioms ScratchFT19d.mixed_ion_apparentBeta_le_neutral_bound
