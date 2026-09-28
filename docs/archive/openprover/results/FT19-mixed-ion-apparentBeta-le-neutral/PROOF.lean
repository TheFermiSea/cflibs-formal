-- Summary: Complete FT19 proof: ion-pair apparent beta ≤ neutral-pair apparent beta (helpers + main theorem).
import Mathlib
import CflibsFormal.InhomogeneityBias
import CflibsFormal.SahaStability

open CflibsFormal

namespace Plan.FT19

-- Ion reweight factor rho(T) = 2 θ(T)^{3/2} e^{-χ/(kB T)} / ne.
noncomputable def ionReweight (kB me h chi ne T : ℝ) : ℝ :=
  2 * thermalBracket kB T me h ^ (3/2 : ℝ) * Real.exp (-chi / (kB * T)) / ne

-- rho is strictly increasing in T on (0, ∞).
theorem ionReweight_strictMonoOn {kB me h chi ne : ℝ} (hkB : 0 < kB) (hme : 0 < me)
    (hh : 0 < h) (hchi : 0 ≤ chi) (hne : 0 < ne) :
    StrictMonoOn (ionReweight kB me h chi ne) (Set.Ioi 0) := by
  intro T1 hT1 T2 hT2 hlt
  simp only [Set.mem_Ioi] at hT1 hT2
  dsimp [ionReweight]
  have hθ1 : 0 < thermalBracket kB T1 me h := thermalBracket_pos hkB hT1 hme hh
  have hθ2 : 0 < thermalBracket kB T2 me h := thermalBracket_pos hkB hT2 hme hh
  have hθlt : thermalBracket kB T1 me h < thermalBracket kB T2 me h :=
    thermalBracket_strictMono hkB hme hh hlt
  have hX : (thermalBracket kB T1 me h) ^ (3/2 : ℝ) < (thermalBracket kB T2 me h) ^ (3/2 : ℝ) :=
    Real.rpow_lt_rpow hθ1.le hθlt (by norm_num)
  have hY : Real.exp (-chi / (kB * T1)) ≤ Real.exp (-chi / (kB * T2)) := by
    rw [Real.exp_le_exp]
    rw [neg_div, neg_div, neg_le_neg_iff]
    exact div_le_div_of_nonneg_left hchi (mul_pos hkB hT1)
      (mul_le_mul_of_nonneg_left hlt.le hkB.le)
  have h2X : 2 * (thermalBracket kB T1 me h) ^ (3/2 : ℝ) <
             2 * (thermalBracket kB T2 me h) ^ (3/2 : ℝ) := by
    linarith [hX]
  have hYpos : 0 < Real.exp (-chi / (kB * T2)) := Real.exp_pos _
  have hprod : 2 * (thermalBracket kB T1 me h) ^ (3/2 : ℝ) * Real.exp (-chi / (kB * T1)) <
               2 * (thermalBracket kB T2 me h) ^ (3/2 : ℝ) * Real.exp (-chi / (kB * T2)) :=
    mul_lt_mul_of_lt_of_le_of_nonneg_of_pos h2X hY (by positivity) hYpos
  exact div_lt_div_of_pos_right hprod hne

-- Higher zoneBeta = lower temperature = smaller reweight.
theorem ionReweight_anti {ζ : Type*} {kB me h chi ne : ℝ} {T : ζ → ℝ}
    (hkB : 0 < kB) (hme : 0 < me) (hh : 0 < h) (hchi : 0 ≤ chi) (hne : 0 < ne)
    (hT : ∀ z, 0 < T z) :
    ∀ x y, zoneBeta kB T x < zoneBeta kB T y →
      ionReweight kB me h chi ne (T y) ≤ ionReweight kB me h chi ne (T x) := by
  intro x y hxy
  simp only [zoneBeta] at hxy
  have hlt : kB * T y < kB * T x :=
    (one_div_lt_one_div (mul_pos hkB (hT x)) (mul_pos hkB (hT y))).mp hxy
  have hltT : T y < T x := lt_of_mul_lt_mul_left hlt hkB.le
  exact ((ionReweight_strictMonoOn hkB hme hh hchi hne) (hT y) (hT x) hltT).le

-- Ion zone weight = neutral zone weight * rho (ion partition function cancels).
theorem ion_zoneWeight_eq {ζ ι κ : Type*} [Fintype ζ] [Fintype ι] [Fintype κ] [Nonempty ι] [Nonempty κ]
    {kB Fcal me h chi ne : ℝ} {T NI NII : ζ → ℝ} {gZ EZ : ι → ℝ} {gZ1 EZ1 : κ → ℝ}
    (hne : 0 < ne) (hgZ : ∀ k, 0 < gZ k) (hgZ1 : ∀ k, 0 < gZ1 k)
    (hNII : ∀ z, NII z = NI z * sahaFactor kB (T z) me h chi gZ EZ gZ1 EZ1 / ne) :
    zoneWeight kB Fcal T NII gZ1 EZ1
      = fun z => zoneWeight kB Fcal T NI gZ EZ z * ionReweight kB me h chi ne (T z) := by
  funext z
  have hU1 : 0 < partitionFunction kB (T z) gZ1 EZ1 := partitionFunction_pos hgZ1
  have hU2 : 0 < partitionFunction kB (T z) gZ EZ := partitionFunction_pos hgZ
  simp only [zoneWeight, hNII, sahaFactor, ionReweight]
  field_simp [hU1.ne', hU2.ne', hne.ne']

-- Each Chebyshev term is ≤ 0 under antivariance.
theorem cheb_double_sum_nonpos {ζ : Type*} [Fintype ζ] {u b ρ : ζ → ℝ}
    (hu : ∀ z, 0 < u z) (hanti : ∀ i j, b i < b j → ρ j ≤ ρ i) :
    ∑ i, ∑ j, u i * u j * ((ρ i - ρ j) * (b i - b j)) ≤ 0 := by
  apply Finset.sum_nonpos; intro i _
  apply Finset.sum_nonpos; intro j _
  have huij : 0 < u i * u j := mul_pos (hu i) (hu j)
  have key : (ρ i - ρ j) * (b i - b j) ≤ 0 := by
    rcases lt_trichotomy (b i) (b j) with h | h | h
    · have := hanti i j h
      exact mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
    · simp [h]
    · have := hanti j i h
      exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  exact mul_nonpos_of_nonneg_of_nonpos huij.le key

-- Chebyshev double-sum identity.
theorem cheb_identity {ζ : Type*} [Fintype ζ] (u b ρ : ζ → ℝ) :
    ∑ i, ∑ j, u i * u j * ((ρ i - ρ j) * (b i - b j)) =
      2 * ((∑ z, u z * ρ z * b z) * (∑ z, u z) - (∑ z, u z * b z) * (∑ z, u z * ρ z)) := by
  calc
    _ = ∑ i, ∑ j, ((u i * ρ i * b i) * u j + (-(u i * ρ i)) * (u j * b j) + (-(u i * b i)) * (u j * ρ j) + u i * (u j * ρ j * b j)) := by
        apply Finset.sum_congr rfl; intro i _
        apply Finset.sum_congr rfl; intro j _
        ring
    _ = (∑ i, ∑ j, (u i * ρ i * b i) * u j) + (∑ i, ∑ j, -(u i * ρ i) * (u j * b j)) +
        (∑ i, ∑ j, -(u i * b i) * (u j * ρ j)) + (∑ i, ∑ j, u i * (u j * ρ j * b j)) := by
        simp only [Finset.sum_add_distrib]
    _ = (∑ i, u i * ρ i * b i) * (∑ j, u j) + (∑ i, -(u i * ρ i)) * (∑ j, u j * b j) +
        (∑ i, -(u i * b i)) * (∑ j, u j * ρ j) + (∑ i, u i) * (∑ j, u j * ρ j * b j) := by
        rw [← Finset.sum_mul_sum, ← Finset.sum_mul_sum, ← Finset.sum_mul_sum, ← Finset.sum_mul_sum]
    _ = (∑ i, u i * ρ i * b i) * (∑ j, u j) + (-(∑ i, u i * ρ i)) * (∑ j, u j * b j) +
        (-(∑ i, u i * b i)) * (∑ j, u j * ρ j) + (∑ i, u i) * (∑ j, u j * ρ j * b j) := by
        simp only [Finset.sum_neg_distrib]
    _ = 2 * ((∑ z, u z * ρ z * b z) * (∑ z, u z) - (∑ z, u z * b z) * (∑ z, u z * ρ z)) := by
        ring

-- Weighted Chebyshev inequality.
theorem weighted_cheb {ζ : Type*} [Fintype ζ] {u b ρ : ζ → ℝ}
    (hu : ∀ z, 0 < u z) (hanti : ∀ i j, b i < b j → ρ j ≤ ρ i) :
    (∑ z, u z * ρ z * b z) * (∑ z, u z) ≤ (∑ z, u z * b z) * (∑ z, u z * ρ z) := by
  have h1 := cheb_double_sum_nonpos hu hanti
  rw [cheb_identity] at h1
  linarith

-- Reweighting by an antivariant rho lowers the tilted mean.
theorem tiltMean_reweight_le {ζ : Type*} [Fintype ζ] [Nonempty ζ] {w b ρ : ζ → ℝ}
    (hw : ∀ z, 0 < w z) (hρ : ∀ z, 0 < ρ z) (hanti : ∀ i j, b i < b j → ρ j ≤ ρ i) (a : ℝ) :
    tiltMean (fun z => w z * ρ z) b a ≤ tiltMean w b a := by
  let u : ζ → ℝ := fun z => w z * Real.exp (-(a * b z))
  let uρ : ζ → ℝ := fun z => w z * ρ z * Real.exp (-(a * b z))
  have hu : ∀ z, 0 < u z := fun z => mul_pos (hw z) (Real.exp_pos _)
  have hsumu : 0 < ∑ z, u z := Finset.sum_pos (fun z _ => hu z) Finset.univ_nonempty
  have hsumur : 0 < ∑ z, u z * ρ z :=
    Finset.sum_pos (fun z _ => mul_pos (hu z) (hρ z)) Finset.univ_nonempty
  have hsumur' : 0 < ∑ z, uρ z :=
    Finset.sum_pos (fun z _ => mul_pos (mul_pos (hw z) (hρ z)) (Real.exp_pos _)) Finset.univ_nonempty
  have hmean_w : tiltMean w b a = (∑ z, u z * b z) / ∑ z, u z := by
    simp only [tiltMean, tiltWeight, mixture]
    have h1 : ∑ z, (w z * Real.exp (-(a * b z)) / ∑ z, w z * Real.exp (-(a * b z))) * b z =
              ∑ z, (u z / ∑ z, u z) * b z := by
      apply Finset.sum_congr rfl; intro z _
      rfl
    rw [h1]
    have h2 : ∑ z, (u z / ∑ z, u z) * b z = ∑ z, (u z * b z) / ∑ z, u z := by
      apply Finset.sum_congr rfl; intro z _
      field_simp [hsumu.ne']
    rw [h2, ← Finset.sum_div]
  have hmean_wr : tiltMean (fun z => w z * ρ z) b a = (∑ z, u z * ρ z * b z) / ∑ z, u z * ρ z := by
    simp only [tiltMean, tiltWeight, mixture]
    have h1 : ∑ z, (w z * ρ z * Real.exp (-(a * b z)) / ∑ z, w z * ρ z * Real.exp (-(a * b z))) * b z =
              ∑ z, (uρ z / ∑ z, uρ z) * b z := by
      apply Finset.sum_congr rfl; intro z _
      rfl
    rw [h1]
    have h2 : ∑ z, (uρ z / ∑ z, uρ z) * b z = ∑ z, (uρ z * b z) / ∑ z, uρ z := by
      apply Finset.sum_congr rfl; intro z _
      field_simp [hsumur'.ne']
    have hn : ∑ z, uρ z * b z = ∑ z, u z * ρ z * b z := by
      apply Finset.sum_congr rfl; intro z _
      dsimp only [u, uρ]; ring
    have hd : ∑ z, uρ z = ∑ z, u z * ρ z := by
      apply Finset.sum_congr rfl; intro z _
      dsimp only [u, uρ]; ring
    rw [h2, ← Finset.sum_div, hn, hd]
  rw [hmean_wr, hmean_w, div_le_div_iff₀ hsumur hsumu]
  exact weighted_cheb hu hanti

-- Chain on log-mixtures: ion pair slope ≤ neutral pair slope.
theorem logMixture_chain {ζ : Type*} [Fintype ζ] [Nonempty ζ] {w b ρ : ζ → ℝ}
    (hw : ∀ z, 0 < w z) (hρ : ∀ z, 0 < ρ z) (hanti : ∀ i j, b i < b j → ρ j ≤ ρ i)
    {e1 e2 f1 f2 : ℝ} (h12 : e1 < e2) (hf : f1 < f2) (hanchor : e2 ≤ f1) :
    apparentBeta f1 (logMixture (fun z => w z * ρ z) b f1) f2 (logMixture (fun z => w z * ρ z) b f2)
      ≤ apparentBeta e1 (logMixture w b e1) e2 (logMixture w b e2) := by
  have hwρ : ∀ z, 0 < w z * ρ z := fun z => mul_pos (hw z) (hρ z)
  have h3 : tiltMean w b f1 ≤ tiltMean w b e2 := by
    rcases hanchor.lt_or_eq with h | h
    · exact (tiltMean_le_pairSlope hw h).trans (pairSlope_le_tiltMean hw h)
    · exact h ▸ le_rfl
  calc
    _ ≤ tiltMean (fun z => w z * ρ z) b f1 := pairSlope_le_tiltMean hwρ hf
    _ ≤ tiltMean w b f1 := tiltMean_reweight_le hw hρ hanti f1
    _ ≤ tiltMean w b e2 := h3
    _ ≤ apparentBeta e1 (logMixture w b e1) e2 (logMixture w b e2) := tiltMean_le_pairSlope hw h12

-- Ion ordinate as a log-mixture with weights w_I * rho.
theorem ion_ordinate {ζ ι κ : Type*} [Fintype ζ] [Fintype ι] [Fintype κ] [Nonempty ι] [Nonempty κ]
    {kB Fcal me h chi ne : ℝ} {T NI NII : ζ → ℝ} {gZ EZ : ι → ℝ} {gZ1 EZ1 AII : κ → ℝ}
    (hkB : 0 < kB) (hT : ∀ z, 0 < T z) (hne : 0 < ne) (hgZ : ∀ k, 0 < gZ k)
    (hgZ1 : ∀ k, 0 < gZ1 k) (hAII : ∀ k, 0 < AII k)
    (hNII : ∀ z, NII z = NI z * sahaFactor kB (T z) me h chi gZ EZ gZ1 EZ1 / ne) (k : κ) :
    Real.log (mixedLineIntensity kB T NII Fcal gZ1 EZ1 AII k / (gZ1 k * AII k))
      = logMixture (fun z => zoneWeight kB Fcal T NI gZ EZ z * ionReweight kB me h chi ne (T z))
          (zoneBeta kB T) (EZ1 k) := by
  rw [mixed_boltzmann_ordinate (N := NII) (Fcal := Fcal) hkB hT hgZ1 hAII k,
      ion_zoneWeight_eq (Fcal := Fcal) hne hgZ hgZ1 hNII]

-- Main theorem.
theorem mixed_ion_apparentBeta_le_neutral {ζ ι κ : Type*} [Fintype ζ] [Fintype ι] [Fintype κ]
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
    apparentBeta (EZ1 i')
        (Real.log (mixedLineIntensity kB T NII Fcal gZ1 EZ1 AII i' / (gZ1 i' * AII i')))
        (EZ1 j')
        (Real.log (mixedLineIntensity kB T NII Fcal gZ1 EZ1 AII j' / (gZ1 j' * AII j')))
      ≤ apparentBeta (EZ i)
        (Real.log (mixedLineIntensity kB T NI Fcal gZ EZ AI i / (gZ i * AI i)))
        (EZ j)
        (Real.log (mixedLineIntensity kB T NI Fcal gZ EZ AI j / (gZ j * AI j))) := by
  have hρ : ∀ z, 0 < ionReweight kB me h chi ne (T z) := by
    intro z
    have := thermalBracket_pos hkB (hT z) hme hh
    unfold ionReweight; positivity
  have key := logMixture_chain
    (fun z => zoneWeight_pos (T := T) (kB := kB) (E := EZ) hgZ hNI hFcal z) hρ
    (ionReweight_anti hkB hme hh hchi hne hT) hij hij' hanchor
  rw [ion_ordinate (Fcal := Fcal) (NI := NI) hkB hT hne hgZ hgZ1 hAII hNII i',
      ion_ordinate (Fcal := Fcal) (NI := NI) hkB hT hne hgZ hgZ1 hAII hNII j',
      mixed_boltzmann_ordinate (N := NI) (Fcal := Fcal) hkB hT hgZ hAI i,
      mixed_boltzmann_ordinate (N := NI) (Fcal := Fcal) hkB hT hgZ hAI j]
  exact key

end Plan.FT19
