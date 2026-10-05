/-
Copyright (c) 2026 Brian Squires. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Squires
-/
import Mathlib
import CflibsFormal.InhomogeneityBias
import CflibsFormal.SahaStability

/-!
# Ion and neutral apparent temperatures in a line-of-sight mixture

`InhomogeneityBias` shows that a two-line Boltzmann plot of an inhomogeneous plasma reads an
apparent inverse temperature bracketed by tilted means of the zone inverse temperatures. This
module compares the plots of two adjacent ionization stages of one element observed through the
same zones. If every zone is in LTE, the ion density follows from Saha balance at one electron
density `n_e` shared by all zones, and the ion line pair lies above the neutral pair in energy,
then the ion-pair apparent inverse temperature is at most the neutral-pair one: the ion
apparent temperature is at least the neutral apparent temperature.

* `ion_zoneWeight_eq` — under Saha balance at uniform `n_e`, the ion-stage zone weight is the
  neutral-stage zone weight times `SahaStability.ionReweight`; the partition functions cancel.
* `mixed_ion_apparentBeta_le_neutral` — the comparison above (REDUCED relation).
* `mixed_ion_apparentBeta_le_neutral_shift` — the same conclusion under the shifted anchor
  `EZ j ≤ EZ1 i' + χ` and with no sign condition on `χ` (frontier FT-19d). For `χ ≥ 0`, which
  the original assumes, the shifted anchor is the weaker one.
* `mixed_ion_apparentBeta_le_neutral_bound` — the anchor is automatic when the neutral upper
  level is bound (`EZ j ≤ χ`) and the ion lower-line energy is nonnegative.
* `ion_apparentT_ge_neutral` — the temperature form: both apparent inverse temperatures are
  positive and `1/(k_B β_I) ≤ 1/(k_B β_II)`.

The proof chains four inequalities: the ion pair slope is at most the ion tilted mean at the
lower ion line (`pairSlope_le_tiltMean`); reweighting by `ionReweight`, which is larger in
hotter zones (`ionReweight_strictMonoOn`), lowers the tilted mean (`tiltMean_reweight_le`); the
neutral tilted mean is antitone in the anchor energy (the anchor hypothesis); and the neutral
tilted mean at the upper neutral line is at most the neutral pair slope
(`tiltMean_le_pairSlope`).

## Scope

REDUCED: uniform `n_e` across zones, LTE (Saha–Boltzmann) in each zone, optically thin lines
(`mixedLineIntensity`), and two-line pairs, not the `n`-line least-squares slope. The anchor
hypothesis `EZ j ≤ EZ1 i'` of the first form (the whole ion pair above the whole neutral pair)
is restrictive and may fail for the line pairs used in practice. The shifted form needs only
`EZ j ≤ EZ1 i' + χ`: ion level energies measured from the ion ground state are compared after
adding the ionization energy, which is the common energy scale of a Saha–Boltzmann plot. For
that form the anchor holds for every bound neutral level and every ion level
(`mixed_ion_apparentBeta_le_neutral_bound`). The result says nothing about the size of the gap
between the two apparent temperatures, and nothing about measurement accuracy.

## Literature

The Saha balance between adjacent stages is the Saha–Eggert equation in the form given by Griem
(`sahaFactor`). The optically thin Boltzmann plot of each stage is the CF-LIBS construction of
Ciucci 1999; its line-of-sight mixture is `InhomogeneityBias`. Boltzmann plots of neutral and
ion lines from one laser-induced plasma, and their Saha–Boltzmann combination, are the subject
of Aguilera & Aragón 2007 (Spectrochim. Acta B 62, 378–385). The measurement the comparison is
consistent with (ion apparent temperature above the neutral one) is Aguilera & Aragón 2007,
J. Phys.: Conf. Ser. 59, 210–217.
-/

namespace CflibsFormal

/-- Higher zone inverse temperature (a cooler zone) gives a smaller ion reweight. -/
private theorem ionReweight_anti {ζ : Type*} {kB me h chi ne : ℝ} {T : ζ → ℝ}
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

/-- **Ion zone weight = neutral zone weight × ion reweight (REDUCED).** If the ion density of
every zone is fixed by Saha balance at one electron density `n_e` shared by all zones
(`hNII : NII z = NI z · S(T z)/n_e`), then the ion-stage zone weight
`zoneWeight kB Fcal T NII gZ1 EZ1` equals the neutral-stage zone weight times
`ionReweight kB me h chi ne (T z)`. The ion partition function `U_{z+1}` in the ion zone weight
cancels against the one in `sahaFactor`, and the neutral one `U_z` becomes the neutral zone
weight's. Reductions: uniform `n_e` and per-zone LTE Saha balance. -/
theorem ion_zoneWeight_eq {ζ ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty ι] [Nonempty κ]
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

/-- The four-step chain on log-mixtures: the reweighted upper-pair slope is at most the
unweighted lower-pair slope when the upper pair lies above the lower pair. -/
private theorem logMixture_chain {ζ : Type*} [Fintype ζ] [Nonempty ζ] {w b ρ : ζ → ℝ}
    (hw : ∀ z, 0 < w z) (hρ : ∀ z, 0 < ρ z) (hanti : ∀ i j, b i < b j → ρ j ≤ ρ i)
    {e1 e2 f1 f2 : ℝ} (h12 : e1 < e2) (hf : f1 < f2) (hanchor : e2 ≤ f1) :
    apparentBeta f1 (logMixture (fun z => w z * ρ z) b f1) f2
        (logMixture (fun z => w z * ρ z) b f2)
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
    _ ≤ apparentBeta e1 (logMixture w b e1) e2 (logMixture w b e2) :=
        tiltMean_le_pairSlope hw h12

/-- The ion Boltzmann-plot ordinate is a log-mixture with zone weights `w_I · ionReweight`. -/
private theorem ion_ordinate {ζ ι κ : Type*} [Fintype ζ] [Fintype ι] [Fintype κ] [Nonempty ι]
    [Nonempty κ]
    {kB Fcal me h chi ne : ℝ} {T NI NII : ζ → ℝ} {gZ EZ : ι → ℝ} {gZ1 EZ1 AII : κ → ℝ}
    (hkB : 0 < kB) (hT : ∀ z, 0 < T z) (hne : 0 < ne) (hgZ : ∀ k, 0 < gZ k)
    (hgZ1 : ∀ k, 0 < gZ1 k) (hAII : ∀ k, 0 < AII k)
    (hNII : ∀ z, NII z = NI z * sahaFactor kB (T z) me h chi gZ EZ gZ1 EZ1 / ne) (k : κ) :
    Real.log (mixedLineIntensity kB T NII Fcal gZ1 EZ1 AII k / (gZ1 k * AII k))
      = logMixture (fun z => zoneWeight kB Fcal T NI gZ EZ z * ionReweight kB me h chi ne (T z))
          (zoneBeta kB T) (EZ1 k) := by
  rw [mixed_boltzmann_ordinate (N := NII) (Fcal := Fcal) hkB hT hgZ1 hAII k,
      ion_zoneWeight_eq (Fcal := Fcal) hne hgZ hgZ1 hNII]

/-- **Ion apparent temperature ≥ neutral apparent temperature (REDUCED).** Observe one element
through a line-of-sight mixture of LTE zones at temperatures `T z > 0`, with neutral densities
`NI z > 0` and ion densities fixed by Saha balance at one electron density `n_e` shared by all
zones (`hNII`). Read a two-line apparent inverse temperature `apparentBeta` from a neutral line
pair `EZ i < EZ j` and from an ion line pair `EZ1 i' < EZ1 j'` lying above it
(`hanchor : EZ j ≤ EZ1 i'`). Then the ion value is at most the neutral value, so the ion
apparent temperature is at least the neutral one.

Reductions: uniform `n_e`, per-zone LTE, optically thin lines, two-line pairs (not the `n`-line
least-squares slope). The anchor `hanchor` is restrictive and may fail for line pairs used in
practice. The result is *consistent with*, and does not prove, the measurement of Aguilera and
Aragón in J. Phys.: Conf. Ser. 59 (2007) 210–217 (doi 10.1088/1742-6596/59/1/046), which
reports ion apparent temperatures above neutral ones from multi-line Boltzmann plots of a
laser-induced plasma (the citation whitelist records that paper as opened and verified on
2026-09-28). -/
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

/-! ### The shifted anchor and the temperature form (frontier FT-19d) -/

/-- Shifting both abscissae by `c` leaves a two-point slope unchanged. -/
private lemma apparentBeta_shift (E₁ y₁ E₂ y₂ c : ℝ) :
    apparentBeta E₁ y₁ E₂ y₂ = apparentBeta (E₁ + c) y₁ (E₂ + c) y₂ := by
  unfold apparentBeta; congr 1; ring

/-- The `e^{−χ b}` factor of the ion reweight is an abscissa shift of the log-mixture: the ion
ordinate at energy `E` with ionization energy `χ` is the `χ`-free ordinate at `E + χ`. -/
private lemma logMixture_ionReweight_shift {ζ : Type*} [Fintype ζ] {kB me h chi ne : ℝ}
    {T : ζ → ℝ} (w : ζ → ℝ) (hkB : 0 < kB) (hT : ∀ z, 0 < T z) (E : ℝ) :
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

/-- **Ion apparent temperature ≥ neutral apparent temperature, shifted anchor (FT-19d).** The
conclusion of `mixed_ion_apparentBeta_le_neutral` under the anchor `EZ j ≤ EZ1 i' + χ` in place
of `EZ j ≤ EZ1 i'`, and with no sign condition on `χ`. For `χ ≥ 0`, the case the original
theorem assumes, this anchor is weaker, so the result then contains the original; for `χ < 0`,
which this statement admits, the shifted anchor is the stronger of the two.

Why the shift is the right anchor: the Boltzmann factor of an ion level relative to the neutral
ground state carries `E + χ`, so on the common energy scale the ion lower line sits at
`EZ1 i' + χ`. The proof moves the `e^{−χ/(k_B T)}` of the Saha reweight into that abscissa
shift (which leaves the two-point slope unchanged) and then runs the original chain with the
`χ`-free reweight, whose monotonicity in `T` needs no sign of `χ`.

Reductions and caveats are those of `mixed_ion_apparentBeta_le_neutral`: uniform `n_e`,
per-zone LTE, optically thin lines, two-line pairs. Scope: REDUCED. -/
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
  have hw : ∀ z, 0 < zoneWeight kB Fcal T NI gZ EZ z :=
    fun z => zoneWeight_pos (T := T) (kB := kB) (E := EZ) hgZ hNI hFcal z
  have hρ0 : ∀ z, 0 < ionReweight kB me h 0 ne (T z) := by
    intro z
    have := thermalBracket_pos hkB (hT z) hme hh
    unfold ionReweight; positivity
  have hion : ∀ k : κ,
      Real.log (mixedLineIntensity kB T NII Fcal gZ1 EZ1 AII k / (gZ1 k * AII k))
        = logMixture (fun z => zoneWeight kB Fcal T NI gZ EZ z * ionReweight kB me h 0 ne (T z))
            (zoneBeta kB T) (EZ1 k + chi) := by
    intro k
    rw [ion_ordinate (Fcal := Fcal) (NI := NI) hkB hT hne hgZ hgZ1 hAII hNII k]
    exact logMixture_ionReweight_shift (chi := chi) _ hkB hT (EZ1 k)
  have key := logMixture_chain hw hρ0 (ionReweight_anti hkB hme hh le_rfl hne hT) hij
    (by linarith : EZ1 i' + chi < EZ1 j' + chi) hanchor
  rw [hion i', hion j',
    mixed_boltzmann_ordinate (N := NI) (Fcal := Fcal) hkB hT hgZ hAI i,
    mixed_boltzmann_ordinate (N := NI) (Fcal := Fcal) hkB hT hgZ hAI j,
    apparentBeta_shift (EZ1 i') _ (EZ1 j') _ chi]
  exact key

/-- **Bound neutral levels discharge the anchor (FT-19d).** If the neutral upper level is bound
(`EZ j ≤ χ`) and the ion lower-line energy is nonnegative (`0 ≤ EZ1 i'`, ion energies measured
from the ion ground state), the anchor of `mixed_ion_apparentBeta_le_neutral_shift` holds. Both
conditions are satisfied by every tabulated bound level, so for such data the comparison needs
no condition relating the two line pairs. Scope and reductions as there (REDUCED). -/
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

/-- **Temperature form (FT-19).** Under the hypotheses of
`mixed_ion_apparentBeta_le_neutral_bound`, both two-line apparent inverse temperatures are
positive, and the neutral apparent temperature `1/(k_B β_I)` is at most the ion one
`1/(k_B β_II)`.

The positivity is part of the statement because `1/(k_B β)` is a temperature only for `β > 0`;
it comes from every zone having a positive inverse temperature (`pairSlope_pos`). Scope and
reductions as in `mixed_ion_apparentBeta_le_neutral` (REDUCED). -/
theorem ion_apparentT_ge_neutral {ζ ι κ : Type*} [Fintype ζ] [Fintype ι] [Fintype κ]
    [Nonempty ζ] [Nonempty ι] [Nonempty κ]
    {kB Fcal me h chi ne : ℝ} {T NI NII : ζ → ℝ}
    {gZ EZ AI : ι → ℝ} {gZ1 EZ1 AII : κ → ℝ}
    (hkB : 0 < kB) (hme : 0 < me) (hh : 0 < h) (hne : 0 < ne)
    (hFcal : 0 < Fcal) (hT : ∀ z, 0 < T z) (hNI : ∀ z, 0 < NI z)
    (hgZ : ∀ k, 0 < gZ k) (hgZ1 : ∀ k, 0 < gZ1 k)
    (hAI : ∀ k, 0 < AI k) (hAII : ∀ k, 0 < AII k)
    (hNII : ∀ z, NII z = NI z * sahaFactor kB (T z) me h chi gZ EZ gZ1 EZ1 / ne)
    (i j : ι) (hij : EZ i < EZ j) (i' j' : κ) (hij' : EZ1 i' < EZ1 j')
    (hbound : EZ j ≤ chi) (hion0 : 0 ≤ EZ1 i') :
    0 < apparentBeta (EZ1 i')
          (Real.log (mixedLineIntensity kB T NII Fcal gZ1 EZ1 AII i' / (gZ1 i' * AII i')))
          (EZ1 j')
          (Real.log (mixedLineIntensity kB T NII Fcal gZ1 EZ1 AII j' / (gZ1 j' * AII j')))
      ∧ 0 < apparentBeta (EZ i)
          (Real.log (mixedLineIntensity kB T NI Fcal gZ EZ AI i / (gZ i * AI i)))
          (EZ j)
          (Real.log (mixedLineIntensity kB T NI Fcal gZ EZ AI j / (gZ j * AI j)))
      ∧ 1 / (kB * apparentBeta (EZ i)
              (Real.log (mixedLineIntensity kB T NI Fcal gZ EZ AI i / (gZ i * AI i)))
              (EZ j)
              (Real.log (mixedLineIntensity kB T NI Fcal gZ EZ AI j / (gZ j * AI j))))
          ≤ 1 / (kB * apparentBeta (EZ1 i')
              (Real.log (mixedLineIntensity kB T NII Fcal gZ1 EZ1 AII i' / (gZ1 i' * AII i')))
              (EZ1 j')
              (Real.log
                (mixedLineIntensity kB T NII Fcal gZ1 EZ1 AII j' / (gZ1 j' * AII j')))) := by
  have hmain := mixed_ion_apparentBeta_le_neutral_bound hkB hme hh hne hFcal hT hNI hgZ hgZ1
    hAI hAII hNII i j hij i' j' hij' hbound hion0
  have hNIIpos : ∀ z, 0 < NII z := by
    intro z; rw [hNII z]
    exact div_pos (mul_pos (hNI z) (sahaFactor_pos hkB (hT z) hme hh hgZ hgZ1)) hne
  have hb0 : ∀ z, 0 < zoneBeta kB T z := fun z => by
    simp only [zoneBeta]; exact one_div_pos.mpr (mul_pos hkB (hT z))
  have hII : 0 < apparentBeta (EZ1 i')
      (Real.log (mixedLineIntensity kB T NII Fcal gZ1 EZ1 AII i' / (gZ1 i' * AII i')))
      (EZ1 j')
      (Real.log (mixedLineIntensity kB T NII Fcal gZ1 EZ1 AII j' / (gZ1 j' * AII j'))) := by
    rw [mixed_boltzmann_ordinate (N := NII) (Fcal := Fcal) hkB hT hgZ1 hAII i',
      mixed_boltzmann_ordinate (N := NII) (Fcal := Fcal) hkB hT hgZ1 hAII j']
    exact pairSlope_pos (fun z => zoneWeight_pos (T := T) (kB := kB) (E := EZ1) hgZ1 hNIIpos
      hFcal z) hb0 hij'
  exact ⟨hII, lt_of_lt_of_le hII hmain, apparentTemperature_ge hkB hII hmain⟩

end CflibsFormal
