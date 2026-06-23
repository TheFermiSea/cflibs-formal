/-
Copyright (c) 2026 Brian Squires. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Squires
-/
import Mathlib
import CflibsFormal.Boltzmann
import CflibsFormal.ForwardMap
import CflibsFormal.Saha
import CflibsFormal.Identifiability
import CflibsFormal.Closure

/-!
# Saha–Boltzmann formalization — Part 6: coupling Saha into the inverse problem

This module *couples* the Saha ionization equilibrium into the Boltzmann-plot
inverse problem, formalizing the **Saha–Boltzmann plot** that places
neutral-stage and ion-stage lines on a single straight line for the joint
determination of temperature `T` and electron density `n_e`.

Earlier modules treated the Boltzmann (temperature/density) inverse and the
Saha (electron-density) diagnostic *separately* (`ForwardMap.lean`,
`Saha.lean`, `Identifiability.lean`). Here we tie them together:

* `sahaBoltzmannOrdinate` — the per-line Saha–Boltzmann plot ordinate
  `Y = log(I_{ki}/(g_k A_{ki}))`, a thin wrapper over the forward map. By
  `boltzmann_plot_intensity` it is affine in the upper-level energy with slope
  `-1/(k_B T)` and stage intercept `log(Fcal·N/U(T))`.
* `stageIntercept` — the ordinate intercept (value at `E = 0`) for a single
  ionization stage, `b = log(Fcal·N/U(T))`.
* `sahaBoltzmann_plot` — both the neutral and ion stage ordinates lie on a line
  of common slope `-1/(k_B T)`, and the inter-stage intercept shift is computed
  in closed form. The shift carries the stage density ratio `log(Nz1/Nz)`.
* `sahaBoltzmann_shift_eq_log_saha` — under the structural Saha law the
  inter-stage shift equals `log S − log n_e + (log U_z − log U_{z+1})`,
  exhibiting `n_e` explicitly inside the Saha–Boltzmann plot offset.
* `saha_joint_identifiability` — **the genuine coupling.** From observed line
  intensities of BOTH stages — a distinct-energy neutral pair (shared slope), a
  neutral line, and an ION line — BOTH `T` (slope, via `temperature_identifiability`)
  AND `n_e` are uniquely determined: the neutral and ion densities are each recovered
  from their observed lines (`density_identifiability`, ion stage included), the stage
  ratio is *derived*, and the Saha law forces `n_e`. The electron density is recovered
  from observations, never taken as input nor via a smuggled stage ratio.

## Literature

The Saha–Boltzmann plot construction formalized here is that of
S. Yalcin, D. R. Crosley, G. P. Smith and G. W. Faris, "Influence of ambient
conditions on the laser air spark," *Applied Physics B* **68** (1999) 121,
which combines neutral- and ionized-stage lines on a single Saha–Boltzmann
plot for the joint determination of temperature and electron density; and
J. A. Aguilera and C. Aragón, "Multi-element Saha–Boltzmann and Boltzmann
plots in laser-induced plasmas," *Spectrochimica Acta Part B* **62** (2007)
378, which develops the multi-element Saha–Boltzmann plot whose common slope
fixes `T` and whose inter-stage ordinate offset encodes the electron density
`n_e`. The definitions and equations below match the cited method: a single
shared slope `-1/(k_B T)` across ionization stages and a stage-dependent
ordinate offset equal to the Saha term.
-/

namespace CflibsFormal

open Finset Real
open scoped BigOperators

variable {ι : Type*} [Fintype ι]
variable {κ : Type*} [Fintype κ]

/-- **Saha–Boltzmann plot ordinate (single stage / single line).** The standard
Boltzmann-plot ordinate `Y = log (I_{ki} / (g_k A_{ki}))` for the line with upper
level `k`. By `boltzmann_plot_intensity` this equals `log(Fcal·N/U(T)) - E_k/(k_B T)`:
affine in the upper-level energy with slope `-1/(k_B T)` and stage intercept
`log(Fcal·N/U(T))`. This is the per-line quantity that gets plotted; the multi-stage
Saha–Boltzmann plot stacks the neutral- and ion-stage ordinates on one line. -/
noncomputable def sahaBoltzmannOrdinate (kB T N Fcal : ℝ) (g E A : ι → ℝ) (k : ι) : ℝ :=
  Real.log (lineIntensity kB T N Fcal g E A k / (g k * A k))

/-- **Stage intercept of the Saha–Boltzmann plot.** The ordinate intercept (value at
`E = 0`) for a single ionization stage with total density `N` and partition function
`U(T) = partitionFunction kB T g E`: `b = log (Fcal · N / U(T))`. The neutral and ion
stages have intercepts `b_z` and `b_{z+1}`; their vertical separation `b_{z+1} - b_z`
encodes the stage population ratio, and via Saha the electron density `n_e`. -/
noncomputable def stageIntercept (kB T N Fcal : ℝ) (g E : ι → ℝ) : ℝ :=
  Real.log (Fcal * N / partitionFunction kB T g E)

/-- **Saha–Boltzmann plot.** Establishes that the neutral-stage and ion-stage lines
BOTH lie on a single straight line of common slope `-1/(k_B T)` (parts 1 and 2, one
per stage), and computes the inter-stage vertical shift between the two stage
intercepts in closed form (part 3). This is the Saha–Boltzmann plot construction of
Yalcin et al. and Aguilera & Aragón: a shared slope across stages with a
stage-dependent ordinate offset. The shift formula
`log(Nz1/Nz) + (log U_z − log U_{z+1})` is the bridge to the Saha relation:
combined with the Saha law `Nz1/Nz = S/n_e`, the shift carries `n_e` (made explicit
in `sahaBoltzmann_shift_eq_log_saha`). -/
theorem sahaBoltzmann_plot [Nonempty ι] [Nonempty κ]
    {kB T Nz Nz1 Fcal : ℝ} {gZ EZ AZ : ι → ℝ} {gZ1 EZ1 AZ1 : κ → ℝ}
    (hgZ : ∀ k, 0 < gZ k) (hgZ1 : ∀ k, 0 < gZ1 k)
    (hNz : 0 < Nz) (hNz1 : 0 < Nz1) (hFcal : 0 < Fcal)
    (hAZ : ∀ k, 0 < AZ k) (hAZ1 : ∀ k, 0 < AZ1 k)
    (kz : ι) (kz1 : κ) :
    (sahaBoltzmannOrdinate kB T Nz Fcal gZ EZ AZ kz
        = stageIntercept kB T Nz Fcal gZ EZ - EZ kz / (kB * T))
      ∧ (sahaBoltzmannOrdinate kB T Nz1 Fcal gZ1 EZ1 AZ1 kz1
          = stageIntercept kB T Nz1 Fcal gZ1 EZ1 - EZ1 kz1 / (kB * T))
      ∧ stageIntercept kB T Nz1 Fcal gZ1 EZ1 - stageIntercept kB T Nz Fcal gZ EZ
          = Real.log (Nz1 / Nz)
            + (Real.log (partitionFunction kB T gZ EZ)
                - Real.log (partitionFunction kB T gZ1 EZ1)) := by
  have hUz : 0 < partitionFunction kB T gZ EZ := partitionFunction_pos hgZ
  have hUz1 : 0 < partitionFunction kB T gZ1 EZ1 := partitionFunction_pos hgZ1
  refine ⟨?_, ?_, ?_⟩
  · -- neutral stage: ordinate = intercept − E/(kBT)
    unfold sahaBoltzmannOrdinate stageIntercept
    exact boltzmann_plot_intensity hgZ hNz hFcal hAZ kz
  · -- ion stage: ordinate = intercept − E/(kBT)
    unfold sahaBoltzmannOrdinate stageIntercept
    exact boltzmann_plot_intensity hgZ1 hNz1 hFcal hAZ1 kz1
  · -- intercept shift in closed form
    unfold stageIntercept
    rw [Real.log_div (mul_pos hFcal hNz1).ne' hUz1.ne',
        Real.log_div (mul_pos hFcal hNz).ne' hUz.ne',
        Real.log_mul hFcal.ne' hNz1.ne',
        Real.log_mul hFcal.ne' hNz.ne',
        Real.log_div hNz1.ne' hNz.ne']
    ring

/-- **Saha–Boltzmann shift equals the log Saha factor.** Couples the Saha equation
into the inter-stage shift: under the structural Saha law `Nz1·n_e/Nz = S(T)` (so
`Nz1/Nz = S/n_e`), the Saha–Boltzmann intercept shift equals
`log S − log n_e + (log U_z − log U_{z+1})`. Because `log S` is itself the closed
form of `log_sahaFactor` (affine in `1/(k_B T)`), the shift is an explicit function
of `n_e` and `T`: this is the precise sense in which the vertical offset between
neutral and ion lines on the Saha–Boltzmann plot encodes the electron density. -/
theorem sahaBoltzmann_shift_eq_log_saha [Nonempty ι] [Nonempty κ]
    {kB T me h chi Nz Nz1 ne Fcal : ℝ} {gZ EZ : ι → ℝ} {gZ1 EZ1 : κ → ℝ}
    (hkB : 0 < kB) (hT : 0 < T) (hme : 0 < me) (hh : 0 < h)
    (hgZ : ∀ k, 0 < gZ k) (hgZ1 : ∀ k, 0 < gZ1 k)
    (hNz : 0 < Nz) (hNz1 : 0 < Nz1) (hFcal : 0 < Fcal) (hne : 0 < ne)
    (hsaha : Nz1 * ne / Nz = sahaFactor kB T me h chi gZ EZ gZ1 EZ1) :
    stageIntercept kB T Nz1 Fcal gZ1 EZ1 - stageIntercept kB T Nz Fcal gZ EZ
      = Real.log (sahaFactor kB T me h chi gZ EZ gZ1 EZ1)
        - Real.log ne
        + (Real.log (partitionFunction kB T gZ EZ)
            - Real.log (partitionFunction kB T gZ1 EZ1)) := by
  have hS : 0 < sahaFactor kB T me h chi gZ EZ gZ1 EZ1 :=
    sahaFactor_pos hkB hT hme hh hgZ hgZ1
  -- The closed-form intercept shift: log(Nz1/Nz) + (log U_z − log U_{z+1}).
  have hshift :
      stageIntercept kB T Nz1 Fcal gZ1 EZ1 - stageIntercept kB T Nz Fcal gZ EZ
        = Real.log (Nz1 / Nz)
          + (Real.log (partitionFunction kB T gZ EZ)
              - Real.log (partitionFunction kB T gZ1 EZ1)) :=
    (sahaBoltzmann_plot (AZ := fun _ => (1 : ℝ)) (AZ1 := fun _ => (1 : ℝ))
      hgZ hgZ1 hNz hNz1 hFcal (fun _ => one_pos) (fun _ => one_pos)
      (Classical.arbitrary ι) (Classical.arbitrary κ)).2.2
  -- From the Saha law: Nz1/Nz = S/ne.
  have hratio : Nz1 / Nz = sahaFactor kB T me h chi gZ EZ gZ1 EZ1 / ne := by
    rw [div_eq_div_iff hNz.ne' hne.ne']
    field_simp at hsaha
    linarith [hsaha]
  rw [hshift, hratio, Real.log_div hS.ne' hne.ne']

/-- **Joint identifiability of `(T, n_e)` from the Saha–Boltzmann plot.** THE genuine
coupling theorem. The observations are line INTENSITIES from both ionization stages:
a distinct-energy neutral-line pair `(i,j)` (`hslope`), one further neutral line `uz`
(`hNeutObs`), and one ION line `uz1` (`hIonObs`), all at a shared (matched) calibration
`Fcal`. From these, BOTH the temperature `T` AND the electron density `n_e` are uniquely
determined:

* `T` from the neutral-line Boltzmann-plot slope (`temperature_identifiability`);
* the neutral density `Nz` and the ION density `Nz1` are each recovered from their
  observed line intensities at the now-common `T` (`density_identifiability`, applied to
  the ion stage too — the ion stage is genuinely observed);
* hence the stage ratio `Nz1/Nz` is *derived* (not assumed), and the Saha law then forces
  `n_e` to agree.

The electron density `n_e` is recovered from the observed neutral- AND ion-line
intensities, never taken as input and never via a smuggled stage-ratio hypothesis. This
is the joint `(T, n_e)` recovery that Yalcin et al. and Aguilera & Aragón obtain from a
multi-element Saha–Boltzmann plot, and the new content beyond prior modules (which proved
`T` and `n_e` identifiability separately). The atomic data and calibration are shared
across the two candidate states, so the two Saha factors coincide after `T₁ = T₂`. -/
theorem saha_joint_identifiability [Nonempty ι] [Nonempty κ]
    {kB me h chi : ℝ} {T₁ T₂ Nz₁ Nz₂ Nz1₁ Nz1₂ Fcal ne₁ ne₂ : ℝ}
    {gZ EZ AZ : ι → ℝ} {gZ1 EZ1 AZ1 : κ → ℝ}
    (hkB : 0 < kB) (_hme : 0 < me) (_hh : 0 < h)
    (hT₁ : 0 < T₁) (hT₂ : 0 < T₂)
    (hgZ : ∀ k, 0 < gZ k) (hgZ1 : ∀ k, 0 < gZ1 k)
    (hAZ : ∀ k, 0 < AZ k) (hAZ1 : ∀ k, 0 < AZ1 k)
    (hNz₁ : 0 < Nz₁) (hNz₂ : 0 < Nz₂) (hNz1₁ : 0 < Nz1₁) (_hNz1₂ : 0 < Nz1₂)
    (hFcal : 0 < Fcal)
    (_hne₁ : 0 < ne₁) (_hne₂ : 0 < ne₂)
    (i j : ι) (hE : EZ i ≠ EZ j) (uz : ι) (uz1 : κ)
    (hslope :
      lineIntensity kB T₁ Nz₁ Fcal gZ EZ AZ j / lineIntensity kB T₁ Nz₁ Fcal gZ EZ AZ i
        = lineIntensity kB T₂ Nz₂ Fcal gZ EZ AZ j / lineIntensity kB T₂ Nz₂ Fcal gZ EZ AZ i)
    (hNeutObs :
      lineIntensity kB T₁ Nz₁ Fcal gZ EZ AZ uz = lineIntensity kB T₂ Nz₂ Fcal gZ EZ AZ uz)
    (hIonObs :
      lineIntensity kB T₁ Nz1₁ Fcal gZ1 EZ1 AZ1 uz1 = lineIntensity kB T₂ Nz1₂ Fcal gZ1 EZ1 AZ1 uz1)
    (hsaha₁ : Nz1₁ * ne₁ / Nz₁ = sahaFactor kB T₁ me h chi gZ EZ gZ1 EZ1)
    (hsaha₂ : Nz1₂ * ne₂ / Nz₂ = sahaFactor kB T₂ me h chi gZ EZ gZ1 EZ1) :
    T₁ = T₂ ∧ ne₁ = ne₂ := by
  -- Step 1: the shared neutral-line slope fixes the temperature.
  have hT : T₁ = T₂ :=
    temperature_identifiability hkB hT₁ hT₂ hgZ hNz₁ hNz₂ hFcal hFcal hAZ i j hE hslope
  refine ⟨hT, ?_⟩
  subst hT
  -- Step 2: equal observed line intensities ⇒ equal densities (neutral AND ion stage),
  -- via the already-proven density_identifiability — the ion stage is genuinely observed.
  have hNzeq : Nz₁ = Nz₂ := density_identifiability hgZ hFcal uz (hAZ uz) hNeutObs
  have hNz1eq : Nz1₁ = Nz1₂ := density_identifiability hgZ1 hFcal uz1 (hAZ1 uz1) hIonObs
  -- Step 3: the stage ratio is now DERIVED, and the Saha law forces n_e to agree.
  have hR : Nz1₁ / Nz₁ = Nz1₂ / Nz₂ := by rw [hNzeq, hNz1eq]
  have hr : (0 : ℝ) < Nz1₁ / Nz₁ := div_pos hNz1₁ hNz₁
  have e1 : (Nz1₁ / Nz₁) * ne₁ = sahaFactor kB T₁ me h chi gZ EZ gZ1 EZ1 := by
    rw [← hsaha₁]; field_simp
  have e2 : (Nz1₁ / Nz₁) * ne₂ = sahaFactor kB T₁ me h chi gZ EZ gZ1 EZ1 := by
    rw [hR, ← hsaha₂]; field_simp
  exact mul_left_cancel₀ hr.ne' (e1.trans e2.symm)

end CflibsFormal
