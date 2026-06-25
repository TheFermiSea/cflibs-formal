/-
Copyright (c) 2026 Brian Squires. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Squires
-/
import Mathlib
import CflibsFormal.Boltzmann

/-!
# Saha–Boltzmann formalization — Part 2: the Saha ionization equilibrium

Saha ionization equilibrium between two adjacent ionization stages `z` and `z+1`
of a species in LTE.  With `U_z = partitionFunction kB T gZ EZ` (stage `z`) and
`U_{z+1} = partitionFunction kB T gZ1 EZ1` (stage `z+1`, a possibly different
level set, hence a second index type `κ`), the physical law is

`n_{z+1} · n_e / n_z = 2 · (U_{z+1}/U_z) · (2π·m_e·k_B·T / h²)^(3/2) · exp(−χ/(k_B T))`.

We package the right-hand side (everything except `n_e` and the stage ratio) as
`sahaFactor`, and prove:

* `sahaFactor_pos` — the Saha factor is a strictly positive real;
* `saha_relation` — the diagnostic form `n_e = S/R` is equivalent to the Saha law
  `R · n_e = S`, where `R = n_{z+1}/n_z`;
* `electronDensity_antitone` — `R ↦ n_e = S/R` is strictly antitone on positive
  `R`, hence injective: a measured stage ratio pins down a unique `n_e`;
* `log_sahaFactor` — the closed-form Saha-plot identity: `log S` is affine in
  `1/(k_B T)` (slope `−χ`) plus a `(3/2)·log T` term plus constants — the
  ionization analogue of `boltzmann_plot`;
* `chargeNeutrality_two_stage` — a small charge-neutrality consistency lemma.

All quantities are real; the `(3/2)` power uses `Real.rpow`.
-/

namespace CflibsFormal

open Finset Real
open scoped BigOperators

variable {ι : Type*} [Fintype ι]
variable {κ : Type*} [Fintype κ]

/-- The de-Broglie bracket `2π·m_e·k_B·T / h²` appearing (to the `3/2` power) in
the Saha factor.  Factored out so positivity and the log identity reuse it. -/
noncomputable def thermalBracket (kB T me h : ℝ) : ℝ :=
  (2 * Real.pi * me * kB * T) / h ^ 2

/-- The thermal-de-Broglie bracket is strictly positive when the physical
constants and temperature are positive (`h ≠ 0` suffices, here via `h > 0`). -/
lemma thermalBracket_pos {kB T me h : ℝ}
    (hkB : 0 < kB) (hT : 0 < T) (hme : 0 < me) (hh : 0 < h) :
    0 < thermalBracket kB T me h := by
  unfold thermalBracket
  have hnum : 0 < 2 * Real.pi * me * kB * T :=
    mul_pos (mul_pos (mul_pos (mul_pos (by norm_num) Real.pi_pos) hme) hkB) hT
  exact div_pos hnum (pow_pos hh 2)

/-- **Saha factor** `S(T)`: the full right-hand side of the Saha equation
*excluding* the electron density `n_e` and the stage population ratio.  With
`U_z = partitionFunction kB T gZ EZ`, `U_{z+1} = partitionFunction kB T gZ1 EZ1`:
`S(T) = 2 · (U_{z+1}/U_z) · (2π·m_e·k_B·T / h²)^(3/2) · exp(−χ/(k_B T))`.

The full Saha law then reads `(n_{z+1} · n_e)/n_z = S(T)`, equivalently
`n_e = S(T) / (n_{z+1}/n_z)`.  The leading `2` is the free-electron spin
statistical weight `2·g_e` with `g_e = 1`; the exponent sign `−χ/(k_B T)`
reflects that ionization *costs* energy `χ > 0`; the `(3/2)` power (via
`Real.rpow`) is the thermal-de-Broglie volume scaling. -/
noncomputable def sahaFactor (kB T me h chi : ℝ) (gZ EZ : ι → ℝ) (gZ1 EZ1 : κ → ℝ) : ℝ :=
  2 * (partitionFunction kB T gZ1 EZ1 / partitionFunction kB T gZ EZ)
    * (thermalBracket kB T me h) ^ (3 / 2 : ℝ)
    * Real.exp (-chi / (kB * T))

/-- **Saha density diagnostic.** Given a measured stage population ratio
`R = n_{z+1}/n_z`, the electron density implied by the Saha equation is
`n_e = S(T) / R`.  This is the inversion map used to read `n_e` off two stage
populations at known `T` and atomic data. -/
noncomputable def electronDensityFromRatio (kB T me h chi : ℝ) (gZ EZ : ι → ℝ)
    (gZ1 EZ1 : κ → ℝ) (R : ℝ) : ℝ :=
  sahaFactor kB T me h chi gZ EZ gZ1 EZ1 / R

/-- **Charge neutrality** for a multi-stage plasma: the electron density equals
the sum over ionization stages `s` of `z s · n_s` (charge-weighted ion
densities). -/
def chargeNeutrality {σ : Type*} [Fintype σ] (z : σ → ℝ) (nDens : σ → ℝ) (ne : ℝ) : Prop :=
  ne = ∑ s, z s * nDens s

/-- **Positivity of the Saha factor.** Given positive physical constants and
temperature, and positive statistical weights for both stages, `S(T) > 0`.  The
ionization energy `χ` is unconstrained: `exp(−χ/(k_B T))` is positive for any
sign of `χ`. -/
theorem sahaFactor_pos [Nonempty ι] [Nonempty κ] {kB T me h chi : ℝ}
    {gZ EZ : ι → ℝ} {gZ1 EZ1 : κ → ℝ}
    (hkB : 0 < kB) (hT : 0 < T) (hme : 0 < me) (hh : 0 < h)
    (hgZ : ∀ k, 0 < gZ k) (hgZ1 : ∀ k, 0 < gZ1 k) :
    0 < sahaFactor kB T me h chi gZ EZ gZ1 EZ1 := by
  unfold sahaFactor
  have hbr : 0 < thermalBracket kB T me h := thermalBracket_pos hkB hT hme hh
  have hrpow : 0 < (thermalBracket kB T me h) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hbr _
  have hUratio : 0 < partitionFunction kB T gZ1 EZ1 / partitionFunction kB T gZ EZ :=
    div_pos (partitionFunction_pos hgZ1) (partitionFunction_pos hgZ)
  have hexp : 0 < Real.exp (-chi / (kB * T)) := Real.exp_pos _
  exact mul_pos (mul_pos (mul_pos (by norm_num) hUratio) hrpow) hexp

/-- **Saha law ⇔ density inversion.** For a nonzero stage ratio `R`, the
diagnostic form `n_e = S/R` is equivalent to the structural Saha law
`R · n_e = S`.  The hypothesis `R ≠ 0` is load-bearing (otherwise `S/R` is
ill-posed). -/
theorem saha_relation {kB T me h chi : ℝ} {gZ EZ : ι → ℝ} {gZ1 EZ1 : κ → ℝ}
    {R ne : ℝ} (hR : R ≠ 0) :
    ne = electronDensityFromRatio kB T me h chi gZ EZ gZ1 EZ1 R
      ↔ R * ne = sahaFactor kB T me h chi gZ EZ gZ1 EZ1 := by
  unfold electronDensityFromRatio
  rw [eq_div_iff hR]
  constructor <;> intro h <;> linarith

/-- **Density diagnostic is injective.** The map `R ↦ n_e = S(T)/R` is strictly
antitone on the positive reals: a larger measured stage ratio yields a strictly
smaller inferred electron density, so a measured ratio determines `n_e` uniquely.
This relies on `S(T) > 0`. -/
theorem electronDensity_antitone [Nonempty ι] [Nonempty κ] {kB T me h chi : ℝ}
    {gZ EZ : ι → ℝ} {gZ1 EZ1 : κ → ℝ}
    (hkB : 0 < kB) (hT : 0 < T) (hme : 0 < me) (hh : 0 < h)
    (hgZ : ∀ k, 0 < gZ k) (hgZ1 : ∀ k, 0 < gZ1 k) :
    StrictAntiOn (electronDensityFromRatio kB T me h chi gZ EZ gZ1 EZ1) (Set.Ioi 0) := by
  intro a ha b hb hab
  have hS : 0 < sahaFactor kB T me h chi gZ EZ gZ1 EZ1 :=
    sahaFactor_pos hkB hT hme hh hgZ hgZ1
  unfold electronDensityFromRatio
  exact (div_lt_div_iff_of_pos_left hS (Set.mem_Ioi.mp hb) (Set.mem_Ioi.mp ha)).mpr hab

/-- **Saha-plot log identity.** The closed form of `log S(T)`: it is affine in
`1/(k_B T)` with slope `−χ` (the `−χ/(k_B T)` term), plus a `(3/2)·log(bracket)`
term (which contains `(3/2)·log T`), plus the constant `log 2` and the
partition-function difference `log U_{z+1} − log U_z`.  This is the ionization
analogue of `boltzmann_plot`, underlying linearized Saha-plot fitting. -/
theorem log_sahaFactor [Nonempty ι] [Nonempty κ] {kB T me h chi : ℝ}
    {gZ EZ : ι → ℝ} {gZ1 EZ1 : κ → ℝ}
    (hkB : 0 < kB) (hT : 0 < T) (hme : 0 < me) (hh : 0 < h)
    (hgZ : ∀ k, 0 < gZ k) (hgZ1 : ∀ k, 0 < gZ1 k) :
    Real.log (sahaFactor kB T me h chi gZ EZ gZ1 EZ1)
      = Real.log 2
        + (Real.log (partitionFunction kB T gZ1 EZ1)
            - Real.log (partitionFunction kB T gZ EZ))
        + (3 / 2 : ℝ) * Real.log (thermalBracket kB T me h)
        - chi / (kB * T) := by
  have hbr : 0 < thermalBracket kB T me h := thermalBracket_pos hkB hT hme hh
  have hUz1 : 0 < partitionFunction kB T gZ1 EZ1 := partitionFunction_pos hgZ1
  have hUz : 0 < partitionFunction kB T gZ EZ := partitionFunction_pos hgZ
  have hUratio : 0 < partitionFunction kB T gZ1 EZ1 / partitionFunction kB T gZ EZ :=
    div_pos hUz1 hUz
  have hrpow : 0 < (thermalBracket kB T me h) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hbr _
  unfold sahaFactor
  -- `sahaFactor = ((2 * Uratio) * bracket^(3/2)) * exp`.
  rw [Real.log_mul (mul_pos (mul_pos (by norm_num) hUratio) hrpow).ne' (Real.exp_ne_zero _),
      Real.log_mul (mul_pos (by norm_num) hUratio).ne' hrpow.ne',
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hUratio.ne',
      Real.log_div hUz1.ne' hUz.ne', Real.log_rpow hbr, Real.log_exp]
  ring

/-- **Charge neutrality, two-stage form.** With the neutral stage carrying charge
`0` and the singly-ionized stage charge `1`, charge neutrality holds iff the
electron density equals the once-ionized density. -/
theorem chargeNeutrality_two_stage {nZ nZ1 ne : ℝ} :
    chargeNeutrality (σ := Fin 2) ![0, 1] ![nZ, nZ1] ne ↔ ne = nZ1 := by
  simp [chargeNeutrality, Fin.sum_univ_two]

end CflibsFormal

