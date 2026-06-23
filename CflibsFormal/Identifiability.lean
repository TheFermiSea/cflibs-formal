/-
Copyright (c) 2026 Brian Squires. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Squires
-/
import Mathlib
import CflibsFormal.Boltzmann
import CflibsFormal.Saha
import CflibsFormal.ForwardMap

/-!
# Saha–Boltzmann formalization — Part 5: identifiability of the inverse problem

This module turns the *forward* CF-LIBS model (`ForwardMap.lineIntensity`, the
`Boltzmann` populations, the `Saha` ionization diagnostic) into rigorous
**identifiability** (injectivity) statements: precisely when, and under which
explicit nondegeneracy hypotheses, the plasma parameters `(T, n_e, N_s)` are
*uniquely* recoverable from line intensities.

We reuse the already-built definitions verbatim — nothing here re-defines the
forward model:

* `lineIntensity` from `ForwardMap.lean` (`I_{ki} = Fcal · A · n_k`,
  `n_k = population kB T N g E k`),
* `population`, `partitionFunction`, `boltzmannFactor` from `Boltzmann.lean`,
* `electronDensityFromRatio`, `sahaFactor`, and the strict-antitone inverse
  `electronDensity_antitone` from `Saha.lean`.

The three theorems are:

* `temperature_identifiability` — **Target 1.** Two same-species lines with
  *distinct upper-level energies* fix `T` uniquely: if two parameter sets
  produce the same intensity *ratio* on such a line pair, then `T₁ = T₂`. The
  calibration `Fcal`, density `N`, partition function `U`, degeneracies `g`, and
  Einstein coefficient `A` all cancel; the proof reduces to injectivity of
  `Real.exp` and `E i ≠ E j`.
* `density_identifiability` — **Target 2.** With `T` and atomic data fixed and
  nondegenerate, the species total number density `N` is recovered from a single
  line intensity (equal intensities ⇒ equal `N`). Since composition `C_s` is `N_s`
  up to the closure normalization `∑ C_s = 1`, this is the per-species core of
  composition identifiability.
* `electron_density_identifiability` — **Target 3.** At fixed `T` (hence fixed
  Saha factor `S = sahaFactor … > 0`) the density diagnostic `R ↦ n_e = S/R` is
  *injective* on positive stage ratios: two ratios giving the same inferred `n_e`
  must coincide, so a measured electron density back-determines `R` uniquely.
  Obtained from the proven strict antitonicity `electronDensity_antitone`; it
  rests only on `S > 0`, the Saha factor's internal structure being certified
  separately by `sahaFactor_pos` / `log_sahaFactor`.

All hypotheses are satisfiable (see the witness discussion in each docstring), so
the theorems are non-vacuous.
-/

namespace CflibsFormal

open Finset Real
open scoped BigOperators

variable {ι : Type*} [Fintype ι]
variable {κ : Type*} [Fintype κ]

/-- **Target 1 — temperature identifiability.**

Two same-species lines with **distinct upper-level energies** `E i ≠ E j` fix the
temperature uniquely. If two parameter sets (possibly differing in calibration
`Fcal`, total density `N`, and temperature `T`) produce the *same intensity ratio*
`I_j / I_i` on this line pair, and both temperatures are positive, then `T₁ = T₂`.

Inside one parameter set the ratio is
`I_j/I_i = ((g_j·A_j)/(g_i·A_i)) · exp((E_i − E_j)/(k_B T))` — the common positive
prefactor `(g_j·A_j)/(g_i·A_i)` (shared across both sides because `g`, `E`, `A`, the
species, are the same) cancels *across* the two sides, after which `Real.exp` injectivity
plus `E i ≠ E j` and `k_B > 0` force `T₁ = T₂`. `Fcal`, `N`, and the partition function
`U` all cancel.

Non-vacuous: e.g. `ι = Fin 2`, `kB = 1`, `g = A = fun _ => 1`, `E = ![0,1]`
(so `E 0 ≠ E 1`), `N = Fcal = 1`, any `T₁, T₂ > 0`. Then the ratio is
`exp((E i − E j)/(kB·T))`, a non-constant function of `T`; equality genuinely
forces `T₁ = T₂` (it depends on `Real.exp` injectivity, not `rfl`). -/
theorem temperature_identifiability [Nonempty ι]
    {kB : ℝ} {T₁ T₂ N₁ N₂ Fcal₁ Fcal₂ : ℝ} {g E A : ι → ℝ}
    (hkB : 0 < kB) (hT₁ : 0 < T₁) (hT₂ : 0 < T₂)
    (hg : ∀ k, 0 < g k) (hN₁ : 0 < N₁) (hN₂ : 0 < N₂)
    (hFcal₁ : 0 < Fcal₁) (hFcal₂ : 0 < Fcal₂) (hA : ∀ k, 0 < A k)
    (i j : ι) (hE : E i ≠ E j)
    (hratio :
      lineIntensity kB T₁ N₁ Fcal₁ g E A j / lineIntensity kB T₁ N₁ Fcal₁ g E A i
        = lineIntensity kB T₂ N₂ Fcal₂ g E A j / lineIntensity kB T₂ N₂ Fcal₂ g E A i) :
    T₁ = T₂ := by
  -- A clean closed form for the within-set intensity ratio:
  -- `I_j / I_i = (g j · A j) / (g i · A i) · exp((E i − E j)/(kB·T))`.
  have key : ∀ (T N Fcal : ℝ), 0 < T → 0 < N → 0 < Fcal →
      lineIntensity kB T N Fcal g E A j / lineIntensity kB T N Fcal g E A i
        = (g j * A j) / (g i * A i) * Real.exp ((E i - E j) / (kB * T)) := by
    intro T N Fcal hT hN hFcal
    have hU : 0 < partitionFunction kB T g E := partitionFunction_pos hg
    have hgi : g i ≠ 0 := (hg i).ne'
    have hgj : g j ≠ 0 := (hg j).ne'
    have hAi : A i ≠ 0 := (hA i).ne'
    have hAj : A j ≠ 0 := (hA j).ne'
    have hNne : N ≠ 0 := hN.ne'
    have hFne : Fcal ≠ 0 := hFcal.ne'
    have hexp : Real.exp ((E i - E j) / (kB * T))
        = Real.exp (-E j / (kB * T)) / Real.exp (-E i / (kB * T)) := by
      rw [← Real.exp_sub]; ring_nf
    rw [hexp]
    simp only [lineIntensity, population, boltzmannFactor]
    field_simp
  rw [key T₁ N₁ Fcal₁ hT₁ hN₁ hFcal₁, key T₂ N₂ Fcal₂ hT₂ hN₂ hFcal₂] at hratio
  -- Cancel the common positive prefactor `(g j · A j) / (g i · A i)`.
  have hc : (0 : ℝ) < (g j * A j) / (g i * A i) :=
    div_pos (mul_pos (hg j) (hA j)) (mul_pos (hg i) (hA i))
  have hexp : Real.exp ((E i - E j) / (kB * T₁)) = Real.exp ((E i - E j) / (kB * T₂)) :=
    mul_left_cancel₀ hc.ne' hratio
  -- `exp` injective ⇒ equal arguments.
  rw [Real.exp_eq_exp] at hexp
  -- `(E i − E j)/(kB·T₁) = (E i − E j)/(kB·T₂)` with `E i − E j ≠ 0`, `kB > 0`.
  have hEij : E i - E j ≠ 0 := sub_ne_zero.mpr hE
  rw [div_eq_div_iff (mul_pos hkB hT₁).ne' (mul_pos hkB hT₂).ne'] at hexp
  -- `(E i − E j)·(kB·T₂) = (E i − E j)·(kB·T₁)`.
  have h2 : kB * T₂ = kB * T₁ := mul_left_cancel₀ hEij hexp
  exact (mul_left_cancel₀ hkB.ne' h2).symm

/-- **Target 2 — relative-density / composition identifiability.**

With `T` and the atomic data (`Fcal`, `A`, `g`, `E`, `U`) fixed and nondegenerate
(`Fcal > 0`, `A u > 0`, `g k > 0`), the species total number density `N` is uniquely
recovered from a single line intensity: equal intensities ⇒ equal `N`. Since the
composition `C_s` is `N_s` up to the closure normalization `∑ C_s = 1`
(`composition_sum_one` in `Closure.lean`), equal `N` for every species gives equal
composition; this lemma is the per-species core.

The map `N ↦ I` is multiplication by the strictly positive constant
`c = Fcal · A_u · g u · exp(−E_u/(k_B T)) / U(T)`, so it is injective but not
trivially so (the constant is genuine physics, so the proof needs
`mul_left_cancel₀`, not `rfl`).

Non-vacuous: `ι = Fin 1`, `kB = T = Fcal = 1`, `g = A = fun _ => 1`,
`E = fun _ => 0`, `u = 0`; then `I = c · N` with `c > 0`, so `N₁ = 3 ≠ N₂ = 5`
give distinct intensities. `T` may be any real (positivity of `T` is *not* needed:
`exp` and the partition function are positive regardless of `T`'s sign). -/
theorem density_identifiability [Nonempty ι]
    {kB T Fcal : ℝ} {g E A : ι → ℝ} {N₁ N₂ : ℝ}
    (hg : ∀ k, 0 < g k) (hFcal : 0 < Fcal) (u : ι) (hA : 0 < A u)
    (hI : lineIntensity kB T N₁ Fcal g E A u = lineIntensity kB T N₂ Fcal g E A u) :
    N₁ = N₂ := by
  have hU : 0 < partitionFunction kB T g E := partitionFunction_pos hg
  simp only [lineIntensity, population] at hI
  -- Pull out the positive constant `c` multiplying `N`.
  set c : ℝ := Fcal * A u * (g u * boltzmannFactor kB T (E u) / partitionFunction kB T g E)
    with hcdef
  have hc : 0 < c := by
    rw [hcdef]
    exact mul_pos (mul_pos hFcal hA)
      (div_pos (mul_pos (hg u) (boltzmannFactor_pos _ _ _)) hU)
  have hI' : c * N₁ = c * N₂ := by rw [hcdef]; ring_nf; ring_nf at hI; linarith
  exact mul_left_cancel₀ hc.ne' hI'

/-- **Target 3 — electron-density / stage-ratio identifiability via Saha.**

At fixed temperature `T` (hence fixed Saha factor `S = sahaFactor … > 0`), the Saha
density diagnostic `R ↦ n_e = S/R = electronDensityFromRatio` is **injective** on
positive stage ratios: if two positive ratios `R₁, R₂` yield the same inferred
electron density, then `R₁ = R₂`. Equivalently, the diagnostic is invertible — a
measured `n_e` back-determines the stage ratio `R` uniquely. (The forward reading
`n_e = S/R` from a known `R` is, of course, mere function evaluation; the content
here is the converse: no two distinct ratios alias to the same `n_e`.)

This is exactly the injectivity packaged from the proven strict antitonicity
`electronDensity_antitone` (`R ↦ S/R` strictly decreasing on `(0,∞)`). It rests
*only* on `S > 0`; identifiability does not — and need not — re-derive the Saha
factor's internal structure: the exponent sign `−χ/(k_B T)`, the `(3/2)` thermal
power, the spin weight `2`, and the partition-function ratio are certified
separately by `sahaFactor_pos` and the closed form `log_sahaFactor`. (`S = 0` would
make the map constantly `0`, destroying injectivity, so positivity is load-bearing.)

Non-vacuous: with `S > 0` (guaranteed by `sahaFactor_pos` under positive physical
constants/weights) and `R₁ = R₂ = 2`, both sides equal `S/2`; the antitone map
forces `R₁ = R₂`. -/
theorem electron_density_identifiability [Nonempty ι] [Nonempty κ]
    {kB T me h chi : ℝ} {gZ EZ : ι → ℝ} {gZ1 EZ1 : κ → ℝ} {R₁ R₂ : ℝ}
    (hkB : 0 < kB) (hT : 0 < T) (hme : 0 < me) (hh : 0 < h)
    (hgZ : ∀ k, 0 < gZ k) (hgZ1 : ∀ k, 0 < gZ1 k)
    (hR₁ : 0 < R₁) (hR₂ : 0 < R₂)
    (hne : electronDensityFromRatio kB T me h chi gZ EZ gZ1 EZ1 R₁
        = electronDensityFromRatio kB T me h chi gZ EZ gZ1 EZ1 R₂) :
    R₁ = R₂ := by
  -- The inverse map is strictly antitone on `(0,∞)`, hence injective there.
  have hanti : StrictAntiOn (electronDensityFromRatio kB T me h chi gZ EZ gZ1 EZ1)
      (Set.Ioi 0) := electronDensity_antitone hkB hT hme hh hgZ hgZ1
  exact hanti.injOn (Set.mem_Ioi.mpr hR₁) (Set.mem_Ioi.mpr hR₂) hne

end CflibsFormal

