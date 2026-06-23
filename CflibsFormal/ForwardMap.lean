/-
Copyright (c) 2026 Brian Squires. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Squires
-/
import Mathlib
import CflibsFormal.Boltzmann

/-!
# Saha–Boltzmann formalization — Part 4: the optically-thin forward map

The optically-thin line-emission forward model for CF-LIBS. For a bound-bound
transition with **upper level** `k` of an emitting species/stage, the integrated
line intensity is

  `I_{ki} = Fcal · A_{ki} · n_k`,

where `n_k = population kB T N g E k` is the LTE upper-level number density (reused
verbatim from `Boltzmann.lean`), `A_{ki}` is the Einstein spontaneous-emission
coefficient, and `Fcal` is the instrument/geometry constant (absorbing
`h c / 4π λ_{ki}`).

We prove the key CF-LIBS identities that *lift* the population-level Boltzmann plot
to **observable** intensities:

* `lineIntensity_pos` — the model is a positive observable given positive inputs.
* `boltzmann_plot_intensity` — `log (I_{ki} / (g_k A_{ki}))` is *affine* in the
  upper-level energy `E k`, with slope `-1 / (k_B T)` and intercept
  `log (Fcal · N / U(T))`. This is the core of CF-LIBS temperature determination:
  it lifts `boltzmann_plot` from level populations to measured intensities.
* `temperature_from_two_lines` — the intensity-Boltzmann-plot slope between any two
  distinct-energy lines of the same species recovers `1 / (k_B T)` exactly, with the
  calibration `Fcal`, number density `N`, partition function `U`, degeneracies `g`,
  and Einstein coefficients `A` all cancelling.

All quantities are real. This is the forward direction.
-/

namespace CflibsFormal

open Finset Real
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- Integrated intensity of the optically-thin emission line for the bound-bound
transition with **upper level** `k`:
  `I_{ki} = Fcal · A_k · n_k`,
where `n_k = population kB T N g E k = N · g_k · exp(-E_k/(k_B T)) / U(T)` is the LTE
upper-level number density (reused verbatim from `Boltzmann.lean`), `A k = A_{ki}` is the
**per-line** Einstein spontaneous-emission coefficient (each transition has its own
`A`, hence `A : ι → ℝ`), and `Fcal` is the instrument/geometry constant (absorbing
`h c / 4π λ_{ki}`). Expanding `population`,
  `I_{ki} = Fcal · (g_k · A_k / U(T)) · N · exp(-E_k/(k_B T))`,
the CF-LIBS forward line-emission model. -/
noncomputable def lineIntensity (kB T N Fcal : ℝ) (g E A : ι → ℝ) (k : ι) : ℝ :=
  Fcal * A k * population kB T N g E k

/-- **Positivity of the observable.** The line intensity is positive given positive
calibration, density, Einstein coefficient, and degeneracies. Establishes the model is
physically well-posed and is the precondition for taking `Real.log` below. -/
theorem lineIntensity_pos [Nonempty ι] {kB T N Fcal : ℝ} {g E A : ι → ℝ}
    (hg : ∀ k, 0 < g k) (hN : 0 < N) (hFcal : 0 < Fcal) (hA : ∀ k, 0 < A k) (k : ι) :
    0 < lineIntensity kB T N Fcal g E A k := by
  unfold lineIntensity population
  exact mul_pos (mul_pos hFcal (hA k))
    (div_pos (mul_pos (mul_pos hN (hg k)) (boltzmannFactor_pos _ _ _))
      (partitionFunction_pos hg))

/-- **Intensity Boltzmann-plot identity.** `log (I_{ki} / (g_k A)) = log (Fcal · N / U)
- E_k / (k_B T)`, i.e. the Boltzmann plot built from *measured* line intensities is
affine in the upper-level energy `E k` with slope `-1 / (k_B T)` and intercept
`log (Fcal · N / U(T))`. This lifts `boltzmann_plot` from level populations to
observables — the core of CF-LIBS temperature determination. -/
theorem boltzmann_plot_intensity [Nonempty ι] {kB T N Fcal : ℝ} {g E A : ι → ℝ}
    (hg : ∀ k, 0 < g k) (hN : 0 < N) (hFcal : 0 < Fcal) (hA : ∀ k, 0 < A k) (k : ι) :
    Real.log (lineIntensity kB T N Fcal g E A k / (g k * A k))
      = Real.log (Fcal * N / partitionFunction kB T g E) - E k / (kB * T) := by
  have hU : 0 < partitionFunction kB T g E := partitionFunction_pos hg
  have hgk : g k ≠ 0 := (hg k).ne'
  have hAne : A k ≠ 0 := (hA k).ne'
  have hsplit : lineIntensity kB T N Fcal g E A k / (g k * A k)
      = (Fcal * N / partitionFunction kB T g E) * Real.exp (-E k / (kB * T)) := by
    simp only [lineIntensity, population, boltzmannFactor]
    field_simp
  rw [hsplit, Real.log_mul (div_pos (by positivity) hU).ne' (Real.exp_ne_zero _),
    Real.log_exp]
  ring

/-- **Temperature from two lines.** The slope of the intensity Boltzmann plot between
any two distinct-energy lines of the same species recovers `1 / (k_B T)` exactly. The
calibration `Fcal`, number density `N`, partition function `U`, degeneracies `g`, and
Einstein coefficients `A` all cancel. (`hE` prevents division by zero; the identity is
physically meaningful for `k_B T ≠ 0`.) -/
theorem temperature_from_two_lines [Nonempty ι] {kB T N Fcal : ℝ} {g E A : ι → ℝ}
    (hg : ∀ k, 0 < g k) (hN : 0 < N) (hFcal : 0 < Fcal) (hA : ∀ k, 0 < A k)
    (i j : ι) (hE : E i ≠ E j) :
    (Real.log (lineIntensity kB T N Fcal g E A j / (g j * A j))
        - Real.log (lineIntensity kB T N Fcal g E A i / (g i * A i))) / (E i - E j)
      = 1 / (kB * T) := by
  have hEij : E i - E j ≠ 0 := sub_ne_zero.mpr hE
  rw [boltzmann_plot_intensity hg hN hFcal hA i,
    boltzmann_plot_intensity hg hN hFcal hA j]
  field_simp
  ring

end CflibsFormal
