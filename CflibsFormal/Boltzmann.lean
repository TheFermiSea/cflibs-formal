/-
Copyright (c) 2026 Brian Squires. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Squires
-/
import Mathlib

/-!
# Saha–Boltzmann formalization — Part 1: the Boltzmann distribution

Forward-model definitions for a single-zone LTE plasma at temperature `T`, with a
finite set `ι` of bound energy levels (energies `E k`, statistical weights `g k`,
Boltzmann constant `kB`, total number density `N`).

We prove the cornerstone facts the classical CF-LIBS inversion relies on:

* `population_sum` — the level populations sum to the total number density `N`
  (normalization / closure of the single-species level populations).
* `boltzmann_plot` — `log (n k / g k)` is *affine* in the level energy `E k`,
  with slope `-1 / (k_B T)`: the identity underlying the Boltzmann-plot
  temperature estimate.
* `temperature_from_two_levels` — the Boltzmann-plot slope between any two
  distinct-energy levels recovers `1 / (k_B T)` exactly.

All quantities are real. This is the forward direction; the inverse problem
(recovering `T`, `n_e`, composition from intensities) is later work.
-/

namespace CflibsFormal

open Finset Real
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- Boltzmann factor `exp(-E / (k_B T))` for a level of energy `E`. Always positive. -/
noncomputable def boltzmannFactor (kB T E : ℝ) : ℝ := Real.exp (-E / (kB * T))

lemma boltzmannFactor_pos (kB T E : ℝ) : 0 < boltzmannFactor kB T E := Real.exp_pos _

/-- Partition function `U(T) = ∑ₖ gₖ · exp(-Eₖ / (k_B T))`. -/
noncomputable def partitionFunction (kB T : ℝ) (g E : ι → ℝ) : ℝ :=
  ∑ k, g k * boltzmannFactor kB T (E k)

lemma partitionFunction_pos [Nonempty ι] {kB T : ℝ} {g E : ι → ℝ}
    (hg : ∀ k, 0 < g k) : 0 < partitionFunction kB T g E := by
  refine Finset.sum_pos (fun k _ => ?_) univ_nonempty
  exact mul_pos (hg k) (boltzmannFactor_pos _ _ _)

/-- LTE level population `nₖ = N · gₖ · exp(-Eₖ / (k_B T)) / U(T)`. -/
noncomputable def population (kB T N : ℝ) (g E : ι → ℝ) (k : ι) : ℝ :=
  N * g k * boltzmannFactor kB T (E k) / partitionFunction kB T g E

/-- **Normalization.** The level populations sum to the total number density `N`. -/
theorem population_sum [Nonempty ι] {kB T N : ℝ} {g E : ι → ℝ}
    (hg : ∀ k, 0 < g k) : ∑ k, population kB T N g E k = N := by
  have hU : partitionFunction kB T g E ≠ 0 := (partitionFunction_pos hg).ne'
  unfold population
  rw [← Finset.sum_div, div_eq_iff hU]
  simp only [partitionFunction]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun k _ => by ring)

/-- **Boltzmann-plot identity.** `log (nₖ / gₖ) = log (N / U) - Eₖ / (k_B T)`,
i.e. affine in the level energy `E k` with slope `-1 / (k_B T)`. This is the
mathematical content of the classical "temperature from the Boltzmann-plot slope"
step. -/
theorem boltzmann_plot [Nonempty ι] {kB T N : ℝ} {g E : ι → ℝ}
    (hg : ∀ k, 0 < g k) (hN : 0 < N) (k : ι) :
    Real.log (population kB T N g E k / g k)
      = Real.log (N / partitionFunction kB T g E) - E k / (kB * T) := by
  have hU : 0 < partitionFunction kB T g E := partitionFunction_pos hg
  have hgk : g k ≠ 0 := (hg k).ne'
  have hsplit : population kB T N g E k / g k
      = (N / partitionFunction kB T g E) * Real.exp (-E k / (kB * T)) := by
    simp only [population, boltzmannFactor]
    field_simp
  rw [hsplit, Real.log_mul (div_pos hN hU).ne' (Real.exp_ne_zero _), Real.log_exp]
  ring

/-- **Temperature from two levels.** The Boltzmann-plot slope between any two
distinct-energy levels recovers `1 / (k_B T)` exactly — independent of `N`, the
partition function, and the degeneracies. -/
theorem temperature_from_two_levels [Nonempty ι] {kB T N : ℝ} {g E : ι → ℝ}
    (hg : ∀ k, 0 < g k) (hN : 0 < N) (i j : ι) (hE : E i ≠ E j) :
    (Real.log (population kB T N g E j / g j)
        - Real.log (population kB T N g E i / g i)) / (E i - E j)
      = 1 / (kB * T) := by
  have hEij : E i - E j ≠ 0 := sub_ne_zero.mpr hE
  rw [boltzmann_plot hg hN i, boltzmann_plot hg hN j]
  field_simp
  ring

end CflibsFormal
