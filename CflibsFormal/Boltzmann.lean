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
(recovering `T`, `n_e`, composition from intensities) is treated in later modules
(`Classic`, `Inverse`, `Identifiability`, `SahaInverse`).

## Literature

The physics-tagged results of this module cite the following keys in
`docs/scope-tags.tsv`; the full reference and what was checked for each is in
`docs/citation-whitelist.tsv`.

* Boltzmann — status CONVENTION (the name of a law or equation, not a bibliographic reference).
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

section LevelCutoff

/-! ### Truncated partition function (frontier FT-05)

`partitionFunctionCut` sums the Boltzmann terms of the levels strictly below a cutoff energy.
Owner decision D17 fixes the level-cutoff policy: continuous policies only, with Hummer–Mihalas
occupation probabilities as the physics candidate and a fixed sharp cutoff at the unperturbed
ionization energy as the baseline; the `n_e`-dependent sharp cutoff is retired. With a fixed
`cut` this definition is that baseline. The results below are properties of finite exponential
sums (`PURE-MATH`). -/

/-- **Truncated partition function** `U_cut(T) = ∑_{k : E k < cut} g k · exp(−E k/(k_B T))`: the
Boltzmann sum `partitionFunction` restricted to the levels strictly below the cutoff energy
`cut`. Convention: a level with `E k < cut` is kept; a level with `cut ≤ E k`, including one
exactly at the cutoff, is dropped. `cut` is a free real in the units of `E` (energies measured
from the stage's ground state). With `cut` a fixed constant (the unperturbed ionization energy)
this is the fixed-cutoff baseline of owner decision D17. The definition evaluates the sum at the
given `cut` and asserts no value for it; an `n_e`-dependent sharp cutoff, which D17 retires,
would make `U_cut` discontinuous in `n_e`. -/
noncomputable def partitionFunctionCut (kB T cut : ℝ) (g E : ι → ℝ) : ℝ :=
  ∑ k ∈ univ.filter (fun k => E k < cut), g k * boltzmannFactor kB T (E k)

/-- **Kept/dropped split of the partition function.** `U = U_cut + D`, with `D` the Boltzmann
sum over the dropped levels (`cut ≤ E k`). `PURE-MATH`: a finite-sum identity. -/
lemma partitionFunction_eq_cut_add_tail (kB T cut : ℝ) (g E : ι → ℝ) :
    partitionFunction kB T g E = partitionFunctionCut kB T cut g E
      + ∑ k ∈ univ.filter (fun k => cut ≤ E k), g k * boltzmannFactor kB T (E k) := by
  unfold partitionFunction partitionFunctionCut
  rw [← Finset.sum_filter_add_sum_filter_not univ (fun k => E k < cut)]
  simp only [not_lt]

/-- **The truncated partition function is positive** once one level is kept (`hkeep`) and the
weights are positive. `PURE-MATH`. -/
lemma partitionFunctionCut_pos {kB T cut : ℝ} {g E : ι → ℝ} (hg : ∀ k, 0 < g k)
    (hkeep : ∃ k, E k < cut) : 0 < partitionFunctionCut kB T cut g E := by
  obtain ⟨k0, hk0⟩ := hkeep
  exact Finset.sum_pos (fun k _ => mul_pos (hg k) (boltzmannFactor_pos _ _ _))
    ⟨k0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk0⟩⟩

/-- Termwise sign crux: for a kept level `Ek < cut` and a dropped level `cut ≤ Ed`,
`bf(T1, Ed)·bf(T2, Ek) < bf(T2, Ed)·bf(T1, Ek)` when `0 < T1 < T2`. -/
private lemma bf_cross_lt {kB T1 T2 cut Ed Ek : ℝ} (hkB : 0 < kB) (hT1 : 0 < T1)
    (hT12 : T1 < T2) (hk : Ek < cut) (hd : cut ≤ Ed) :
    boltzmannFactor kB T1 Ed * boltzmannFactor kB T2 Ek
      < boltzmannFactor kB T2 Ed * boltzmannFactor kB T1 Ek := by
  unfold boltzmannFactor
  rw [← Real.exp_add, ← Real.exp_add, Real.exp_lt_exp]
  have hkT1 : 0 < kB * T1 := mul_pos hkB hT1
  have hβ : 1 / (kB * T2) < 1 / (kB * T1) :=
    one_div_lt_one_div_of_lt hkT1 (mul_lt_mul_of_pos_left hT12 hkB)
  have e1 : -Ed / (kB * T1) + -Ek / (kB * T2)
      = -(Ed * (1 / (kB * T1))) - Ek * (1 / (kB * T2)) := by ring
  have e2 : -Ed / (kB * T2) + -Ek / (kB * T1)
      = -(Ed * (1 / (kB * T2))) - Ek * (1 / (kB * T1)) := by ring
  rw [e1, e2]
  nlinarith [mul_pos (sub_pos.mpr (lt_of_lt_of_le hk hd)) (sub_pos.mpr hβ)]

/-- **The truncation ratio is strictly increasing in temperature (FT-05 (ii)).**

If at least one level is kept (`hkeep`) and at least one is dropped (`hdrop`), the ratio
`U(T)/U_cut(T)` of the full to the truncated partition function is strictly increasing in `T`
on `(0, ∞)`. Writing `U = U_cut + D` with `D` the sum over dropped levels,
`U/U_cut = 1 + D/U_cut`, and, for `T1 < T2`, cross-multiplying by `U_cut(T1)·U_cut(T2) > 0`
reduces the claim to `D(T1)·U_cut(T2) < D(T2)·U_cut(T1)`: a double sum over (dropped `d`, kept
`k`) pairs in which each term's exponent gap is `(1/(k_B T1) − 1/(k_B T2))·(E_d − E_k) > 0`,
since `E_d ≥ cut > E_k`. No gap, sign or ordering hypothesis on the energies is needed beyond
`hkeep`/`hdrop`, because every dropped level lies above every kept one. Consequence (follow-up
results, not proved here): the ratio is injective in `T`, so no temperature-independent factor,
such as a `gA` calibration, can absorb a change of cutoff at two distinct temperatures.

Hypotheses and why each is present:
* `hkB : 0 < kB`: `1/(k_B T)` is then strictly decreasing in `T` on `(0, ∞)`.
* `hg : ∀ k, 0 < g k`: makes `U_cut > 0` (with `hkeep`) and supplies strictness.
* `hkeep`: otherwise `U_cut = 0` and the ratio is Lean's junk value `0`.
* `hdrop`: otherwise the ratio is identically `1`, not strictly increasing.

Scope (two-axis): own relation PURE-MATH (a property of finite exponential sums; no physical
claim); definitions used: `partitionFunction` (the Boltzmann sum over the supplied list) and
`partitionFunctionCut` (the sum over the kept levels, at any fixed `cut`); published tag
PURE-MATH. -/
theorem cutRatio_strictMonoOn_temp {kB cut : ℝ} {g E : ι → ℝ} (hkB : 0 < kB)
    (hg : ∀ k, 0 < g k) (hkeep : ∃ k, E k < cut) (hdrop : ∃ k, cut ≤ E k) :
    StrictMonoOn (fun T => partitionFunction kB T g E / partitionFunctionCut kB T cut g E)
      (Set.Ioi 0) := by
  intro T1 hT1 T2 hT2 hlt
  simp only [Set.mem_Ioi] at hT1 hT2
  change partitionFunction kB T1 g E / partitionFunctionCut kB T1 cut g E
      < partitionFunction kB T2 g E / partitionFunctionCut kB T2 cut g E
  have hK1 : 0 < partitionFunctionCut kB T1 cut g E := partitionFunctionCut_pos hg hkeep
  have hK2 : 0 < partitionFunctionCut kB T2 cut g E := partitionFunctionCut_pos hg hkeep
  obtain ⟨d0, hd0⟩ := hdrop
  obtain ⟨k0, hk0⟩ := hkeep
  have hdropN : (univ.filter (fun k => cut ≤ E k)).Nonempty :=
    ⟨d0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd0⟩⟩
  have hkeepN : (univ.filter (fun k => E k < cut)).Nonempty :=
    ⟨k0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk0⟩⟩
  have hcross :
      (∑ k ∈ univ.filter (fun k => cut ≤ E k), g k * boltzmannFactor kB T1 (E k))
          * partitionFunctionCut kB T2 cut g E
        < (∑ k ∈ univ.filter (fun k => cut ≤ E k), g k * boltzmannFactor kB T2 (E k))
          * partitionFunctionCut kB T1 cut g E := by
    simp only [partitionFunctionCut, Finset.sum_mul_sum]
    exact Finset.sum_lt_sum_of_nonempty hdropN
      (fun d hd =>
        Finset.sum_lt_sum_of_nonempty hkeepN
          (fun k hk =>
            have hd' := (Finset.mem_filter.mp hd).2
            have hk' := (Finset.mem_filter.mp hk).2
            calc g d * boltzmannFactor kB T1 (E d) * (g k * boltzmannFactor kB T2 (E k))
                = (g d * g k) * (boltzmannFactor kB T1 (E d) * boltzmannFactor kB T2 (E k)) := by
                  ring
              _ < (g d * g k) * (boltzmannFactor kB T2 (E d) * boltzmannFactor kB T1 (E k)) :=
                  mul_lt_mul_of_pos_left (bf_cross_lt hkB hT1 hlt hk' hd')
                    (mul_pos (hg d) (hg k))
              _ = g d * boltzmannFactor kB T2 (E d) * (g k * boltzmannFactor kB T1 (E k)) := by
                  ring))
  rw [partitionFunction_eq_cut_add_tail kB T1 cut, partitionFunction_eq_cut_add_tail kB T2 cut,
    div_lt_div_iff₀ hK1 hK2]
  nlinarith [hcross]

end LevelCutoff

end CflibsFormal
