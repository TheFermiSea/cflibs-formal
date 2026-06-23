/-
Copyright (c) 2026 Brian Squires. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Squires
-/
import Mathlib
import CflibsFormal.SelfAbsorption
import CflibsFormal.Inverse
import CflibsFormal.ForwardMap
import CflibsFormal.Identifiability
import CflibsFormal.Closure

/-!
# Self-absorption coupled into the inverse problem — identifiability preserved vs. lost

This module folds the optically-thick (self-absorbed) forward map of `SelfAbsorption.lean`
into the inverse-problem framework of `Inverse.lean`, and characterizes exactly when
self-absorption preserves or destroys composition identifiability.

The measured observable for species `s` is the **self-absorbed** intensity of its single
emitting line `emit s` at per-line optical depth `tau s`, reusing
`SelfAbsorption.selfAbsorbedIntensity` (`= lineIntensity · SA(tau s)`).

We prove the two-sided result:

* **PRESERVED (known `τ`).** `thick_density_identifiability` /
  `thick_composition_identifiability`: if two parameter sets produce equal optically-thick
  observations at **matched, known** optical depths `tau`, then (with the usual
  nondegeneracy and shared `T` / calibration / atomic data) they have equal densities and
  equal composition. The known positive `SA(tau)` cancels per line, reducing the thick
  case to the proven thin `density_identifiability` — the exact curve-of-growth correction.

* **LOST (unknown `τ`).** `selfAbsorption_breaks_identifiability`: for fixed atomic data
  and `T`, two **genuinely different** densities at **different** optical depths produce the
  **same** measured thick intensity, because a single line constrains only the product
  `N · SA(τ)`. A concrete, IVT-free witness using `SA(0) = 1` and `SA(1) = 1 - exp(-1)`.

Reuses `SelfAbsorption` and `Identifiability` verbatim; nothing is reproven. The only new
algebraic helper is `lineIntensity_smul_left` (the `N`-linearity of the forward map), the
root of the density/self-absorption degeneracy.
-/

namespace CflibsFormal

open Finset Real
open scoped BigOperators

variable {species levelIndex : Type*}

/-- **`N`-linearity of the optically-thin forward map.** Scaling the species density by a
constant `c` scales the line intensity by the same `c`:
`lineIntensity … (c · N) … = c · lineIntensity … N …`. This is the structural fact the
LOST construction exploits — the measured intensity constrains only the product `N · SA(τ)`,
so density and self-absorption cannot be separated from a single line. (`ForwardMap` proves
positivity and the Boltzmann-plot identity, never this linearity, so this is a genuine new
helper, not a reproof.) -/
theorem lineIntensity_smul_left {ι : Type*} [Fintype ι] (kB T N Fcal c : ℝ)
    (g E A : ι → ℝ) (k : ι) :
    lineIntensity kB T (c * N) Fcal g E A k = c * lineIntensity kB T N Fcal g E A k := by
  unfold lineIntensity population
  ring

/-- **Optically-thick observation map.** The self-absorption-aware analogue of
`Inverse.observe`: the observable for species `s` is the **measured** (self-absorbed)
intensity of its single emitting line `emit s` at per-line optical depth `tau s`, reusing
`SelfAbsorption.selfAbsorbedIntensity` verbatim. When `tau ≡ 0` this collapses to
`Inverse.observe`, since `SA 0 = 1`. -/
noncomputable def thickObserve [Fintype levelIndex] (kB Fcal : ℝ)
    (emit : species → levelIndex) (tau : species → ℝ)
    (p : PlasmaParams species levelIndex) (s : species) : ℝ :=
  selfAbsorbedIntensity kB p.T (p.N s) Fcal p.g p.E p.A (emit s) (tau s)

/-- **PRESERVED (known, matched `τ`) — per-species density identifiability.** If two
densities produce equal **measured** thick intensities of the same line at the **same**
known optical depth `tau`, then the densities are equal. The known positive `SA(tau)`
cancels, reducing to the proven thin `density_identifiability`. This is exactly the
curve-of-growth correction (`lineIntensity_eq_selfAbsorbedIntensity_div`) made injective:
self-absorption is invertible when its optical depth is known. -/
theorem thick_density_identifiability {ι : Type*} [Fintype ι] [Nonempty ι]
    {kB T Fcal : ℝ} {g E A : ι → ℝ} {N₁ N₂ : ℝ}
    (hg : ∀ k, 0 < g k) (hFcal : 0 < Fcal) (u : ι) (hA : 0 < A u)
    {tau : ℝ} (htau : 0 ≤ tau)
    (hI : selfAbsorbedIntensity kB T N₁ Fcal g E A u tau
        = selfAbsorbedIntensity kB T N₂ Fcal g E A u tau) :
    N₁ = N₂ := by
  have hSA := selfAbsorptionFactor_pos htau
  unfold selfAbsorbedIntensity at hI
  exact density_identifiability hg hFcal u hA (mul_right_cancel₀ hSA.ne' hI)

variable [Fintype species]

/-- **PRESERVED (known, matched `τ`) — multi-species composition identifiability.** With
shared `T`, calibration `Fcal`, and atomic data `g E A`, if two admissible parameter sets
produce equal **measured** thick spectra at **matched, known** optical depths `tau`, then
they have equal closure composition. Per line the known `SA(tau s)` cancels (via
`thick_density_identifiability`), giving equal `N s` for every species, hence equal
`trueComposition`. The direct self-absorption analogue of `general_identifiability`'s
composition conclusion; `T` equality is supplied honestly (one line per species cannot pin
`T`), and `tau` being matched/known is precisely the PRESERVED hypothesis.

`trueComposition` is the estimator-independent target, so the statement is non-tautological. -/
theorem thick_composition_identifiability [Fintype levelIndex] [Nonempty levelIndex]
    {kB Fcal₁ Fcal₂ : ℝ} {emit : species → levelIndex} {tau : species → ℝ}
    {p₁ p₂ : PlasmaParams species levelIndex}
    (ha₁ : p₁.Admissible) (_ha₂ : p₂.Admissible)
    (hgeq : p₁.g = p₂.g) (hEeq : p₁.E = p₂.E) (hAeq : p₁.A = p₂.A)
    (hTeq : p₁.T = p₂.T) (hFcal₁ : 0 < Fcal₁) (hFeq : Fcal₁ = Fcal₂)
    (htau : ∀ s, 0 ≤ tau s)
    (hObs : thickObserve kB Fcal₁ emit tau p₁ = thickObserve kB Fcal₂ emit tau p₂) :
    ∀ s, trueComposition p₁ s = trueComposition p₂ s := by
  obtain ⟨hT₁, hN₁, hg₁, hA₁⟩ := ha₁
  have hNeq : ∀ s, p₁.N s = p₂.N s := by
    intro s
    have hObs_s :
        selfAbsorbedIntensity kB p₁.T (p₁.N s) Fcal₁ p₁.g p₁.E p₁.A (emit s) (tau s)
          = selfAbsorbedIntensity kB p₂.T (p₂.N s) Fcal₂ p₂.g p₂.E p₂.A (emit s) (tau s) := by
      have := congrFun hObs s
      simpa only [thickObserve] using this
    rw [← hTeq, ← hFeq, ← hgeq, ← hEeq, ← hAeq] at hObs_s
    exact thick_density_identifiability hg₁ hFcal₁ (emit s) (hA₁ (emit s)) (htau s) hObs_s
  have hNfun : p₁.N = p₂.N := funext hNeq
  intro s
  simp only [trueComposition, hNfun]

/-- **LOST (unknown `τ`) — self-absorption breaks identifiability.** For fixed atomic data
and `T`, there exist two **genuinely different** densities `N₁ ≠ N₂` at optical depths
`tau₁`, `tau₂` whose **measured** thick intensities coincide. A single line cannot separate
density from self-absorption — the measurement constrains only the product `N · SA(τ)`.

Concrete, IVT-free witness: `tau₁ = 0`, `tau₂ = 1`, `N₁ = (1 - exp(-1)) · N`, `N₂ = N`.
Then `SA(0) = 1`, `SA(1) = 1 - exp(-1)`, and both measured intensities equal
`(1 - exp(-1)) · lineIntensity(… N …)` by `N`-linearity. `N₁ ≠ N₂` since `exp(-1) ≠ 0`.
The smaller `N₁ < N₂` is the classic self-absorption density bias. This precisely
characterizes when self-absorption destroys composition identifiability. -/
theorem selfAbsorption_breaks_identifiability {ι : Type*} [Fintype ι] [Nonempty ι]
    (kB T Fcal : ℝ) (g E A : ι → ℝ) (u : ι) (N : ℝ) (hN : 0 < N) :
    ∃ (N₁ N₂ tau₁ tau₂ : ℝ), 0 ≤ tau₁ ∧ 0 ≤ tau₂ ∧ N₁ ≠ N₂ ∧
      selfAbsorbedIntensity kB T N₁ Fcal g E A u tau₁
        = selfAbsorbedIntensity kB T N₂ Fcal g E A u tau₂ := by
  refine ⟨(1 - Real.exp (-1)) * N, N, 0, 1, le_refl 0, zero_le_one, ?_, ?_⟩
  · -- `(1 - exp(-1)) · N ≠ N`, since `1 - exp(-1) < 1` and `0 < N`.
    have hlt : (1 - Real.exp (-1)) < 1 := by
      have := Real.exp_pos (-1)
      linarith
    have hne : (1 - Real.exp (-1)) * N < N := by
      have := mul_lt_mul_of_pos_right hlt hN
      rwa [one_mul] at this
    exact ne_of_lt hne
  · -- Both measured intensities equal `(1 - exp(-1)) · lineIntensity(… N …)`.
    unfold selfAbsorbedIntensity
    rw [selfAbsorptionFactor, if_pos rfl, selfAbsorptionFactor, if_neg one_ne_zero,
      div_one, lineIntensity_smul_left]
    ring

end CflibsFormal
