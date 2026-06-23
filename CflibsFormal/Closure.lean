/-
Copyright (c) 2026 Brian Squires. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Squires
-/
import Mathlib
import CflibsFormal.Boltzmann

/-!
# CF-LIBS formalization — Closure of species composition

Model a single-zone plasma with a finite index set `κ` of chemical
species (or species-stages). Given nonnegative number densities `n : κ → ℝ`
with positive total, define number fractions `C s = n s / N_tot`.

We prove the CF-LIBS closure facts:

* `composition_sum_one` — `∑ₛ C s = 1`, the normalization identity (holds
  whenever the total density is nonzero).
* `composition_nonneg` / `composition_le_one` — each fraction lies in the
  unit interval `[0, 1]`.
* `composition_mem_stdSimplex` — nonnegativity together with `∑ₛ C s = 1`: the
  composition vector lies in the standard probability simplex. This is the
  faithful statement of the CF-LIBS closure constraint `Σ Cₛ = 1`.
* `composition_smul_invariant` — fractions are invariant under rescaling all
  densities by a nonzero constant (they are intensive variables).

This mirrors the structure of `population_sum` in `CflibsFormal.Boltzmann`.
The index type is named `κ` (species/stages) to distinguish it from the
energy-level index `ι` used in `Boltzmann.lean`.
-/

namespace CflibsFormal

open Finset Real
open scoped BigOperators

variable {κ : Type*} [Fintype κ]

/-- Total number density `N_tot = ∑ₛ n s` summed over all species/stages `s`. -/
noncomputable def totalDensity (n : κ → ℝ) : ℝ :=
  ∑ s, n s

/-- Number fraction (composition) of species `s`: `C s = n s / N_tot`,
the CF-LIBS closure variable with constraint `∑ₛ C s = 1`. -/
noncomputable def composition (n : κ → ℝ) (s : κ) : ℝ :=
  n s / totalDensity n

/-- The total density is positive when at least one species exists and every
species has strictly positive density. Mirrors `partitionFunction_pos`. -/
lemma totalDensity_pos [Nonempty κ] {n : κ → ℝ}
    (hpos : ∀ s, 0 < n s) : 0 < totalDensity n := by
  unfold totalDensity
  exact Finset.sum_pos (fun s _ => hpos s) Finset.univ_nonempty

/-- **Normalization identity.** The number fractions sum to one: `∑ₛ C s = 1`,
whenever the total density is positive (the hypothesis `0 < totalDensity n`; the proof in
fact only needs it nonzero). This is an affine normalization identity;
combined with nonnegativity it gives genuine probability-simplex membership
(`composition_mem_stdSimplex`), the full CF-LIBS closure constraint. -/
theorem composition_sum_one {n : κ → ℝ}
    (hN : 0 < totalDensity n) : ∑ s, composition n s = 1 := by
  unfold composition
  rw [← Finset.sum_div, div_eq_iff hN.ne']
  simp only [totalDensity]
  ring

/-- Each number fraction is nonnegative (left end of the unit interval). -/
theorem composition_nonneg {n : κ → ℝ} (hn : ∀ s, 0 ≤ n s)
    (hN : 0 < totalDensity n) (s : κ) : 0 ≤ composition n s := by
  unfold composition
  exact div_nonneg (hn s) hN.le

/-- Each number fraction is at most one (right end of the unit interval). -/
theorem composition_le_one {n : κ → ℝ} (hn : ∀ s, 0 ≤ n s)
    (hN : 0 < totalDensity n) (s : κ) : composition n s ≤ 1 := by
  unfold composition
  rw [div_le_one hN]
  simp only [totalDensity]
  exact Finset.single_le_sum (fun t _ => hn t) (Finset.mem_univ s)

/-- **Closure as simplex membership.** With nonnegative densities and a positive
total, the composition vector lies in the standard probability simplex
`stdSimplex ℝ κ`: every fraction is nonnegative and they sum to one. This is the
faithful, fully physical statement of the CF-LIBS closure constraint `Σ Cₛ = 1`
(it requires the nonnegativity that the bare sum-to-one identity does not). -/
theorem composition_mem_stdSimplex {n : κ → ℝ} (hn : ∀ s, 0 ≤ n s)
    (hN : 0 < totalDensity n) : composition n ∈ stdSimplex ℝ κ :=
  ⟨fun s => composition_nonneg hn hN s, composition_sum_one hN⟩

/-- **Scale invariance.** Rescaling all densities by a nonzero constant `c`
leaves every number fraction unchanged: the fractions are intensive. -/
theorem composition_smul_invariant {n : κ → ℝ} {c : ℝ}
    (hc : c ≠ 0) (s : κ) :
    composition (fun t => c * n t) s = composition n s := by
  unfold composition totalDensity
  rw [← Finset.mul_sum]
  exact mul_div_mul_left (n s) (∑ t, n t) hc

end CflibsFormal
