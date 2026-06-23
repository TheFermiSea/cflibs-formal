/-
Copyright (c) 2026 Brian Squires. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Squires
-/
import Mathlib
import CflibsFormal.Closure
import CflibsFormal.MultiSpecies
import CflibsFormal.Robustness

/-!
# CF-LIBS formalization — Whole-composition-vector error propagation

`Robustness.lean` bounds only *pairwise* recovered quantities (`twoLineBeta`,
`logRatioIntercept`). This module extends the reliability analysis to the **whole
normalized composition vector** `C s = composition N s = N s / ∑ₜ N t`, the
per-element reliability deliverable for many-element alloys.

Given true positive densities `N` and a perturbed recovery `Nhat` (both
`κ → ℝ`), with positive totals and a per-species absolute error bound
`|Nhat s - N s| ≤ δ`, we derive **explicit, asymptotics-free** bounds on the
composition error, generalizing the pairwise Lipschitz constants of
`Robustness.lean` to each entry of the composition vector.

* `totalDensity_abs_sub_le` — the shared CORE: the total density is stable under
  per-species perturbation with constant `card κ` (triangle inequality over the
  sum).
* `composition_sub_eq` — the exact algebraic decomposition of the composition
  error into a numerator-perturbation term and a denominator-perturbation term.
* `composition_abs_sub_le` — **HEADLINE** per-fraction stability bound:
  `|C̃ s - C s| ≤ δ/Ŝ + (N s/(S·Ŝ))·(card κ)·δ`.
* `composition_abs_sub_le_bound` — the same bound restated via the named
  `compositionErrorBound`.
* `composition_dist_vector_le` — **WHOLE-VECTOR** ℓ¹ bound:
  `∑ₛ |C̃ s - C s| ≤ 2·(card κ)·δ / Ŝ`.

All quantities are real; `composition` and `totalDensity` are reused verbatim
from `Closure.lean` (the normalization map is not redefined).
-/

namespace CflibsFormal

open Finset Real
open scoped BigOperators

variable {κ : Type*} [Fintype κ]

/-- Explicit a-priori bound on the per-species composition error
`|composition Nhat s - composition N s|` in terms of the per-species absolute
density error `delta`, the perturbed total `Shat = totalDensity Nhat`, the true
total `S = totalDensity N`, the true density `N s`, and the species count
`Fintype.card κ`. Equal to `delta/Shat + (N s/(S·Shat))·(card κ)·delta`.
Provided as a named quantity so the headline stability theorem states a clean
closed form. This is a pure algebraic packaging of the bound's right-hand side;
it is not an estimator and carries no proof obligation. -/
noncomputable def compositionErrorBound (N : κ → ℝ) (Shat delta : ℝ) (s : κ) : ℝ :=
  delta / Shat + (N s / (totalDensity N * Shat)) * (Fintype.card κ : ℝ) * delta

/-- **Total-density stability (shared CORE).** The total density is stable under a
per-species perturbation bounded by `delta`, with explicit constant `card κ`:
`|N̂_tot - N_tot| ≤ (card κ)·δ`. This is the genuinely new content beyond the
pairwise bounds of `Robustness.lean`, on which the per-fraction and whole-vector
composition bounds rest. Proved by the triangle inequality over the sum. -/
theorem totalDensity_abs_sub_le {N Nhat : κ → ℝ} {delta : ℝ}
    (hdelta : ∀ s, |Nhat s - N s| ≤ delta) :
    |totalDensity Nhat - totalDensity N| ≤ (Fintype.card κ : ℝ) * delta := by
  unfold totalDensity
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_card_nsmul _ _ delta (fun s _ => hdelta s)).trans ?_
  simp [nsmul_eq_mul, Finset.card_univ]

/-- **Exact composition-error decomposition.** The error of the normalization map
splits into a numerator-perturbation term and a denominator-perturbation term:
`C̃ s - C s = (N̂ s - N s)/Ŝ - N s·(Ŝ - S)/(S·Ŝ)`, where `S = totalDensity N`,
`Ŝ = totalDensity Nhat`. A pure field identity (both totals nonzero are
load-bearing for the divisions); the bridge that makes the explicit per-fraction
bound provable. -/
theorem composition_sub_eq {N Nhat : κ → ℝ}
    (hS : 0 < totalDensity N) (hShat : 0 < totalDensity Nhat) (s : κ) :
    composition Nhat s - composition N s
      = (Nhat s - N s) / totalDensity Nhat
        - N s * (totalDensity Nhat - totalDensity N)
          / (totalDensity N * totalDensity Nhat) := by
  unfold composition
  have hSne : totalDensity N ≠ 0 := hS.ne'
  have hShatne : totalDensity Nhat ≠ 0 := hShat.ne'
  field_simp
  ring

/-- **HEADLINE per-fraction stability bound.** The normalization map `N ↦ C` is
stable under density perturbation with an explicit, asymptotics-free constant:
`|C̃ s - C s| ≤ δ/Ŝ + (N s/(S·Ŝ))·(card κ)·δ`. This is the per-element
reliability deliverable for many-element alloys — the direct generalization of
`Robustness.twoLineBeta_stable` / `logRatioIntercept_stable` from pairwise
quantities to each entry of the whole composition vector. The hypotheses
`hN`, `hS`, `hShat` are all load-bearing (signs / nonzero denominators). -/
theorem composition_abs_sub_le {N Nhat : κ → ℝ} {delta : ℝ}
    (hN : ∀ s, 0 ≤ N s)
    (hS : 0 < totalDensity N) (hShat : 0 < totalDensity Nhat)
    (hdelta : ∀ s, |Nhat s - N s| ≤ delta) (s : κ) :
    |composition Nhat s - composition N s|
      ≤ delta / totalDensity Nhat
        + (N s / (totalDensity N * totalDensity Nhat)) * (Fintype.card κ : ℝ) * delta := by
  rw [composition_sub_eq hS hShat s]
  -- |A - B| ≤ |A| + |B| via the green Robustness.lean pattern.
  rw [sub_eq_add_neg]
  refine (abs_add_le _ _).trans ?_
  rw [abs_neg]
  have hSpos : (0 : ℝ) < totalDensity N * totalDensity Nhat := mul_pos hS hShat
  -- Bound term 1.
  have hterm1 : |(Nhat s - N s) / totalDensity Nhat| ≤ delta / totalDensity Nhat := by
    rw [abs_div, abs_of_pos hShat]
    gcongr
    exact hdelta s
  -- Bound term 2.
  have hterm2 : |N s * (totalDensity Nhat - totalDensity N)
        / (totalDensity N * totalDensity Nhat)|
      ≤ (N s / (totalDensity N * totalDensity Nhat)) * (Fintype.card κ : ℝ) * delta := by
    rw [abs_div, abs_mul, abs_of_nonneg (hN s), abs_of_pos hSpos]
    have hrhs : (N s / (totalDensity N * totalDensity Nhat)) * (Fintype.card κ : ℝ) * delta
        = N s * ((Fintype.card κ : ℝ) * delta) / (totalDensity N * totalDensity Nhat) := by
      field_simp
    rw [hrhs]
    gcongr
    · exact hN s
    · exact totalDensity_abs_sub_le hdelta
  exact add_le_add hterm1 hterm2

/-- The headline bound restated in terms of the named `compositionErrorBound`,
giving downstream callers a single clean symbol for the per-element error
budget. -/
theorem composition_abs_sub_le_bound {N Nhat : κ → ℝ} {delta : ℝ}
    (hN : ∀ s, 0 ≤ N s)
    (hS : 0 < totalDensity N) (hShat : 0 < totalDensity Nhat)
    (hdelta : ∀ s, |Nhat s - N s| ≤ delta) (s : κ) :
    |composition Nhat s - composition N s|
      ≤ compositionErrorBound N (totalDensity Nhat) delta s := by
  unfold compositionErrorBound
  exact composition_abs_sub_le hN hS hShat hdelta s

/-- **WHOLE-VECTOR error bound.** The total ℓ¹ deviation of the composition vector
is controlled by the same data with the clean closed-form constant:
`∑ₛ |C̃ s - C s| ≤ 2·(card κ)·δ / Ŝ`. The denominator-perturbation contribution
collapses using `∑ₛ N s = totalDensity N`, yielding the factor `2`. This is the
aggregate reliability statement for many-element alloys. -/
theorem composition_dist_vector_le {N Nhat : κ → ℝ} {delta : ℝ}
    (hN : ∀ s, 0 ≤ N s)
    (hS : 0 < totalDensity N) (hShat : 0 < totalDensity Nhat)
    (hdelta : ∀ s, |Nhat s - N s| ≤ delta) :
    ∑ s, |composition Nhat s - composition N s|
      ≤ 2 * (Fintype.card κ : ℝ) * delta / totalDensity Nhat := by
  refine (Finset.sum_le_sum
    (fun s _ => composition_abs_sub_le hN hS hShat hdelta s)).trans ?_
  -- ∑ s, (delta/Shat + (N s/(S*Shat))*card*delta)
  rw [Finset.sum_add_distrib]
  -- First summand: ∑ s, delta/Shat = card * (delta/Shat).
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  -- Second summand: pull out the common factors so the N s sum is exposed.
  have hSpos : (0 : ℝ) < totalDensity N * totalDensity Nhat := mul_pos hS hShat
  have hrw : ∀ s, (N s / (totalDensity N * totalDensity Nhat))
        * (Fintype.card κ : ℝ) * delta
      = N s * ((Fintype.card κ : ℝ) * delta / (totalDensity N * totalDensity Nhat)) := by
    intro s
    field_simp
  rw [Finset.sum_congr rfl (fun s _ => hrw s)]
  rw [← Finset.sum_mul]
  -- ∑ s, N s = totalDensity N
  have hsumN : ∑ s, N s = totalDensity N := rfl
  rw [hsumN]
  -- Now: card * (delta/Shat) + S * (card*delta/(S*Shat)) = 2*card*delta/Shat (equality)
  have hSne : totalDensity N ≠ 0 := hS.ne'
  have hShatne : totalDensity Nhat ≠ 0 := hShat.ne'
  apply le_of_eq
  field_simp
  ring

end CflibsFormal
