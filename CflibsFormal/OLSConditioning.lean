/-
Copyright (c) 2026 Brian Squires. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Squires
-/
import Mathlib
import CflibsFormal.OLS
import CflibsFormal.Analysis

/-!
# CF-LIBS formalization — quantitative conditioning of the Boltzmann-plot normal matrix

This module upgrades the *binary* singular / non-singular rank gate for the two-column
Boltzmann-plot normal matrix (`designNormalMatrix_det_ne_zero_iff`, `OLS.lean:220`) to a
**quantitative coercivity bound** on the associated quadratic form — a lower bound on the
minimum eigenvalue obtained *purely by completing the square*, with **no spectral theory**.

## The elementary 2×2 coercivity identity

For a symmetric `M = ![![a, b], ![b, d]]` with `a, d > 0`, `Δ := a·d − b² ≥ 0`, and
`t := a + d > 0`, the pointwise Rayleigh identity

  `t · (v ⬝ᵥ M v) − Δ · (v₀² + v₁²) = (a·v₀ + b·v₁)² + (b·v₀ + d·v₁)²`

is a bare ring rearrangement whose right-hand side is manifestly nonnegative. Dividing by
`t > 0` gives the **coercivity bound** `v ⬝ᵥ M v ≥ (Δ/t) · (v₀² + v₁²)` — i.e. the coercivity
constant `Δ/t` is a lower bound on the minimum eigenvalue `λ_min`, obtained without any
eigenvalue machinery. The symmetric upper bound `v ⬝ᵥ M v ≤ t · (v₀² + v₁²)` gives
`λ_max ≤ t = trace M`; together they yield the condition-number bound `κ ≤ t²/Δ`
(`sym2x2_condition`, in cross-multiplied form to avoid division).

## Instantiation for the Boltzmann-plot design

For `designNormalMatrix E = ![![∑ Eₖ², ∑ Eₖ], ![∑ Eₖ, n]]` (`n = card ι`) the discriminant is
`Δ = n · ∑ₖ (Eₖ − Ē)² = n · SS_E` (via `det_designNormalMatrix`), so the explicit coercivity
constant is `Δ/t = n · SS_E / (∑ Eₖ² + n)` — a lower bound on `λ_min` as an explicit function
of the line-energy spread `SS_E`. As the energy variance `SS_E → 0` the constant `Δ/t → 0`:
the design degenerates toward ill-conditioning (`κ = t²/Δ → ∞`), which is the quantitative
refinement of the qualitative rank gate.

## Literature and scope

Scope tag: **PURE-MATH**. Citation: **—**. Every declaration below is elementary real
algebra of a symmetric `2×2` matrix (completing the square) plus the determinant identity
`det_designNormalMatrix` from `OLS.lean`; there is no physics content in the statements. The
condition-number reading (`λ_min ≥ Δ/t`, `λ_max ≤ t`, `κ ≤ t²/Δ`) is the textbook
diagonally-dominant / Rayleigh-quotient bound (Golub & Van Loan, *Matrix Computations*, §2.6 —
standard numerical linear algebra, not a LIBS-specific citation), specialized to the raw
(uncentered) two-column design.
-/

namespace CflibsFormal

open Matrix Finset Real
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- **Instantiation: the explicit Boltzmann-plot coercivity constant.** For the raw two-column
normal matrix `designNormalMatrix E = ![![∑ Eₖ², ∑ Eₖ], ![∑ Eₖ, n]]` (`n = card ι`), whenever
the energies are not all zero (`0 < ∑ Eₖ²`) the Rayleigh quotient is bounded below by the
explicit constant `Δ/t = n·SS_E / (∑ Eₖ² + n)`:

  `n·(∑ₖ (Eₖ − Ē)²) / (∑ Eₖ² + n) · (v₀² + v₁²) ≤ v ⬝ᵥ (designNormalMatrix E *ᵥ v)`.

The discriminant `Δ = (∑ Eₖ²)·n − (∑ Eₖ)² = n·SS_E` is supplied by `det_designNormalMatrix`
(the variance identity), so the coercivity constant is an explicit function of the line-energy
spread `SS_E`; as `SS_E → 0` it vanishes (the design degenerates to ill-conditioning). Note this is
*genuine* coercivity (a strictly positive lower bound) exactly when `SS_E > 0`; at `SS_E = 0` the
matrix is singular and the statement degrades to the positive-semidefinite bound `0 ≤ vᵀMv`. This is
the quantitative upgrade of `designNormalMatrix_det_ne_zero_iff`'s binary rank gate. -/
theorem designNormalMatrix_coercive [Nonempty ι] (E : ι → ℝ)
    (hE : 0 < ∑ k, E k ^ 2) (v : Fin 2 → ℝ) :
    (Fintype.card ι : ℝ) * (∑ k, (E k - mean E) ^ 2) / ((∑ k, E k ^ 2) + (Fintype.card ι : ℝ))
        * (v 0 ^ 2 + v 1 ^ 2)
      ≤ v ⬝ᵥ (designNormalMatrix E *ᵥ v) := by
  have hcard : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  -- `det = (∑E²)·n − (∑E)² = n·SS_E`
  have hdet : (∑ k, E k ^ 2) * (Fintype.card ι : ℝ) - (∑ k, E k) ^ 2
      = (Fintype.card ι : ℝ) * ∑ k, (E k - mean E) ^ 2 := by
    have h1 : (designNormalMatrix E).det
        = (∑ k, E k ^ 2) * (Fintype.card ι : ℝ) - (∑ k, E k) ^ 2 := by
      unfold designNormalMatrix
      rw [Matrix.det_fin_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      ring
    rw [← h1, det_designNormalMatrix]
  have hΔ : 0 ≤ (∑ k, E k ^ 2) * (Fintype.card ι : ℝ) - (∑ k, E k) ^ 2 := by
    rw [hdet]
    exact mul_nonneg hcard.le (Finset.sum_nonneg (fun k _ => sq_nonneg _))
  have hM : designNormalMatrix E
      = !![∑ k, E k ^ 2, ∑ k, E k; ∑ k, E k, (Fintype.card ι : ℝ)] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [hM, ← hdet]
  exact sym2x2_coercive (∑ k, E k ^ 2) (∑ k, E k) (Fintype.card ι : ℝ) hE hcard hΔ v

/-! ### Non-vacuity witnesses on the explicit two-line design `E = ![0, 1]` -/

/-- **Non-vacuity (hypothesis satisfiable).** Two lines at energies `E = (0, 1)` have
`∑ Eₖ² = 1 > 0`, so `hE` of `designNormalMatrix_coercive` holds on genuine data. -/
example : (0 : ℝ) < ∑ k, (![0, 1] : Fin 2 → ℝ) k ^ 2 := by
  norm_num [Fin.sum_univ_two]

/-- **Non-vacuity (constant is a concrete positive number).** For `E = (0, 1)`:
`n = 2`, `∑ Eₖ² = 1`, `SS_E = ∑ₖ (Eₖ − ½)² = ½`, so the coercivity constant is
`Δ/t = n·SS_E/(∑ Eₖ² + n) = 2·½/(1 + 2) = 1/3` — a strictly positive rational, so the bound
of `designNormalMatrix_coercive` is a genuinely non-trivial lower bound, not `0 ≤ …`. -/
example : (Fintype.card (Fin 2) : ℝ) * (∑ k, ((![0, 1] : Fin 2 → ℝ) k - mean ![0, 1]) ^ 2)
    / ((∑ k, (![0, 1] : Fin 2 → ℝ) k ^ 2) + (Fintype.card (Fin 2) : ℝ)) = 1 / 3 := by
  simp only [mean, Fin.sum_univ_two, Fintype.card_fin]
  norm_num

/-- **Non-vacuity (the bound is genuinely applied).** Instantiating `designNormalMatrix_coercive`
on `E = (0, 1)` with the test vector `v = (2, 3)` yields the concrete true inequality
`13/3 ≤ 34`: the normal matrix is `![![1, 1], ![1, 2]]`, `v ⬝ᵥ (M v) = 34`, and the coercivity
constant `1/3` times `‖v‖² = 13` gives `13/3`. The theorem's conclusion holds non-vacuously
on real data. -/
example :
    (13 : ℝ) / 3
      ≤ (![2, 3] : Fin 2 → ℝ) ⬝ᵥ (designNormalMatrix (![0, 1] : Fin 2 → ℝ) *ᵥ ![2, 3]) := by
  have h := designNormalMatrix_coercive (![0, 1] : Fin 2 → ℝ)
    (by norm_num [Fin.sum_univ_two]) (![2, 3] : Fin 2 → ℝ)
  have e1 : (Fintype.card (Fin 2) : ℝ) * (∑ k, ((![0, 1] : Fin 2 → ℝ) k - mean ![0, 1]) ^ 2)
      / ((∑ k, (![0, 1] : Fin 2 → ℝ) k ^ 2) + (Fintype.card (Fin 2) : ℝ))
      * ((![2, 3] : Fin 2 → ℝ) 0 ^ 2 + (![2, 3] : Fin 2 → ℝ) 1 ^ 2) = 13 / 3 := by
    simp only [mean, Fin.sum_univ_two, Fintype.card_fin]
    norm_num
  rw [e1] at h
  exact h

end CflibsFormal
