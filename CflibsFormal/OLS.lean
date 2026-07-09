/-
Copyright (c) 2026 Brian Squires. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Squires
-/
import Mathlib

/-!
# CF-LIBS formalization — the ordinary-least-squares algebraic foundation

This module holds the **pure-algebra OLS machinery** — `mean`, `olsSlope`, `olsIntercept`,
`olsWeight`, the centering identities (`centered_sum_zero`, `mean_affine`,
`olsSlope_eq_centered`, `olsSlope_sub_eq`, `centered_mul_self`), the noise gain
(`olsSlope_noise_gain`), and the noise-free recovery `ols_recovers_line` — shared across the
project:

* `Alt.LeastSquares` (the Boltzmann-plot OLS estimator),
* `ErrorBudget` (deterministic error propagation),
* `Alt.OLSVariance` / `Alt.GaussMarkov` (the probabilistic / optimality statistics layers).

The ordinary-least-squares foundation is **pure algebra** — no physics — so this module is
`Mathlib`-only (`import Mathlib`, nothing from `CflibsFormal`). It is the single home for these
declarations so that no downstream module re-derives them: the Boltzmann-plot estimator, the
error budget, and the Gauss–Markov variance law all `import CflibsFormal.OLS` and reuse them
verbatim.

All declarations are pure-algebra and need only `[Fintype ι]` / `[Nonempty ι]`.
-/

namespace CflibsFormal

open Finset Real
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- Arithmetic mean of `f` over the `Fintype` of lines: `(∑ k, f k) / card ι`. A plain
algebraic helper (no specific citation); `Ebar = mean E`, `ybar = mean y`. The division by
`card ι` is genuine (not `0/0`) under `[Nonempty ι]`. -/
noncomputable def mean (f : ι → ℝ) : ℝ := (∑ k, f k) / (Fintype.card ι)

/-- Ordinary-least-squares slope of the Boltzmann-plot points `(E k, y k)`: covariance over
variance,
  `(∑_k (E k − mean E)(y k − mean y)) / (∑_k (E k − mean E)²)`.
The least-squares fit over all lines of a species (Tognoni et al. 2010). -/
noncomputable def olsSlope (E y : ι → ℝ) : ℝ :=
  (∑ k, (E k - mean E) * (y k - mean y)) / (∑ k, (E k - mean E) ^ 2)

/-- Ordinary-least-squares intercept `b = ybar − m·Ebar`. By the Boltzmann-plot identity
this intercept carries the species concentration via `b = log (Fcal·N/U)` (Ciucci et al.
1999). -/
noncomputable def olsIntercept (E y : ι → ℝ) : ℝ :=
  mean y - olsSlope E y * mean E

/-- **Gauss–Markov weight** `wₖ = (Eₖ − Ē)/SS_E` with `SS_E = ∑ⱼ (Eⱼ − Ē)²`. Written in the exact
form of `olsSlope_noise_gain`'s summand (below) so that `∑ₖ wₖ² = 1/SS_E` rewrites literally.
With these weights `β̂(y) = ∑ₖ wₖ yₖ` (`olsSlope_eq_centered`), `∑ₖ wₖ = 0`, and `∑ₖ wₖ Eₖ = 1`. -/
noncomputable def olsWeight (E : ι → ℝ) (k : ι) : ℝ :=
  (E k - mean E) / (∑ j, (E j - mean E) ^ 2)

/-- The centered energies sum to zero: `∑ₖ (Eₖ − Ē) = 0`. The lever that makes the OLS slope a
*centered-linear* functional of the ordinates (the `mean y` term drops out). Needs at least one
line (`[Nonempty ι]`, so `card ι ≠ 0`). -/
theorem centered_sum_zero [Nonempty ι] (E : ι → ℝ) :
    ∑ k, (E k - mean E) = 0 := by
  have hcard : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  unfold mean
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp
  ring

/-- **Mean of an affine transform.** `mean (m0·E + b0) = m0·mean E + b0`. Isolates the only
Finset-sum content of the intercept recovery so the variance/covariance identity stays
readable. -/
theorem mean_affine [Nonempty ι] (E : ι → ℝ) (m0 b0 : ℝ) :
    mean (fun k => m0 * E k + b0) = m0 * mean E + b0 := by
  have hcard : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  unfold mean
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  field_simp

/-- **OLS slope is centered-linear in the ordinates.** `olsSlope E y =
(∑ₖ (Eₖ − Ē)·yₖ) / SS_E`: centering kills the `mean y` term because `∑ (Eₖ − Ē) = 0`. This is
the representation `β̂(y) = ∑ₖ wₖ yₖ` with weights `wₖ = (Eₖ − Ē)/SS_E` on which every
sensitivity bound below rests. -/
theorem olsSlope_eq_centered [Nonempty ι] (E y : ι → ℝ) :
    olsSlope E y = (∑ k, (E k - mean E) * y k) / (∑ k, (E k - mean E) ^ 2) := by
  unfold olsSlope
  congr 1
  have h0 : ∑ k, (E k - mean E) = 0 := centered_sum_zero E
  calc ∑ k, (E k - mean E) * (y k - mean y)
      = ∑ k, ((E k - mean E) * y k - (E k - mean E) * mean y) := by
        refine Finset.sum_congr rfl (fun k _ => ?_); ring
    _ = (∑ k, (E k - mean E) * y k) - (∑ k, (E k - mean E)) * mean y := by
        rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
    _ = ∑ k, (E k - mean E) * y k := by rw [h0]; ring

/-- **Slope perturbation is linear in the ordinate perturbation.**
`olsSlope E ŷ − olsSlope E y = (∑ₖ (Eₖ − Ē)(ŷₖ − yₖ)) / SS_E`. The bridge for the Lipschitz
bounds: the slope error is the centered-energy-weighted sum of the per-line ordinate errors. -/
theorem olsSlope_sub_eq [Nonempty ι] (E y yHat : ι → ℝ) :
    olsSlope E yHat - olsSlope E y
      = (∑ k, (E k - mean E) * (yHat k - y k)) / (∑ k, (E k - mean E) ^ 2) := by
  rw [olsSlope_eq_centered E yHat, olsSlope_eq_centered E y, div_sub_div_same]
  congr 1
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  ring

/-- **Centered–energy identity** `∑ₖ (Eₖ − Ē)·Eₖ = ∑ₖ (Eₖ − Ē)² = SS_E`. The `mean E` term drops
because `∑ₖ (Eₖ − Ē) = 0` (`centered_sum_zero`). Isolated so the estimator algebra stays clean. -/
theorem centered_mul_self [Nonempty ι] (E : ι → ℝ) :
    ∑ k, (E k - mean E) * E k = ∑ k, (E k - mean E) ^ 2 := by
  have h0 : ∑ k, (E k - mean E) = 0 := centered_sum_zero E
  calc ∑ k, (E k - mean E) * E k
      = ∑ k, ((E k - mean E) ^ 2 + (E k - mean E) * mean E) :=
        Finset.sum_congr rfl (fun k _ => by ring)
    _ = ∑ k, (E k - mean E) ^ 2 := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, h0, zero_mul, add_zero]

/-- **OLS slope noise gain.** `∑ₖ wₖ² = 1/SS_E` for the weights `wₖ = (Eₖ − Ē)/SS_E`. This is
the deterministic kernel of the Gauss–Markov variance law `Var(β̂) = σ²·∑ wₖ² = σ²/SS_E`: under
independent ordinate noise of variance `σ²` the slope variance is `σ²/SS_E`, which (with
`SS_E ≈ N·Var(E)`) is the principled origin of the "more lines ⇒ better" rule. The probabilistic
`Var` layer is formalized in `Alt.OLSVariance` (`olsSlope_variance_eq`); this identity is its
purely-algebraic kernel. -/
theorem olsSlope_noise_gain (E : ι → ℝ) (hvar : 0 < ∑ k, (E k - mean E) ^ 2) :
    ∑ k, ((E k - mean E) / (∑ j, (E j - mean E) ^ 2)) ^ 2
      = 1 / (∑ k, (E k - mean E) ^ 2) := by
  have hS : (∑ k, (E k - mean E) ^ 2) ≠ 0 := hvar.ne'
  calc ∑ k, ((E k - mean E) / (∑ j, (E j - mean E) ^ 2)) ^ 2
      = ∑ k, (E k - mean E) ^ 2 / (∑ j, (E j - mean E) ^ 2) ^ 2 := by
        refine Finset.sum_congr rfl (fun k _ => ?_); rw [div_pow]
    _ = (∑ k, (E k - mean E) ^ 2) / (∑ j, (E j - mean E) ^ 2) ^ 2 := by rw [← Finset.sum_div]
    _ = 1 / (∑ k, (E k - mean E) ^ 2) := by rw [sq]; field_simp

/-- **THE CRUX.** In the noise-free forward-model case the Boltzmann-plot points are exactly
collinear (`y_k = m0·E_k + b0`); when the energies are not all equal
(`∑ (E_k − mean E)² > 0`, i.e. at least two distinct `E_k`) ordinary least squares recovers
the exact slope `m0` AND intercept `b0`. This is the genuine Finset covariance/variance
identity that justifies fitting ALL lines (Tognoni et al. 2010), generalizing the two-point
slope of the classic method (Ciucci et al. 1999). The `hvar` hypothesis is satisfiable
(distinct energies) AND necessary (with all `E_k` equal the denominator vanishes and the
slope is undefined). -/
theorem ols_recovers_line [Nonempty ι] {E y : ι → ℝ} {m0 b0 : ℝ}
    (hcol : ∀ k, y k = m0 * E k + b0)
    (hvar : 0 < ∑ k, (E k - mean E) ^ 2) :
    olsSlope E y = m0 ∧ olsIntercept E y = b0 := by
  have hmean : mean y = m0 * mean E + b0 := by
    have hy : y = (fun k => m0 * E k + b0) := funext hcol
    rw [hy, mean_affine E m0 b0]
  -- Center the ordinates: `y k − mean y = m0 · (E k − mean E)`.
  have hyk : ∀ k, y k - mean y = m0 * (E k - mean E) := fun k => by
    rw [hcol k, hmean]; ring
  -- Slope leg.
  have hslope : olsSlope E y = m0 := by
    unfold olsSlope
    have hnum : (∑ k, (E k - mean E) * (y k - mean y))
        = m0 * ∑ k, (E k - mean E) ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [hyk k]; ring
    rw [hnum, mul_div_assoc, div_self hvar.ne', mul_one]
  -- Intercept leg.
  refine ⟨hslope, ?_⟩
  unfold olsIntercept
  rw [hslope, hmean]; ring

/-- **Non-vacuity witness for `ols_recovers_line`.** Two lines at energies `E = (0, 1)`
(so `∑ₖ (Eₖ − Ē)² = 1/2 > 0`, satisfying `hvar`) with collinear ordinates `y = 2·E + 3`:
OLS recovers the exact slope `2` and intercept `3` — a genuine non-degenerate line (slope `≠ 0`),
so the hypotheses are jointly satisfiable and the recovery is non-trivial. -/
example : olsSlope ![0, 1] ![3, 5] = 2 ∧ olsIntercept ![0, 1] ![3, 5] = 3 := by
  refine ols_recovers_line (m0 := 2) (b0 := 3) (fun k => ?_) ?_
  · fin_cases k <;> norm_num
  · simp [mean, Fin.sum_univ_two]; norm_num

/-- **Design-matrix normal matrix of the Boltzmann-plot fit.** Least squares against the
two-column design `[E | 1]` (energies and a constant) has the `2×2` normal matrix
`M = XᵀX = ![![∑ Eₖ², ∑ Eₖ], ![∑ Eₖ, n]]` with `n = card ι`. Its nonsingularity is the exact
rank/condition gate the runtime fit must pass before inverting the normal equations. Pure
linear algebra of the two-column Boltzmann-plot design (no physics content in the definition
itself). -/
noncomputable def designNormalMatrix (E : ι → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  ![![∑ k, E k ^ 2, ∑ k, E k], ![∑ k, E k, (Fintype.card ι : ℝ)]]

/-- **THE determinant identity (Lagrange / variance identity).** The determinant of the
Boltzmann-plot normal matrix equals `n · SS_E`, i.e.
`det M = n · ∑ₖ (Eₖ − Ē)²`, where `n = card ι` and `Ē = mean E`. Via `Matrix.det_fin_two`
this reduces to `n · ∑ Eₖ² − (∑ Eₖ)²`, which is exactly `n · ∑ (Eₖ − Ē)²` after expanding
`∑ (Eₖ − Ē)² = ∑ Eₖ² − 2 Ē ∑ Eₖ + n Ē²` with `Ē = (∑ Eₖ)/n`. Needs at least one line
(`[Nonempty ι]`, so `n ≠ 0`). Pure algebra — no physics. -/
theorem det_designNormalMatrix [Nonempty ι] (E : ι → ℝ) :
    (designNormalMatrix E).det = (Fintype.card ι : ℝ) * ∑ k, (E k - mean E) ^ 2 := by
  have hcard : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hexp : ∑ k, (E k - mean E) ^ 2
      = (∑ k, E k ^ 2) - 2 * mean E * (∑ k, E k)
        + (Fintype.card ι : ℝ) * mean E ^ 2 := by
    rw [show (∑ k, (E k - mean E) ^ 2)
        = ∑ k, (E k ^ 2 - 2 * mean E * E k + mean E ^ 2) from
        Finset.sum_congr rfl (fun k _ => by ring)]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  unfold designNormalMatrix
  rw [Matrix.det_fin_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [hexp]
  unfold mean
  field_simp
  ring

/-- **Nonsingularity ⇔ positive energy spread (the runtime rank gate).** Under `[Nonempty ι]`
the Boltzmann-plot normal matrix is nonsingular exactly when the energies have positive spread:
`det M ≠ 0 ↔ 0 < ∑ₖ (Eₖ − Ē)²`. Because `det M = n · SS_E` with `n = card ι > 0` and
`SS_E = ∑ (Eₖ − Ē)² ≥ 0` always, `det M ≠ 0 ⇔ SS_E ≠ 0 ⇔ SS_E > 0`. This grounds the runtime
rank gate: the `hvar` hypothesis of `ols_recovers_line` (and of `olsSlope_noise_gain`) *is*
design-matrix nonsingularity, so "at least two distinct energies" is the exact rank condition
for the multi-line Boltzmann-plot fit (Tognoni et al. 2010). -/
theorem designNormalMatrix_det_ne_zero_iff [Nonempty ι] (E : ι → ℝ) :
    (designNormalMatrix E).det ≠ 0 ↔ 0 < ∑ k, (E k - mean E) ^ 2 := by
  rw [det_designNormalMatrix]
  have hcard : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hnn : 0 ≤ ∑ k, (E k - mean E) ^ 2 := Finset.sum_nonneg (fun k _ => sq_nonneg _)
  constructor
  · intro h
    apply lt_of_le_of_ne hnn
    intro heq
    exact h (by rw [← heq, mul_zero])
  · intro h
    exact (mul_pos hcard h).ne'

/-- **Non-vacuity witness (nonsingular case).** Two lines at distinct energies `E = (0, 1)`:
the normal matrix `![![1, 1], ![1, 2]]` has determinant `1·2 − 1·1 = 1 ≠ 0`, matching
`det = n · SS_E = 2 · (1/2) = 1`. So `designNormalMatrix_det_ne_zero_iff` is non-trivially
satisfiable. -/
private def nvDmE01 : Fin 2 → ℝ := ![0, 1]

/-- **Non-vacuity witness (degenerate case).** Two lines at *equal* energies `E = (1, 1)`:
the normal matrix `![![2, 2], ![2, 2]]` is singular (`det = 2·2 − 2·2 = 0`), matching
`det = n · SS_E = 2 · 0 = 0`. So the rank gate genuinely rejects the "all energies equal"
design. -/
private def nvDmE11 : Fin 2 → ℝ := ![1, 1]

example : (designNormalMatrix nvDmE01).det = 1 := by
  unfold designNormalMatrix nvDmE01
  rw [Matrix.det_fin_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Fin.sum_univ_two, Fintype.card_fin]
  norm_num

example : (designNormalMatrix nvDmE11).det = 0 := by
  unfold designNormalMatrix nvDmE11
  rw [Matrix.det_fin_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Fin.sum_univ_two, Fintype.card_fin]
  norm_num

/-! ### Centered design normal matrix: diagonalization keystone (Frontier 06, Phase 1) -/
variable {ι : Type*} [Fintype ι]

/-- **Centered design normal matrix.** The normal matrix `BᵀB` of the two-column *centered*
Boltzmann-plot design `B = [(E − Ē) | 1]`, where `Ē = mean E`:
`![![∑ₖ (Eₖ − Ē)², ∑ₖ (Eₖ − Ē)], ![∑ₖ (Eₖ − Ē), n]]` with `n = card ι`. Unlike the raw
`designNormalMatrix` (`OLS.lean:185`), the off-diagonal entries here are the sum of *centered*
energies, which vanishes identically (`centered_sum_zero`) — this is what
`centeredDesignNormalMatrix_eq_diagonal` exploits. Pure linear algebra of the centered
two-column design (no physics content in the definition itself). -/
noncomputable def centeredDesignNormalMatrix (E : ι → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  ![![∑ k, (E k - mean E) ^ 2, ∑ k, (E k - mean E)],
    ![∑ k, (E k - mean E),     (Fintype.card ι : ℝ)]]

/-- **THE keystone: the centered normal matrix is diagonal.** `centeredDesignNormalMatrix E
= Matrix.diagonal ![SS_E, n]` with `SS_E = ∑ₖ (Eₖ − Ē)²` and `n = card ι`. The off-diagonal
entries are `∑ₖ (Eₖ − Ē) = 0` (`centered_sum_zero`, `OLS.lean:64`) because the constant column
`1` is orthogonal to the centered energy column exactly when the energies are referenced to
their own mean. This exhibits the eigenvalues of the centered design as the literal diagonal
entries `SS_E` and `n`, with no spectral machinery needed — the keystone for the condition
number `κ = max(SS_E, n) / min(SS_E, n)` (dossier `06-condition-numbers.md` §4 M1). -/
theorem centeredDesignNormalMatrix_eq_diagonal [Nonempty ι] (E : ι → ℝ) :
    centeredDesignNormalMatrix E
      = Matrix.diagonal ![∑ k, (E k - mean E) ^ 2, (Fintype.card ι : ℝ)] := by
  have h0 : ∑ k, (E k - mean E) = 0 := centered_sum_zero E
  unfold centeredDesignNormalMatrix
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.diagonal, h0]

/-- **Non-vacuity witness.** Two lines at distinct energies `E = (0, 1)`: `mean E = 1/2`, so
`SS_E = ∑ₖ (Eₖ − 1/2)² = 1/2` and `n = 2`. The centered normal matrix is
`![![1/2, 0], ![0, 2]]` — genuinely diagonal with two *distinct*, both-nonzero, entries
(`1/2 ≠ 2`), so `centeredDesignNormalMatrix_eq_diagonal` is non-trivially satisfiable and its
conclusion is not the zero matrix or a degenerate `diag(c, c)`. -/
private def nvCenteredE01 : Fin 2 → ℝ := ![0, 1]

example : centeredDesignNormalMatrix nvCenteredE01
    = Matrix.diagonal ![(1 : ℝ) / 2, 2] := by
  have h := centeredDesignNormalMatrix_eq_diagonal nvCenteredE01
  rw [h]
  congr 1
  unfold nvCenteredE01 mean
  simp [Fin.sum_univ_two]
  norm_num

example : (centeredDesignNormalMatrix nvCenteredE01) 0 0
    ≠ (centeredDesignNormalMatrix nvCenteredE01) 1 1 := by
  have h := centeredDesignNormalMatrix_eq_diagonal nvCenteredE01
  rw [h]
  unfold nvCenteredE01 mean
  simp [Matrix.diagonal, Fin.sum_univ_two]
  norm_num

/-- **M2 — determinant consistency (centering is unimodular).** Via the diagonal exhibition
(`centeredDesignNormalMatrix_eq_diagonal`) and `Matrix.det_diagonal` (`det = ∏ dᵢ`), the
determinant of the *centered* normal matrix is the same `n · SS_E` as the raw
`designNormalMatrix` (`det_designNormalMatrix`, `OLS.lean:194`) — a cross-check confirming
centering preserves the determinant (it is a unimodular row operation). Pure linear algebra;
no physics content. -/
theorem det_centeredDesignNormalMatrix [Nonempty ι] (E : ι → ℝ) :
    (centeredDesignNormalMatrix E).det = (Fintype.card ι : ℝ) * ∑ k, (E k - mean E) ^ 2 := by
  rw [centeredDesignNormalMatrix_eq_diagonal, Matrix.det_diagonal]
  simp [Fin.prod_univ_two, mul_comm]

/-- **M3 — the Boltzmann-plot condition number (2×2 diagonal `κ`).** Because
`centeredDesignNormalMatrix_eq_diagonal` exhibits the centered normal matrix as
`Matrix.diagonal ![SS_E, n]`, its eigenvalues *are* the diagonal entries `SS_E` and `n` with no
spectral machinery required; `κ := max(SS_E, n) / min(SS_E, n)` is the textbook 2-norm
condition number `λ_max/λ_min` (Golub & Van Loan, *Matrix Computations*, §2.6 — standard
numerical linear algebra, not a LIBS-specific citation) specialized to this diagonal case.
**Honesty note** (dossier `06-condition-numbers.md` §5/§6): this raw `max/min` ratio mixes
units (`SS_E` has units of energy², `n` is a bare count) and is *not* scale-invariant; it is
NOT proposed as a shift/scale-invariant physical quantity. Its scale-free counterpart is
`centeredScaledDesign_orthonormal` (`κ_scaled = 1`) below — see that theorem's docstring for
the honest headline. -/
noncomputable def boltzmannConditionNumber (E : ι → ℝ) : ℝ :=
  max (∑ k, (E k - mean E) ^ 2) (Fintype.card ι)
    / min (∑ k, (E k - mean E) ^ 2) (Fintype.card ι)

/-- **`κ ≥ 1` always.** Immediate from `min ≤ max` (`min_le_max`) together with
`min(SS_E, n) > 0` (needs `hvar : 0 < SS_E` and `n > 0` from `[Nonempty ι]`). Confirms
`boltzmannConditionNumber` is a genuine condition number in the textbook sense (never
sub-unity; `κ = 1` exactly at `SS_E = n`). -/
theorem boltzmannConditionNumber_ge_one [Nonempty ι] (E : ι → ℝ)
    (hvar : 0 < ∑ k, (E k - mean E) ^ 2) :
    1 ≤ boltzmannConditionNumber E := by
  unfold boltzmannConditionNumber
  have hcard : (0:ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hmin : 0 < min (∑ k, (E k - mean E) ^ 2) (Fintype.card ι) := lt_min hvar hcard
  rw [le_div_iff₀ hmin, one_mul]
  exact min_le_max

/-- **M4 — per-channel perturbation bound (the payoff).** On the diagonal centered system
`diag(SS_E, n)·x = c`, a perturbation `Δc` of the right-hand side propagates componentwise as
`Δx = (Δc₀/SS_E, Δc₁/n)`; this bounds the squared 2-norm of `Δx` by the squared 2-norm of `Δc`
scaled by `1/min(SS_E, n)²`. The slope channel's gain `1/SS_E` is *literally* the summand
identity behind `olsSlope_noise_gain` (`OLS.lean:128`, `∑ wₖ² = 1/SS_E`) and the intercept
channel's gain `1/n` is *literally* `olsIntercept_stable_centered`'s gain
(`ErrorBudget.lean:297`); this theorem is the statement that these two known per-channel
sensitivities are exactly the diagonal entries of one matrix condition-number bound — not a
new physical constant, but the packaging the ledger residual (`SOLVER_FORMALIZATION_GAPS.md:76`)
was asking for. Pure algebra on two reals. -/
theorem centeredSolve_perturbation [Nonempty ι] (E : ι → ℝ)
    (hvar : 0 < ∑ k, (E k - mean E) ^ 2) (Δc : Fin 2 → ℝ) :
    (Δc 0 / (∑ k, (E k - mean E) ^ 2)) ^ 2 + (Δc 1 / (Fintype.card ι : ℝ)) ^ 2
      ≤ (Δc 0 ^ 2 + Δc 1 ^ 2) / (min (∑ k, (E k - mean E) ^ 2) (Fintype.card ι)) ^ 2 := by
  set S := ∑ k, (E k - mean E) ^ 2 with hS
  set n := (Fintype.card ι : ℝ) with hn
  have hcard : (0:ℝ) < n := by rw [hn]; exact_mod_cast Fintype.card_pos
  have hmin : 0 < min S n := lt_min hvar hcard
  have hSge : min S n ≤ S := min_le_left _ _
  have hnge : min S n ≤ n := min_le_right _ _
  have h1 : (Δc 0 / S) ^ 2 ≤ (Δc 0 / min S n) ^ 2 := by
    rw [div_pow, div_pow]
    exact div_le_div_of_nonneg_left (sq_nonneg _) (pow_pos hmin 2)
      (pow_le_pow_left₀ hmin.le hSge 2)
  have h2 : (Δc 1 / n) ^ 2 ≤ (Δc 1 / min S n) ^ 2 := by
    rw [div_pow, div_pow]
    exact div_le_div_of_nonneg_left (sq_nonneg _) (pow_pos hmin 2)
      (pow_le_pow_left₀ hmin.le hnge 2)
  calc (Δc 0 / S) ^ 2 + (Δc 1 / n) ^ 2
      ≤ (Δc 0 / min S n) ^ 2 + (Δc 1 / min S n) ^ 2 := add_le_add h1 h2
    _ = (Δc 0 ^ 2 + Δc 1 ^ 2) / (min S n) ^ 2 := by
        rw [div_pow, div_pow, ← add_div]

/-- **M5 — the textbook relative-condition statement.** Assembles the component bounds
`‖Δx‖ ≤ (1/λ_min)·‖Δc‖` (from `centeredSolve_perturbation`, `λ_min = min(SS_E, n)`) and
`‖c‖ ≤ λ_max·‖x‖` (the symmetric lower bound on the diagonal solve, `λ_max = max(SS_E, n)`)
into the standard NLA perturbation theorem `‖Δx‖/‖x‖ ≤ κ·‖Δc‖/‖c‖` (Golub & Van Loan §2.6),
specialized to the `2×2` diagonal centered normal system, with `x = (c₀/SS_E, c₁/n)` the
centered-design solve and `κ = boltzmannConditionNumber E`. Requires `c ≠ 0` (`hc`) so the
relative denominators are nonzero. Pure algebra/`Real.sqrt` bookkeeping — no new mathematical
content beyond `centeredSolve_perturbation` and `boltzmannConditionNumber`. -/
theorem centeredSolve_relative_condition [Nonempty ι] (E : ι → ℝ)
    (hvar : 0 < ∑ k, (E k - mean E) ^ 2) (c Δc : Fin 2 → ℝ)
    (hc : c 0 ^ 2 + c 1 ^ 2 ≠ 0) :
    Real.sqrt ((Δc 0 / (∑ k, (E k - mean E) ^ 2)) ^ 2 + (Δc 1 / (Fintype.card ι : ℝ)) ^ 2)
        / Real.sqrt ((c 0 / (∑ k, (E k - mean E) ^ 2)) ^ 2 + (c 1 / (Fintype.card ι : ℝ)) ^ 2)
      ≤ boltzmannConditionNumber E
          * Real.sqrt (Δc 0 ^ 2 + Δc 1 ^ 2) / Real.sqrt (c 0 ^ 2 + c 1 ^ 2) := by
  set S := ∑ k, (E k - mean E) ^ 2 with hS
  set n := (Fintype.card ι : ℝ) with hn
  have hcard : (0:ℝ) < n := by rw [hn]; exact_mod_cast Fintype.card_pos
  set m := min S n with hmdef
  set M := max S n with hMdef
  have hm : 0 < m := lt_min hvar hcard
  have hM : 0 < M := lt_of_lt_of_le hvar (le_max_left _ _)
  have hSM : S ≤ M := le_max_left _ _
  have hnM : n ≤ M := le_max_right _ _
  set P := Δc 0 ^ 2 + Δc 1 ^ 2 with hPdef
  set Q := c 0 ^ 2 + c 1 ^ 2 with hQdef
  have hQnn : 0 ≤ Q := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hQpos : 0 < Q := lt_of_le_of_ne hQnn (Ne.symm hc)
  have hPnn : 0 ≤ P := add_nonneg (sq_nonneg _) (sq_nonneg _)
  -- lower bound: Q / M^2 ≤ B
  have hlow : Q / M ^ 2 ≤ (c 0 / S) ^ 2 + (c 1 / n) ^ 2 := by
    have h1 : c 0 ^ 2 / M ^ 2 ≤ (c 0 / S) ^ 2 := by
      rw [div_pow]
      exact div_le_div_of_nonneg_left (sq_nonneg _) (pow_pos hvar 2)
        (pow_le_pow_left₀ hvar.le hSM 2)
    have h2 : c 1 ^ 2 / M ^ 2 ≤ (c 1 / n) ^ 2 := by
      rw [div_pow]
      exact div_le_div_of_nonneg_left (sq_nonneg _) (pow_pos hcard 2)
        (pow_le_pow_left₀ hcard.le hnM 2)
    calc Q / M ^ 2 = c 0 ^ 2 / M ^ 2 + c 1 ^ 2 / M ^ 2 := by rw [hQdef, add_div]
      _ ≤ (c 0 / S) ^ 2 + (c 1 / n) ^ 2 := add_le_add h1 h2
  have hAP : (Δc 0 / S) ^ 2 + (Δc 1 / n) ^ 2 ≤ P / m ^ 2 := centeredSolve_perturbation E hvar Δc
  have hAsqrt : Real.sqrt ((Δc 0 / S) ^ 2 + (Δc 1 / n) ^ 2) ≤ Real.sqrt P / m := by
    calc Real.sqrt ((Δc 0 / S) ^ 2 + (Δc 1 / n) ^ 2) ≤ Real.sqrt (P / m ^ 2) :=
          Real.sqrt_le_sqrt hAP
      _ = Real.sqrt P / m := by rw [Real.sqrt_div hPnn, Real.sqrt_sq hm.le]
  have hBsqrt : Real.sqrt Q / M ≤ Real.sqrt ((c 0 / S) ^ 2 + (c 1 / n) ^ 2) := by
    calc Real.sqrt Q / M = Real.sqrt (Q / M ^ 2) := by
          rw [Real.sqrt_div hQnn, Real.sqrt_sq hM.le]
      _ ≤ Real.sqrt ((c 0 / S) ^ 2 + (c 1 / n) ^ 2) := Real.sqrt_le_sqrt hlow
  have hBnn : 0 ≤ (c 0 / S) ^ 2 + (c 1 / n) ^ 2 := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hBpos : 0 < (c 0 / S) ^ 2 + (c 1 / n) ^ 2 :=
    lt_of_lt_of_le (div_pos hQpos (pow_pos hM 2)) hlow
  have hBsqrtpos : 0 < Real.sqrt ((c 0 / S) ^ 2 + (c 1 / n) ^ 2) := Real.sqrt_pos.mpr hBpos
  have hQsqrtpos : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQpos
  have step1 : Real.sqrt ((Δc 0 / S) ^ 2 + (Δc 1 / n) ^ 2)
      / Real.sqrt ((c 0 / S) ^ 2 + (c 1 / n) ^ 2)
      ≤ (Real.sqrt P / m) / Real.sqrt ((c 0 / S) ^ 2 + (c 1 / n) ^ 2) :=
    (div_le_div_iff_of_pos_right hBsqrtpos).mpr hAsqrt
  have step2 : (Real.sqrt P / m) / Real.sqrt ((c 0 / S) ^ 2 + (c 1 / n) ^ 2)
      ≤ (Real.sqrt P / m) / (Real.sqrt Q / M) := by
    apply div_le_div_of_nonneg_left (div_nonneg (Real.sqrt_nonneg _) hm.le)
      (div_pos hQsqrtpos hM) hBsqrt
  have hκ : boltzmannConditionNumber E = M / m := by
    unfold boltzmannConditionNumber
    rw [← hS, ← hn, ← hMdef, ← hmdef]
  have step3 : (Real.sqrt P / m) / (Real.sqrt Q / M)
      = boltzmannConditionNumber E * Real.sqrt P / Real.sqrt Q := by
    rw [hκ]
    field_simp
  calc Real.sqrt ((Δc 0 / S) ^ 2 + (Δc 1 / n) ^ 2) / Real.sqrt ((c 0 / S) ^ 2 + (c 1 / n) ^ 2)
      ≤ (Real.sqrt P / m) / Real.sqrt ((c 0 / S) ^ 2 + (c 1 / n) ^ 2) := step1
    _ ≤ (Real.sqrt P / m) / (Real.sqrt Q / M) := step2
    _ = boltzmannConditionNumber E * Real.sqrt P / Real.sqrt Q := step3

/-- **M6 — THE HONEST HEADLINE: the scaled centered design is orthonormal, so `κ_scaled = 1`.**
Scale each centered-design column to unit norm — `u = (E − Ē)/√SS_E`, `v = 1/√n` — and this
correlation-matrix normalization makes the two columns exactly orthonormal (`⟨u,u⟩ = ⟨v,v⟩ = 1`,
`⟨u,v⟩ = 0`). The condition number of an orthonormal design is `1`: the *entire* conditioning
"problem" reported by `boltzmannConditionNumber` (M3) is an artifact of the two raw columns
carrying different scales (`SS_E` in units of energy², `n` a bare count — note the mixed
units, itself the reason `boltzmannConditionNumber`'s raw `max/min` ratio is not scale
invariant, dossier `06-condition-numbers.md` §5/§6). After scaling there is **no** residual
matrix-conditioning content: the only genuine, scale-free sensitivity left is the slope
channel's noise gain `1/SS_E` (`olsSlope_noise_gain`, `OLS.lean:128`) and the intercept
channel's `1/n` (`olsIntercept_stable_centered`, `ErrorBudget.lean:297`) — both already
proven. This theorem is the honest statement of what a matrix condition number adds (and does
not add) over those two existing constants for the two-column Boltzmann-plot design. -/
theorem centeredScaledDesign_orthonormal [Nonempty ι] (E : ι → ℝ)
    (hvar : 0 < ∑ k, (E k - mean E) ^ 2) :
    (∑ k, ((E k - mean E) / Real.sqrt (∑ k, (E k - mean E) ^ 2)) ^ 2 = 1)
      ∧ (∑ _k : ι, (1 / Real.sqrt (Fintype.card ι : ℝ)) ^ 2 = (1:ℝ))
      ∧ (∑ k, ((E k - mean E) / Real.sqrt (∑ k, (E k - mean E) ^ 2))
            * (1 / Real.sqrt (Fintype.card ι : ℝ)) = 0) := by
  set S := ∑ k, (E k - mean E) ^ 2 with hS
  set n := (Fintype.card ι : ℝ) with hn
  have hcard : (0:ℝ) < n := by rw [hn]; exact_mod_cast Fintype.card_pos
  have hSsqrt : Real.sqrt S ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hvar)
  have hnsqrt : Real.sqrt n ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hcard)
  refine ⟨?_, ?_, ?_⟩
  · have : ∀ k, ((E k - mean E) / Real.sqrt S) ^ 2 = (E k - mean E) ^ 2 / S := by
      intro k
      rw [div_pow, Real.sq_sqrt hvar.le]
    simp_rw [this]
    rw [← Finset.sum_div, div_self hvar.ne']
  · have : (1 / Real.sqrt n) ^ 2 = 1 / n := by rw [div_pow, Real.sq_sqrt hcard.le, one_pow]
    rw [Finset.sum_const, this, nsmul_eq_mul, Finset.card_univ, hn]
    field_simp
  · have h0 : ∑ k, (E k - mean E) = 0 := centered_sum_zero E
    have heq : ∀ k, ((E k - mean E) / Real.sqrt S) * (1 / Real.sqrt n)
        = (E k - mean E) * (1 / (Real.sqrt S * Real.sqrt n)) := by
      intro k; ring
    simp_rw [heq]
    rw [← Finset.sum_mul, h0, zero_mul]

/-- **Joint Saha–Boltzmann design normal matrix.** The Gram matrix `XᵀX` of the three-column
design `[1 | E | s]` (intercept, excitation energy, ion-stage indicator) that underlies the
*joint* Saha–Boltzmann fit (temperature AND electron density from one regression, Aguilera &
Aragón 2007). Row/column order is `(intercept, E, s)`:
`M = ![![n, ∑E, ∑s], ![∑E, ∑E², ∑Es], ![∑s, ∑Es, ∑s²]]` with `n = card ι`. Pure linear algebra
of the three-column design (no physics content in the definition itself); the physical content
lives in `jointDesign_det_pos_iff`'s docstring. -/
noncomputable def jointDesignNormalMatrix (E s : ι → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  ![![(Fintype.card ι : ℝ), ∑ k, E k, ∑ k, s k],
    ![∑ k, E k, ∑ k, E k ^ 2, ∑ k, E k * s k],
    ![∑ k, s k, ∑ k, E k * s k, ∑ k, s k ^ 2]]

/-- Expansion helper: `∑ₖ (fₖ − f̄)² = ∑ fₖ² − 2·f̄·∑fₖ + n·f̄²`. Same shape as the helper used
inline in `det_designNormalMatrix`; isolated here because the joint proof needs it for both
`E` and `s`. -/
private theorem sq_expand [Nonempty ι] (f : ι → ℝ) :
    ∑ k, (f k - mean f) ^ 2
      = (∑ k, f k ^ 2) - 2 * mean f * (∑ k, f k) + (Fintype.card ι : ℝ) * mean f ^ 2 := by
  rw [show (∑ k, (f k - mean f) ^ 2)
      = ∑ k, (f k ^ 2 - 2 * mean f * f k + mean f ^ 2) from
      Finset.sum_congr rfl (fun k _ => by ring)]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- Cross-term expansion helper: `∑ₖ (Eₖ − Ē)(sₖ − s̄) = ∑ Eₖsₖ − Ē·∑sₖ − s̄·∑Eₖ + n·Ē·s̄`. -/
private theorem cross_expand [Nonempty ι] (E s : ι → ℝ) :
    ∑ k, (E k - mean E) * (s k - mean s)
      = (∑ k, E k * s k) - mean E * (∑ k, s k) - mean s * (∑ k, E k)
        + (Fintype.card ι : ℝ) * mean E * mean s := by
  rw [show (∑ k, (E k - mean E) * (s k - mean s))
      = ∑ k, (E k * s k - mean E * s k - mean s * E k + mean E * mean s) from
      Finset.sum_congr rfl (fun k _ => by ring)]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

/-- **THE closed-form determinant of the joint design.** `det (jointDesignNormalMatrix E s)
= n · (SS_E · SS_s − S_Es²)` where `SS_E = ∑(Eₖ−Ē)²`, `SS_s = ∑(sₖ−s̄)²`,
`S_Es = ∑(Eₖ−Ē)(sₖ−s̄)`. The three-column (intercept, energy, ion-indicator) upgrade of
`det_designNormalMatrix` (`OLS.lean:194`): expand `Matrix.det_fin_three`, expand the three
centered sums back to raw sums via `sq_expand`/`cross_expand`, and match — the `n·Ē²·s̄²` cross
terms cancel identically, leaving exactly the raw-sum determinant. Pure algebra, no physics. -/
theorem det_jointDesignNormalMatrix [Nonempty ι] (E s : ι → ℝ) :
    (jointDesignNormalMatrix E s).det
      = (Fintype.card ι : ℝ) *
        ((∑ k, (E k - mean E) ^ 2) * (∑ k, (s k - mean s) ^ 2)
          - (∑ k, (E k - mean E) * (s k - mean s)) ^ 2) := by
  have hcard : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [sq_expand E, sq_expand s, cross_expand E s]
  unfold jointDesignNormalMatrix
  rw [Matrix.det_fin_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  unfold mean
  field_simp
  ring

/-- Sum-of-squares expansion of `∑ₖ (t·aₖ − bₖ)²` for a scalar `t`, used to complete the square
in the Cauchy–Schwarz equality-case proof below. -/
private theorem complete_square_expand (a b : ι → ℝ) (t : ℝ) :
    ∑ k, (t * a k - b k) ^ 2
      = t ^ 2 * (∑ k, a k ^ 2) - 2 * t * (∑ k, a k * b k) + ∑ k, b k ^ 2 := by
  rw [show (∑ k, (t * a k - b k) ^ 2)
      = ∑ k, (t ^ 2 * a k ^ 2 - 2 * t * (a k * b k) + b k ^ 2) from
      Finset.sum_congr rfl (fun k _ => by ring)]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

/-- **Cauchy–Schwarz, squared form, is always nonnegative** — `(∑a²)(∑b²) ≥ (∑ab)²` for any
`a b : ι → ℝ` (no centering, no hypothesis). Proof: if `∑a² = 0` then `a ≡ 0` so both sides
vanish; otherwise complete the square with `t₀ = (∑ab)/(∑a²)`: `(∑a²)·∑(t₀a−b)² = (∑a²)(∑b²) −
(∑ab)²`, and the left side is a nonnegative times a sum of squares. -/
private theorem sq_mul_sq_sub_sq_sum_nonneg [Nonempty ι] (a b : ι → ℝ) :
    0 ≤ (∑ k, a k ^ 2) * (∑ k, b k ^ 2) - (∑ k, a k * b k) ^ 2 := by
  rcases eq_or_lt_of_le (Finset.sum_nonneg (fun k (_ : k ∈ univ) => sq_nonneg (a k)))
    with hSa | hSa
  · have ha0 : ∀ k, a k = 0 := by
      intro k
      have h := (Finset.sum_eq_zero_iff_of_nonneg
        (fun k (_ : k ∈ univ) => sq_nonneg (a k))).1 hSa.symm k (mem_univ k)
      exact pow_eq_zero_iff (two_ne_zero) |>.1 h
    have hab0 : ∑ k, a k * b k = 0 := Finset.sum_eq_zero (fun k _ => by rw [ha0 k]; ring)
    rw [← hSa, hab0]
    norm_num
  · set t0 : ℝ := (∑ k, a k * b k) / (∑ k, a k ^ 2) with ht0
    have hSane : (∑ k, a k ^ 2) ≠ 0 := hSa.ne'
    have hkey : (∑ k, a k ^ 2) * ∑ k, (t0 * a k - b k) ^ 2
        = (∑ k, a k ^ 2) * (∑ k, b k ^ 2) - (∑ k, a k * b k) ^ 2 := by
      rw [complete_square_expand a b t0, ht0]
      field_simp
      ring
    rw [← hkey]
    exact mul_nonneg hSa.le (Finset.sum_nonneg (fun k _ => sq_nonneg _))

/-- **Cauchy–Schwarz equality case, in coefficient-pair form.** `(∑a²)(∑b²) = (∑ab)²` iff `a`
and `b` are proportional as a pair: `∃ c d, (c,d) ≠ (0,0) ∧ ∀k, c·aₖ = d·bₖ`. This symmetric
existential is the honest "not linearly independent" reading that also covers the degenerate
case `a ≡ 0` (witness `(c,d) = (1,0)`). Pure algebra: the `≠ 0` branch is `complete_square_expand`
again, reading off `t₀·aₖ = bₖ` from a vanishing sum of squares; the `⇐` branch is a direct
computation once `d ≠ 0` lets you solve `b = (c/d)·a`, and `d = 0` is impossible together with
`a ≢ 0` and `c ≠ 0`, `c·a ≡ 0`. -/
private theorem sq_mul_sq_sub_sq_eq_zero_iff [Nonempty ι] (a b : ι → ℝ) :
    (∑ k, a k ^ 2) * (∑ k, b k ^ 2) = (∑ k, a k * b k) ^ 2
      ↔ ∃ c d : ℝ, (c, d) ≠ (0, 0) ∧ ∀ k, c * a k = d * b k := by
  rcases eq_or_lt_of_le (Finset.sum_nonneg (fun k (_ : k ∈ univ) => sq_nonneg (a k)))
    with hSa | hSa
  · have ha0 : ∀ k, a k = 0 := by
      intro k
      have h := (Finset.sum_eq_zero_iff_of_nonneg
        (fun k (_ : k ∈ univ) => sq_nonneg (a k))).1 hSa.symm k (mem_univ k)
      exact pow_eq_zero_iff (two_ne_zero) |>.1 h
    have hab0 : ∑ k, a k * b k = 0 := Finset.sum_eq_zero (fun k _ => by rw [ha0 k]; ring)
    constructor
    · intro _
      exact ⟨1, 0, by simp, fun k => by rw [ha0 k]; ring⟩
    · intro _
      rw [← hSa, hab0]; norm_num
  · have hSane : (∑ k, a k ^ 2) ≠ 0 := hSa.ne'
    set t0 : ℝ := (∑ k, a k * b k) / (∑ k, a k ^ 2) with ht0
    have hkey : (∑ k, a k ^ 2) * ∑ k, (t0 * a k - b k) ^ 2
        = (∑ k, a k ^ 2) * (∑ k, b k ^ 2) - (∑ k, a k * b k) ^ 2 := by
      rw [complete_square_expand a b t0, ht0]
      field_simp
      ring
    constructor
    · intro heq
      have hz : (∑ k, a k ^ 2) * ∑ k, (t0 * a k - b k) ^ 2 = 0 := by rw [hkey]; linarith
      have hz2 : ∑ k, (t0 * a k - b k) ^ 2 = 0 := by
        rcases mul_eq_zero.1 hz with h | h
        · exact absurd h hSane
        · exact h
      have hall : ∀ k, t0 * a k - b k = 0 := by
        intro k
        have h := (Finset.sum_eq_zero_iff_of_nonneg
          (fun k (_ : k ∈ univ) => sq_nonneg (t0 * a k - b k))).1 hz2 k (mem_univ k)
        exact pow_eq_zero_iff (two_ne_zero) |>.1 h
      exact ⟨t0, 1, by simp, fun k => by have := hall k; linarith⟩
    · rintro ⟨c, d, hcd, hprop⟩
      rcases eq_or_ne d 0 with hd0 | hdne
      · exfalso
        subst hd0
        have hc0 : c ≠ 0 := by
          intro hc0'; apply hcd; simp [hc0']
        have : ∀ k, a k = 0 := by
          intro k
          have h := hprop k
          simp only [zero_mul] at h
          exact (mul_eq_zero.1 h).resolve_left hc0
        have : (∑ k, a k ^ 2) = 0 :=
          Finset.sum_eq_zero (fun k _ => by rw [this k]; ring)
        exact absurd this hSane
      · have hb : ∀ k, b k = (c / d) * a k := by
          intro k
          have h := hprop k
          field_simp
          linarith [h]
        have hab : ∑ k, a k * b k = (c / d) * ∑ k, a k ^ 2 := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun k _ => by rw [hb k]; ring)
        have hbb : ∑ k, b k ^ 2 = (c / d) ^ 2 * ∑ k, a k ^ 2 := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun k _ => by rw [hb k]; ring)
        rw [hab, hbb]
        ring

/-- **The centered energies and ion-indicator are proportional**, as a pair: `∃ (c,d) ≠ (0,0)`
with `c·(Eₖ − Ē) = d·(sₖ − s̄)` for every line `k`. The honest "linearly dependent" reading of
rank-deficiency for the two non-intercept columns of the joint design — symmetric in `E`/`s`
(no privileged direction) and correctly covers the degenerate case where one column is
constant (witness `(1, 0)` or `(0, 1)`). Pure linear algebra, no physics. -/
def jointDesignCenteredProportional (E s : ι → ℝ) : Prop :=
  ∃ c d : ℝ, (c, d) ≠ (0, 0) ∧ ∀ k, c * (E k - mean E) = d * (s k - mean s)

/-- **THE rank gate for the joint Saha–Boltzmann design.** `det (jointDesignNormalMatrix E s) > 0`
iff the centered energies and centered ion-indicator are NOT proportional
(`jointDesignCenteredProportional`) — the three-column upgrade of
`designNormalMatrix_det_ne_zero_iff` (`OLS.lean:220`). Physical reading: the *joint* fit that
recovers temperature (from `E`) AND electron density (from the Saha ion-stage shift `s`) in one
regression is identifiable exactly when the ion-stage indicator is not collinear with the
excitation energies across the fitted lines (Aguilera & Aragón 2007) — i.e. when the design
carries genuinely independent T- and nₑ-information, not merely a rescaled copy of one energy
axis. Proof: `det = n · (SS_E·SS_s − S_Es²)` (`det_jointDesignNormalMatrix`) with `n > 0` and
`SS_E·SS_s − S_Es² ≥ 0` always (`sq_mul_sq_sub_sq_sum_nonneg`), so `det > 0 ↔ SS_E·SS_s ≠ S_Es²
↔ ¬Proportional` (`sq_mul_sq_sub_sq_eq_zero_iff`). No spectral/eigenvalue machinery — the
refusal recorded in the frontier dossier (§5/§6): this is a determinant-sign gate, not a
condition number. -/
theorem jointDesign_det_pos_iff [Nonempty ι] (E s : ι → ℝ) :
    0 < (jointDesignNormalMatrix E s).det ↔ ¬ jointDesignCenteredProportional E s := by
  rw [det_jointDesignNormalMatrix]
  have hcard : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  set a : ι → ℝ := fun k => E k - mean E with ha
  set b : ι → ℝ := fun k => s k - mean s with hb
  have hnn := sq_mul_sq_sub_sq_sum_nonneg a b
  have heqiff := sq_mul_sq_sub_sq_eq_zero_iff a b
  unfold jointDesignCenteredProportional
  constructor
  · intro hpos hprop
    have heq0 : (∑ k, a k ^ 2) * (∑ k, b k ^ 2) - (∑ k, a k * b k) ^ 2 = 0 := by
      rw [sub_eq_zero]; exact heqiff.2 hprop
    have : (Fintype.card ι : ℝ) *
        ((∑ k, a k ^ 2) * (∑ k, b k ^ 2) - (∑ k, a k * b k) ^ 2) = 0 := by
      rw [heq0, mul_zero]
    exact absurd this hpos.ne'
  · intro hnp
    have hne : (∑ k, a k ^ 2) * (∑ k, b k ^ 2) - (∑ k, a k * b k) ^ 2 ≠ 0 := by
      intro h
      apply hnp
      exact heqiff.1 (by rw [← sub_eq_zero]; exact h)
    have hpos2 : 0 < (∑ k, a k ^ 2) * (∑ k, b k ^ 2) - (∑ k, a k * b k) ^ 2 :=
      lt_of_le_of_ne hnn (Ne.symm hne)
    exact mul_pos hcard hpos2

/-- **Non-vacuity witness for the joint design.** Three lines with energies `E = (0, 1, 2)` and
ion-stage indicator `s = (0, 0, 1)` (two lines from the neutral stage, one from the singly
ionized stage — a genuine, non-degenerate joint Saha–Boltzmann design). `Ē = 1`, `s̄ = 1/3`, so
`SS_E = 1 + 0 + 1 = 2`, `SS_s = 1/9 + 1/9 + 4/9 = 6/9 = 2/3`, `S_Es = (-1)(-1/3) + 0·(-1/3) +
1·(2/3) = 1/3 + 2/3 = 1`, giving `det = 3·(2·(2/3) − 1²) = 3·(4/3 − 1) = 3·(1/3) = 1 > 0` — a
concrete strictly positive determinant, so `jointDesign_det_pos_iff` is non-trivially
satisfiable and the joint fit is genuinely identifiable on this data. -/
private def nvJointE : Fin 3 → ℝ := ![0, 1, 2]

private def nvJointS : Fin 3 → ℝ := ![0, 0, 1]

example : (jointDesignNormalMatrix nvJointE nvJointS).det = 1 := by
  rw [det_jointDesignNormalMatrix]
  unfold nvJointE nvJointS mean
  simp [Fin.sum_univ_three]
  norm_num

/-- The witness data is genuinely identifiable: the positive determinant above and
`jointDesign_det_pos_iff` together certify that the centered energies and ion-indicator are
NOT proportional on this concrete design. -/
example : ¬ jointDesignCenteredProportional nvJointE nvJointS := by
  rw [← jointDesign_det_pos_iff]
  have h : (jointDesignNormalMatrix nvJointE nvJointS).det = 1 := by
    rw [det_jointDesignNormalMatrix]
    unfold nvJointE nvJointS mean
    simp [Fin.sum_univ_three]
    norm_num
  rw [h]; norm_num

end CflibsFormal
