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

end CflibsFormal
