/-
Copyright (c) 2026 Brian Squires. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Squires
-/
import Mathlib
import CflibsFormal.OLS

/-!
# CF-LIBS formalization — the ordinary-least-squares projection / feasibility inverse

`OLS.lean` builds the OLS estimator `(olsSlope, olsIntercept)` and proves the *noise-free*
recovery `ols_recovers_line` (exactly collinear points ⇒ exact slope and intercept). That is the
identifiability core: it presumes the data lies **on** the linear manifold `y_k = m·E_k + b`.
Real spectra never do — measured Boltzmann-plot ordinates are noisy, off-manifold points.

This module formalizes the **least-squares / projection inverse** for that off-manifold case —
the property the strict-mode solver actually relies on when it fits a line to noisy data:

* `rss` — the residual sum of squares `∑ₖ (m·Eₖ + b − yₖ)²`, the least-squares objective.
* `residual_sum_zero`, `residual_dot_energy_zero` — the **normal equations**: at the OLS
  estimates the residual vector is orthogonal to the constant regressor `1` and to the energy
  regressor `E`. These are the stationarity conditions of `rss`.
* `rss_decomposition` — the **Pythagorean / projection identity**
  `rss E y m b = rss E y (olsSlope E y) (olsIntercept E y) + ∑ₖ ((m−m̂)·Eₖ + (b−b̂))²`.
  The excess of any fit over the OLS fit is a sum of squares.
* `ols_minimizes_rss` — **existence of the minimizer, constructively:** `(olsSlope E y,
  olsIntercept E y)` globally minimizes `rss E y` over all `(m,b) ∈ ℝ²`, for **arbitrary**
  (noisy, off-manifold) ordinates `y`. The minimizer is the closed-form OLS estimate, so
  existence needs no compactness/continuity argument — it is exhibited.
* `LeastSquaresFeasible` + `leastSquaresFeasible_iff_exists` — a **residual-based feasibility
  predicate**: the best achievable residual is `≤ ε` iff *some* line fits within `ε`. This is
  the runtime feasibility gate — a fit is admissible only when its minimal residual is small.
* `leastSquaresResidual_eq_zero_iff` — **on-manifold characterization:** the minimal residual is
  `0` iff the data lies exactly on the OLS line. So feasibility at `ε = 0` ⟺ on-manifold.
* `ols_minimizer_eq_inverse` — the **bridge to the identifiable inverse:** when the data *is*
  on-manifold (`yₖ = m₀·Eₖ + b₀`), the least-squares minimizer equals the exact identifiable
  parameters `(m₀, b₀)` (via `OLS.ols_recovers_line`) **and** the minimal residual is `0`. This
  is the precise condition under which the projection inverse coincides with the identifiable
  inverse.

## Scope (honest)

Everything here is **pure algebra** (`PURE-MATH`): the projection theorem for a two-column
design matrix `[E | 1]`, i.e. the classical least-squares normal equations (Gauss–Legendre,
c. 1805). It is `Mathlib`-only (`import CflibsFormal.OLS`, nothing else from `CflibsFormal`).
The *physics* — that `(m,b)` are the Boltzmann-plot slope `−1/(k_B T)` and the
concentration-bearing intercept `log(Fcal·N/U)`, so the projection inverse fits `(T, N)` to a
noisy spectrum and coincides with the identifiable inverse on the noise-free forward fixpoint —
is one corollary away, in `Alt/LeastSquares.lean` (`olsBoltzmann_forward_feasible`). Off the
manifold there is *no* ground-truth `(T, N)` to recover: the estimator returns the orthogonal
projection, and `leastSquaresResidual` quantifies the model mismatch. That is exactly why the
solver refuses when the minimal residual exceeds tolerance rather than reporting a fit.
-/

namespace CflibsFormal

open Finset Real
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- **Residual sum of squares** of the affine fit `k ↦ m·Eₖ + b` to the ordinates `y`:
`rss E y m b = ∑ₖ (m·Eₖ + b − yₖ)²`. The ordinary-least-squares objective; the OLS estimates
`(olsSlope E y, olsIntercept E y)` are its global minimizer (`ols_minimizes_rss`). -/
noncomputable def rss (E y : ι → ℝ) (m b : ℝ) : ℝ := ∑ k, (m * E k + b - y k) ^ 2

/-- **Normal equation (constant regressor).** At the OLS estimates the residuals sum to zero:
`∑ₖ (olsSlope·Eₖ + olsIntercept − yₖ) = 0`. Stationarity of `rss` in the intercept `b`. Follows
from `centered_sum_zero` on both `E` and `y` (needs `[Nonempty ι]`, i.e. `card ≠ 0`); no
nondegeneracy on `E` is required. -/
theorem residual_sum_zero [Nonempty ι] (E y : ι → ℝ) :
    ∑ k, (olsSlope E y * E k + olsIntercept E y - y k) = 0 := by
  have hcongr : ∀ k ∈ Finset.univ,
      olsSlope E y * E k + olsIntercept E y - y k
        = olsSlope E y * (E k - mean E) - (y k - mean y) := by
    intro k _; unfold olsIntercept; ring
  rw [Finset.sum_congr rfl hcongr, Finset.sum_sub_distrib, ← Finset.mul_sum,
    centered_sum_zero E, centered_sum_zero y, mul_zero, sub_zero]

/-- **Normal equation (centered energy regressor).** At the OLS estimates the residuals are
orthogonal to the centered energies: `∑ₖ (Eₖ − Ē)·(olsSlope·Eₖ + olsIntercept − yₖ) = 0`. This
is stationarity of `rss` in the slope `m`; it needs the nonzero energy spread `hvar` (the OLS
slope's denominator) to cancel. -/
theorem residual_centered_dot_zero [Nonempty ι] (E y : ι → ℝ)
    (hvar : 0 < ∑ k, (E k - mean E) ^ 2) :
    ∑ k, (E k - mean E) * (olsSlope E y * E k + olsIntercept E y - y k) = 0 := by
  have hcongr : ∀ k ∈ Finset.univ,
      (E k - mean E) * (olsSlope E y * E k + olsIntercept E y - y k)
        = olsSlope E y * (E k - mean E) ^ 2 - (E k - mean E) * (y k - mean y) := by
    intro k _; unfold olsIntercept; ring
  rw [Finset.sum_congr rfl hcongr, Finset.sum_sub_distrib, ← Finset.mul_sum, olsSlope,
    div_mul_cancel₀ _ hvar.ne', sub_self]

/-- **Normal equation (raw energy regressor).** `∑ₖ Eₖ·(olsSlope·Eₖ + olsIntercept − yₖ) = 0`.
The raw-energy form of orthogonality, obtained from the centered form
(`residual_centered_dot_zero`) plus `residual_sum_zero` via `Eₖ = (Eₖ − Ē) + Ē`. Used to kill
the cross term in `rss_decomposition`. -/
theorem residual_dot_energy_zero [Nonempty ι] (E y : ι → ℝ)
    (hvar : 0 < ∑ k, (E k - mean E) ^ 2) :
    ∑ k, E k * (olsSlope E y * E k + olsIntercept E y - y k) = 0 := by
  have hcongr : ∀ k ∈ Finset.univ,
      E k * (olsSlope E y * E k + olsIntercept E y - y k)
        = (E k - mean E) * (olsSlope E y * E k + olsIntercept E y - y k)
          + mean E * (olsSlope E y * E k + olsIntercept E y - y k) := by
    intro k _; ring
  rw [Finset.sum_congr rfl hcongr, Finset.sum_add_distrib,
    residual_centered_dot_zero E y hvar, ← Finset.mul_sum, residual_sum_zero E y,
    mul_zero, add_zero]

/-- **Projection / Pythagorean identity.** For any candidate `(m, b)`,
`rss E y m b = rss E y (olsSlope E y) (olsIntercept E y) + ∑ₖ ((m−m̂)·Eₖ + (b−b̂))²`,
where `(m̂, b̂) = (olsSlope E y, olsIntercept E y)`. The residual of any fit decomposes
orthogonally into the OLS residual plus the (squared) displacement of the fitted line from the
OLS line; the cross term vanishes by the normal equations. -/
theorem rss_decomposition [Nonempty ι] (E y : ι → ℝ)
    (hvar : 0 < ∑ k, (E k - mean E) ^ 2) (m b : ℝ) :
    rss E y m b
      = rss E y (olsSlope E y) (olsIntercept E y)
        + ∑ k, ((m - olsSlope E y) * E k + (b - olsIntercept E y)) ^ 2 := by
  unfold rss
  have hpt : ∀ k ∈ Finset.univ,
      (m * E k + b - y k) ^ 2
        = (olsSlope E y * E k + olsIntercept E y - y k) ^ 2
          + (2 * (m - olsSlope E y) * (E k * (olsSlope E y * E k + olsIntercept E y - y k))
             + 2 * (b - olsIntercept E y) * (olsSlope E y * E k + olsIntercept E y - y k))
          + ((m - olsSlope E y) * E k + (b - olsIntercept E y)) ^ 2 := by
    intro k _; ring
  have hcross :
      ∑ k, (2 * (m - olsSlope E y) * (E k * (olsSlope E y * E k + olsIntercept E y - y k))
        + 2 * (b - olsIntercept E y) * (olsSlope E y * E k + olsIntercept E y - y k)) = 0 := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      residual_dot_energy_zero E y hvar, residual_sum_zero E y]
    ring
  rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_add_distrib, hcross]
  ring

/-- **THE CRUX — OLS is the least-squares minimizer.** For arbitrary (noisy, off-manifold)
ordinates `y`, the OLS estimates `(olsSlope E y, olsIntercept E y)` globally minimize the
residual sum of squares over all affine fits: `rss E y (olsSlope E y) (olsIntercept E y) ≤
rss E y m b` for every `(m, b)`. This is the *existence of a least-squares minimizer* — supplied
constructively by the closed-form OLS estimate, so no compactness argument is needed — and the
excess of any other fit is the sum of squares from `rss_decomposition`. The `hvar` hypothesis
(nonzero energy spread) is the standing nondegeneracy that makes the OLS slope well-defined. -/
theorem ols_minimizes_rss [Nonempty ι] (E y : ι → ℝ)
    (hvar : 0 < ∑ k, (E k - mean E) ^ 2) (m b : ℝ) :
    rss E y (olsSlope E y) (olsIntercept E y) ≤ rss E y m b := by
  rw [rss_decomposition E y hvar m b]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun k _ => sq_nonneg _)

/-- **Minimal (least-squares) residual** of the data `(E, y)`: the residual sum of squares at the
OLS estimates, `rss E y (olsSlope E y) (olsIntercept E y)`. By `ols_minimizes_rss` this is the
global minimum of `rss E y` over all affine fits — the smallest achievable misfit. -/
noncomputable def leastSquaresResidual (E y : ι → ℝ) : ℝ :=
  rss E y (olsSlope E y) (olsIntercept E y)

/-- The minimal residual is nonnegative (a sum of squares). Companion fact to
`LeastSquaresFeasible`: feasibility is impossible at any tolerance `ε < 0`, so the runtime gate
only ever tests `ε ≥ 0`. -/
theorem leastSquaresResidual_nonneg (E y : ι → ℝ) : 0 ≤ leastSquaresResidual E y := by
  unfold leastSquaresResidual rss
  exact Finset.sum_nonneg fun k _ => sq_nonneg _

/-- **Least-squares feasibility** at tolerance `ε`: the minimal residual is within `ε`,
`leastSquaresResidual E y ≤ ε`. The runtime admissibility gate — a linear fit to the (noisy)
data is feasible at level `ε` exactly when *some* line fits within `ε`
(`leastSquaresFeasible_iff_exists`). -/
def LeastSquaresFeasible (E y : ι → ℝ) (ε : ℝ) : Prop :=
  leastSquaresResidual E y ≤ ε

/-- **Feasibility is minimality.** The data is least-squares-feasible at tolerance `ε` iff *some*
affine fit achieves residual `≤ ε`. Forward: the OLS fit itself witnesses it. Backward: OLS beats
every fit (`ols_minimizes_rss`), so if any line fits within `ε` then the OLS minimum does too.
This grounds the runtime feasibility gate on the achievable-misfit floor rather than on a lucky
guess. -/
theorem leastSquaresFeasible_iff_exists [Nonempty ι] (E y : ι → ℝ)
    (hvar : 0 < ∑ k, (E k - mean E) ^ 2) (ε : ℝ) :
    LeastSquaresFeasible E y ε ↔ ∃ m b, rss E y m b ≤ ε := by
  unfold LeastSquaresFeasible leastSquaresResidual
  constructor
  · intro h
    exact ⟨olsSlope E y, olsIntercept E y, h⟩
  · rintro ⟨m, b, hmb⟩
    exact (ols_minimizes_rss E y hvar m b).trans hmb

/-- **On-manifold characterization.** The minimal residual is `0` iff the data lies exactly on
the OLS line: `leastSquaresResidual E y = 0 ↔ ∀ k, y k = olsSlope E y · E k + olsIntercept E y`.
A sum of squares vanishes iff each term does. So least-squares feasibility at `ε = 0` is exactly
the on-manifold condition — the boundary between the noisy regime (`> 0`) and the exact-fit
regime of `ols_recovers_line`. -/
theorem leastSquaresResidual_eq_zero_iff (E y : ι → ℝ) :
    leastSquaresResidual E y = 0 ↔ ∀ k, y k = olsSlope E y * E k + olsIntercept E y := by
  unfold leastSquaresResidual rss
  rw [Finset.sum_eq_zero_iff_of_nonneg fun k _ => sq_nonneg _]
  constructor
  · intro h k
    have hk : (olsSlope E y * E k + olsIntercept E y - y k) ^ 2 = 0 := h k (Finset.mem_univ k)
    have := sq_eq_zero_iff.mp hk
    linarith
  · intro h k _
    rw [h k]; ring

/-- **Bridge — the least-squares minimizer equals the identifiable inverse on-manifold.** When
the data is exactly collinear (`y_k = m₀·E_k + b₀`, the noise-free forward case) with nonzero
energy spread, the least-squares minimizer recovers the exact parameters
(`olsSlope E y = m₀`, `olsIntercept E y = b₀`, from `OLS.ols_recovers_line`) **and** the minimal
residual is `0` (a perfect fit). This is the precise "conditions under which the minimizer equals
the identifiable inverse" — the least-squares/projection inverse and the exact-fit injective
inverse coincide exactly on the manifold. -/
theorem ols_minimizer_eq_inverse [Nonempty ι] {E y : ι → ℝ} {m0 b0 : ℝ}
    (hcol : ∀ k, y k = m0 * E k + b0)
    (hvar : 0 < ∑ k, (E k - mean E) ^ 2) :
    olsSlope E y = m0 ∧ olsIntercept E y = b0 ∧ leastSquaresResidual E y = 0 := by
  obtain ⟨hm, hb⟩ := ols_recovers_line hcol hvar
  refine ⟨hm, hb, ?_⟩
  rw [leastSquaresResidual_eq_zero_iff]
  intro k
  rw [hm, hb]
  exact hcol k

/-! ### Non-vacuity witnesses -/

/-- **On-manifold witness.** Collinear data `E = (0,1)`, `y = 2·E + 3` (nonzero energy spread):
the least-squares minimizer recovers the exact slope `2`, intercept `3`, and a `0` minimal
residual — a genuine non-degenerate line (slope `≠ 0`). So `ols_minimizer_eq_inverse`'s
hypotheses are jointly satisfiable and its conclusion is non-trivial. -/
example : olsSlope ![0, 1] ![3, 5] = 2 ∧ olsIntercept ![0, 1] ![3, 5] = 3
    ∧ leastSquaresResidual ![0, 1] ![3, 5] = 0 := by
  refine ols_minimizer_eq_inverse (m0 := 2) (b0 := 3) (fun k => ?_) ?_
  · fin_cases k <;> norm_num
  · norm_num [mean, Fin.sum_univ_two]

/-- **Off-manifold (noisy) witness.** The three points `(E, y) = ((0,0), (1,0), (2,1))` are NOT
collinear — no affine `m·E + b` fits all three — so a zero minimal residual is impossible (it
would put the data on the OLS line, `leastSquaresResidual_eq_zero_iff`). Hence
`leastSquaresResidual > 0`: the projection inverse genuinely operates in the noisy regime the gap
targets, distinct from the collinear `ols_recovers_line` case (residual `0`). This is what makes
`ols_minimizes_rss` / `leastSquaresFeasible_iff_exists` non-vacuous off the manifold. -/
example : 0 < leastSquaresResidual ![0, 1, 2] ![0, 0, 1] := by
  have hnn : 0 ≤ leastSquaresResidual ![0, 1, 2] ![0, 0, 1] := leastSquaresResidual_nonneg _ _
  have hne : leastSquaresResidual ![0, 1, 2] ![0, 0, 1] ≠ 0 := by
    intro hzero
    rw [leastSquaresResidual_eq_zero_iff] at hzero
    have h0 := hzero 0
    have h1 := hzero 1
    have h2 := hzero 2
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, mul_zero, mul_one, zero_add] at h0 h1 h2
    linarith
  exact hnn.lt_of_ne (Ne.symm hne)

end CflibsFormal
