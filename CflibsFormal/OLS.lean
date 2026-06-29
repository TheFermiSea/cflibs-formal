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

end CflibsFormal
