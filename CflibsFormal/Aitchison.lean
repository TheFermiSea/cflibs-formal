/-
Copyright (c) 2026 Brian Squires. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Squires
-/
import Mathlib

/-!
# 2DCOS-LIBS formalization — Aitchison compositional identities

The 2DCOS-LIBS composition step maps a raw nonnegative concentration vector into
the probability simplex. This file formalizes the *sound* algebra of that step:
Aitchison's closure operator, the softmax map, and the centered-log-ratio (clr)
transform, together with the exact identity that pins down what the pipeline's
`jax.nn.softmax(jnp.log(x))` actually computes.

## The C3 identity (audit-critical)

The monograph (§2.2) claimed the concentration vector is projected into the
simplex "using the Isometric Log-Ratio (ILR) transformation." That is FALSE.
`softmax_log_eq_closure` proves `softmax (log x) = closure x`: softmax∘log is
*exactly* Aitchison's closure `C(x) = x / ∑x` — ordinary re-normalization onto
the simplex `Sᴰ`. It is NOT ILR. A genuine ILR (Egozcue et al. 2003) is
`ilr(x) = Vᵀ · clr(x)` with `V` an orthonormal basis of the `(D−1)`-dimensional
clr-plane: an isometry `Sᴰ → ℝ^(D−1)` that strictly reduces dimension and gives
subcompositional coherence. The softmax∘log map does none of that — the `log`
and softmax's internal `exp` cancel identically. See `docs/2dcos/ERRATA.md` (C3).

## What is deliberately NOT formalized

Per `docs/2dcos/ERRATA.md`, the unsound "Model A" dynamic-temperature-integration
composition claim and "Model B" standardless/electron-density-free quantification
are NOT formalized here — they are not valid mathematics. Only the true
compositional algebra (closure / softmax / clr) is stated. A genuine ILR
round-trip and isometry (needing an explicit orthonormal SBP/Helmert basis in
`ℝ^(D−1)`) is recorded as an open target, not asserted.

## Literature

* J. Aitchison, *The Statistical Analysis of Compositional Data*, Chapman & Hall
  (1986) — closure operator `C(x)`, clr.
* J. J. Egozcue, V. Pawlowsky-Glahn, G. Mateu-Figueras, C. Barceló-Vidal,
  *Isometric logratio transformations for compositional data analysis*,
  Math. Geol. 35(3):279–300 (2003) — ILR `= Vᵀ clr(x)`.
-/

namespace CflibsFormal

open Finset Real
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- Aitchison **closure** operator `C(x) k = x k / ∑ⱼ x j`: re-normalize a vector
onto the simplex by dividing by its total. This is the operator the 2DCOS-LIBS
composition step actually applies (see `softmax_log_eq_closure`); it is NOT the
Isometric Log-Ratio transform (`docs/2dcos/ERRATA.md`, C3). Aitchison 1986. -/
noncomputable def closure (x : ι → ℝ) (k : ι) : ℝ :=
  x k / ∑ j, x j

/-- Softmax map `softmax v k = exp(v k) / ∑ⱼ exp(v j)`. -/
noncomputable def softmax (v : ι → ℝ) (k : ι) : ℝ :=
  Real.exp (v k) / ∑ j, Real.exp (v j)

/-- Centered log-ratio `clr(x) k = log(x k) − (∑ⱼ log(x j)) / D`, with `D = |ι|`
the number of components. The clr coordinates live in the hyperplane `∑ = 0`
(`clr_sum_zero`); a genuine ILR is `Vᵀ · clr` for an orthonormal basis `V` of
that hyperplane (Egozcue et al. 2003), NOT formalized here. Aitchison 1986. -/
noncomputable def clr (x : ι → ℝ) (k : ι) : ℝ :=
  Real.log (x k) - (∑ j, Real.log (x j)) / (Fintype.card ι)

/-- **Closure normalization.** The closure of any vector with nonzero total sums
to one: `∑ₖ C(x) k = 1` whenever `∑ⱼ x j ≠ 0`. This is the simplex constraint the
composition step enforces. Aitchison 1986. -/
theorem closure_sum_one {x : ι → ℝ} (hx : (∑ j, x j) ≠ 0) :
    ∑ k, closure x k = 1 := by
  unfold closure
  rw [← Finset.sum_div, div_self hx]

/-- **Softmax normalization.** Softmax outputs sum to one, `∑ₖ softmax v k = 1`
(the denominator `∑ⱼ exp(v j) > 0` is automatic for a nonempty index type). -/
theorem softmax_sum_one [Nonempty ι] {v : ι → ℝ} :
    ∑ k, softmax v k = 1 := by
  have hpos : 0 < ∑ j, Real.exp (v j) :=
    Finset.sum_pos (fun j _ => Real.exp_pos _) Finset.univ_nonempty
  unfold softmax
  rw [← Finset.sum_div, div_self hpos.ne']

/-- **The C3 identity (audit-critical).** For a strictly positive vector,
`softmax (log x) = C(x)`: softmax∘log is *exactly* Aitchison closure, plain
re-normalization onto the simplex. It is **NOT** the Isometric Log-Ratio (ILR)
transform — there is no orthonormal basis, no `D → D−1` dimension reduction, and
no isometry (the `log` and softmax's internal `exp` cancel identically). This is
the identity behind `docs/2dcos/ERRATA.md` C3, which refutes the monograph's
"ILR projection" claim. Aitchison 1986; ILR: Egozcue et al. 2003. -/
theorem softmax_log_eq_closure {x : ι → ℝ} (hx : ∀ k, 0 < x k) :
    softmax (fun k => Real.log (x k)) = closure x := by
  funext k
  unfold softmax closure
  rw [Real.exp_log (hx k)]
  congr 1
  exact Finset.sum_congr rfl (fun j _ => Real.exp_log (hx j))

/-- **clr sums to zero.** The centered-log-ratio coordinates lie in the
hyperplane `∑ₖ clr(x) k = 0`; this is the `(D−1)`-dimensional plane on which a
genuine ILR would pick an orthonormal basis. No positivity hypothesis is needed
(it is an affine identity in `log x`). Aitchison 1986. -/
theorem clr_sum_zero [Nonempty ι] {x : ι → ℝ} :
    ∑ k, clr x k = 0 := by
  have hc : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [clr, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp
  ring

/-! ### Non-vacuity witnesses (concrete data, `D = 3`) -/

/-- `closure_sum_one` fires on concrete positive data `(1, 2, 3)`. -/
example : ∑ k, closure (![1, 2, 3] : Fin 3 → ℝ) k = 1 :=
  closure_sum_one (by simp [Fin.sum_univ_three]; norm_num)

/-- `softmax_sum_one` fires on concrete data `(1, 2, 3)`. -/
example : ∑ k, softmax (![1, 2, 3] : Fin 3 → ℝ) k = 1 := softmax_sum_one

/-- The C3 identity fires on concrete positive data `(1, 2, 3)`. -/
example : softmax (fun k => Real.log ((![1, 2, 3] : Fin 3 → ℝ) k)) = closure ![1, 2, 3] :=
  softmax_log_eq_closure (by intro k; fin_cases k <;> norm_num)

/-- `clr_sum_zero` fires on concrete data `(1, 2, 3)`. -/
example : ∑ k, clr (![1, 2, 3] : Fin 3 → ℝ) k = 0 := clr_sum_zero

end CflibsFormal
