/-
Copyright (c) 2026 Brian Squires. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Squires
-/
import Mathlib
import CflibsFormal.TwoDCOS

/-!
# 2DCOS-LIBS formalization — the sequential-order (lead/lag) sign algebra

This module isolates the **pure-algebraic backbone** of Noda's sequential-order
("lead/lag") sign rule. Given two dynamic temporal traces `u v : Fin m → ℝ`
sampled over `m` gate-delays, the **Noda cross-form** is

`B m u v = u ⬝ᵥ (hilbertNoda m *ᵥ v)`,

the scalar `∑ⱼₖ uⱼ Nⱼₖ vₖ` built from the Hilbert–Noda kernel `N` of
`CflibsFormal.TwoDCOS`. By construction it is the un-normalized `(u, v)` entry of the
asynchronous map `Ψ` (`asyncMatrix`): for two bands `u = Y a`, `v = Y b`, the identity
`Ψ a b = (1/(m−1)) · B m u v` is *definitional* — it is not stated as a separate named theorem, and
the sign / lead-lag reading of `Ψ` from `B` is likewise informal.

We prove the exact sign algebra of `B`:

* `B_antisymm` — `B m u v = − B m v u` (from `hilbertNoda_transpose_neg`,
  `Nᵀ = −N`). This is the algebra behind "the sign of the asynchronous
  cross-peak flips under `j ↔ k`": `sign(Ψ_jk) = − sign(Ψ_kj)`.
* `B_add_left`, `B_smul_left`, `B_add_right`, `B_smul_right` — `B` is bilinear.
  Hence for bands carrying dynamic weights `c_j • u` and `c_k • v` the
  asynchronous value scales as `c_j·c_k · B m u v` (`B_smul_smul`), so its sign
  is governed by `B m u v` up to the sign of the trace amplitudes.
* `B_selfZero` — `B m u u = 0` (the zero-diagonal law, specialized).
* A concrete **non-vacuity sign witness** at `m = 3`: for a rising step
  `u = ![0,1,1]` and its one-gate-delayed copy `v = ![0,0,1]`,
  `B 3 u v = 1/π > 0` (`B_stepDelay_pos`), while `B 3 v u = −1/π < 0`. So the
  sign rule is non-trivial: the ordered pair has a definite, nonzero sign.

## Literature and scope

* Scope tag: **PURE-MATH**. Citation: "—".
* This file states and proves *only the sign algebra* of the bilinear form `B`.
  The **physical lead/lag reading** — that a positive `B m u v` means band `u`'s
  intensity changes *before* (leads) band `v`'s along the gate-delay axis — is an
  **empirical interpretation** placed on the sign of `B`, in the tradition of
  Noda's sequential-order rule. It is **NOT** a theorem of this module and is
  **not** asserted here; we prove the antisymmetry, bilinearity, and a definite
  computed sign on explicit data, nothing about physical time-ordering.
* Builds on `CflibsFormal.TwoDCOS` (`hilbertNoda`, `hilbertNoda_transpose_neg`).
  The unsound quantification claims of the source drafts are refuted in
  `docs/2dcos/ERRATA.md` and are deliberately NOT formalized.

Reference for the correlation framework: Noda, *Appl. Spectrosc.* **47** (1993)
1329; **54** (2000) 994.
-/

open Matrix Finset Real
open scoped BigOperators

namespace CflibsFormal

variable {m : ℕ}

/-- The **Noda cross-form** `B m u v = u ⬝ᵥ (N *ᵥ v) = ∑ⱼₖ uⱼ Nⱼₖ vₖ`, the
scalar bilinear form of the Hilbert–Noda kernel `N = hilbertNoda m`. It is the
un-normalized `(u, v)` entry of the asynchronous 2DCOS map (`asyncMatrix`). -/
noncomputable def B (m : ℕ) (u v : Fin m → ℝ) : ℝ :=
  u ⬝ᵥ (hilbertNoda m *ᵥ v)

/-- Unfolded form: `B m u v = ∑ⱼ ∑ₖ uⱼ · Nⱼₖ · vₖ`. -/
theorem B_eq_sum (u v : Fin m → ℝ) :
    B m u v = ∑ j, ∑ k, u j * hilbertNoda m j k * v k := by
  simp only [B, dotProduct, Matrix.mulVec, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- **Antisymmetry of the Noda cross-form**, `B m u v = − B m v u`. This is the
algebra behind the sign-flip of the asynchronous cross-peak under `j ↔ k`
(`sign(Ψ_jk) = − sign(Ψ_kj)`). Proved from `Nᵀ = −N`
(`hilbertNoda_transpose_neg`) via the `dotProduct`/`mulVec`/`transpose`
identities. -/
theorem B_antisymm (u v : Fin m → ℝ) : B m u v = - B m v u := by
  have h : B m u v = ((hilbertNoda m)ᵀ *ᵥ u) ⬝ᵥ v := by
    rw [B, dotProduct_mulVec, ← mulVec_transpose]
  rw [h, hilbertNoda_transpose_neg, neg_mulVec, neg_dotProduct, dotProduct_comm]
  rfl

/-- **Additivity of `B` in the left argument.** -/
theorem B_add_left (u u' v : Fin m → ℝ) :
    B m (u + u') v = B m u v + B m u' v := by
  simp only [B, add_dotProduct]

/-- **Homogeneity of `B` in the left argument.** -/
theorem B_smul_left (c : ℝ) (u v : Fin m → ℝ) :
    B m (c • u) v = c * B m u v := by
  simp only [B, smul_dotProduct, smul_eq_mul]

/-- **Additivity of `B` in the right argument.** -/
theorem B_add_right (u v v' : Fin m → ℝ) :
    B m u (v + v') = B m u v + B m u v' := by
  simp only [B, mulVec_add, dotProduct_add]

/-- **Homogeneity of `B` in the right argument.** -/
theorem B_smul_right (c : ℝ) (u v : Fin m → ℝ) :
    B m u (c • v) = c * B m u v := by
  simp only [B, mulVec_smul, dotProduct_smul, smul_eq_mul]

/-- **Dynamic-weight scaling.** Two bands whose traces carry scalar amplitudes
`c_j` and `c_k` (`c_j • u`, `c_k • v`) have asynchronous value
`c_j·c_k · B m u v`: the sign is governed by `B m u v` up to the sign of the
amplitude product. -/
theorem B_smul_smul (cj ck : ℝ) (u v : Fin m → ℝ) :
    B m (cj • u) (ck • v) = cj * ck * B m u v := by
  rw [B_smul_left, B_smul_right]; ring

/-- **Self-value vanishes**, `B m u u = 0`: the zero-diagonal law of the
asynchronous map, specialized to the cross-form. Immediate from antisymmetry
`B m u u = − B m u u` over `ℝ`. -/
theorem B_selfZero (u : Fin m → ℝ) : B m u u = 0 := by
  have h := B_antisymm u u
  linarith

/-! ### Non-vacuity sign witness (explicit small data, `m = 3`)

A rising step `u = ![0,1,1]` (intensity rises at gate-delay `1`) against its
one-gate-delayed copy `v = ![0,0,1]` (rises at gate-delay `2`). The Noda
cross-form has a definite positive sign, and its transpose the opposite sign —
so the ordered sign rule is genuinely non-vacuous. -/

/-- The cross-form on the rising step vs its one-gate-delayed copy evaluates to
the explicit value `1/π`. -/
theorem B_stepDelay_eq : B 3 (![0, 1, 1]) (![0, 0, 1]) = 1 / π := by
  rw [B_eq_sum, Fin.sum_univ_three]
  simp only [Fin.sum_univ_three, hilbertNoda, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
    Fin.isValue, Fin.reduceEq, if_true, if_false]
  norm_num

/-- **Definite positive sign of the ordered pair.** `B 3 u v = 1/π > 0` for the
rising step `u` and its one-gate-delayed copy `v`: the sign rule is non-vacuous
(it computes a nonzero, sign-definite value on genuine data). -/
theorem B_stepDelay_pos : 0 < B 3 (![0, 1, 1]) (![0, 0, 1]) := by
  rw [B_stepDelay_eq]; positivity

/-- **Sign flip under order reversal.** The reversed pair has the opposite
(negative) sign, `B 3 v u = −1/π < 0`: `sign(B u v) = − sign(B v u)`. -/
theorem B_stepDelay_rev_neg : B 3 (![0, 0, 1]) (![0, 1, 1]) < 0 := by
  have h : B 3 (![0, 0, 1]) (![0, 1, 1]) = - B 3 (![0, 1, 1]) (![0, 0, 1]) := by
    rw [← B_antisymm]
  rw [h, B_stepDelay_eq]
  have : (0 : ℝ) < 1 / π := by positivity
  linarith

end CflibsFormal
