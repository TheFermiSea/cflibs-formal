/-
Copyright (c) 2026 Brian Squires. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Squires
-/
import Mathlib

/-!
# 2DCOS-LIBS formalization — Noda two-dimensional correlation algebra

The sound algebraic core of generalized two-dimensional correlation
spectroscopy (2DCOS) applied to gated-delay LIBS. The data is a *dynamic*
(mean-centered) spectrum: `n` channels, each a real time-trace over `m`
gate-delays, held as a matrix `Y : Matrix (Fin n) (Fin m) ℝ` whose row `a`
is channel `a`'s temporal profile.

We formalize the *correlation matrices* and their exact structural laws:

* `hilbertNoda` — the Hilbert–Noda kernel `N`, and `hilbertNoda_transpose_neg`
  (`Nᵀ = −N`, skew-symmetry).
* `syncMatrix` — the synchronous map `Φ = (1/(m−1))·Y Yᵀ`, with
  `syncMatrix_symm` (`Φᵀ = Φ`), `syncMatrix_diag_eq_variance` (the diagonal is
  the per-channel temporal variance `(1/(m−1))·∑ₜ (Y a t)²`), and
  `syncMatrix_diag_nonneg` (that variance is `≥ 0` for `m ≥ 2`).
* `asyncMatrix` — the asynchronous map `Ψ = (1/(m−1))·Y N Yᵀ`, with
  `asyncMatrix_antisymm` (`Ψᵀ = −Ψ`) and the **zero-diagonal law**
  `asyncMatrix_diag_zero` (`Ψ a a = 0`).
* `asyncMatrix_singleDriver_zero` — a single common temporal driver
  (`Y a t = s a · δ t`, a rank-1 dynamic spectrum) yields `Ψ ≡ 0`:
  asynchronicity requires ≥ 2 independent temporal profiles (phase diversity).

## Literature

Noda, *Appl. Spectrosc.* **47** (1993) 1329 (generalized 2DCOS; the
zero asynchronous diagonal). Noda, *Appl. Spectrosc.* **54** (2000) 994
(the Hilbert–Noda matrix). The compositional-data identities that accompany
this framework (Aitchison 1986; Egozcue et al. 2003) are formalized
separately.

The **zero-diagonal law is a standard, universal property** of Noda's
antisymmetric operator — true for *every* dynamic dataset — and is therefore
**not** a novel named "Law"; being universal it can falsify no physical model
(see `docs/2dcos/ERRATA.md`, entries C8/C22).

The unsound "Model A/B" claims of the source drafts — standardless /
temperature-free / electron-density-eliminating quantification, the
async-as-Wronskian-flux identity, and the energy-weighted-covariance
quantification claim — are refuted in `docs/2dcos/ERRATA.md` and are
**deliberately NOT formalized here**. Only the true correlation algebra is.
-/

open Matrix Finset Real
open scoped BigOperators

namespace CflibsFormal

variable {n m : ℕ}

/-- The **Hilbert–Noda kernel** `N : Matrix (Fin m) (Fin m) ℝ`: `Nⱼₖ = 0` on
the diagonal and `1/(π·(k−j))` off it (Noda 2000). This discrete Hilbert-
transform operator is what turns the raw temporal cross-covariance into the
asynchronous (out-of-phase) correlation map. -/
noncomputable def hilbertNoda (m : ℕ) : Matrix (Fin m) (Fin m) ℝ :=
  fun j k => if j = k then 0 else 1 / (π * ((k : ℝ) - (j : ℝ)))

/-- **Skew-symmetry of the Hilbert–Noda kernel**, `Nᵀ = −N` (Noda 1993, 2000).
The off-diagonal entries flip sign under `j ↔ k` because `k − j = −(j − k)`;
the diagonal entries are `0`. This is the single algebraic fact from which the
antisymmetry and zero-diagonal law of the asynchronous map follow. -/
theorem hilbertNoda_transpose_neg (m : ℕ) :
    (hilbertNoda m)ᵀ = - hilbertNoda m := by
  ext j k
  simp only [Matrix.transpose_apply, Matrix.neg_apply, hilbertNoda]
  by_cases h : j = k
  · subst h; simp
  · rw [if_neg (Ne.symm h), if_neg h,
      show π * ((k : ℝ) - (j : ℝ)) = -(π * ((j : ℝ) - (k : ℝ))) from by ring,
      div_neg, neg_neg]

/-- The **synchronous 2DCOS matrix** `Φ = (1/(m−1))·Y Yᵀ` (Noda 1993): the
temporal cross-covariance of the `n` channel traces over `m` gate-delays. The
`(m−1)` factor is honest real division; it is well-behaved for `m ≥ 2`. -/
noncomputable def syncMatrix (Y : Matrix (Fin n) (Fin m) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (1 / ((m : ℝ) - 1)) • (Y * Yᵀ)

/-- **The synchronous map is symmetric**, `Φᵀ = Φ` (Noda 1993). Immediate from
`(Y Yᵀ)ᵀ = Y Yᵀ`. -/
theorem syncMatrix_symm (Y : Matrix (Fin n) (Fin m) ℝ) :
    (syncMatrix Y)ᵀ = syncMatrix Y := by
  simp only [syncMatrix, Matrix.transpose_smul, Matrix.transpose_mul,
    Matrix.transpose_transpose]

/-- **Diagonal of the synchronous map = temporal variance.** `Φ a a` equals
`(1/(m−1))·∑ₜ (Y a t)²`, the auto-power (mean-square fluctuation) of channel
`a`'s time trace. -/
theorem syncMatrix_diag_eq_variance (Y : Matrix (Fin n) (Fin m) ℝ) (a : Fin n) :
    syncMatrix Y a a = (1 / ((m : ℝ) - 1)) * ∑ t, (Y a t) ^ 2 := by
  simp only [syncMatrix, Matrix.smul_apply, Matrix.mul_apply, Matrix.transpose_apply,
    smul_eq_mul, pow_two]

/-- **The synchronous auto-power is nonnegative** for `m ≥ 2`: `0 ≤ Φ a a`. The
prefactor `1/(m−1) ≥ 0` and the sum of squares is nonnegative. -/
theorem syncMatrix_diag_nonneg (hm : 2 ≤ m) (Y : Matrix (Fin n) (Fin m) ℝ) (a : Fin n) :
    0 ≤ syncMatrix Y a a := by
  rw [syncMatrix_diag_eq_variance]
  apply mul_nonneg
  · apply div_nonneg zero_le_one
    have : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  · exact Finset.sum_nonneg (fun t _ => sq_nonneg _)

/-- The **asynchronous 2DCOS matrix** `Ψ = (1/(m−1))·Y N Yᵀ` (Noda 1993, 2000),
where `N` is the Hilbert–Noda kernel `hilbertNoda m`: the out-of-phase (Hilbert-
transformed) temporal cross-correlation of the channel traces. -/
noncomputable def asyncMatrix (Y : Matrix (Fin n) (Fin m) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (1 / ((m : ℝ) - 1)) • (Y * hilbertNoda m * Yᵀ)

/-- **The asynchronous map is antisymmetric**, `Ψᵀ = −Ψ` (Noda 1993, 2000).
Follows from `Nᵀ = −N` (`hilbertNoda_transpose_neg`): transposing `Y N Yᵀ`
returns `Y Nᵀ Yᵀ = −Y N Yᵀ`. -/
theorem asyncMatrix_antisymm (Y : Matrix (Fin n) (Fin m) ℝ) :
    (asyncMatrix Y)ᵀ = - asyncMatrix Y := by
  simp only [asyncMatrix, Matrix.transpose_smul, Matrix.transpose_mul,
    Matrix.transpose_transpose, hilbertNoda_transpose_neg, Matrix.mul_neg,
    Matrix.neg_mul, Matrix.mul_assoc, smul_neg]

/-- **Zero-diagonal law**: `Ψ a a = 0` for every channel `a` (Noda 1993). The
asynchronous map has no auto-peaks. This is a *standard, universal* consequence
of antisymmetry (`M a a = −M a a ⇒ M a a = 0` over `ℝ`), true for *all* data —
it is **not** a novel named "Law" and, being universal, falsifies no physical
model (see `docs/2dcos/ERRATA.md`, C8/C22). -/
theorem asyncMatrix_diag_zero (Y : Matrix (Fin n) (Fin m) ℝ) (a : Fin n) :
    asyncMatrix Y a a = 0 := by
  have h := congrFun (congrFun (asyncMatrix_antisymm Y) a) a
  rw [Matrix.transpose_apply, Matrix.neg_apply] at h
  linarith

/-- **Skew quadratic form vanishes.** For a real skew-symmetric matrix `M`
(`Mᵀ = −M`) and any vector `v`, the quadratic form `∑ⱼ ∑ₖ vⱼ Mⱼₖ vₖ` is `0`:
swapping the summation indices and using `M k j = −M j k` sends the form to its
own negation. The `δᵀ N δ = 0` fact behind the single-driver theorem. -/
lemma skew_quadForm_zero {p : ℕ} (M : Matrix (Fin p) (Fin p) ℝ)
    (hM : Mᵀ = -M) (v : Fin p → ℝ) :
    ∑ j, ∑ k, v j * M j k * v k = 0 := by
  have hMkj : ∀ j k, M k j = - M j k := fun j k => by
    have := congrFun (congrFun hM j) k
    rwa [Matrix.transpose_apply, Matrix.neg_apply] at this
  have hcomm : (∑ j, ∑ k, v j * M j k * v k)
      = ∑ j, ∑ k, v k * M k j * v j := by
    rw [Finset.sum_comm]
  have hsum : (∑ j, ∑ k, v j * M j k * v k)
      + (∑ j, ∑ k, v k * M k j * v j) = 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro j _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro k _
    rw [hMkj j k]
    ring
  linarith [hsum, hcomm]

/-- **Single common driver ⇒ vanishing asynchronous map.** If every channel
trace is a scalar multiple of ONE shared temporal profile `δ` (a rank-1 dynamic
spectrum, `Y a t = s a · δ t`), then `Ψ = 0`. A single monotone cooling driver
produces no asynchronous signal; asynchronicity requires ≥ 2 independent
temporal profiles (phase diversity). Proved via `δᵀ N δ = 0`
(`skew_quadForm_zero`). -/
theorem asyncMatrix_singleDriver_zero (s : Fin n → ℝ) (δ : Fin m → ℝ)
    {Y : Matrix (Fin n) (Fin m) ℝ} (hY : ∀ a t, Y a t = s a * δ t) :
    asyncMatrix Y = 0 := by
  have hquad : (∑ j, ∑ k, δ j * hilbertNoda m j k * δ k) = 0 :=
    skew_quadForm_zero (hilbertNoda m) (hilbertNoda_transpose_neg m) δ
  have hswap : (∑ u, ∑ t, δ t * hilbertNoda m t u * δ u)
      = ∑ j, ∑ k, δ j * hilbertNoda m j k * δ k := by
    rw [Finset.sum_comm]
  ext a b
  have core : (Y * hilbertNoda m * Yᵀ) a b
      = s a * s b * (∑ u, ∑ t, δ t * hilbertNoda m t u * δ u) := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro t _
    rw [hY a t, hY b u]
    ring
  simp only [asyncMatrix, Matrix.smul_apply, Matrix.zero_apply, smul_eq_mul]
  rw [core, hswap, hquad]
  ring

/-! ### Non-vacuity witnesses (concrete small data, `n = 2`, `m = 3`) -/

/-- The Hilbert–Noda skew-symmetry is a nontrivial statement at `m = 3`. -/
example : (hilbertNoda 3)ᵀ = - hilbertNoda 3 := hilbertNoda_transpose_neg 3

/-- The kernel genuinely has a zero diagonal (not vacuous). -/
example : hilbertNoda 3 0 0 = 0 := by simp [hilbertNoda]

example (Y : Matrix (Fin 2) (Fin 3) ℝ) : (syncMatrix Y)ᵀ = syncMatrix Y :=
  syncMatrix_symm Y

example (Y : Matrix (Fin 2) (Fin 3) ℝ) (a : Fin 2) :
    syncMatrix Y a a = (1 / ((3 : ℝ) - 1)) * ∑ t, (Y a t) ^ 2 :=
  syncMatrix_diag_eq_variance Y a

example (Y : Matrix (Fin 2) (Fin 3) ℝ) (a : Fin 2) : 0 ≤ syncMatrix Y a a :=
  syncMatrix_diag_nonneg (by norm_num) Y a

example (Y : Matrix (Fin 2) (Fin 3) ℝ) : (asyncMatrix Y)ᵀ = - asyncMatrix Y :=
  asyncMatrix_antisymm Y

example (Y : Matrix (Fin 2) (Fin 3) ℝ) (a : Fin 2) : asyncMatrix Y a a = 0 :=
  asyncMatrix_diag_zero Y a

/-- A rank-1 (single-driver) dynamic spectrum has an identically zero
asynchronous map. -/
example (s : Fin 2 → ℝ) (δ : Fin 3 → ℝ) :
    asyncMatrix (fun a t => s a * δ t) = 0 :=
  asyncMatrix_singleDriver_zero s δ (fun _ _ => rfl)

/-- **Content of the single-driver theorem.** With ≥ 2 independent temporal
profiles the asynchronous map is *not* zero: for `Y = 1` (channel `a` fires
only at gate-delay `a`), the off-diagonal `Ψ 0 1 = 1/π ≠ 0`. So the vanishing
above is a genuine consequence of phase-degeneracy, not a triviality. -/
example : asyncMatrix (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 1 ≠ 0 := by
  have h : asyncMatrix (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 1
      = (1 / ((2 : ℝ) - 1)) * (1 / (π * ((1 : ℝ) - 0))) := by
    simp [asyncMatrix, hilbertNoda]
  rw [h]; positivity

end CflibsFormal
