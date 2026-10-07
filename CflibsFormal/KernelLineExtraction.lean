/-
Copyright (c) 2026 Brian Squires. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Squires
-/
import Mathlib

/-!
# CF-LIBS formalization — kernel least-squares line extraction under profile misspecification

Line intensities are extracted from a spectrum by least squares against a kernel of assumed line
profiles (pixels `P`, lines `L`). When the true profiles differ from the assumed ones, the
extracted intensities are biased. This module bounds that error entrywise and gives it in closed
form (frontier FT-16 of the 2026-09-24 audit).

## Main results

* `kernelLS_error_linfty`: if the Gram matrix `KᵀK` of the assumed kernel is strictly
  row-diagonally dominant with margin `δ > 0`, every solution `Î` of the normal equations obeys
  `|Î_l − I_l| ≤ max_k |(Kᵀ((K_t − K)·I + η))_k| / δ`. The proof goes through the exact error
  identity `KᵀK·(Î − I) = Kᵀ((K_t − K)·I + η)` and the diagonal-dominance bound
  `δ·‖x‖∞ ≤ ‖M·x‖∞`.
* `extractor_bias_identity`: when `KᵀK` is invertible, the extractor `Î = (KᵀK)⁻¹Kᵀ d` has the
  exact error `Î − I = (KᵀK)⁻¹Kᵀ((K_t − K)·I) + (KᵀK)⁻¹Kᵀ η`, a misspecification bias plus a
  linear noise term.

## Scope

`PURE-MATH`: linear algebra over real matrices; no physics definition is used. Only the margin
`δ` is checkable at runtime from the extractor's own kernel; the numerator (profile
misspecification acting on the true intensities, plus noise) is an assumed input. The physics
reading (optically thin plasma, additive line profiles, kernel fixed within a solver step) is a
reduced model and stays in prose.

## Literature

No physics citation applies: the result is linear algebra. The classical diagonal-dominance
`ℓ∞` bound is not cited until it passes citation integrity. For the instrument function that
the kernel models, see Cremers & Radziemski 2013 (*Handbook of Laser-Induced Breakdown
Spectroscopy*).
-/

open Finset Matrix

namespace CflibsFormal

variable {P L : Type*} [Fintype P] [Fintype L] [DecidableEq L]

/-- For a strictly row-diagonally-dominant matrix with margin `δ`, every component of `x` is
bounded by the sup norm of `A x` divided by `δ`. -/
private theorem linfty_le_of_rowDiagDominant [Nonempty L]
    (A : Matrix L L ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hdom : ∀ k, δ + ∑ j ∈ univ.erase k, |A k j| ≤ |A k k|) (x : L → ℝ) :
    ∀ i, |x i| ≤ (univ.sup' univ_nonempty fun k => |(A *ᵥ x) k|) / δ := by
  intro i
  obtain ⟨i0, -, hi0⟩ := Finset.exists_max_image univ (fun i => |x i|) univ_nonempty
  have hsplit : (A *ᵥ x) i0 = A i0 i0 * x i0 + ∑ j ∈ univ.erase i0, A i0 j * x j := by
    simp only [mulVec, dotProduct]
    rw [← Finset.add_sum_erase _ _ (mem_univ i0)]
  have hrest : |∑ j ∈ univ.erase i0, A i0 j * x j|
      ≤ (∑ j ∈ univ.erase i0, |A i0 j|) * |x i0| := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum (fun j _ => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hi0 j (mem_univ j)) (abs_nonneg _)
  have hkey : δ * |x i0| ≤ |(A *ᵥ x) i0| := by
    have h1 : |A i0 i0 * x i0| ≤ |(A *ᵥ x) i0| + |∑ j ∈ univ.erase i0, A i0 j * x j| := by
      have hA : A i0 i0 * x i0 = (A *ᵥ x) i0 - ∑ j ∈ univ.erase i0, A i0 j * x j := by
        rw [hsplit]; ring
      rw [hA]
      exact abs_sub _ _
    rw [abs_mul] at h1
    have h2 := mul_le_mul_of_nonneg_right (hdom i0) (abs_nonneg (x i0))
    nlinarith [h1, h2, hrest]
  have hsup : |(A *ᵥ x) i0| ≤ univ.sup' univ_nonempty fun k => |(A *ᵥ x) k| :=
    Finset.le_sup' (fun k => |(A *ᵥ x) k|) (mem_univ i0)
  rw [le_div_iff₀ hδ]
  nlinarith [hi0 i (mem_univ i), hkey, hsup, abs_nonneg (x i)]

omit [DecidableEq L] in
/-- The normal equations under a misspecified kernel give the error identity
`Kᵀ K (Î − I) = Kᵀ ((K̃ − K) I + η)`. -/
private theorem normal_error_identity (K Kt : Matrix P L ℝ) (I Ihat : L → ℝ) (η : P → ℝ)
    (hnormal : (Kᵀ * K).mulVec Ihat = Kᵀ.mulVec (Kt.mulVec I + η)) :
    (Kᵀ * K).mulVec (Ihat - I) = Kᵀ.mulVec ((Kt - K).mulVec I + η) := by
  rw [Matrix.mulVec_sub, hnormal, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_sub]
  abel

/-- **ℓ∞ error of kernel least-squares line extraction under a misspecified profile kernel.**
Pixels `P`, lines `L`. The data are `d = K_t·I + η` (true kernel `Kt`, true line intensities
`I`, noise `η`); the extractor uses an assumed kernel `K` and returns any `Î` solving the normal
equations `KᵀK·Î = Kᵀ·d` (`hnormal`). If the Gram matrix `KᵀK` is strictly row-diagonally
dominant with margin `δ > 0` (`hdom`), then every extracted intensity satisfies
  `|Î_l − I_l| ≤ max_k |(Kᵀ((K_t − K)·I + η))_k| / δ`.
Reason: `KᵀK·(Î − I) = Kᵀ((K_t − K)·I + η)` exactly, and for a row-diagonally dominant `M` with
margin `δ`, `δ·‖x‖∞ ≤ ‖M·x‖∞` (take the row of a maximal `|x_i|`). Not vacuous: with `K_t = K`
and `η = 0` the right side is `0` and the extraction is exact.

Honest reading: the numerator is an **assumed** input (a bound on the profile misspecification
`K_t − K` acting on `I`, plus a noise bound); only the margin `δ` of `hdom` is checkable at runtime
from the extractor's own kernel. `hdom` also makes `KᵀK` invertible, so `Î` is unique, but the
theorem does not need that. Hypotheses: `hδ` (a strict margin; the division by `δ` needs
`δ > 0`); `hdom` (the checkable margin condition); `hnormal` (what the extractor computes);
`[Nonempty L]` (the maximum over lines is over a nonempty set); `[DecidableEq L]` (for
`univ.erase`).

Scope: relation PURE-MATH (abstract real matrices); no physics definition is used; published
PURE-MATH. The physics reading (optically thin, additive line profiles, kernel fixed per solver
step) is REDUCED and stays in prose. No citation: the classical diagonal-dominance bound is not
yet on the citation whitelist. -/
theorem kernelLS_error_linfty [Nonempty L] (K Kt : Matrix P L ℝ) (I Ihat : L → ℝ) (η : P → ℝ)
    {δ : ℝ} (hδ : 0 < δ)
    (hdom : ∀ k, δ + ∑ j ∈ univ.erase k, |(Kᵀ * K) k j| ≤ |(Kᵀ * K) k k|)
    (hnormal : (Kᵀ * K).mulVec Ihat = Kᵀ.mulVec (Kt.mulVec I + η)) (l : L) :
    |Ihat l - I l|
      ≤ (univ.sup' univ_nonempty fun k => |(Kᵀ.mulVec ((Kt - K).mulVec I + η)) k|) / δ := by
  have h := linfty_le_of_rowDiagDominant (Kᵀ * K) hδ hdom (Ihat - I) l
  rw [normal_error_identity K Kt I Ihat η hnormal, Pi.sub_apply] at h
  exact h

/-- **Closed-form error identity of the kernel least-squares extractor (FT-16).** Pixels `P`,
lines `L`. Let the data be `d = K_t·I + η` (true kernel `Kt`, true intensities `I`, noise `η`)
and let the extractor use an assumed kernel `K` with invertible Gram matrix `KᵀK` (`hdet`), so
it returns `Î = (KᵀK)⁻¹Kᵀ d`. Then exactly
  `Î - I = (KᵀK)⁻¹Kᵀ((K_t - K)·I) + (KᵀK)⁻¹Kᵀ η`,
the sum of a misspecification bias and a linear noise term.

Reading: the first term is the bias from profile misspecification; it vanishes when `K_t = K`,
so an extractor built at the true kernel recovers `I` up to the noise term only (an "oracle"
extractor validates structure, not misspecification). The identity is the explicit-inverse
counterpart of the normal-equation identity behind `kernelLS_error_linfty`. It is only algebra
on the inverse: `G = (KᵀK)⁻¹Kᵀ` is a left inverse of `K`, and `mulVec` is linear.

Hypotheses: `hdet : IsUnit (KᵀK).det` is needed: it gives `(KᵀK)⁻¹KᵀK = 1`. Without it
Mathlib's `⁻¹` is `0` and the identity fails (e.g. `K = 0`, `I ≠ 0`: left side `-I`, right side
`0`). `hdet` holds iff `K` has full column rank; the row-diagonal-dominance margin of
`kernelLS_error_linfty` implies it, but that link is not part of this statement.
`[DecidableEq L]` is required by `Matrix.inv`.

Scope: PURE-MATH (linear algebra over real matrices; no physics definition is used). The physics
reading (optically thin plasma, additive line profiles, kernel fixed within a solver step) is
REDUCED and stays in prose. No citation (linear algebra). -/
theorem extractor_bias_identity (K Kt : Matrix P L ℝ) (I : L → ℝ) (η : P → ℝ)
    (hdet : IsUnit (Kᵀ * K).det) :
    ((Kᵀ * K)⁻¹ * Kᵀ).mulVec (Kt.mulVec I + η) - I
      = ((Kᵀ * K)⁻¹ * Kᵀ).mulVec ((Kt - K).mulVec I) + ((Kᵀ * K)⁻¹ * Kᵀ).mulVec η := by
  have hG : (Kᵀ * K)⁻¹ * Kᵀ * K = 1 := by
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet]
  have hI : ((Kᵀ * K)⁻¹ * Kᵀ).mulVec (K.mulVec I) = I := by
    rw [Matrix.mulVec_mulVec, hG, Matrix.one_mulVec]
  rw [Matrix.mulVec_add, Matrix.sub_mulVec, Matrix.mulVec_sub, hI]
  abel

/-- Non-vacuity of `extractor_bias_identity` with a nonzero bias: one pixel, one line, assumed
kernel `K = (1)`, true kernel `K_t = (2)`, `I = 1`, no noise. `KᵀK = (1)` is invertible, and
the extractor returns `2`, a bias of `1`. -/
example : ((!![(1 : ℝ)]ᵀ * !![(1 : ℝ)])⁻¹ * !![(1 : ℝ)]ᵀ).mulVec
      ((!![(2 : ℝ)] - !![(1 : ℝ)]).mulVec ![1]) = ![1] ∧
    ((!![(1 : ℝ)]ᵀ * !![(1 : ℝ)])⁻¹ * !![(1 : ℝ)]ᵀ).mulVec (!![(2 : ℝ)].mulVec ![1] + 0) - ![1]
      = ((!![(1 : ℝ)]ᵀ * !![(1 : ℝ)])⁻¹ * !![(1 : ℝ)]ᵀ).mulVec
          ((!![(2 : ℝ)] - !![(1 : ℝ)]).mulVec ![1])
        + ((!![(1 : ℝ)]ᵀ * !![(1 : ℝ)])⁻¹ * !![(1 : ℝ)]ᵀ).mulVec 0 := by
  refine ⟨?_, extractor_bias_identity _ _ _ _ (by simp [Matrix.mul_apply])⟩
  ext i
  fin_cases i
  simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]
  norm_num

end CflibsFormal
