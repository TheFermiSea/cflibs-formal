import Mathlib

/-!
# Queue target FT16-kernelLS-error-linfty (deep audit 2026-09-24, FT-16 item 3)

Line extraction by kernel least squares under profile misspecification: a row-diagonal-dominance
margin of the Gram matrix turns a bound on the misspecification-plus-noise residual into an
entrywise (ℓ∞) bound on the extracted intensities. Statement file for the proof queue: one target
theorem, one `sorry`.
-/

open Finset Matrix

namespace Plan.FT16

variable {P L : Type*} [Fintype P] [Fintype L] [DecidableEq L]

theorem linfty_le_of_rowDiagDominant [Nonempty L]
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
theorem normal_error_identity (K Kt : Matrix P L ℝ) (I Ihat : L → ℝ) (η : P → ℝ)
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

Scope (two-axis): relation PURE-MATH (abstract real matrices); no physics definitions are used;
published PURE-MATH. The physics reading (optically thin, additive line profiles, kernel fixed per
solver step) is REDUCED and stays in prose. Citation pending citation-integrity (the classical
diagonal-dominance bound is not on the whitelist; do not cite it until it is). -/
theorem kernelLS_error_linfty [Nonempty L] (K Kt : Matrix P L ℝ) (I Ihat : L → ℝ) (η : P → ℝ)
    {δ : ℝ} (hδ : 0 < δ)
    (hdom : ∀ k, δ + ∑ j ∈ univ.erase k, |(Kᵀ * K) k j| ≤ |(Kᵀ * K) k k|)
    (hnormal : (Kᵀ * K).mulVec Ihat = Kᵀ.mulVec (Kt.mulVec I + η)) (l : L) :
    |Ihat l - I l|
      ≤ (univ.sup' univ_nonempty fun k => |(Kᵀ.mulVec ((Kt - K).mulVec I + η)) k|) / δ := by
  have h := linfty_le_of_rowDiagDominant (Kᵀ * K) hδ hdom (Ihat - I) l
  rw [normal_error_identity K Kt I Ihat η hnormal, Pi.sub_apply] at h
  exact h

end Plan.FT16
