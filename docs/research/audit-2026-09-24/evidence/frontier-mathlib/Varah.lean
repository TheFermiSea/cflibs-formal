import Mathlib

namespace AuditVarah
open Matrix Finset

theorem linfty_le_of_rowDiagDominant {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (A : Matrix n n ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hdom : ∀ k, δ + ∑ j ∈ univ.erase k, |A k j| ≤ |A k k|) (x : n → ℝ) :
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

end AuditVarah
#print axioms AuditVarah.linfty_le_of_rowDiagDominant
