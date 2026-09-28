-- Summary: Weighted Chebyshev proof of tiltMean_reweight_le.
import Mathlib
import CflibsFormal.InhomogeneityBias

open CflibsFormal Finset

namespace Plan.FT19

-- Each term u_i u_j (ρ_i-ρ_j)(b_i-b_j) ≤ 0 by trichotomy on b_i, b_j.
theorem cheb_double_sum_nonpos {ζ : Type*} [Fintype ζ] {u b ρ : ζ → ℝ}
    (hu : ∀ z, 0 < u z) (hanti : ∀ i j, b i < b j → ρ j ≤ ρ i) :
    ∑ i, ∑ j, u i * u j * ((ρ i - ρ j) * (b i - b j)) ≤ 0 := by
  apply Finset.sum_nonpos; intro i _
  apply Finset.sum_nonpos; intro j _
  have huij : 0 < u i * u j := mul_pos (hu i) (hu j)
  have key : (ρ i - ρ j) * (b i - b j) ≤ 0 := by
    rcases lt_trichotomy (b i) (b j) with h | h | h
    · have := hanti i j h
      exact mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
    · simp [h]
    · have := hanti j i h
      exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  exact mul_nonpos_of_nonneg_of_nonpos huij.le key

-- Chebyshev double-sum identity.
theorem cheb_identity {ζ : Type*} [Fintype ζ] (u b ρ : ζ → ℝ) :
    ∑ i, ∑ j, u i * u j * ((ρ i - ρ j) * (b i - b j)) =
      2 * ((∑ z, u z * ρ z * b z) * (∑ z, u z) - (∑ z, u z * b z) * (∑ z, u z * ρ z)) := by
  calc
    _ = ∑ i, ∑ j, ((u i * ρ i * b i) * u j + (-(u i * ρ i)) * (u j * b j) + (-(u i * b i)) * (u j * ρ j) + u i * (u j * ρ j * b j)) := by
        apply Finset.sum_congr rfl; intro i _
        apply Finset.sum_congr rfl; intro j _
        ring
    _ = (∑ i, ∑ j, (u i * ρ i * b i) * u j) + (∑ i, ∑ j, -(u i * ρ i) * (u j * b j)) +
        (∑ i, ∑ j, -(u i * b i) * (u j * ρ j)) + (∑ i, ∑ j, u i * (u j * ρ j * b j)) := by
        simp only [Finset.sum_add_distrib]
    _ = (∑ i, u i * ρ i * b i) * (∑ j, u j) + (∑ i, -(u i * ρ i)) * (∑ j, u j * b j) +
        (∑ i, -(u i * b i)) * (∑ j, u j * ρ j) + (∑ i, u i) * (∑ j, u j * ρ j * b j) := by
        rw [← Finset.sum_mul_sum, ← Finset.sum_mul_sum, ← Finset.sum_mul_sum, ← Finset.sum_mul_sum]
    _ = (∑ i, u i * ρ i * b i) * (∑ j, u j) + (-(∑ i, u i * ρ i)) * (∑ j, u j * b j) +
        (-(∑ i, u i * b i)) * (∑ j, u j * ρ j) + (∑ i, u i) * (∑ j, u j * ρ j * b j) := by
        simp only [Finset.sum_neg_distrib]
    _ = 2 * ((∑ z, u z * ρ z * b z) * (∑ z, u z) - (∑ z, u z * b z) * (∑ z, u z * ρ z)) := by
        ring

-- Weighted Chebyshev.
theorem weighted_cheb {ζ : Type*} [Fintype ζ] {u b ρ : ζ → ℝ}
    (hu : ∀ z, 0 < u z) (hanti : ∀ i j, b i < b j → ρ j ≤ ρ i) :
    (∑ z, u z * ρ z * b z) * (∑ z, u z) ≤ (∑ z, u z * b z) * (∑ z, u z * ρ z) := by
  have h1 := cheb_double_sum_nonpos hu hanti
  rw [cheb_identity] at h1
  linarith

-- Main theorem: closed forms for both tilted means, cross-multiply, weighted Chebyshev.
theorem tiltMean_reweight_le {ζ : Type*} [Fintype ζ] [Nonempty ζ] {w b ρ : ζ → ℝ}
    (hw : ∀ z, 0 < w z) (hρ : ∀ z, 0 < ρ z) (hanti : ∀ i j, b i < b j → ρ j ≤ ρ i) (a : ℝ) :
    tiltMean (fun z => w z * ρ z) b a ≤ tiltMean w b a := by
  let u : ζ → ℝ := fun z => w z * Real.exp (-(a * b z))
  let uρ : ζ → ℝ := fun z => w z * ρ z * Real.exp (-(a * b z))
  have hu : ∀ z, 0 < u z := fun z => mul_pos (hw z) (Real.exp_pos _)
  have hsumu : 0 < ∑ z, u z := Finset.sum_pos (fun z _ => hu z) Finset.univ_nonempty
  have hsumur : 0 < ∑ z, u z * ρ z :=
    Finset.sum_pos (fun z _ => mul_pos (hu z) (hρ z)) Finset.univ_nonempty
  have hsumur' : 0 < ∑ z, uρ z :=
    Finset.sum_pos (fun z _ => mul_pos (mul_pos (hw z) (hρ z)) (Real.exp_pos _)) Finset.univ_nonempty
  have hmean_w : tiltMean w b a = (∑ z, u z * b z) / ∑ z, u z := by
    simp only [tiltMean, tiltWeight, mixture]
    have h1 : ∑ z, (w z * Real.exp (-(a * b z)) / ∑ z, w z * Real.exp (-(a * b z))) * b z =
              ∑ z, (u z / ∑ z, u z) * b z := by
      apply Finset.sum_congr rfl; intro z _
      rfl
    rw [h1]
    have h2 : ∑ z, (u z / ∑ z, u z) * b z = ∑ z, (u z * b z) / ∑ z, u z := by
      apply Finset.sum_congr rfl; intro z _
      field_simp [hsumu.ne']
    rw [h2, ← Finset.sum_div]
  have hmean_wr : tiltMean (fun z => w z * ρ z) b a = (∑ z, u z * ρ z * b z) / ∑ z, u z * ρ z := by
    simp only [tiltMean, tiltWeight, mixture]
    have h1 : ∑ z, (w z * ρ z * Real.exp (-(a * b z)) / ∑ z, w z * ρ z * Real.exp (-(a * b z))) * b z =
              ∑ z, (uρ z / ∑ z, uρ z) * b z := by
      apply Finset.sum_congr rfl; intro z _
      rfl
    rw [h1]
    have h2 : ∑ z, (uρ z / ∑ z, uρ z) * b z = ∑ z, (uρ z * b z) / ∑ z, uρ z := by
      apply Finset.sum_congr rfl; intro z _
      field_simp [hsumur'.ne']
    have hn : ∑ z, uρ z * b z = ∑ z, u z * ρ z * b z := by
      apply Finset.sum_congr rfl; intro z _
      dsimp only [u, uρ]; ring
    have hd : ∑ z, uρ z = ∑ z, u z * ρ z := by
      apply Finset.sum_congr rfl; intro z _
      dsimp only [u, uρ]; ring
    rw [h2, ← Finset.sum_div, hn, hd]
  rw [hmean_wr, hmean_w, div_le_div_iff₀ hsumur hsumu]
  exact weighted_cheb hu hanti

end Plan.FT19
