import Mathlib
import CflibsFormal.SahaEquilibrium

open Finset

namespace Scratch

/-- A-posteriori bound for a box contraction (sketch). -/
theorem aposteriori_box {Φ : ℝ → ℝ} {a b q x xs : ℝ} (hq : q < 1)
    (hL : ∀ u ∈ Set.Icc a b, ∀ v ∈ Set.Icc a b, |Φ u - Φ v| ≤ q * |u - v|)
    (hx : x ∈ Set.Icc a b) (hxs : xs ∈ Set.Icc a b) (hfix : Φ xs = xs) :
    |x - xs| ≤ |Φ x - x| / (1 - q) := by
  rw [le_div_iff₀ (by linarith)]
  have h1 : |x - xs| ≤ |x - Φ x| + |Φ x - Φ xs| := by
    calc |x - xs| = |(x - Φ x) + (Φ x - xs)| := by ring_nf
      _ ≤ |x - Φ x| + |Φ x - xs| := abs_add_le _ _
      _ = |x - Φ x| + |Φ x - Φ xs| := by rw [hfix]
  have h2 := hL x hx xs hxs
  rw [abs_sub_comm x (Φ x)] at h1
  nlinarith [abs_nonneg (x - xs)]

/-- Damped (Krasnoselskii–Mann) step: the stop test sees `α` times the map residual. -/
theorem aposteriori_damped {Φ : ℝ → ℝ} {a b q α x xs : ℝ} (hq : q < 1) (hα : 0 < α)
    (hL : ∀ u ∈ Set.Icc a b, ∀ v ∈ Set.Icc a b, |Φ u - Φ v| ≤ q * |u - v|)
    (hx : x ∈ Set.Icc a b) (hxs : xs ∈ Set.Icc a b) (hfix : Φ xs = xs) :
    |x - xs| ≤ |((1 - α) * x + α * Φ x) - x| / (α * (1 - q)) := by
  have hstep : ((1 - α) * x + α * Φ x) - x = α * (Φ x - x) := by ring
  rw [hstep, abs_mul, abs_of_pos hα, mul_div_mul_left _ _ hα.ne']
  exact aposteriori_box hq hL hx hxs hfix

/-- No q-free stopping rule is sound: tiny residual, large error. -/
theorem stopping_needs_rate (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ q : ℝ, 0 ≤ q ∧ q < 1 ∧ |(q * ε) - ε| ≤ δ ∧ ε ≤ |ε - 0| := by
  refine ⟨max 0 (1 - δ / ε), le_max_left _ _, ?_, ?_, by simp [abs_of_pos hε]⟩
  · rcases le_total 0 (1 - δ / ε) with h | h
    · rw [max_eq_right h]; have : 0 < δ / ε := div_pos hδ hε; linarith
    · rw [max_eq_left h]; norm_num
  · have hq1 : max 0 (1 - δ / ε) ≤ 1 := max_le (by norm_num) (by have := div_pos hδ hε; linarith)
    rw [show max 0 (1 - δ / ε) * ε - ε = -((1 - max 0 (1 - δ / ε)) * ε) by ring, abs_neg,
      abs_of_nonneg (mul_nonneg (by linarith) hε.le)]
    have : 1 - δ / ε ≤ max 0 (1 - δ / ε) := le_max_right _ _
    have h2 : (1 - max 0 (1 - δ / ε)) * ε ≤ (δ / ε) * ε := by
      apply mul_le_mul_of_nonneg_right _ hε.le; linarith
    rwa [div_mul_cancel₀ δ hε.ne'] at h2

variable {ι : Type*} [Fintype ι]

/-- Newton error identity for multi-element charge neutrality (termwise). -/
theorem newton_term_identity {a S x xs : ℝ} (hx : 0 < x + S) (hxs : 0 < xs + S) :
    a / (xs + S) - a / (x + S) - (-(a / (x + S) ^ 2)) * (xs - x)
      = a * (x - xs) ^ 2 / ((x + S) ^ 2 * (xs + S)) := by
  field_simp
  ring

end Scratch
