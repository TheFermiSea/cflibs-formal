import CflibsFormal

open Finset Real Filter Topology
open scoped BigOperators

namespace SlateProofs2
open CflibsFormal

/-- FT-07 clr is additive under perturbation. -/
theorem clr_mul {ι : Type*} [Fintype ι] {x a : ι → ℝ} (hx : ∀ k, 0 < x k) (ha : ∀ k, 0 < a k) :
    clr (fun k => a k * x k) = fun k => clr a k + clr x k := by
  funext k
  unfold clr
  have hlog : ∀ j, Real.log (a j * x j) = Real.log (a j) + Real.log (x j) := fun j =>
    Real.log_mul (ha j).ne' (hx j).ne'
  simp only [hlog, Finset.sum_add_distrib]
  ring

/-- FT-07 relative closure bound (abundance-scaled). -/
theorem composition_rel_error_mul {ι : Type*} [Fintype ι] {N Nhat : ι → ℝ} {η : ℝ}
    (hN : ∀ s, 0 < N s) (hη0 : 0 ≤ η) (hη1 : η < 1) (hmul : ∀ s, |Nhat s - N s| ≤ η * N s)
    (s : ι) :
    |composition Nhat s - composition N s| ≤ (2 * η / (1 - η)) * composition N s := by
  have hS : 0 < ∑ t, N t := Finset.sum_pos (fun t _ => hN t) ⟨s, Finset.mem_univ s⟩
  have hlo : ∀ t, (1 - η) * N t ≤ Nhat t := fun t => by
    have := (abs_le.mp (hmul t)).1; linarith
  have hhi : ∀ t, Nhat t ≤ (1 + η) * N t := fun t => by
    have := (abs_le.mp (hmul t)).2; linarith
  have hSh_lo : (1 - η) * ∑ t, N t ≤ ∑ t, Nhat t := by
    rw [Finset.mul_sum]; exact Finset.sum_le_sum fun t _ => hlo t
  have hSh_hi : ∑ t, Nhat t ≤ (1 + η) * ∑ t, N t := by
    rw [Finset.mul_sum]; exact Finset.sum_le_sum fun t _ => hhi t
  have h1η : 0 < 1 - η := by linarith
  have hSh : 0 < ∑ t, Nhat t := lt_of_lt_of_le (mul_pos h1η hS) hSh_lo
  unfold composition totalDensity
  set S := ∑ t, N t
  set Sh := ∑ t, Nhat t
  have key : Nhat s / Sh - N s / S = (Nhat s * S - N s * Sh) / (Sh * S) := by
    field_simp
  rw [key, abs_div, abs_of_pos (mul_pos hSh hS)]
  rw [div_le_iff₀ (mul_pos hSh hS)]
  -- |Nhat s·S − N s·Sh| ≤ 2η N s S ; then divide
  have hnum : |Nhat s * S - N s * Sh| ≤ 2 * η * N s * S := by
    rw [abs_le]; constructor
    · nlinarith [hlo s, hSh_hi, hN s, hS]
    · nlinarith [hhi s, hSh_lo, hN s, hS]
  have hfac : 2 * η * N s * S ≤ 2 * η / (1 - η) * (N s / S) * (Sh * S) := by
    rw [show 2 * η / (1 - η) * (N s / S) * (Sh * S) = 2 * η * N s * (Sh / (1 - η)) by
      field_simp]
    have : S ≤ Sh / (1 - η) := by rw [le_div_iff₀ h1η]; linarith
    have hc : 0 ≤ 2 * η * N s := by have := hN s; positivity
    exact mul_le_mul_of_nonneg_left this hc
  linarith

/-- FT-01 unit-invariant 2×2 gate (⇐ direction, the constructive half used by a certificate). -/
theorem weights_of_gate {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (h1 : a < 1) (h2 : d < 1) (h3 : b * c < (1 - a) * (1 - d)) :
    ∃ r : ℝ, 0 < r ∧ a + b * r < 1 ∧ c / r + d < 1 := by
  have hd1 : 0 < 1 - d := by linarith
  have ha1 : 0 < 1 - a := by linarith
  rcases hb.eq_or_lt with hb0 | hbpos
  · subst hb0
    refine ⟨c / (1 - d) + 1, by positivity, by linarith, ?_⟩
    have hr : 0 < c / (1 - d) + 1 := by positivity
    rw [div_add' _ _ _ hr.ne', div_lt_one hr]
    have : c = c / (1 - d) * (1 - d) := by field_simp
    nlinarith
  · set r := (c / (1 - d) + (1 - a) / b) / 2
    have hlo : c / (1 - d) < (1 - a) / b := by
      rw [div_lt_div_iff₀ hd1 hbpos]; nlinarith
    have hr : 0 < r := by
      have : 0 ≤ c / (1 - d) := by positivity
      have : 0 < (1 - a) / b := by positivity
      simp only [r]; linarith
    refine ⟨r, hr, ?_, ?_⟩
    · have : r < (1 - a) / b := by simp only [r]; linarith
      have := (lt_div_iff₀ hbpos).mp this
      linarith
    · have : c / (1 - d) < r := by simp only [r]; linarith
      have h' : c < r * (1 - d) := by rwa [div_lt_iff₀ hd1] at this
      have : c / r < 1 - d := by rw [div_lt_iff₀ hr]; linarith
      linarith

end SlateProofs2

#print axioms SlateProofs2.clr_mul
#print axioms SlateProofs2.composition_rel_error_mul
#print axioms SlateProofs2.weights_of_gate
