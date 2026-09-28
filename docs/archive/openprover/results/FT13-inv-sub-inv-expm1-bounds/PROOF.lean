-- Summary: Full Lean proof of 0 < 1/τ - 1/(e^τ-1) < 1/2 for τ>0.
import Mathlib

namespace Plan.FT13

theorem exp_mul_one_sub_lt_one {x : ℝ} (hx : 0 < x) :
    Real.exp x * (1 - x) < 1 := by
  have h1 : 1 - x < Real.exp (-x) := Real.one_sub_lt_exp_neg hx.ne'
  have h2 : Real.exp x * (1 - x) < Real.exp x * Real.exp (-x) :=
    mul_lt_mul_of_pos_left h1 (Real.exp_pos x)
  rwa [← Real.exp_add, add_neg_cancel, Real.exp_zero] at h2

theorem f_hasDerivAt (t : ℝ) :
    HasDerivAt (fun t => Real.exp t * (t - 2) + t + 2)
      (Real.exp t * (t - 2) + Real.exp t * 1 + 1) t :=
  (((Real.hasDerivAt_exp t).mul ((hasDerivAt_id t).sub_const 2)).add (hasDerivAt_id t)).add_const 2

theorem f_pos {τ : ℝ} (hτ : 0 < τ) : 0 < Real.exp τ * (τ - 2) + τ + 2 := by
  have hmono : StrictMonoOn (fun t => Real.exp t * (t - 2) + t + 2) (Set.Ici (0:ℝ)) := by
    refine strictMonoOn_of_hasDerivWithinAt_pos (convex_Ici (0:ℝ)) ?_
      (fun x _ => (f_hasDerivAt x).hasDerivWithinAt) ?_
    · fun_prop
    · intro x hx
      rw [interior_Ici] at hx
      have hx' : 0 < x := hx
      nlinarith [exp_mul_one_sub_lt_one hx', Real.exp_pos x]
  have h0 : (0:ℝ) ∈ Set.Ici (0:ℝ) := Set.mem_Ici.mpr le_rfl
  have hτ' : τ ∈ Set.Ici (0:ℝ) := Set.mem_Ici.mpr hτ.le
  have := hmono h0 hτ' hτ
  simp at this
  linarith

theorem inv_sub_inv_exp_sub_one_mem {τ : ℝ} (hτ : 0 < τ) :
    0 < 1 / τ - 1 / (Real.exp τ - 1) ∧ 1 / τ - 1 / (Real.exp τ - 1) < 1 / 2 := by
  constructor
  · have hlt : τ < Real.exp τ - 1 := by linarith [Real.add_one_lt_exp hτ.ne']
    have := one_div_lt_one_div_of_lt hτ hlt
    linarith
  · have hE : 0 < Real.exp τ - 1 := by linarith [Real.add_one_lt_exp hτ.ne']
    have hf := f_pos hτ
    rw [div_sub_div _ _ hτ.ne' hE.ne', div_lt_div_iff₀ (mul_pos hτ hE) (by norm_num : (0:ℝ) < 2)]
    nlinarith [hf, Real.exp_pos τ]

end Plan.FT13
