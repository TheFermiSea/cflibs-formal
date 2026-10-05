-- Summary: Full Lean proof: L4a helpers + upper_side + log_selfAbsorptionFactor_lipschitz.
import Mathlib
import CflibsFormal.SelfAbsorption

open CflibsFormal

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

theorem SA_eq {t : ℝ} (ht : 0 < t) :
    selfAbsorptionFactor t = (1 - Real.exp (-t)) / t := by
  rw [selfAbsorptionFactor, if_neg ht.ne']

theorem endpoint_nonneg {b : ℝ} (hb : 0 < b) :
    0 ≤ Real.log ((1 - Real.exp (-b)) / b) + b / 2 := by
  have hs : b ≤ Real.exp (b / 2) - Real.exp (-(b / 2)) := by
    have h := Real.self_le_sinh_iff.mpr (by linarith : (0:ℝ) ≤ b / 2)
    rw [Real.sinh_eq (b / 2)] at h
    linarith
  have hE : 0 < Real.exp (-(b / 2)) := Real.exp_pos (-(b / 2))
  have hmul : Real.exp (b / 2) * Real.exp (-(b / 2)) = 1 := by
    rw [← Real.exp_add, show b / 2 + -(b / 2) = 0 by ring, Real.exp_zero]
  have hE2 : Real.exp (-b) = Real.exp (-(b / 2)) * Real.exp (-(b / 2)) := by
    rw [show -b = -(b / 2) + -(b / 2) by ring, Real.exp_add]
  have h1 : Real.exp (-(b / 2)) * b ≤ 1 - Real.exp (-(b / 2)) * Real.exp (-(b / 2)) := by
    calc
      _ ≤ Real.exp (-(b / 2)) * (Real.exp (b / 2) - Real.exp (-(b / 2))) :=
        mul_le_mul_of_nonneg_left hs hE.le
      _ = Real.exp (-(b / 2)) * Real.exp (b / 2) - Real.exp (-(b / 2)) * Real.exp (-(b / 2)) := by ring
      _ = 1 - Real.exp (-(b / 2)) * Real.exp (-(b / 2)) := by rw [mul_comm, hmul]
  have h2 : Real.exp (-(b / 2)) ≤ (1 - Real.exp (-b)) / b := by
    rw [le_div_iff₀ hb, hE2]
    exact h1
  have h3 : -(b / 2) ≤ Real.log ((1 - Real.exp (-b)) / b) := by
    rw [← Real.log_exp (-(b / 2))]
    exact Real.log_le_log hE h2
  linarith

theorem log_SA_antitone {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    Real.log (selfAbsorptionFactor b) ≤ Real.log (selfAbsorptionFactor a) := by
  have hle : selfAbsorptionFactor b ≤ selfAbsorptionFactor a := by
    rcases ha.eq_or_lt with h0 | hpos
    · subst h0
      simp [selfAbsorptionFactor]
      exact selfAbsorptionFactor_le_one hab
    · exact selfAbsorptionFactor_strictAntiOn.antitoneOn hpos (lt_of_lt_of_le hpos hab) hab
  exact Real.log_le_log (selfAbsorptionFactor_pos (ha.trans hab)) hle

theorem one_sub_exp_neg_pos {t : ℝ} (ht : 0 < t) : 0 < 1 - Real.exp (-t) := by
  have := Real.exp_lt_exp.mpr (show -t < 0 by linarith)
  rw [Real.exp_zero] at this
  linarith

theorem hasDerivAt_g {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => Real.log (1 - Real.exp (-s)) - Real.log s)
      (1 / (Real.exp t - 1) - 1 / t) t := by
  have he : HasDerivAt (fun s : ℝ => Real.exp (-s)) (Real.exp (-t) * -1) t :=
    (Real.hasDerivAt_exp (-t)).comp t ((hasDerivAt_id t).neg)
  have H := ((he.const_sub 1).log (one_sub_exp_neg_pos ht).ne').sub (Real.hasDerivAt_log ht.ne')
  have hpos : 0 < Real.exp t - 1 := by linarith [Real.add_one_lt_exp ht.ne']
  have hx : Real.exp (-t) * Real.exp t = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have h1 : 1 - Real.exp (-t) = Real.exp (-t) * (Real.exp t - 1) := by
    rw [mul_sub, hx, mul_one]
  have hv : -(Real.exp (-t) * -1) / (1 - Real.exp (-t)) - t⁻¹ = 1 / (Real.exp t - 1) - 1 / t := by
    have hdiv : Real.exp (-t) / (1 - Real.exp (-t)) = 1 / (Real.exp t - 1) := by
      rw [div_eq_div_iff (one_sub_exp_neg_pos ht).ne' hpos.ne']
      rw [h1]; ring
    rw [show -(Real.exp (-t) * -1) = Real.exp (-t) by ring, hdiv]; ring
  exact H.congr_deriv hv

theorem hasDerivAt_logSA {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => Real.log (selfAbsorptionFactor s))
      (1 / (Real.exp t - 1) - 1 / t) t := by
  refine (hasDerivAt_g ht).congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds ht] with s hs
  rw [SA_eq hs, Real.log_div (one_sub_exp_neg_pos hs).ne' (ne_of_gt hs)]

theorem h_monotoneOn_Ioi :
    MonotoneOn (fun s => Real.log (selfAbsorptionFactor s) + s / 2) (Set.Ioi (0:ℝ)) := by
  have hd : ∀ x, 0 < x → HasDerivAt (fun s => Real.log (selfAbsorptionFactor s) + s / 2)
      (1 / (Real.exp x - 1) - 1 / x + 1 / 2) x :=
    fun x hx => (hasDerivAt_logSA hx).add ((hasDerivAt_id x).div_const 2)
  exact monotoneOn_of_hasDerivWithinAt_nonneg
      (f' := fun x => 1 / (Real.exp x - 1) - 1 / x + 1 / 2) (convex_Ioi 0)
    (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
    (fun x hx => by
      rw [interior_Ioi] at hx ⊢
      exact (hd x hx).hasDerivWithinAt)
    (fun x hx => by rw [interior_Ioi] at hx; linarith [(inv_sub_inv_exp_sub_one_mem hx).2])

lemma upper_side {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    Real.log (selfAbsorptionFactor a) - Real.log (selfAbsorptionFactor b) ≤ (b - a) / 2 := by
  by_cases ha0 : a = 0
  · by_cases hb0 : b = 0
    · subst ha0 hb0
      simp [selfAbsorptionFactor]
    · have hb' : 0 < b := lt_of_le_of_ne (ha0 ▸ hab) (Ne.symm hb0)
      have hSA0 : selfAbsorptionFactor a = 1 := by simp [ha0, selfAbsorptionFactor]
      rw [hSA0, SA_eq hb', Real.log_one]
      linarith [endpoint_nonneg hb']
  · have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    have hb' : 0 < b := by linarith
    have hmono := h_monotoneOn_Ioi ha' hb' hab
    simp only at hmono
    linarith

theorem log_selfAbsorptionFactor_lipschitz {τ τ' : ℝ} (hτ : 0 ≤ τ) (hτ' : 0 ≤ τ') :
    |Real.log (selfAbsorptionFactor τ) - Real.log (selfAbsorptionFactor τ')|
      ≤ |τ - τ'| / 2 := by
  cases le_total τ τ' with
  | inl hle =>
    have hant := log_SA_antitone hτ hle
    have hsub : 0 ≤ Real.log (selfAbsorptionFactor τ) - Real.log (selfAbsorptionFactor τ') := by linarith
    rw [abs_of_nonneg hsub]
    have hup := upper_side hτ hle
    have hd : 0 ≤ τ' - τ := by linarith
    rw [abs_sub_comm, abs_of_nonneg hd]
    linarith
  | inr hle =>
    have hant := log_SA_antitone hτ' hle
    have hsub' : Real.log (selfAbsorptionFactor τ) - Real.log (selfAbsorptionFactor τ') ≤ 0 := by linarith
    have hup := upper_side hτ' hle
    have hd : 0 ≤ τ - τ' := by linarith
    rw [abs_of_nonpos hsub', abs_of_nonneg hd]
    linarith

end Plan.FT13
