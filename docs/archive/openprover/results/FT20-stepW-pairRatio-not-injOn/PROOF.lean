-- Summary: Full compiling proof of stepW_pairRatio_not_injOn (encl, ratio bounds r1/r3/r10, power forms, f_one/f_three/f_ten, continuity, IVT assembly).
import Mathlib

namespace Plan.FT20

noncomputable def stepW (η M τ : ℝ) : ℝ :=
  (1 - Real.exp (-(τ * (1 + η)))) + (M - 1) * (1 - Real.exp (-(τ * η)))

-- b = exp(-1/100) ∈ [0.99, 0.9901] via 1 + x ≤ exp x.
lemma hb_encl : (0.99:ℝ) ≤ Real.exp (-(1/100)) ∧ Real.exp (-(1/100)) ≤ 0.9901 := by
  constructor
  · have := Real.add_one_le_exp (-(1/100:ℝ)); linarith
  · have h := Real.add_one_le_exp (1/100:ℝ)
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]; linarith

-- a = exp(-101/100) = b / e ∈ [0.3642, 0.3643] via 9-digit bounds on e.
lemma ha_encl : (0.3642:ℝ) ≤ Real.exp (-(101/100)) ∧ Real.exp (-(101/100)) ≤ 0.3643 := by
  obtain ⟨hb1, hb2⟩ := hb_encl
  have e : Real.exp (-(101/100:ℝ)) = Real.exp (-(1/100)) / Real.exp 1 := by
    rw [← Real.exp_sub]; norm_num
  have h1 := Real.exp_one_gt_d9; have h2 := Real.exp_one_lt_d9
  rw [e]; constructor
  · rw [le_div_iff₀ (by linarith)]; nlinarith
  · rw [div_le_iff₀ (by linarith)]; nlinarith

lemma r3 (a b : ℝ) (ha1 : 0.3642 ≤ a) (ha2 : a ≤ 0.3643) (hb1 : 0.99 ≤ b) (hb2 : b ≤ 0.9901) :
    ((1 - a^6) + 19*(1 - b^6)) / ((1 - a^3) + 19*(1 - b^3)) < 29/20 := by
  have hu1 : (0.3642:ℝ)^3 ≤ a^3 := pow_le_pow_left₀ (by norm_num) ha1 3
  have hu2 : a^3 ≤ (0.3643:ℝ)^3 := pow_le_pow_left₀ (by linarith) ha2 3
  have hv1 : (0.99:ℝ)^3 ≤ b^3 := pow_le_pow_left₀ (by norm_num) hb1 3
  have hv2 : b^3 ≤ (0.9901:ℝ)^3 := pow_le_pow_left₀ (by linarith) hb2 3
  have e6a : a^6 = (a^3)^2 := by ring
  have e6b : b^6 = (b^3)^2 := by ring
  rw [e6a, e6b]
  generalize a^3 = u at *; generalize b^3 = v at *
  norm_num at hu1 hu2 hv1 hv2
  rw [div_lt_iff₀ (by nlinarith)]; nlinarith

lemma r1 (a b : ℝ) (ha1 : 0.3642 ≤ a) (ha2 : a ≤ 0.3643) (hb1 : 0.99 ≤ b) (hb2 : b ≤ 0.9901) :
    (29/20:ℝ) < ((1 - a^2) + 19*(1 - b^2)) / ((1 - a) + 19*(1 - b)) := by
  norm_num at ha1 ha2 hb1 hb2
  rw [lt_div_iff₀ (by nlinarith)]
  nlinarith [mul_nonneg (sub_nonneg.2 ha1) (sub_nonneg.2 ha2),
    mul_nonneg (sub_nonneg.2 hb1) (sub_nonneg.2 hb2),
    mul_nonneg (sub_nonneg.2 ha1) (sub_nonneg.2 hb1),
    mul_nonneg (sub_nonneg.2 ha2) (sub_nonneg.2 hb2)]

lemma r10uv (u v : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1/1000) (hv1 : 9/10 ≤ v) (hv2 : v ≤ 91/100) :
    (29/20:ℝ) < ((1 - u^2) + 19*(1 - v^2)) / ((1 - u) + 19*(1 - v)) := by
  rw [lt_div_iff₀ (by nlinarith)]
  nlinarith [mul_nonneg hu0 hu0, mul_nonneg (sub_nonneg.2 hv1) (sub_nonneg.2 hv2),
    mul_nonneg (sub_nonneg.2 hu0) (sub_nonneg.2 hu1)]

lemma r10 (a b : ℝ) (ha1 : 0.3642 ≤ a) (ha2 : a ≤ 0.3643) (hb1 : 0.99 ≤ b) (hb2 : b ≤ 0.9901) :
    (29/20:ℝ) < ((1 - a^20) + 19*(1 - b^20)) / ((1 - a^10) + 19*(1 - b^10)) := by
  have ha0 : (0:ℝ) ≤ a := by linarith
  have hu0 : (0:ℝ) ≤ a^10 := pow_nonneg ha0 10
  have hu1 : a^10 ≤ 1/1000 := by
    calc a^10 ≤ (0.3643:ℝ)^10 := pow_le_pow_left₀ ha0 ha2 10
      _ ≤ 1/1000 := by norm_num
  have hv1 : (9/10:ℝ) ≤ b^10 := by
    calc (9/10:ℝ) ≤ (0.99:ℝ)^10 := by norm_num
      _ ≤ b^10 := pow_le_pow_left₀ (by norm_num) hb1 10
  have hv2 : b^10 ≤ 91/100 := by
    calc b^10 ≤ (0.9901:ℝ)^10 := pow_le_pow_left₀ (by linarith) hb2 10
      _ ≤ 91/100 := by norm_num
  have e20a : a^20 = (a^10)^2 := by ring
  have e20b : b^20 = (b^10)^2 := by ring
  rw [e20a, e20b]
  exact r10uv (a^10) (b^10) hu0 hu1 hv1 hv2

lemma e_a6 : Real.exp (-(2 * 3 * (1 + 1/100))) = Real.exp (-(101/100)) ^ 6 := by
  rw [← Real.exp_nat_mul]; norm_num
lemma e_a3 : Real.exp (-(3 * (1 + 1/100))) = Real.exp (-(101/100)) ^ 3 := by
  rw [← Real.exp_nat_mul]; norm_num
lemma e_b6 : Real.exp (-(2 * 3 * (1/100))) = Real.exp (-(1/100)) ^ 6 := by
  rw [← Real.exp_nat_mul]; norm_num
lemma e_b3 : Real.exp (-(3 * (1/100))) = Real.exp (-(1/100)) ^ 3 := by
  rw [← Real.exp_nat_mul]; norm_num
lemma e_a2 : Real.exp (-(2 * 1 * (1 + 1/100))) = Real.exp (-(101/100)) ^ 2 := by
  rw [← Real.exp_nat_mul]; norm_num
lemma e_a1 : Real.exp (-(1 * (1 + 1/100))) = Real.exp (-(101/100)) ^ 1 := by
  rw [← Real.exp_nat_mul]; norm_num
lemma e_b2 : Real.exp (-(2 * 1 * (1/100))) = Real.exp (-(1/100)) ^ 2 := by
  rw [← Real.exp_nat_mul]; norm_num
lemma e_b1 : Real.exp (-(1 * (1/100))) = Real.exp (-(1/100)) ^ 1 := by
  rw [← Real.exp_nat_mul]; norm_num
lemma e_a20 : Real.exp (-(2 * 10 * (1 + 1/100))) = Real.exp (-(101/100)) ^ 20 := by
  rw [← Real.exp_nat_mul]; norm_num
lemma e_a10 : Real.exp (-(10 * (1 + 1/100))) = Real.exp (-(101/100)) ^ 10 := by
  rw [← Real.exp_nat_mul]; norm_num
lemma e_b20 : Real.exp (-(2 * 10 * (1/100))) = Real.exp (-(1/100)) ^ 20 := by
  rw [← Real.exp_nat_mul]; norm_num
lemma e_b10 : Real.exp (-(10 * (1/100))) = Real.exp (-(1/100)) ^ 10 := by
  rw [← Real.exp_nat_mul]; norm_num

lemma stepW_six : stepW (1/100) 20 (2*3) =
    (1 - Real.exp (-(101/100)) ^ 6) + 19 * (1 - Real.exp (-(1/100)) ^ 6) := by
  unfold stepW; rw [e_a6, e_b6]; norm_num
lemma stepW_three : stepW (1/100) 20 3 =
    (1 - Real.exp (-(101/100)) ^ 3) + 19 * (1 - Real.exp (-(1/100)) ^ 3) := by
  unfold stepW; rw [e_a3, e_b3]; norm_num
lemma stepW_two : stepW (1/100) 20 (2*1) =
    (1 - Real.exp (-(101/100)) ^ 2) + 19 * (1 - Real.exp (-(1/100)) ^ 2) := by
  unfold stepW; rw [e_a2, e_b2]; norm_num
lemma stepW_one : stepW (1/100) 20 1 =
    (1 - Real.exp (-(101/100))) + 19 * (1 - Real.exp (-(1/100))) := by
  unfold stepW; rw [e_a1, e_b1]; norm_num
lemma stepW_twenty : stepW (1/100) 20 (2*10) =
    (1 - Real.exp (-(101/100)) ^ 20) + 19 * (1 - Real.exp (-(1/100)) ^ 20) := by
  unfold stepW; rw [e_a20, e_b20]; norm_num
lemma stepW_ten : stepW (1/100) 20 10 =
    (1 - Real.exp (-(101/100)) ^ 10) + 19 * (1 - Real.exp (-(1/100)) ^ 10) := by
  unfold stepW; rw [e_a10, e_b10]; norm_num

lemma f_three : stepW (1/100) 20 (2*3) / stepW (1/100) 20 3 < 29/20 := by
  rw [stepW_six, stepW_three]
  exact r3 _ _ ha_encl.1 ha_encl.2 hb_encl.1 hb_encl.2

lemma f_one : (29/20:ℝ) < stepW (1/100) 20 (2*1) / stepW (1/100) 20 1 := by
  rw [stepW_two, stepW_one]
  exact r1 _ _ ha_encl.1 ha_encl.2 hb_encl.1 hb_encl.2

lemma f_ten : (29/20:ℝ) < stepW (1/100) 20 (2*10) / stepW (1/100) 20 10 := by
  rw [stepW_twenty, stepW_ten]
  exact r10 _ _ ha_encl.1 ha_encl.2 hb_encl.1 hb_encl.2

lemma f_contOn : ContinuousOn (fun n : ℝ => stepW (1 / 100) 20 (2 * n) / stepW (1 / 100) 20 n)
    (Set.Icc 1 10) := by
  apply ContinuousOn.div (by unfold stepW; fun_prop) (by unfold stepW; fun_prop)
  intro n hn
  apply ne_of_gt
  unfold stepW
  have h1 : Real.exp (-(n * (1 + 1/100))) < 1 := Real.exp_lt_one_iff.2 (by nlinarith [hn.1])
  have h2 : Real.exp (-(n * (1/100))) < 1 := Real.exp_lt_one_iff.2 (by nlinarith [hn.1])
  nlinarith

theorem stepW_pairRatio_not_injOn :
    ¬ Set.InjOn (fun n : ℝ => stepW (1 / 100) 20 (2 * n) / stepW (1 / 100) 20 n)
      (Set.Ioi 0) := by
  intro hinj
  have hc := f_contOn
  have h1 : (29/20:ℝ) < (fun n : ℝ => stepW (1 / 100) 20 (2 * n) / stepW (1 / 100) 20 n) 1 := f_one
  have h3 : (fun n : ℝ => stepW (1 / 100) 20 (2 * n) / stepW (1 / 100) 20 n) 3 < 29/20 := f_three
  have h10 : (29/20:ℝ) < (fun n : ℝ => stepW (1 / 100) 20 (2 * n) / stepW (1 / 100) 20 n) 10 := f_ten
  obtain ⟨x, hx, hfx⟩ := intermediate_value_Icc' (by norm_num : (1:ℝ) ≤ 3)
    (hc.mono (Set.Icc_subset_Icc le_rfl (by norm_num))) ⟨h3.le, h1.le⟩
  obtain ⟨y, hy, hfy⟩ := intermediate_value_Icc (by norm_num : (3:ℝ) ≤ 10)
    (hc.mono (Set.Icc_subset_Icc (by norm_num) le_rfl)) ⟨h3.le, h10.le⟩
  have hxy : x = y := hinj (show (0:ℝ) < x by linarith [hx.1]) (show (0:ℝ) < y by linarith [hy.1])
    (hfx.trans hfy.symm)
  have hx3 : x = 3 := le_antisymm hx.2 (hxy ▸ hy.1)
  rw [hx3] at hfx
  linarith

end Plan.FT20
