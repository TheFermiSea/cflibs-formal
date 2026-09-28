-- Summary: Complete Lean proof that ionReweight is strictly increasing on (0,∞).
import Mathlib
import CflibsFormal.SahaStability

open CflibsFormal

namespace Plan.FT19

noncomputable def ionReweight (kB me h chi ne T : ℝ) : ℝ :=
  2 * thermalBracket kB T me h ^ (3/2 : ℝ) * Real.exp (-chi / (kB * T)) / ne

theorem ionReweight_strictMonoOn {kB me h chi ne : ℝ} (hkB : 0 < kB) (hme : 0 < me)
    (hh : 0 < h) (hchi : 0 ≤ chi) (hne : 0 < ne) :
    StrictMonoOn (ionReweight kB me h chi ne) (Set.Ioi 0) := by
  intro T1 hT1 T2 hT2 hlt
  simp only [Set.mem_Ioi] at hT1 hT2
  dsimp [ionReweight]
  have hθ1 : 0 < thermalBracket kB T1 me h := thermalBracket_pos hkB hT1 hme hh
  have hθ2 : 0 < thermalBracket kB T2 me h := thermalBracket_pos hkB hT2 hme hh
  have hθlt : thermalBracket kB T1 me h < thermalBracket kB T2 me h :=
    thermalBracket_strictMono hkB hme hh hlt
  have hX : (thermalBracket kB T1 me h) ^ (3/2 : ℝ) < (thermalBracket kB T2 me h) ^ (3/2 : ℝ) :=
    Real.rpow_lt_rpow hθ1.le hθlt (by norm_num)
  have hY : Real.exp (-chi / (kB * T1)) ≤ Real.exp (-chi / (kB * T2)) := by
    rw [Real.exp_le_exp]
    rw [neg_div, neg_div, neg_le_neg_iff]
    exact div_le_div_of_nonneg_left hchi (mul_pos hkB hT1)
      (mul_le_mul_of_nonneg_left hlt.le hkB.le)
  have h2X : 2 * (thermalBracket kB T1 me h) ^ (3/2 : ℝ) <
             2 * (thermalBracket kB T2 me h) ^ (3/2 : ℝ) := by
    linarith [hX]
  have hYpos : 0 < Real.exp (-chi / (kB * T2)) := Real.exp_pos _
  have hprod : 2 * (thermalBracket kB T1 me h) ^ (3/2 : ℝ) * Real.exp (-chi / (kB * T1)) <
               2 * (thermalBracket kB T2 me h) ^ (3/2 : ℝ) * Real.exp (-chi / (kB * T2)) :=
    mul_lt_mul_of_lt_of_le_of_nonneg_of_pos h2X hY (by positivity) hYpos
  exact div_lt_div_of_pos_right hprod hne

end Plan.FT19
