import Mathlib
import CflibsFormal.Boltzmann

open Finset CflibsFormal

namespace Plan.FT15

variable {ι : Type*} [Fintype ι]

noncomputable def meanExcitation (kB T : ℝ) (g E : ι → ℝ) : ℝ :=
  (∑ k, g k * E k * boltzmannFactor kB T (E k)) / partitionFunction kB T g E

/-- `boltzmannFactor` in inverse-temperature form. -/
lemma boltzmannFactor_eq_exp_beta (kB T e : ℝ) :
    boltzmannFactor kB T e = Real.exp (-(1 / (kB * T) * e)) := by
  unfold boltzmannFactor; congr 1; ring

/-- Product of two Boltzmann factors as one exponential. -/
lemma bf_mul_bf (kB Ta Tb x y : ℝ) :
    boltzmannFactor kB Ta x * boltzmannFactor kB Tb y
      = Real.exp (-(1 / (kB * Ta) * x) - 1 / (kB * Tb) * y) := by
  rw [boltzmannFactor_eq_exp_beta, boltzmannFactor_eq_exp_beta, ← Real.exp_add]; ring_nf

/-- Termwise sign for the symmetrized double sum (no sign condition on energies):
for `0 < T1 ≤ T2`, `(Ej − Ek)·(bf(T2,Ej)·bf(T1,Ek) − bf(T1,Ej)·bf(T2,Ek)) ≥ 0`. -/
lemma sym_term_nonneg {kB T1 T2 Ej Ek : ℝ} (hkB : 0 < kB) (hT1 : 0 < T1) (hT12 : T1 ≤ T2) :
    0 ≤ (Ej - Ek) * (boltzmannFactor kB T2 Ej * boltzmannFactor kB T1 Ek
      - boltzmannFactor kB T1 Ej * boltzmannFactor kB T2 Ek) := by
  have hkT1 : 0 < kB * T1 := mul_pos hkB hT1
  have hβ : 1 / (kB * T2) ≤ 1 / (kB * T1) :=
    one_div_le_one_div_of_le hkT1 (mul_le_mul_of_nonneg_left hT12 hkB.le)
  rw [bf_mul_bf, bf_mul_bf]
  rcases le_total Ek Ej with h | h
  · apply mul_nonneg (sub_nonneg.mpr h)
    apply sub_nonneg.mpr
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr h) (sub_nonneg.mpr hβ)]
  · apply mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr h)
    apply sub_nonpos.mpr
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr h) (sub_nonneg.mpr hβ)]

/-- `⟨E⟩ ≥ 0` for nonnegative energies. -/
lemma meanExcitation_nonneg [Nonempty ι] {kB T : ℝ} {g E : ι → ℝ} (hg : ∀ k, 0 < g k)
    (hE : ∀ k, 0 ≤ E k) : 0 ≤ meanExcitation kB T g E :=
  div_nonneg (Finset.sum_nonneg fun k _ =>
    mul_nonneg (mul_nonneg (hg k).le (hE k)) (boltzmannFactor_pos _ _ _).le)
    (partitionFunction_pos hg).le

end Plan.FT15
