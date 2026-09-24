import CflibsFormal

/-! Frontier-verifier scratch (2026-09-24): refutations and corrected statements for FT-01..FT-10. -/

open Finset Real Filter Topology
open scoped BigOperators

namespace FV
open CflibsFormal

/-! ### FT-09: `affine_gA_gauge` is a 5-line corollary of the EXISTING
`HeteroAtomicData.olsSlope_aliasing_A` (+ `OLS.ols_recovers_line`). -/
theorem affine_gA_gauge_of_aliasing {ι : Type*} [Fintype ι] [Nonempty ι]
    {kB T N Fcal α b : ℝ} {g E A A' : ι → ℝ}
    (hg : ∀ k, 0 < g k) (hA : ∀ k, 0 < A k) (hN : 0 < N)
    (hFcal : 0 < Fcal) (haff : ∀ k, A' k = A k * Real.exp (-(α + b * E k)))
    (hvar : 0 < ∑ k, (E k - mean E) ^ 2) :
    olsSlope E (fun k => Real.log (lineIntensity kB T N Fcal g E A k / (g k * A' k)))
      = -(1 / (kB * T)) + b := by
  have hA' : ∀ k, 0 < A' k := fun k => by rw [haff k]; exact mul_pos (hA k) (Real.exp_pos _)
  rw [olsSlope_aliasing_A hg hN hFcal hA hA' hvar]
  congr 1
  refine (ols_recovers_line (m0 := b) (b0 := α) (fun k => ?_) hvar).1
  rw [haff k, div_mul_eq_div_div, div_self (hA k).ne', one_div, ← Real.exp_neg, neg_neg,
    Real.log_exp]
  ring

/-! ### FT-02: the correct vehicle for "composition is IPD-invariant on the ratio route" is an
exact cancellation of the Saha RATIO `S_s(χ_s)/n̂`, not `composition_smul_invariant`. -/
theorem sahaFactor_sub {ι κ : Type*} [Fintype ι] [Fintype κ] (kB T me h c d : ℝ)
    (a b : ι → ℝ) (a' b' : κ → ℝ) :
    sahaFactor kB T me h (c - d) a b a' b'
      = sahaFactor kB T me h c a b a' b' * Real.exp (d / (kB * T)) := by
  unfold sahaFactor
  rw [show -(c - d) / (kB * T) = -c / (kB * T) + d / (kB * T) by ring, Real.exp_add]
  ring

theorem sahaRatio_ipd_gauge {ι κ ι' κ' : Type*} [Fintype ι] [Fintype κ] [Fintype ι']
    [Fintype κ'] {kB T me h chim chis d Rm ne : ℝ} {gZ EZ : ι → ℝ} {gZ1 EZ1 : κ → ℝ}
    {gS ES : ι' → ℝ} {gS1 ES1 : κ' → ℝ} (hR : Rm ≠ 0) (hne : ne ≠ 0)
    (hfwd : Rm * ne = sahaFactor kB T me h (chim - d) gZ EZ gZ1 EZ1) :
    sahaFactor kB T me h chis gS ES gS1 ES1
        / electronDensityFromRatio kB T me h chim gZ EZ gZ1 EZ1 Rm
      = sahaFactor kB T me h (chis - d) gS ES gS1 ES1 / ne := by
  rw [sahaFactor_sub] at hfwd ⊢
  unfold electronDensityFromRatio
  have he : Real.exp (d / (kB * T)) ≠ 0 := Real.exp_ne_zero _
  rw [div_div_eq_mul_div, eq_div_iff hne]
  by_cases hS : sahaFactor kB T me h chim gZ EZ gZ1 EZ1 = 0
  · rw [hS, zero_mul] at hfwd
    exact absurd (mul_eq_zero.mp hfwd) (by tauto)
  · field_simp
    linear_combination (sahaFactor kB T me h chis gS ES gS1 ES1) * hfwd

/-! ### FT-02: the sketched `ipdInverse_twoPoint_sensitivity` (no positivity of `a1`) is FALSE.
Witness: `l1 = 0`, `l2 = -2`, `b = 1/2`, `q = 1/2`, `a1 = -exp(-1/2) < 0 < a2`. -/
noncomputable def ipdLogMap (a b ℓ : ℝ) : ℝ := Real.log a + b * Real.exp (ℓ / 2)

theorem twoPoint_sensitivity_false :
    ¬ ∀ a1 a2 b l1 l2 q : ℝ, q < 1 → ipdLogMap a1 b l1 = l1 → ipdLogMap a2 b l2 = l2 →
        a1 ≤ a2 → b * Real.exp (max l1 l2 / 2) / 2 ≤ q →
        (Real.log a2 - Real.log a1 ≤ l2 - l1 ∧ l2 - l1 ≤ (Real.log a2 - Real.log a1) / (1 - q)) := by
  intro H
  set a1 : ℝ := -Real.exp (-(1 / 2))
  set a2 : ℝ := Real.exp (-2 - 1 / 2 * Real.exp (-1))
  have hl1 : Real.log a1 = -(1 / 2) := by simp [a1, Real.log_neg_eq_log, Real.log_exp]
  have hl2 : Real.log a2 = -2 - 1 / 2 * Real.exp (-1) := by simp [a2, Real.log_exp]
  have h := (H a1 a2 (1 / 2) 0 (-2) (1 / 2) (by norm_num)
    (by simp only [ipdLogMap, hl1]; norm_num)
    (by simp only [ipdLogMap, hl2]; norm_num)
    (by have := Real.exp_pos (-(1 / 2)); have := Real.exp_pos (-2 - 1 / 2 * Real.exp (-1))
        simp only [a1, a2]; linarith)
    (by norm_num)).1
  rw [hl1, hl2] at h
  have : Real.exp (-1) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  linarith

/-- Second witness: even with `0 < a1`, a negative `b` breaks the lower bound
(`b = -1/2`, `l1 = 0`, `l2 = 2`, `q = 0`). So both `0 < a1` and `0 ≤ b` are needed. -/
theorem twoPoint_sensitivity_false_negb :
    ¬ ∀ a1 a2 b l1 l2 q : ℝ, 0 < a1 → q < 1 → ipdLogMap a1 b l1 = l1 →
        ipdLogMap a2 b l2 = l2 → a1 ≤ a2 → b * Real.exp (max l1 l2 / 2) / 2 ≤ q →
        (Real.log a2 - Real.log a1 ≤ l2 - l1) := by
  intro H
  have he1 : Real.exp (1 : ℝ) > 2 := by
    have := Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0); linarith
  have h := H (Real.exp (1 / 2)) (Real.exp (2 + 1 / 2 * Real.exp 1)) (-1 / 2) 0 2 0
    (Real.exp_pos _) (by norm_num)
    (by simp only [ipdLogMap, Real.log_exp]; norm_num)
    (by simp only [ipdLogMap, Real.log_exp]; norm_num)
    (Real.exp_le_exp.mpr (by nlinarith))
    (by have := Real.exp_pos (max 0 2 / 2); nlinarith)
  rw [Real.log_exp, Real.log_exp] at h
  linarith

/-! ### FT-01: the sketched `single_group_gain` (only `W > 0`) is false without `0 ≤ B`
(or `0 < B + W`). -/
example : ¬ ((-2 : ℝ) / (-2 + 1) < 1) := by norm_num

/-! ### FT-03: the two policies have incompatible guarantees. -/
-- answer-iff-U≤λ can be worse than always answering (violates SC-04's G ≥ 0)
example : ∃ l L U lam : ℝ, L ≤ l ∧ l ≤ U ∧ l < (if U ≤ lam then l else lam) :=
  ⟨1 / 2, 0, 2, 1, by norm_num, by norm_num, by norm_num⟩
-- refuse-iff-L>λ can be worse than always refusing (violates `pas_certified_le_lambda`)
example : ∃ l L U lam : ℝ, L ≤ l ∧ l ≤ U ∧ lam < (if lam < L then lam else l) :=
  ⟨3 / 2, 0, 2, 1, by norm_num, by norm_num, by norm_num⟩

/-! ### FT-06: the Saha-side IPD bracket (true as sketched). -/
theorem saha_ipd_bracket {ι κ : Type*} [Fintype ι] [Fintype κ]
    {kB T me h chi d dmax R ne : ℝ} {gZ EZ : ι → ℝ} {gZ1 EZ1 : κ → ℝ}
    (hkT : 0 < kB * T) (hR : 0 < R) (hne : 0 < ne) (hd : 0 ≤ d) (hdm : d ≤ dmax)
    (hfwd : R * ne = sahaFactor kB T me h (chi - d) gZ EZ gZ1 EZ1) :
    electronDensityFromRatio kB T me h chi gZ EZ gZ1 EZ1 R ≤ ne ∧
      ne ≤ electronDensityFromRatio kB T me h chi gZ EZ gZ1 EZ1 R
            * Real.exp (dmax / (kB * T)) := by
  have hg : sahaFactor kB T me h (chi - d) gZ EZ gZ1 EZ1
      = sahaFactor kB T me h chi gZ EZ gZ1 EZ1 * Real.exp (d / (kB * T)) := by
    unfold sahaFactor
    rw [show -(chi - d) / (kB * T) = -chi / (kB * T) + d / (kB * T) by ring, Real.exp_add]
    ring
  have hn : electronDensityFromRatio kB T me h chi gZ EZ gZ1 EZ1 R
      = ne * Real.exp (-(d / (kB * T))) := by
    unfold electronDensityFromRatio
    rw [hg] at hfwd
    rw [Real.exp_neg, div_eq_iff hR.ne']
    have he : Real.exp (d / (kB * T)) ≠ 0 := Real.exp_ne_zero _
    field_simp
    linarith
  rw [hn]
  have h1 : Real.exp (-(d / (kB * T))) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by have := div_nonneg hd hkT.le; linarith)
  refine ⟨by nlinarith [Real.exp_pos (-(d / (kB * T)))], ?_⟩
  rw [mul_assoc, ← Real.exp_add]
  have : 0 ≤ -(d / (kB * T)) + dmax / (kB * T) := by
    rw [← sub_eq_neg_add, ← sub_div]; exact div_nonneg (by linarith) hkT.le
  nlinarith [Real.one_le_exp this]

/-! ### FT-05: the physically relevant form is two-temperature injectivity, not `¬ ∀ T > 0`. -/
noncomputable def partitionFunctionCut {ι : Type*} [Fintype ι] (kB T cut : ℝ) (g E : ι → ℝ) :
    ℝ := ∑ k ∈ univ.filter (fun k => E k < cut), g k * boltzmannFactor kB T (E k)

theorem cutRatio_injOn {ι : Type*} [Fintype ι] {kB cut : ℝ} {g E : ι → ℝ} (hkB : 0 < kB)
    (hg : ∀ k, 0 < g k) (hkeep : ∃ k, E k < cut) (hdrop : ∃ k, cut ≤ E k) :
    Set.InjOn (fun T => partitionFunction kB T g E / partitionFunctionCut kB T cut g E)
      (Set.Ioi 0) := by sorry

/-! ### FT-09 (revised): observational equivalence, with the gauge-orbit constraint `b·kB·T < 1`. -/
theorem affine_gA_observational_equiv {ι : Type*} [Fintype ι] [Nonempty ι]
    {kB T N Fcal α b : ℝ} {g E A A' : ι → ℝ}
    (hkB : 0 < kB) (hT : 0 < T) (hg : ∀ k, 0 < g k) (hA : ∀ k, 0 < A k) (hN : 0 < N)
    (hFcal : 0 < Fcal) (haff : ∀ k, A' k = A k * Real.exp (-(α + b * E k)))
    (hb : b * (kB * T) < 1) :
    ∃ T' N' : ℝ, 0 < T' ∧ 0 < N' ∧ 1 / (kB * T') = 1 / (kB * T) - b ∧
      ∀ k, Real.log (lineIntensity kB T N Fcal g E A k / (g k * A' k))
        = Real.log (lineIntensity kB T' N' Fcal g E A k / (g k * A k)) := by sorry

end FV

#print axioms FV.affine_gA_gauge_of_aliasing
#print axioms FV.sahaRatio_ipd_gauge
#print axioms FV.twoPoint_sensitivity_false
#print axioms FV.twoPoint_sensitivity_false_negb
#print axioms FV.saha_ipd_bracket
