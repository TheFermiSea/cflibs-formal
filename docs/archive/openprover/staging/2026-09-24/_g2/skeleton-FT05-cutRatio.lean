import Mathlib
import CflibsFormal.Boltzmann

open Finset CflibsFormal

namespace Plan.FT05

variable {ι : Type*} [Fintype ι]

noncomputable def partitionFunctionCut (kB T cut : ℝ) (g E : ι → ℝ) : ℝ :=
  ∑ k ∈ univ.filter (fun k => E k < cut), g k * boltzmannFactor kB T (E k)

/-- `U = U_cut + D`, `D` the sum over dropped levels (`cut ≤ E k`). -/
lemma partitionFunction_eq_cut_add_tail (kB T cut : ℝ) (g E : ι → ℝ) :
    partitionFunction kB T g E = partitionFunctionCut kB T cut g E
      + ∑ k ∈ univ.filter (fun k => cut ≤ E k), g k * boltzmannFactor kB T (E k) := by
  unfold partitionFunction partitionFunctionCut
  rw [← Finset.sum_filter_add_sum_filter_not univ (fun k => E k < cut)]
  simp only [not_lt]

/-- `U_cut > 0` once one level is kept. -/
lemma partitionFunctionCut_pos {kB T cut : ℝ} {g E : ι → ℝ} (hg : ∀ k, 0 < g k)
    (hkeep : ∃ k, E k < cut) : 0 < partitionFunctionCut kB T cut g E := by
  obtain ⟨k0, hk0⟩ := hkeep
  exact Finset.sum_pos (fun k _ => mul_pos (hg k) (boltzmannFactor_pos _ _ _))
    ⟨k0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk0⟩⟩

/-- Termwise sign crux: for a kept level `Ek < cut` and a dropped level `cut ≤ Ed`,
`bf(T1, Ed)·bf(T2, Ek) < bf(T2, Ed)·bf(T1, Ek)` when `0 < T1 < T2`. -/
lemma bf_cross_lt {kB T1 T2 cut Ed Ek : ℝ} (hkB : 0 < kB) (hT1 : 0 < T1) (hT12 : T1 < T2)
    (hk : Ek < cut) (hd : cut ≤ Ed) :
    boltzmannFactor kB T1 Ed * boltzmannFactor kB T2 Ek
      < boltzmannFactor kB T2 Ed * boltzmannFactor kB T1 Ek := by
  unfold boltzmannFactor
  rw [← Real.exp_add, ← Real.exp_add, Real.exp_lt_exp]
  have hkT1 : 0 < kB * T1 := mul_pos hkB hT1
  have hβ : 1 / (kB * T2) < 1 / (kB * T1) :=
    one_div_lt_one_div_of_lt hkT1 (mul_lt_mul_of_pos_left hT12 hkB)
  have e1 : -Ed / (kB * T1) + -Ek / (kB * T2)
      = -(Ed * (1 / (kB * T1))) - Ek * (1 / (kB * T2)) := by ring
  have e2 : -Ed / (kB * T2) + -Ek / (kB * T1)
      = -(Ed * (1 / (kB * T2))) - Ek * (1 / (kB * T1)) := by ring
  rw [e1, e2]
  nlinarith [mul_pos (sub_pos.mpr (lt_of_lt_of_le hk hd)) (sub_pos.mpr hβ)]


theorem cutRatio_strictMonoOn_temp {kB cut : ℝ} {g E : ι → ℝ} (hkB : 0 < kB)
    (hg : ∀ k, 0 < g k) (hkeep : ∃ k, E k < cut) (hdrop : ∃ k, cut ≤ E k) :
    StrictMonoOn (fun T => partitionFunction kB T g E / partitionFunctionCut kB T cut g E)
      (Set.Ioi 0) := by
  intro T1 hT1 T2 hT2 hlt
  simp only [Set.mem_Ioi] at hT1 hT2
  show partitionFunction kB T1 g E / partitionFunctionCut kB T1 cut g E
      < partitionFunction kB T2 g E / partitionFunctionCut kB T2 cut g E
  have hK1 : 0 < partitionFunctionCut kB T1 cut g E := partitionFunctionCut_pos hg hkeep
  have hK2 : 0 < partitionFunctionCut kB T2 cut g E := partitionFunctionCut_pos hg hkeep
  have hcross :
      (∑ k ∈ univ.filter (fun k => cut ≤ E k), g k * boltzmannFactor kB T1 (E k))
          * partitionFunctionCut kB T2 cut g E
        < (∑ k ∈ univ.filter (fun k => cut ≤ E k), g k * boltzmannFactor kB T2 (E k))
          * partitionFunctionCut kB T1 cut g E := by
    sorry
  rw [partitionFunction_eq_cut_add_tail kB T1 cut, partitionFunction_eq_cut_add_tail kB T2 cut,
    div_lt_div_iff₀ hK1 hK2]
  nlinarith [hcross]

end Plan.FT05
