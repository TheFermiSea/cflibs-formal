-- Summary: FT05 full Lean proof: U/U_cut strictly increasing in temperature (partition function truncation).
import Mathlib
import CflibsFormal.Boltzmann

/-!
# FT-05 (items 2-3): the truncation ratio `U/U_cut` is strictly increasing in temperature

Staged queue target, 2026-09-24 deep audit, frontier FT-05 (verdict REVISE, grade A). A generic
statement about truncating the Boltzmann sum at an arbitrary cutoff energy; it asserts no level
cutoff policy (that decision is pending). No module on main defines a truncated partition
function.
-/

open Finset CflibsFormal

namespace Plan.FT05

variable {ι : Type*} [Fintype ι]

/-- **Truncated partition function** `U_cut(T) = ∑_{k : E k < cut} g k · exp(−E k/(k_B T))`: the
Boltzmann sum `partitionFunction` restricted to the levels strictly below the cutoff energy
`cut`. Convention: a level with `E k < cut` is kept; a level with `cut ≤ E k`, including one
exactly at the cutoff, is dropped. `cut` is a free real in the units of `E` (energies measured
from the stage's ground state). The definition asserts no cutoff policy (fixed, IPD-lowered or
density-dependent); choosing one is a separate, pending decision. -/
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

/-- **The truncation ratio is strictly increasing in temperature (FT-05 (ii)).**

If at least one level is kept (`hkeep`) and at least one is dropped (`hdrop`), the ratio
`U(T)/U_cut(T)` of the full to the truncated partition function is strictly increasing in `T`
on `(0, ∞)`. Writing `U = U_cut + D` with `D` the sum over dropped levels,
`U/U_cut = 1 + D/U_cut`, and, for `T1 < T2`, cross-multiplying by `U_cut(T1)·U_cut(T2) > 0`
reduces the claim to `D(T1)·U_cut(T2) < D(T2)·U_cut(T1)`: a double sum over (dropped `d`, kept
`k`) pairs in which each term's exponent gap is `(1/(k_B T1) − 1/(k_B T2))·(E_d − E_k) > 0`,
since `E_d ≥ cut > E_k`. No gap, sign or ordering hypothesis on the energies is needed beyond
`hkeep`/`hdrop`, because every dropped level lies above every kept one. Consequence (follow-up
targets, not proved here): the ratio is injective in `T`, so no temperature-independent factor,
such as a `gA` calibration, can absorb a change of cutoff at two distinct temperatures.

Hypotheses and why each is present:
* `hkB : 0 < kB`: `1/(k_B T)` is then strictly decreasing in `T` on `(0, ∞)`.
* `hg : ∀ k, 0 < g k`: makes `U_cut > 0` (with `hkeep`) and supplies strictness.
* `hkeep`: otherwise `U_cut = 0` and the ratio is Lean's junk value `0`.
* `hdrop`: otherwise the ratio is identically `1`, not strictly increasing.

Scope (two-axis): own relation PURE-MATH (a property of finite exponential sums; no physical
claim); definitions used: `partitionFunction` (the Boltzmann sum over the supplied list) and
`partitionFunctionCut` (a truncation device with no asserted policy); predicted published tag
PURE-MATH. -/
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
  obtain ⟨d0, hd0⟩ := hdrop
  obtain ⟨k0, hk0⟩ := hkeep
  have hdropN : (univ.filter (fun k => cut ≤ E k)).Nonempty :=
    ⟨d0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd0⟩⟩
  have hkeepN : (univ.filter (fun k => E k < cut)).Nonempty :=
    ⟨k0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk0⟩⟩
  have hcross :
      (∑ k ∈ univ.filter (fun k => cut ≤ E k), g k * boltzmannFactor kB T1 (E k))
          * partitionFunctionCut kB T2 cut g E
        < (∑ k ∈ univ.filter (fun k => cut ≤ E k), g k * boltzmannFactor kB T2 (E k))
          * partitionFunctionCut kB T1 cut g E := by
    simp only [partitionFunctionCut, Finset.sum_mul_sum]
    exact Finset.sum_lt_sum_of_nonempty hdropN
      (fun d hd =>
        Finset.sum_lt_sum_of_nonempty hkeepN
          (fun k hk =>
            have hd' := (Finset.mem_filter.mp hd).2
            have hk' := (Finset.mem_filter.mp hk).2
            calc g d * boltzmannFactor kB T1 (E d) * (g k * boltzmannFactor kB T2 (E k))
                = (g d * g k) * (boltzmannFactor kB T1 (E d) * boltzmannFactor kB T2 (E k)) := by ring
              _ < (g d * g k) * (boltzmannFactor kB T2 (E d) * boltzmannFactor kB T1 (E k)) :=
                  mul_lt_mul_of_pos_left (bf_cross_lt hkB hT1 hlt hk' hd') (mul_pos (hg d) (hg k))
              _ = g d * boltzmannFactor kB T2 (E d) * (g k * boltzmannFactor kB T1 (E k)) := by ring))
  rw [partitionFunction_eq_cut_add_tail kB T1 cut, partitionFunction_eq_cut_add_tail kB T2 cut,
    div_lt_div_iff₀ hK1 hK2]
  nlinarith [hcross]

end Plan.FT05
