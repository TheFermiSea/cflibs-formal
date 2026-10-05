-- Summary: Full file: L3 + L1 lemmas + main theorem log_sahaFactor_hasDerivAt_beta (congr_deriv ending, no warnings).
import Mathlib
import CflibsFormal.Saha
open CflibsFormal
namespace Plan.FT08
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

noncomputable def meanExcitation (kB T : ℝ) (g E : ι → ℝ) : ℝ :=
  (∑ k, g k * E k * boltzmannFactor kB T (E k)) / partitionFunction kB T g E

-- exp(-e/(kB * (1/(kB b)))) = exp(-e b)
theorem boltzmannFactor_beta {kB b e : ℝ} (hkB : kB ≠ 0) (hb : b ≠ 0) :
    boltzmannFactor kB (1 / (kB * b)) e = Real.exp (-e * b) := by
  unfold boltzmannFactor
  congr
  field_simp [hkB, hb]

-- partition function as plain sum in b
theorem partitionFunction_beta {kB b : ℝ} (g E : ι → ℝ) (hkB : kB ≠ 0) (hb : b ≠ 0) :
    partitionFunction kB (1 / (kB * b)) g E = ∑ k, g k * Real.exp (-E k * b) := by
  unfold partitionFunction
  apply Finset.sum_congr rfl
  intro k _
  rw [@boltzmannFactor_beta kB b (E k) hkB hb]

-- mean excitation as ratio of plain sums in b
theorem meanExcitation_beta {kB b : ℝ} (g E : ι → ℝ) (hkB : kB ≠ 0) (hb : b ≠ 0) :
    meanExcitation kB (1 / (kB * b)) g E
      = (∑ k, g k * E k * Real.exp (-E k * b)) / (∑ k, g k * Real.exp (-E k * b)) := by
  unfold meanExcitation
  rw [Finset.sum_congr rfl (fun k _ => by rw [@boltzmannFactor_beta kB b (E k) hkB hb])]
  rw [partitionFunction_beta g E hkB hb]

-- thermal bracket at T = 1/(kB b) equals (2π me/h²)/b
theorem thermalBracket_beta {kB b me h : ℝ} (hkB : kB ≠ 0) (hb : b ≠ 0) :
    thermalBracket kB (1 / (kB * b)) me h = (2 * Real.pi * me / h ^ 2) / b := by
  unfold thermalBracket
  field_simp [hkB, hb]

-- log sahaFactor at T = 1/(kB b), b > 0, as an explicit function of b
theorem log_sahaFactor_beta [Nonempty ι] [Nonempty κ] {kB b me h chi : ℝ}
    {gZ EZ : ι → ℝ} {gZ1 EZ1 : κ → ℝ}
    (hkB : 0 < kB) (hb : 0 < b) (hme : 0 < me) (hh : 0 < h)
    (hgZ : ∀ k, 0 < gZ k) (hgZ1 : ∀ k, 0 < gZ1 k) :
    Real.log (sahaFactor kB (1 / (kB * b)) me h chi gZ EZ gZ1 EZ1)
      = Real.log 2 + (Real.log (∑ k, gZ1 k * Real.exp (-EZ1 k * b))
          - Real.log (∑ k, gZ k * Real.exp (-EZ k * b)))
        + (3 / 2 : ℝ) * (Real.log (2 * Real.pi * me / h ^ 2) - Real.log b) - chi * b := by
  have hT : 0 < 1 / (kB * b) := by positivity
  rw [log_sahaFactor hkB hT hme hh hgZ hgZ1,
      partitionFunction_beta gZ1 EZ1 hkB.ne' hb.ne',
      partitionFunction_beta gZ EZ hkB.ne' hb.ne',
      thermalBracket_beta hkB.ne' hb.ne',
      Real.log_div (by positivity) hb.ne']
  rw [show chi / (kB * (1 / (kB * b))) = chi * b by field_simp [hkB.ne', hb.ne']]

-- Derivative of a finite sum of weighted exponentials.
theorem hasDerivAt_sum_exp {ι : Type*} [Fintype ι] (g E : ι → ℝ) (β : ℝ) :
    HasDerivAt (fun b => ∑ k, g k * Real.exp (-E k * b))
      (∑ k, -(g k * E k * Real.exp (-E k * β))) β := by
  have hk : ∀ k, HasDerivAt (fun b => g k * Real.exp (-E k * b)) (-(g k * E k * Real.exp (-E k * β))) β := by
    intro k
    have h1 : HasDerivAt (fun b => -E k * b) (-E k) β := by
      simpa using (hasDerivAt_id' β).const_mul (-E k)
    have h2 : HasDerivAt (fun b => Real.exp (-E k * b)) (Real.exp (-E k * β) * (-E k)) β := by
      simpa using h1.exp
    have h3 : HasDerivAt (fun b => g k * Real.exp (-E k * b)) (g k * (Real.exp (-E k * β) * (-E k))) β := by
      simpa using h2.const_mul (g k)
    convert h3 using 2
    ring
  exact HasDerivAt.fun_sum (fun k _ => hk k)

-- d/dβ log ∑ g exp(-E β) = -(∑ g E exp(-Eβ))/(∑ g exp(-Eβ)).
theorem hasDerivAt_log_sum_exp {ι : Type*} [Fintype ι] [Nonempty ι] {g E : ι → ℝ} {β : ℝ}
    (hg : ∀ k, 0 < g k) :
    HasDerivAt (fun b => Real.log (∑ k, g k * Real.exp (-E k * b)))
      (-((∑ k, g k * E k * Real.exp (-E k * β)) / (∑ k, g k * Real.exp (-E k * β)))) β := by
  have hpos : 0 < ∑ k, g k * Real.exp (-E k * β) :=
    Finset.sum_pos (fun k _ => mul_pos (hg k) (Real.exp_pos _)) Finset.univ_nonempty
  have hlog := (hasDerivAt_sum_exp g E β).log hpos.ne'
  convert hlog using 1
  rw [Finset.sum_neg_distrib, neg_div]

-- Main theorem: d log S / dβ = -(χ + 3/(2β) + ⟨E⟩_II - ⟨E⟩_I).
-- Proof: log S agrees near β (b > 0) with an explicit function F of b (log_sahaFactor_beta);
-- differentiate F term by term, then identify the mean excitations via meanExcitation_beta.
theorem log_sahaFactor_hasDerivAt_beta [Nonempty ι] [Nonempty κ] {kB me h chi β : ℝ}
    {gZ EZ : ι → ℝ} {gZ1 EZ1 : κ → ℝ}
    (hkB : 0 < kB) (hβ : 0 < β) (hme : 0 < me) (hh : 0 < h)
    (hgZ : ∀ k, 0 < gZ k) (hgZ1 : ∀ k, 0 < gZ1 k) :
    HasDerivAt (fun b => Real.log (sahaFactor kB (1 / (kB * b)) me h chi gZ EZ gZ1 EZ1))
      (-(chi + 3 / (2 * β) + meanExcitation kB (1 / (kB * β)) gZ1 EZ1
          - meanExcitation kB (1 / (kB * β)) gZ EZ)) β := by
  have h1 := hasDerivAt_log_sum_exp (E := EZ1) (β := β) hgZ1
  have h2 := hasDerivAt_log_sum_exp (E := EZ) (β := β) hgZ
  have h3 := Real.hasDerivAt_log hβ.ne'
  have h4 := hasDerivAt_id' β
  have hF : HasDerivAt
      (fun b => Real.log 2 + (Real.log (∑ k, gZ1 k * Real.exp (-EZ1 k * b))
        - Real.log (∑ k, gZ k * Real.exp (-EZ k * b)))
        + (3 / 2 : ℝ) * (Real.log (2 * Real.pi * me / h ^ 2) - Real.log b) - chi * b)
      ((-( (∑ k, gZ1 k * EZ1 k * Real.exp (-EZ1 k * β)) / (∑ k, gZ1 k * Real.exp (-EZ1 k * β)) ) - -( (∑ k, gZ k * EZ k * Real.exp (-EZ k * β)) / (∑ k, gZ k * Real.exp (-EZ k * β)) )) + (3 / 2 : ℝ) * (-β⁻¹) - chi * 1) β := by
    exact (((h1.sub h2).const_add (Real.log 2)).add
      ((h3.const_sub (Real.log (2 * Real.pi * me / h ^ 2))).const_mul (3 / 2 : ℝ))).sub
      (h4.const_mul chi)
  have hev : (fun b => Real.log (sahaFactor kB (1 / (kB * b)) me h chi gZ EZ gZ1 EZ1))
      =ᶠ[nhds β]
      (fun b => Real.log 2 + (Real.log (∑ k, gZ1 k * Real.exp (-EZ1 k * b))
        - Real.log (∑ k, gZ k * Real.exp (-EZ k * b)))
        + (3 / 2 : ℝ) * (Real.log (2 * Real.pi * me / h ^ 2) - Real.log b) - chi * b) :=
    Filter.eventually_of_mem (Ioi_mem_nhds hβ) (fun b hb => log_sahaFactor_beta hkB hb hme hh hgZ hgZ1)
  have h := hF.congr_of_eventuallyEq hev
  refine h.congr_deriv ?_
  rw [meanExcitation_beta gZ1 EZ1 hkB.ne' hβ.ne', meanExcitation_beta gZ EZ hkB.ne' hβ.ne']
  ring

end Plan.FT08
