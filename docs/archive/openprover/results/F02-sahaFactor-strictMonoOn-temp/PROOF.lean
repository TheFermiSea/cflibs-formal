-- Summary: M4 (headline) -- sahaFactor is strictly increasing in temperature on (0,infty), assembled from M1/M2/M3 via log_sahaFactor (self-authored, transcribing notes/lean-interface + advisor-flagged fixes for form mismatch, beta-reduction, and Real.log_mul side conditions).
import Mathlib
import CflibsFormal.Saha
import CflibsFormal.PartitionLipschitz
import CflibsFormal.Analysis

open CflibsFormal

namespace DryRun

variable {ι : Type*} [Fintype ι]
variable {κ : Type*} [Fintype κ]

-- M1: thermalBracket is strictly increasing in temperature.
private lemma thermalBracket_strictMono' {kB me h Ta Tb : ℝ}
    (hkB : 0 < kB) (hme : 0 < me) (hh : 0 < h) (hab : Ta < Tb) :
    thermalBracket kB Ta me h < thermalBracket kB Tb me h := by
  unfold thermalBracket
  have hhne : h ≠ 0 := hh.ne'
  have hkey : (2 * Real.pi * me * kB * Tb) / h ^ 2 - (2 * Real.pi * me * kB * Ta) / h ^ 2
      = (2 * Real.pi * me * kB / h ^ 2) * (Tb - Ta) := by
    field_simp
  have hpos : 0 < (2 * Real.pi * me * kB / h ^ 2) * (Tb - Ta) := by
    apply mul_pos
    · positivity
    · linarith
  linarith [hkey, hpos]

-- M3: partitionFunction is monotone (non-strict) in temperature when E ≥ 0. Polymorphic index type τ
-- (kept independent of the ambient ι/κ so it can be instantiated at both stages).
private lemma partitionFunction_mono_temp' {τ : Type*} [Fintype τ] {kB T1 T2 : ℝ} {g E : τ → ℝ}
    (hkB : 0 < kB) (hT1 : 0 < T1) (hT12 : T1 ≤ T2)
    (hg : ∀ k, 0 < g k) (hE : ∀ k, 0 ≤ E k) :
    partitionFunction kB T1 g E ≤ partitionFunction kB T2 g E := by
  have hT2 : 0 < T2 := lt_of_lt_of_le hT1 hT12
  have hd1 : (0:ℝ) < kB * T1 := mul_pos hkB hT1
  have hd2 : (0:ℝ) < kB * T2 := mul_pos hkB hT2
  unfold partitionFunction boltzmannFactor
  apply Finset.sum_le_sum
  intro k _
  apply mul_le_mul_of_nonneg_left _ (hg k).le
  apply Real.exp_le_exp.mpr
  have hkT12 : kB * T1 ≤ kB * T2 := mul_le_mul_of_nonneg_left hT12 hkB.le
  have hinv : 1 / (kB * T2) ≤ 1 / (kB * T1) := one_div_le_one_div_of_le hd1 hkT12
  have h1 : -E k / (kB * T1) = -E k * (1 / (kB * T1)) := by ring
  have h2 : -E k / (kB * T2) = -E k * (1 / (kB * T2)) := by ring
  rw [h1, h2]
  exact mul_le_mul_of_nonpos_left hinv (by linarith [hE k])

-- M2 (crux): partitionFunction upper growth bound across two temperatures, termwise via exp
-- monotonicity and the level-ceiling hypothesis E k ≤ chi. Polymorphic index type τ.
private lemma partitionFunction_upper_growth' {τ : Type*} [Fintype τ] {kB T1 T2 chi : ℝ} {g E : τ → ℝ}
    (hkB : 0 < kB) (hT1 : 0 < T1) (hT12 : T1 ≤ T2)
    (hg : ∀ k, 0 < g k) (hEχ : ∀ k, E k ≤ chi) :
    partitionFunction kB T2 g E
      ≤ Real.exp (chi * (1/(kB*T1) - 1/(kB*T2))) * partitionFunction kB T1 g E := by
  have hT2 : 0 < T2 := lt_of_lt_of_le hT1 hT12
  have hd1 : (0:ℝ) < kB * T1 := mul_pos hkB hT1
  have hd2 : (0:ℝ) < kB * T2 := mul_pos hkB hT2
  have hinv : (0:ℝ) ≤ 1/(kB*T1) - 1/(kB*T2) := by
    have hle : 1/(kB*T2) ≤ 1/(kB*T1) :=
      one_div_le_one_div_of_le hd1 (mul_le_mul_of_nonneg_left hT12 hkB.le)
    linarith
  unfold partitionFunction boltzmannFactor
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _
  have hrw : Real.exp (chi * (1/(kB*T1) - 1/(kB*T2))) * (g k * Real.exp (-(E k) / (kB*T1)))
      = g k * Real.exp (chi * (1/(kB*T1) - 1/(kB*T2)) + (-(E k) / (kB*T1))) := by
    rw [Real.exp_add]; ring
  rw [hrw]
  apply mul_le_mul_of_nonneg_left _ (hg k).le
  apply Real.exp_le_exp.mpr
  have hkey : (E k - chi) * (1/(kB*T1) - 1/(kB*T2)) ≤ 0 := by
    nlinarith [mul_nonneg (by linarith [hEχ k] : (0:ℝ) ≤ chi - E k) hinv]
  have h1 : -E k / (kB * T1) = -E k * (1 / (kB * T1)) := by ring
  have h2 : -E k / (kB * T2) = -E k * (1 / (kB * T2)) := by ring
  rw [h1, h2]
  nlinarith [hkey]

/-- **Saha-factor strict monotonicity in temperature (M4, EXACT, Saha–Eggert (Griem)).**
On the whole positive temperature axis, under the physically universal hypothesis that
every bound level of the lower (neutral) stage sits at or below the ionization limit
(`∀ k, EZ k ≤ chi`), the Saha factor `S(T)` is strictly increasing in `T`. -/
theorem sahaFactor_strictMonoOn_temp [Nonempty ι] [Nonempty κ]
    {kB me h chi : ℝ} {gZ EZ : ι → ℝ} {gZ1 EZ1 : κ → ℝ}
    (hkB : 0 < kB) (hme : 0 < me) (hh : 0 < h) (_hchi : 0 ≤ chi)
    (hgZ : ∀ k, 0 < gZ k) (_hEZ : ∀ k, 0 ≤ EZ k)
    (hgZ1 : ∀ k, 0 < gZ1 k) (hEZ1 : ∀ k, 0 ≤ EZ1 k)
    (hEχ : ∀ k, EZ k ≤ chi) :
    StrictMonoOn (fun T => sahaFactor kB T me h chi gZ EZ gZ1 EZ1) (Set.Ioi 0) := by
  intro T1 hT1mem T2 hT2mem hlt
  have hT1 : 0 < T1 := hT1mem
  have hT2 : 0 < T2 := hT2mem
  show sahaFactor kB T1 me h chi gZ EZ gZ1 EZ1 < sahaFactor kB T2 me h chi gZ EZ gZ1 EZ1
  rw [← Real.log_lt_log_iff (sahaFactor_pos hkB hT1 hme hh hgZ hgZ1)
      (sahaFactor_pos hkB hT2 hme hh hgZ hgZ1)]
  have hlog1 : Real.log (sahaFactor kB T1 me h chi gZ EZ gZ1 EZ1)
      = Real.log 2 + (Real.log (partitionFunction kB T1 gZ1 EZ1) - Real.log (partitionFunction kB T1 gZ EZ))
        + 3/2 * Real.log (thermalBracket kB T1 me h) - chi/(kB*T1) :=
    log_sahaFactor hkB hT1 hme hh hgZ hgZ1
  have hlog2 : Real.log (sahaFactor kB T2 me h chi gZ EZ gZ1 EZ1)
      = Real.log 2 + (Real.log (partitionFunction kB T2 gZ1 EZ1) - Real.log (partitionFunction kB T2 gZ EZ))
        + 3/2 * Real.log (thermalBracket kB T2 me h) - chi/(kB*T2) :=
    log_sahaFactor hkB hT2 hme hh hgZ hgZ1
  rw [hlog1, hlog2]
  -- P1: upper-stage partition function log is monotone (nondecreasing).
  have hP1 : Real.log (partitionFunction kB T1 gZ1 EZ1) ≤ Real.log (partitionFunction kB T2 gZ1 EZ1) :=
    Real.log_le_log (partitionFunction_pos hgZ1)
      (partitionFunction_mono_temp' hkB hT1 hlt.le hgZ1 hEZ1)
  -- Ct - P0: lower-stage partition growth is dominated by the same chi-weighted factor
  -- as the exponential channel.
  have hM2 : partitionFunction kB T2 gZ EZ
      ≤ Real.exp (chi * (1/(kB*T1) - 1/(kB*T2))) * partitionFunction kB T1 gZ EZ :=
    partitionFunction_upper_growth' hkB hT1 hlt.le hgZ hEχ
  have hP0raw : Real.log (partitionFunction kB T2 gZ EZ)
      ≤ Real.log (Real.exp (chi * (1/(kB*T1) - 1/(kB*T2))) * partitionFunction kB T1 gZ EZ) :=
    Real.log_le_log (partitionFunction_pos hgZ) hM2
  have hrhs : Real.log (Real.exp (chi * (1/(kB*T1) - 1/(kB*T2))) * partitionFunction kB T1 gZ EZ)
      = chi * (1/(kB*T1) - 1/(kB*T2)) + Real.log (partitionFunction kB T1 gZ EZ) := by
    rw [Real.log_mul (Real.exp_pos _).ne' (partitionFunction_pos hgZ).ne', Real.log_exp]
  rw [hrhs] at hP0raw
  have heq : chi * (1/(kB*T1) - 1/(kB*T2)) = chi/(kB*T1) - chi/(kB*T2) := by ring
  rw [heq] at hP0raw
  -- Bt: thermal bracket log is strictly increasing -- this is the sole strictness source.
  have hBt : Real.log (thermalBracket kB T1 me h) < Real.log (thermalBracket kB T2 me h) :=
    Real.log_lt_log (thermalBracket_pos hkB hT1 hme hh) (thermalBracket_strictMono' hkB hme hh hlt)
  linarith [hP1, hP0raw, hBt]

end DryRun
