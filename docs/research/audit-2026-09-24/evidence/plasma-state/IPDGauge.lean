import CflibsFormal.Saha
open CflibsFormal
variable {ι κ : Type*} [Fintype ι] [Fintype κ]
/-- IPD gauge: lowering chi by d multiplies the Saha factor by exp(d/(kB T)). -/
theorem sahaFactor_ipd_gauge (kB T me h chi d : ℝ) (gZ EZ : ι → ℝ) (gZ1 EZ1 : κ → ℝ) :
    sahaFactor kB T me h (chi - d) gZ EZ gZ1 EZ1
      = sahaFactor kB T me h chi gZ EZ gZ1 EZ1 * Real.exp (d / (kB * T)) := by
  unfold sahaFactor
  rw [show -(chi - d) / (kB * T) = -chi / (kB * T) + d / (kB * T) by ring, Real.exp_add]
  ring
/-- Consequence: an IPD-off inverse applied to IPD-on forward data reports
n_e * exp(-d/(kB T)) (the 0.9358x of R1-07 at d = 0.0629 eV, kT = 0.948 eV). -/
theorem ne_ipd_mismatch (kB T me h chi d R ne : ℝ) (gZ EZ : ι → ℝ) (gZ1 EZ1 : κ → ℝ)
    (hR : R ≠ 0) (hfwd : R * ne = sahaFactor kB T me h (chi - d) gZ EZ gZ1 EZ1) :
    electronDensityFromRatio kB T me h chi gZ EZ gZ1 EZ1 R = ne * Real.exp (-(d / (kB * T))) := by
  unfold electronDensityFromRatio
  rw [sahaFactor_ipd_gauge] at hfwd
  have he : Real.exp (d / (kB * T)) ≠ 0 := Real.exp_ne_zero _
  rw [Real.exp_neg, div_eq_iff hR]
  field_simp
  linarith [hfwd]
