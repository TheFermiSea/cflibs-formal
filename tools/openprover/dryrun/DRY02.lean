import Mathlib
import CflibsFormal.Saha
import CflibsFormal.PartitionLipschitz
import CflibsFormal.Analysis

open CflibsFormal

namespace DryRun

variable {ι : Type*} [Fintype ι]
variable {κ : Type*} [Fintype κ]

/-- **Saha-factor strict monotonicity in temperature (M4, EXACT, Saha–Eggert (Griem)).**
On the whole positive temperature axis, under the physically universal hypothesis that
every bound level of the lower (neutral) stage sits at or below the ionization limit
(`∀ k, EZ k ≤ chi`), the Saha factor `S(T)` is *strictly* increasing in `T`. Proof:
rewrite `log S(T₁) < log S(T₂)` via `log_sahaFactor` at both temperatures; the upper-stage
partition term is nondecreasing (`partitionFunction_mono_temp`), the lower-stage growth is
dominated by the same χ-weighted factor as the exponential channel
(`partitionFunction_upper_growth`), and the thermal bracket is *strictly* increasing
(`thermalBracket_strictMono`), which alone supplies strictness; assemble by `linarith`
through `Real.log_lt_log_iff` using `sahaFactor_pos`. `hchi` and `hEZ` are carried for API
parity with `sahaFactor_lipschitz_temp` but are not load-bearing in this proof. -/
theorem sahaFactor_strictMonoOn_temp [Nonempty ι] [Nonempty κ]
    {kB me h chi : ℝ} {gZ EZ : ι → ℝ} {gZ1 EZ1 : κ → ℝ}
    (hkB : 0 < kB) (hme : 0 < me) (hh : 0 < h) (_hchi : 0 ≤ chi)
    (hgZ : ∀ k, 0 < gZ k) (_hEZ : ∀ k, 0 ≤ EZ k)
    (hgZ1 : ∀ k, 0 < gZ1 k) (hEZ1 : ∀ k, 0 ≤ EZ1 k)
    (hEχ : ∀ k, EZ k ≤ chi) :
    StrictMonoOn (fun T => sahaFactor kB T me h chi gZ EZ gZ1 EZ1) (Set.Ioi 0) := by
  sorry

end DryRun
