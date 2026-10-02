import Mathlib
import CflibsFormal.Alt.StochasticBudget

/-!
# Queue target FT12-olsSlope-subGaussian-tail-hetero (deep audit 2026-09-24, FT-12 (a) item 1)

Heteroscedastic sub-Gaussian concentration of the OLS Boltzmann slope: per-line variance
proxies. Statement file for the proof queue: one target theorem, one `sorry`.
-/

open Finset CflibsFormal MeasureTheory ProbabilityTheory

namespace Plan.FT12

variable {ι : Type*} [Fintype ι] {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Heteroscedastic sub-Gaussian tail of the OLS Boltzmann slope.** In the linear model
`y k = α + β·E k + ε k` (`Alt.betaHat`), let the log-ordinate noises `ε k` be independent and
each sub-Gaussian with its own variance proxy `c k` (`HasSubgaussianMGF (ε k) (c k) μ`). Then
  `μ {|β̂ − β| ≥ δ} ≤ 2·exp(−δ²/(2·∑ k, w k²·c k))`,  `w k = olsWeight E k = (E k − Ē)/SS_E`.
Reason: `β̂ = β + ∑ k, w k·ε k` exactly (`Alt.olsSlope_estimator_eq`); the weighted sum is
sub-Gaussian with proxy `∑ k, w k²·c k` by independence; a Chernoff bound on each tail and a
union bound give the factor 2. With `c k ≡ c > 0` this is the landed homoscedastic
`Alt.olsSlope_subGaussian_tail`, since `∑ k, w k² = 1/SS_E`; here each line keeps its own proxy,
which is what a per-line SNR supplies. If the proxy sum is `0`, Lean's `x/0 = 0` makes the
right side `2`, a true and trivial bound, so no positivity hypothesis on `c` is needed (the
audit verifier dropped the sketch's `hc`).

Hypotheses: `hvar` (at least two distinct upper-level energies, `SS_E > 0`: the OLS weights and
the estimator identity need it); `hδ` (the Chernoff bound is for nonnegative thresholds);
`hindep` (mutual independence of the noises, needed for the proxy of the sum to be the sum of
proxies); `hsubG` (the per-line proxies, an assumed input). No `[IsProbabilityMeasure μ]`
instance is stated: `hindep` already implies it (`iIndepFun.isProbabilityMeasure`), so the
statement is equivalent to the probability-space version; the instance is omitted as in the
landed twin.

Scope (two-axis): relation PURE-MATH (a concentration inequality); definitions used:
`Alt.betaHat` REDUCED (the OLS slope of the additive-noise linear Boltzmann-plot model
`y k = α + β·E k + ε k`) and `olsWeight` PURE-MATH; published REDUCED (the weaker axis), citation
Aitken 1935, matching the landed homoscedastic twin's row
`Alt/StochasticBudget.lean olsSlope_subGaussian_tail REDUCED Aitken 1935`. The physics binding
`c k ≈ 1/SNR_k²` (delta method on `log I`) is an APPROXIMATION and is not part of this
statement. -/
theorem olsSlope_subGaussian_tail_hetero [Nonempty ι] (E : ι → ℝ) (α β : ℝ) (ε : ι → Ω → ℝ)
    {c : ι → NNReal} {δ : ℝ} (hvar : 0 < ∑ k, (E k - mean E) ^ 2) (hδ : 0 ≤ δ)
    (hindep : iIndepFun ε μ) (hsubG : ∀ k, HasSubgaussianMGF (ε k) (c k) μ) :
    μ.real {ω | δ ≤ |Alt.betaHat E α β ε ω - β|}
      ≤ 2 * Real.exp (-(δ ^ 2) / (2 * ∑ k, olsWeight E k ^ 2 * (c k : ℝ))) := by
  have hindep' : iIndepFun (fun k => (fun x : ℝ => olsWeight E k * x) ∘ ε k) μ :=
    hindep.comp (fun k x => olsWeight E k * x) (fun k => measurable_id.const_mul (olsWeight E k))
  have hsum : HasSubgaussianMGF (fun ω => ∑ k, olsWeight E k * ε k ω)
      (∑ k, (⟨(olsWeight E k) ^ 2, sq_nonneg _⟩ * c k : NNReal)) μ :=
    HasSubgaussianMGF.sum_of_iIndepFun hindep'
      (fun k _ => (hsubG k).const_mul (olsWeight E k))
  have hterm : ∀ k, ((⟨(olsWeight E k) ^ 2, sq_nonneg _⟩ * c k : NNReal) : ℝ)
      = (olsWeight E k) ^ 2 * (c k : ℝ) := fun k => NNReal.coe_mul _ _
  have hpos := hsum.measure_ge_le hδ
  have hneg := hsum.neg.measure_ge_le hδ
  simp only [NNReal.coe_sum, Pi.neg_apply, hterm] at hpos hneg
  have hset : {ω | δ ≤ |Alt.betaHat E α β ε ω - β|}
      = {ω | δ ≤ ∑ k, olsWeight E k * ε k ω}
          ∪ {ω | δ ≤ -(∑ k, olsWeight E k * ε k ω)} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_union]
    rw [Alt.olsSlope_estimator_eq E α β ε hvar,
      show β + (∑ k, olsWeight E k * ε k ω) - β = ∑ k, olsWeight E k * ε k ω from by ring]
    exact le_abs
  rw [hset]
  calc μ.real ({ω | δ ≤ ∑ k, olsWeight E k * ε k ω}
          ∪ {ω | δ ≤ -(∑ k, olsWeight E k * ε k ω)})
      ≤ μ.real {ω | δ ≤ ∑ k, olsWeight E k * ε k ω}
          + μ.real {ω | δ ≤ -(∑ k, olsWeight E k * ε k ω)} := measureReal_union_le _ _
    _ ≤ _ := add_le_add hpos hneg
    _ = _ := by ring

end Plan.FT12
