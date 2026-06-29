/-
Copyright (c) 2026 Brian Squires. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Squires
-/
import Mathlib
import CflibsFormal.Alt.OLSVariance

/-!
# CF-LIBS formalization — Gauss–Markov optimality (BLUE) for the OLS Boltzmann-plot slope

`Alt.OLSVariance` proves the *value* of the OLS slope variance, `Var(β̂) = σ²/SS_E`, but its
honest-scope docstring explicitly **does not claim optimality**: "we prove the variance value and
unbiasedness only — NOT that OLS is the minimum-variance estimator among linear unbiased
estimators (the full Gauss–Markov/Aitken optimality theorem)." **This module discharges that
promise**: among *all* linear unbiased estimators of the slope, OLS has the least variance —
it is the Best Linear Unbiased Estimator (BLUE).

A **general linear estimator** of the ordinates is `Tₐ(ω) = ∑ₖ aₖ·yₖ(ω)` for weights `a : ι → ℝ`,
under the same linear model `yₖ(ω) = α + β·Eₖ + εₖ(ω)` as `Alt.OLSVariance`. We prove:

* `linEstimator_eq` — **pure pointwise algebra (no probability):**
  `Tₐ(ω) = α·(∑ₖaₖ) + β·(∑ₖaₖEₖ) + ∑ₖaₖ·εₖ(ω)`. Under the unbiasedness constraints
  `∑ₖaₖ = 0` and `∑ₖaₖEₖ = 1` the deterministic part collapses to `β` (`linEstimator_eq_unbiased`).
* `linEstimator_expectation` — **`𝔼[Tₐ] = α·(∑ₖaₖ) + β·(∑ₖaₖEₖ)`** (linearity + zero-mean noise).
* `linEstimator_unbiased_iff` — **the unbiasedness characterization is an `iff`:** `Tₐ` is unbiased
  for `β` *for every* `α, β` **iff** `∑ₖaₖ = 0 ∧ ∑ₖaₖEₖ = 1`. The OLS weights satisfy both.
* `linEstimator_variance` — **`Var(Tₐ) = σ²·∑ₖaₖ²`** (uncorrelated-sum variance + scaling), the
  arbitrary-weight generalization of `Alt.OLSVariance.olsSlope_variance_noiseGain`.
* `weight_sq_ge_noiseGain` — **the deterministic algebraic core** `∑ₖwₖ² ≤ ∑ₖaₖ²` for any unbiased
  `a` (`wₖ = olsWeight E k`); the Pythagorean step `∑aₖ² = ∑wₖ² + ∑(aₖ−wₖ)²` after the cross term
  vanishes (`∑ₖwₖaₖ = ∑ₖwₖ² = 1/SS_E`). Reuses `OLS.olsSlope_noise_gain`.
* `ols_is_blue` — **THE headline:** `Var(β̂) ≤ Var(Tₐ)` for *every* unbiased linear estimator `Tₐ`.

## Honest scope

* **EXACT, not approximate.** Every result is an exact identity / inequality under the stated
  linear-Gaussian-free model (no linearization). `weight_sq_ge_noiseGain` is deterministic Finset
  algebra; only `linEstimator_variance`/`ols_is_blue` touch the probability layer.
* **Unbiasedness is an `iff`, quantified over `α, β`.** `linEstimator_unbiased_iff` characterizes
  unbiasedness for *all* intercepts/slopes; "unbiased for one fixed `β`" is strictly weaker and is
  NOT what BLUE optimality requires. `ols_is_blue` takes the two constraints as hypotheses.
* **The classical Gauss–Markov hypothesis — pairwise uncorrelatedness, inherited from
  `Alt.OLSVariance`.** The variance comparison routes through `linEstimator_variance`, which (like
  `olsSlope_variance_noiseGain`) needs only `cov(εᵢ, εⱼ) = 0` for `i ≠ j` — NOT independence. So
  `ols_is_blue` is the genuine Gauss–Markov theorem: minimum variance among linear unbiased
  estimators under exactly the textbook (uncorrelated, homoscedastic, zero-mean) error model.
* **Consistency with `Alt.OLSVariance`.** `ols_is_blue` rewrites `Var(β̂)` via
  `olsSlope_variance_noiseGain` to `σ²·∑wₖ²` and `Var(Tₐ)` via `linEstimator_variance` to `σ²·∑aₖ²`,
  then closes with `weight_sq_ge_noiseGain` and `0 ≤ σ²`; the OLS case `a = w` attains equality,
  so the bound is sharp and agrees with `olsSlope_variance_eq` at `a = olsWeight E`.
* **Physics is in prose only.** With `β = −1/(k_B T)` (Boltzmann plot), BLUE says OLS extracts the
  least-variance inverse temperature among all linear ordinate combinations satisfying the two
  unbiasedness constraints. No physical constant enters any Lean statement.

## Literature

The minimum-variance property of OLS among linear unbiased estimators is the Gauss–Markov theorem;
its modern generalized-least-squares form is A. C. Aitken, "On Least Squares and Linear Combination
of Observations," *Proceedings of the Royal Society of Edinburgh* **55** (1935) 42–48. The
simple-regression statement (slope variance `σ²/Sₓₓ` is least among unbiased linear estimators) is
standard, e.g. N. R. Draper and H. Smith, *Applied Regression Analysis*, 3rd ed.,
Wiley-Interscience (1998), Ch. 1–2. This module formalizes the optimality layer deferred by
`Alt.OLSVariance`; its deterministic kernel is `OLS.olsSlope_noise_gain` (`∑wₖ² = 1/SS_E`).
-/

namespace CflibsFormal.Alt

open CflibsFormal
open MeasureTheory ProbabilityTheory
open Finset Real
open scoped BigOperators ProbabilityTheory

variable {ι : Type*} [Fintype ι]
variable {Ω : Type*}

/-- **A general linear estimator of the ordinates.** For weights `a : ι → ℝ` and the linear model
`yₖ(ω) = α + β·Eₖ + εₖ(ω)`, `linEstimator a E α β ε ω = ∑ₖ aₖ·yₖ(ω)`. The OLS slope `betaHat`
is the special case `a = olsWeight E` (via `OLS.olsSlope_eq_centered`); BLUE optimality
(`ols_is_blue`) ranges over all `a` meeting the unbiasedness constraints. -/
noncomputable def linEstimator (a E : ι → ℝ) (α β : ℝ) (ε : ι → Ω → ℝ) (ω : Ω) : ℝ :=
  ∑ k, a k * (α + β * E k + ε k ω)

/-- **Estimator = deterministic part + weighted noise (pure pointwise algebra, no probability).**
For every `ω`, `Tₐ(ω) = α·(∑ₖaₖ) + β·(∑ₖaₖEₖ) + ∑ₖaₖ·εₖ(ω)`: distribute and regroup. The three
sums are the intercept-, slope-, and noise-channels of a general linear ordinate combination. -/
theorem linEstimator_eq (a E : ι → ℝ) (α β : ℝ) (ε : ι → Ω → ℝ) (ω : Ω) :
    linEstimator a E α β ε ω
      = α * (∑ k, a k) + β * (∑ k, a k * E k) + ∑ k, a k * ε k ω := by
  unfold linEstimator
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun k _ => by ring)

/-- **Under the unbiasedness constraints the deterministic part collapses to `β`.** Given
`∑ₖaₖ = 0` and `∑ₖaₖEₖ = 1`, `Tₐ(ω) = β + ∑ₖaₖ·εₖ(ω)`: the intercept channel vanishes
(`∑aₖ = 0`) and the slope is recovered exactly (`∑aₖEₖ = 1`); only the noise survives. -/
theorem linEstimator_eq_unbiased (a E : ι → ℝ) (α β : ℝ) (ε : ι → Ω → ℝ)
    (ha0 : ∑ k, a k = 0) (ha1 : ∑ k, a k * E k = 1) (ω : Ω) :
    linEstimator a E α β ε ω = β + ∑ k, a k * ε k ω := by
  rw [linEstimator_eq, ha0, ha1]; ring

variable [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **Expectation of a general linear estimator** `𝔼[Tₐ] = α·(∑ₖaₖ) + β·(∑ₖaₖEₖ)`. Linearity of
expectation over the finite weighted noise sum plus zero-mean noise; needs neither independence nor
homoscedasticity. The slope-channel coefficient `∑ₖaₖEₖ` and intercept-channel coefficient `∑ₖaₖ`
are exactly the two quantities the unbiasedness `iff` (`linEstimator_unbiased_iff`) constrains. -/
theorem linEstimator_expectation (a E : ι → ℝ) (α β : ℝ) (ε : ι → Ω → ℝ)
    (hL2 : ∀ k, MemLp (ε k) 2 μ)
    (hmean0 : ∀ k, μ[ε k] = 0) :
    μ[linEstimator a E α β ε] = α * (∑ k, a k) + β * (∑ k, a k * E k) := by
  simp_rw [linEstimator_eq a E α β ε]
  exact expectation_const_add_weightedNoise a (α * (∑ k, a k) + β * (∑ k, a k * E k)) ε hL2 hmean0

/-- **Unbiasedness characterization (an `iff`).** A linear estimator `Tₐ` is unbiased for the slope
`β` *for every* intercept `α` and slope `β` **iff** `∑ₖaₖ = 0 ∧ ∑ₖaₖEₖ = 1`. Forward: evaluate at
`(α,β) = (1,0)` and `(0,1)`; reverse: substitute the two constraints. The OLS weights satisfy both
(`OLS.centered_sum_zero`, `centered_mul_self`), so OLS is admissible in the BLUE class. -/
theorem linEstimator_unbiased_iff (a E : ι → ℝ) (ε : ι → Ω → ℝ)
    (hL2 : ∀ k, MemLp (ε k) 2 μ)
    (hmean0 : ∀ k, μ[ε k] = 0) :
    (∀ α β : ℝ, μ[linEstimator a E α β ε] = β)
      ↔ (∑ k, a k = 0 ∧ ∑ k, a k * E k = 1) := by
  constructor
  · intro h
    have h10 := h 1 0
    have h01 := h 0 1
    rw [linEstimator_expectation a E 1 0 ε hL2 hmean0] at h10
    rw [linEstimator_expectation a E 0 1 ε hL2 hmean0] at h01
    simp only [one_mul, zero_mul, add_zero, zero_add] at h10 h01
    exact ⟨h10, h01⟩
  · rintro ⟨ha0, ha1⟩ α β
    rw [linEstimator_expectation a E α β ε hL2 hmean0, ha0, ha1]; ring

/-- **Variance of a general linear estimator** `Var(Tₐ) = σ²·∑ₖaₖ²`. Strip the constant
deterministic part (`variance_const_add`), expand the weighted-noise sum's variance into its
double-covariance form (`variance_sum`), pull each weight out (`covariance_const_mul`), and read
the diagonal `aₖ²σ²` after uncorrelatedness annihilates the off-diagonal. The arbitrary-weight
generalization of
`Alt.OLSVariance.olsSlope_variance_noiseGain` (which is the case `a = olsWeight E`), and the
right-hand factor `∑ₖaₖ²` is exactly what `weight_sq_ge_noiseGain` minimizes over unbiased `a`. -/
theorem linEstimator_variance (a E : ι → ℝ) (α β σ : ℝ) (ε : ι → Ω → ℝ)
    (hL2 : ∀ k, MemLp (ε k) 2 μ)
    (huncorr : ∀ i j, i ≠ j → covariance (ε i) (ε j) μ = 0)
    (hhom : ∀ k, variance (ε k) μ = σ ^ 2) :
    variance (linEstimator a E α β ε) μ = σ ^ 2 * ∑ k, (a k) ^ 2 := by
  rw [funext (linEstimator_eq a E α β ε)]
  exact variance_const_add_weightedNoise a (α * (∑ k, a k) + β * (∑ k, a k * E k)) σ ε
    hL2 huncorr hhom

/-- **The deterministic algebraic core of Gauss–Markov optimality** `∑ₖwₖ² ≤ ∑ₖaₖ²`, with
`wₖ = olsWeight E k`, for ANY unbiased weights (`∑ₖaₖ = 0`, `∑ₖaₖEₖ = 1`). Pythagorean argument:
the OLS noise gain is `∑wₖ² = 1/SS_E` (`OLS.olsSlope_noise_gain`), the cross term is
`∑wₖaₖ = (∑(Eₖ−Ē)aₖ)/SS_E = 1/SS_E` (using both constraints), so `∑wₖ(aₖ−wₖ) = 0` and hence
`∑aₖ² = ∑wₖ² + ∑(aₖ−wₖ)² ≥ ∑wₖ²`. Pure Finset algebra — no probability. -/
theorem weight_sq_ge_noiseGain [Nonempty ι] (a E : ι → ℝ)
    (hvar : 0 < ∑ k, (E k - mean E) ^ 2)
    (ha0 : ∑ k, a k = 0)
    (ha1 : ∑ k, a k * E k = 1) :
    ∑ k, (olsWeight E k) ^ 2 ≤ ∑ k, (a k) ^ 2 := by
  have hwsq : ∑ k, (olsWeight E k) ^ 2 = 1 / (∑ k, (E k - mean E) ^ 2) := by
    simp only [olsWeight]; exact olsSlope_noise_gain E hvar
  have hcross : ∑ k, olsWeight E k * a k = 1 / (∑ k, (E k - mean E) ^ 2) := by
    have hrw : ∑ k, olsWeight E k * a k
        = (∑ k, (E k - mean E) * a k) / (∑ k, (E k - mean E) ^ 2) := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl (fun k _ => by rw [olsWeight]; ring)
    have hnum : ∑ k, (E k - mean E) * a k = 1 := by
      have hsplit : ∀ k, (E k - mean E) * a k = a k * E k - mean E * a k := fun k => by ring
      rw [Finset.sum_congr rfl (fun k _ => hsplit k), Finset.sum_sub_distrib, ha1,
        ← Finset.mul_sum, ha0, mul_zero, sub_zero]
    rw [hrw, hnum]
  have hmid : ∑ k, olsWeight E k * (a k - olsWeight E k) = 0 := by
    have hrw : ∑ k, olsWeight E k * (a k - olsWeight E k)
        = (∑ k, olsWeight E k * a k) - ∑ k, (olsWeight E k) ^ 2 := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun k _ => by ring)
    rw [hrw, hcross, hwsq, sub_self]
  have hexp : ∑ k, (a k) ^ 2
      = ∑ k, (olsWeight E k) ^ 2 + 2 * (∑ k, olsWeight E k * (a k - olsWeight E k))
        + ∑ k, (a k - olsWeight E k) ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  rw [hexp, hmid, mul_zero, add_zero]
  have hnn : 0 ≤ ∑ k, (a k - olsWeight E k) ^ 2 := Finset.sum_nonneg (fun k _ => sq_nonneg _)
  linarith

/-- **THE headline — OLS is the Best Linear Unbiased Estimator (BLUE) of the slope.** For ANY
linear estimator `Tₐ` that is unbiased (`∑ₖaₖ = 0`, `∑ₖaₖEₖ = 1`), `Var(β̂) ≤ Var(Tₐ)` under the
uncorrelated, homoscedastic, square-integrable noise model. Combines `olsSlope_variance_noiseGain`
(`Var(β̂) = σ²·∑wₖ²`), `linEstimator_variance` (`Var(Tₐ) = σ²·∑aₖ²`), the algebraic core
`weight_sq_ge_noiseGain` (`∑wₖ² ≤ ∑aₖ²`), and `0 ≤ σ²`. Equality at `a = olsWeight E`, so the
bound is sharp. This is the Gauss–Markov/Aitken optimality theorem deferred by `Alt.OLSVariance`. -/
theorem ols_is_blue [Nonempty ι] (a E : ι → ℝ) (α β σ : ℝ) (ε : ι → Ω → ℝ)
    (hvar : 0 < ∑ k, (E k - mean E) ^ 2)
    (hL2 : ∀ k, MemLp (ε k) 2 μ)
    (huncorr : ∀ i j, i ≠ j → covariance (ε i) (ε j) μ = 0)
    (hhom : ∀ k, variance (ε k) μ = σ ^ 2)
    (ha0 : ∑ k, a k = 0)
    (ha1 : ∑ k, a k * E k = 1) :
    variance (betaHat E α β ε) μ ≤ variance (linEstimator a E α β ε) μ := by
  rw [olsSlope_variance_noiseGain E α β σ ε hvar hL2 huncorr hhom,
      linEstimator_variance a E α β σ ε hL2 huncorr hhom]
  exact mul_le_mul_of_nonneg_left (weight_sq_ge_noiseGain a E hvar ha0 ha1) (sq_nonneg σ)

end CflibsFormal.Alt
