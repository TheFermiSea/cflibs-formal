/-
Copyright (c) 2026 Brian Squires. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Squires
-/
import Mathlib
import CflibsFormal.ErrorBudget

/-!
# CF-LIBS formalization — the Gauss–Markov variance law for the OLS Boltzmann-plot slope

`ErrorBudget.lean` proves the *deterministic* error-propagation chain and its algebraic kernel
`olsSlope_noise_gain : ∑ₖ wₖ² = 1/SS_E` (with weights `wₖ = (Eₖ − Ē)/SS_E`,
`SS_E = ∑ₖ (Eₖ − Ē)²`), but its module docstring explicitly **defers the probabilistic `Var`
layer** — "it needs `Mathlib`'s probability stack" — and names the target law
`Var(β̂) = σ²·∑ wₖ² = σ²/SS_E` (Gauss–Markov). **This module discharges that promise.**

We put a probability measure `μ` on the sample space and model the Boltzmann-plot ordinates as a
*linear model with random noise*:
`yₖ(ω) = α + β·Eₖ + εₖ(ω)`, with `εₖ` zero-mean, homoscedastic (common variance `σ²`),
mutually independent, and square-integrable. The OLS slope of the realized points becomes a random
variable `betaHat ω = olsSlope E (y(·,ω))`. We prove:

* `olsSlope_estimator_eq` — **pure pointwise algebra (no probability):** `β̂(ω) = β + ∑ₖ wₖ·εₖ(ω)`.
  The realized intercept `α` cancels (`∑ wₖ = 0`) and the slope `β` is recovered exactly
  (`∑ wₖ Eₖ = 1`); only the noise survives. Reuses `ErrorBudget.olsSlope_eq_centered`.
* `olsSlope_unbiased` — **`𝔼[β̂] = β`** (linearity of expectation + zero-mean noise; needs neither
  independence nor homoscedasticity).
* `olsSlope_variance_noiseGain` — **`Var(β̂) = σ²·∑ₖ wₖ²`** (independent-sum variance + scaling).
* `olsSlope_variance_eq` — **THE headline: `Var(β̂) = σ²/SS_E`** (combine with
  `ErrorBudget.olsSlope_noise_gain`).
* `olsSlope_variance_antitone` — more energy spread ⇒ less slope variance (`SS_E ≤ SS_E'`).

## Honest scope

* **EXACT, not approximate.** `olsSlope_estimator_eq` is a pointwise identity; the unbiasedness and
  variance results are exact identities under the stated model (no linearization).
* **Independence is a REDUCTION — flagged.** The classical Gauss–Markov theorem needs only
  *pairwise-uncorrelated* (zero-covariance), homoscedastic, zero-mean errors. `Mathlib`'s
  `IndepFun.variance_sum` consumes pairwise *independence*, and we supply it from the (stronger)
  mutual independence `iIndepFun ε μ`. So the variance theorems are proved under a hypothesis
  *stronger* than the classical statement requires. (A future strengthening to genuine
  uncorrelatedness would route through `ProbabilityTheory.variance_sum'`, the double-covariance
  form; that is out of scope here.)
* **Optimality / BLUE is NOT claimed.** We prove the variance *value* and unbiasedness only — NOT
  that OLS is the minimum-variance estimator among linear unbiased estimators (the full
  Gauss–Markov/Aitken optimality theorem).
* **Consistency with `ErrorBudget`.** `olsSlope_variance_eq` is literally
  `olsSlope_variance_noiseGain` composed with `ErrorBudget.olsSlope_noise_gain`; both route through
  the single identity `∑ wₖ² = 1/SS_E`, so the two modules cannot disagree on `σ²/SS_E`.
* **The statistical "more lines help".** Unlike the *deterministic* worst-case bound
  `ErrorBudget.olsSlope_stable_l2_sq` (which carries `Fintype.card ι` in the numerator and does
  *not* improve with redundant lines), the variance law has *no* `card ι`: `Var(β̂) = σ²/SS_E`
  strictly decreases as `SS_E` grows (`olsSlope_variance_antitone`). This is the principled
  statistical content the deterministic chain could not supply.
* **Physics is in prose only.** For the Boltzmann plot `yₖ = log(Iₖ/(gₖAₖ))` the slope is
  `β = −1/(k_B T)`, so `Var(β̂) = σ²/SS_E` propagates (via `ErrorBudget.temp_rel_error_eq`) to the
  temperature uncertainty `σ_T/T = k_B T·σ_β`: bunched upper-level energies (small `SS_E`) blow up
  the inverse-temperature variance — the principled origin of the energy-spread threshold. No
  physical constant enters any Lean statement.

## Literature

The slope estimator's variance `Var(β̂) = σ²/Sₓₓ` under zero-mean, homoscedastic, uncorrelated
errors is the Gauss–Markov law; its modern (generalized least squares) form is A. C. Aitken,
"On Least Squares and Linear Combination of Observations," *Proceedings of the Royal Society of
Edinburgh* **55** (1935) 42–48. The closed form `Var(β̂) = σ²/∑(xₖ − x̄)²` for the
simple-regression slope is standard, e.g. N. R. Draper and H. Smith, *Applied Regression
Analysis*, 3rd ed., Wiley-Interscience (1998), Ch. 1–2. In the CF-LIBS setting the multi-line
least-squares Boltzmann-plot fit is reviewed in Tognoni, E.; Cristoforetti, G.; Legnaioli, S.;
Palleschi, V. "Calibration-Free Laser-Induced Breakdown Spectroscopy: State of the art."
*Spectrochimica Acta Part B* **65** (2010) 1–14; the intercept-borne concentration is Ciucci, A.;
Corsi, M.; Palleschi, V.; Rastelli, S.; Salvetti, A.; Tognoni, E. *Applied Spectroscopy* **53**
(1999) 960–964. The probabilistic `Var` layer formalized here is the one deferred by
`CflibsFormal.ErrorBudget`; the algebraic kernel `∑ₖ wₖ² = 1/SS_E` is its `olsSlope_noise_gain`.
-/

namespace CflibsFormal.Alt

open CflibsFormal
open MeasureTheory ProbabilityTheory
open Finset Real
open scoped BigOperators ProbabilityTheory

variable {ι : Type*} [Fintype ι]

/-- **Gauss–Markov weight** `wₖ = (Eₖ − Ē)/SS_E` with `SS_E = ∑ⱼ (Eⱼ − Ē)²`. Written in the exact
form of `ErrorBudget.olsSlope_noise_gain`'s summand so that `∑ₖ wₖ² = 1/SS_E` rewrites literally.
With these weights `β̂(y) = ∑ₖ wₖ yₖ` (`olsSlope_eq_centered`), `∑ₖ wₖ = 0`, and `∑ₖ wₖ Eₖ = 1`. -/
noncomputable def olsWeight (E : ι → ℝ) (k : ι) : ℝ :=
  (E k - mean E) / (∑ j, (E j - mean E) ^ 2)

variable {Ω : Type*}

/-- **The OLS-slope estimator as a random variable.** For the linear model
`yₖ(ω) = α + β·Eₖ + εₖ(ω)`, `betaHat E α β ε ω` is the ordinary-least-squares slope of the realized
Boltzmann-plot points `(Eₖ, yₖ(ω))`. The realized intercept `α` drops out (see
`olsSlope_estimator_eq`), so the estimator's value does not depend on `α`. -/
noncomputable def betaHat (E : ι → ℝ) (α β : ℝ) (ε : ι → Ω → ℝ) (ω : Ω) : ℝ :=
  olsSlope E (fun k => α + β * E k + ε k ω)

/-- **Centered–energy identity** `∑ₖ (Eₖ − Ē)·Eₖ = ∑ₖ (Eₖ − Ē)² = SS_E`. The `mean E` term drops
because `∑ₖ (Eₖ − Ē) = 0` (`centered_sum_zero`). Isolated so the estimator algebra stays clean. -/
theorem centered_mul_self [Nonempty ι] (E : ι → ℝ) :
    ∑ k, (E k - mean E) * E k = ∑ k, (E k - mean E) ^ 2 := by
  have h0 : ∑ k, (E k - mean E) = 0 := centered_sum_zero E
  calc ∑ k, (E k - mean E) * E k
      = ∑ k, ((E k - mean E) ^ 2 + (E k - mean E) * mean E) :=
        Finset.sum_congr rfl (fun k _ => by ring)
    _ = ∑ k, (E k - mean E) ^ 2 := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, h0, zero_mul, add_zero]

/-- **Estimator = truth + weighted noise (pure pointwise algebra, no probability).** For every `ω`,
`β̂(ω) = β + ∑ₖ wₖ·εₖ(ω)` with `wₖ = olsWeight E k`. The realized intercept `α` cancels (`∑ wₖ = 0`)
and the slope `β` is recovered exactly (`∑ wₖ Eₖ = 1`); only the noise survives. Reuses
`olsSlope_eq_centered`, `centered_sum_zero`, and `centered_mul_self`. -/
theorem olsSlope_estimator_eq [Nonempty ι] (E : ι → ℝ) (α β : ℝ) (ε : ι → Ω → ℝ)
    (hvar : 0 < ∑ k, (E k - mean E) ^ 2) (ω : Ω) :
    betaHat E α β ε ω = β + ∑ k, olsWeight E k * ε k ω := by
  have hS : (∑ k, (E k - mean E) ^ 2) ≠ 0 := hvar.ne'
  unfold betaHat
  rw [olsSlope_eq_centered]
  have hsplit : ∀ k, (E k - mean E) * (α + β * E k + ε k ω)
      = α * (E k - mean E) + β * ((E k - mean E) * E k) + (E k - mean E) * ε k ω :=
    fun k => by ring
  have hnum : (∑ k, (E k - mean E) * (α + β * E k + ε k ω))
      = β * (∑ k, (E k - mean E) ^ 2) + ∑ k, (E k - mean E) * ε k ω := by
    rw [Finset.sum_congr rfl (fun k _ => hsplit k), Finset.sum_add_distrib,
      Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      centered_sum_zero E, centered_mul_self E]
    ring
  rw [hnum, add_div, mul_div_assoc, div_self hS, mul_one]
  congr 1
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl (fun k _ => by rw [olsWeight]; ring)

variable [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **Unbiasedness** `𝔼[β̂] = β`. Linearity of expectation over the finite weighted noise sum plus
zero-mean noise. Needs neither independence nor homoscedasticity. -/
theorem olsSlope_unbiased [Nonempty ι] (E : ι → ℝ) (α β : ℝ) (ε : ι → Ω → ℝ)
    (hvar : 0 < ∑ k, (E k - mean E) ^ 2)
    (hL2 : ∀ k, MemLp (ε k) 2 μ)
    (hmean0 : ∀ k, μ[ε k] = 0) :
    μ[betaHat E α β ε] = β := by
  have hint : ∀ k, Integrable (fun ω => olsWeight E k * ε k ω) μ :=
    fun k => ((hL2 k).const_mul (olsWeight E k)).integrable (by norm_num)
  have hSint : Integrable (fun ω => ∑ k, olsWeight E k * ε k ω) μ :=
    (memLp_finsetSum Finset.univ (fun k _ => (hL2 k).const_mul (olsWeight E k))).integrable
      (by norm_num)
  simp_rw [olsSlope_estimator_eq E α β ε hvar]
  rw [integral_add (integrable_const β) hSint,
    integral_finsetSum Finset.univ (fun k _ => hint k)]
  simp [integral_const_mul, hmean0]

/-- **Slope variance as the noise gain** `Var(β̂) = σ²·∑ₖ wₖ²`. Strip the constant `β`
(`variance_const_add`), split the independent weighted noise sum (`IndepFun.variance_sum`), pull
each weight out as `wₖ²` (`variance_const_mul`), then insert homoscedasticity. The `card`-free form
(no `Fintype.card ι` in the numerator) is the genuinely *statistical* "more lines help" statement,
in contrast to the deterministic ℓ² worst case `ErrorBudget.olsSlope_stable_l2_sq`. -/
theorem olsSlope_variance_noiseGain [Nonempty ι] (E : ι → ℝ) (α β σ : ℝ) (ε : ι → Ω → ℝ)
    (hvar : 0 < ∑ k, (E k - mean E) ^ 2)
    (hL2 : ∀ k, MemLp (ε k) 2 μ)
    (hindep : iIndepFun ε μ)
    (hhom : ∀ k, variance (ε k) μ = σ ^ 2) :
    variance (betaHat E α β ε) μ = σ ^ 2 * ∑ k, (olsWeight E k) ^ 2 := by
  have hpt : betaHat E α β ε = fun ω => β + ∑ k, olsWeight E k * ε k ω :=
    funext (olsSlope_estimator_eq E α β ε hvar)
  rw [hpt]
  have hmeas : AEStronglyMeasurable (fun ω => ∑ k, olsWeight E k * ε k ω) μ :=
    (memLp_finsetSum Finset.univ
      (fun k _ => (hL2 k).const_mul (olsWeight E k))).aestronglyMeasurable
  rw [variance_const_add hmeas β]
  have hfun : (fun ω => ∑ k, olsWeight E k * ε k ω)
      = ∑ k, (fun ω => olsWeight E k * ε k ω) := by
    funext ω; simp [Finset.sum_apply]
  rw [hfun, IndepFun.variance_sum
    (fun i _ => (hL2 i).const_mul (olsWeight E i))
    (fun i _ j _ hij =>
      (hindep.indepFun hij).comp
        (measurable_id.const_mul (olsWeight E i))
        (measurable_id.const_mul (olsWeight E j)))]
  simp_rw [variance_const_mul, hhom]
  rw [← Finset.sum_mul]
  ring

/-- **THE headline — the Gauss–Markov slope-variance law** `Var(β̂) = σ²/SS_E`. Combines
`olsSlope_variance_noiseGain` with `ErrorBudget.olsSlope_noise_gain` (`∑ₖ wₖ² = 1/SS_E`). This
fulfills the `Var` layer deferred in `ErrorBudget`'s module docstring and matches its named target.
Physics: `β = −1/(k_B T)` (Boltzmann plot), so a small `SS_E` (energies bunched) blows up the
inverse-temperature variance — the principled origin of the energy-spread threshold. -/
theorem olsSlope_variance_eq [Nonempty ι] (E : ι → ℝ) (α β σ : ℝ) (ε : ι → Ω → ℝ)
    (hvar : 0 < ∑ k, (E k - mean E) ^ 2)
    (hL2 : ∀ k, MemLp (ε k) 2 μ)
    (hindep : iIndepFun ε μ)
    (hhom : ∀ k, variance (ε k) μ = σ ^ 2) :
    variance (betaHat E α β ε) μ = σ ^ 2 / (∑ k, (E k - mean E) ^ 2) := by
  rw [olsSlope_variance_noiseGain E α β σ ε hvar hL2 hindep hhom]
  simp only [olsWeight]
  rw [olsSlope_noise_gain E hvar, mul_one_div]

/-- **Monotonicity — more energy spread ⇒ less slope variance.** With the same noise law,
`SS_E ≤ SS_E'` gives `Var(β̂_{E'}) ≤ Var(β̂_E)`. The `card`-free statistical content that the
deterministic worst-case chain (`ErrorBudget.olsSlope_stable_l2_sq`, `card ι` in the numerator)
could not supply: redundant lines at NEW energies help, by enlarging `SS_E`. -/
theorem olsSlope_variance_antitone [Nonempty ι] (E E' : ι → ℝ) (α β σ : ℝ) (ε : ι → Ω → ℝ)
    (hvar : 0 < ∑ k, (E k - mean E) ^ 2) (hvar' : 0 < ∑ k, (E' k - mean E') ^ 2)
    (hSS : ∑ k, (E k - mean E) ^ 2 ≤ ∑ k, (E' k - mean E') ^ 2)
    (hL2 : ∀ k, MemLp (ε k) 2 μ) (hindep : iIndepFun ε μ)
    (hhom : ∀ k, variance (ε k) μ = σ ^ 2) :
    variance (betaHat E' α β ε) μ ≤ variance (betaHat E α β ε) μ := by
  rw [olsSlope_variance_eq E α β σ ε hvar hL2 hindep hhom,
      olsSlope_variance_eq E' α β σ ε hvar' hL2 hindep hhom]
  gcongr

end CflibsFormal.Alt
