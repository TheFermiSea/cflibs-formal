/-
Copyright (c) 2026 Brian Squires. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Squires
-/
import Mathlib
import CflibsFormal.OLS
import CflibsFormal.Alt.OLSVariance
import CflibsFormal.ErrorBudget

/-!
# CF-LIBS formalization — Chebyshev tail (concentration) bounds for the OLS slope and intercept

`Alt.OLSVariance` proves the *second-moment* laws — `𝔼[β̂] = β`, `Var(β̂) = σ²/SS_E` — and
`ErrorBudget` proves the *deterministic worst-case* reliability budget (`temp_rel_error_eq`,
`relDensity_le`, …). Neither converts the variance of the recovered slope/intercept into a
**probability** that the estimate misses its target by more than a chosen tolerance `δ`. This
module supplies that missing link: it feeds the exact `OLSVariance` moment laws into `Mathlib`'s
Chebyshev inequality (`ProbabilityTheory.meas_ge_le_variance_div_sq`) to obtain **tail / deviation
bounds** — the probabilistic companion of the deterministic `ErrorBudget` chain.

Under the same linear model `yₖ(ω) = α + β·Eₖ + εₖ(ω)` as `Alt.OLSVariance` (zero-mean,
homoscedastic common variance `σ²`, pairwise-uncorrelated, square-integrable noise — the classical
Gauss–Markov hypotheses), with `wₖ = olsWeight E k = (Eₖ − Ē)/SS_E`, `Ē = mean E`,
`SS_E = ∑ₖ (Eₖ − Ē)²`, `n = Fintype.card ι`, we prove:

* `betaHat_memLp_two` — the `L²` membership of `β̂` that Chebyshev demands; `β̂ = β + ∑ₖ wₖ·εₖ`
  (`olsSlope_estimator_eq`) is a constant plus a finite sum of `L²` scalings of `L²` noise (the same
  bookkeeping performed inside `Alt.OLSVariance.variance_const_add_weightedNoise`).
* `olsSlope_chebyshev` — **the slope tail bound**
  `μ {ω | δ ≤ |β̂(ω) − β|} ≤ σ²/(SS_E·δ²)`. Chebyshev on `β̂` after `olsSlope_unbiased` centers the
  event at the truth and `olsSlope_variance_eq` supplies the variance.
* `alphaHat` / `alphaHat_estimator_eq` — the OLS **intercept** estimator as a random variable and
  its
  `α + ∑ₖ aₖ·εₖ` representation with `aₖ = 1/n − wₖ·Ē`. This is again the `c + ∑ₖ aₖ·εₖ` shape of
  the
  two `OLSVariance` kernels, so unbiasedness and variance come for free.
* `alphaHat_unbiased` — `𝔼[α̂] = α`.
* `alphaHat_variance_eq` — **the classical intercept variance** `Var(α̂) = σ²·(1/n + Ē²/SS_E)`, via
  `∑ₖ aₖ² = 1/n + Ē²/SS_E` (`∑ wₖ = 0`, `∑ wₖ² = 1/SS_E`). Collapses to `σ²/n` in the centered
  convention `Ē = 0` (`ErrorBudget.olsIntercept_stable_centered`).
* `alphaHat_memLp_two` / `alphaHat_chebyshev` — the intercept `L²` membership and **the intercept
  tail bound** `μ {ω | δ ≤ |α̂(ω) − α|} ≤ σ²(1/n + Ē²/SS_E)/δ²`.

## Honest scope

* **The moment identities are EXACT; the tail bounds are REDUCED.** `alphaHat_variance_eq` is a
  genuine identity (no slack), like `Alt.OLSVariance.olsSlope_variance_eq`. The Chebyshev tail
  bounds
  `olsSlope_chebyshev` / `alphaHat_chebyshev` carry irreducible slack (a Chebyshev tail is never
  attained), so they are `REDUCED` — matching `ErrorBudget.temp_rel_error_le`, NOT the exact
  identity
  `olsSlope_variance_eq` nor the attainable worst-case bound `relDensity_le`.
* **The classical Gauss–Markov hypothesis — pairwise uncorrelatedness, NOT independence.** Inherited
  verbatim from `Alt.OLSVariance`: the variance and tail results need only `cov(εᵢ,εⱼ) = 0` for
  `i ≠ j` (with homoscedasticity and zero mean), strictly weaker than the mutual independence
  `iIndepFun`. Zero-mean noise (`hmean0`) is load-bearing for the *tail* bounds: it is what makes
  `β`
  (resp. `α`) the mean, so that the event centred at the truth `{ω | δ ≤ |X ω − truth|}` is the
  centred Chebyshev event `{ω | δ ≤ |X ω − 𝔼X|}`.
* **`[IsProbabilityMeasure μ]` supplies Chebyshev's `[IsFiniteMeasure μ]`.** No new probability
  framework — the same `MeasureSpace Ω` / `IsProbabilityMeasure μ` / `MemLp` + `covariance` setting
  as `Alt.OLSVariance`; the tail bounds are `ENNReal.ofReal`-valued because
  `meas_ge_le_variance_div_sq`
  returns an `ℝ≥0∞` measure bound.
* **Physics is in prose only.** For the Boltzmann plot `β = −1/(k_B T)`, so `olsSlope_chebyshev` is
  a
  probability that the recovered *inverse temperature* misses by more than `δ`; `alphaHat_chebyshev`
  is the probability that the intercept (which carries the species concentration via
  `N = exp(b)·U/Fcal`, `ErrorBudget.relDensity_le`) misses by more than `δ`. No physical constant
  enters any Lean statement.

## Literature

The slope and intercept variances `σ²/Sₓₓ` and `σ²·(1/n + x̄²/Sₓₓ)` under zero-mean, homoscedastic,
uncorrelated errors are the Gauss–Markov laws; their modern (generalized least squares) form is
A. C. Aitken, "On Least Squares and Linear Combination of Observations," *Proceedings of the Royal
Society of Edinburgh* **55** (1935) 42–48, and the closed forms are standard, e.g. N. R. Draper and
H. Smith, *Applied Regression Analysis*, 3rd ed., Wiley-Interscience (1998), Ch. 1–2. The tail
bounds
are Chebyshev's inequality (`Mathlib`'s `ProbabilityTheory.meas_ge_le_variance_div_sq`) applied to
those variances. In the CF-LIBS setting the multi-line least-squares Boltzmann-plot fit is reviewed
in Tognoni, E.; Cristoforetti, G.; Legnaioli, S.; Palleschi, V. "Calibration-Free Laser-Induced
Breakdown Spectroscopy: State of the art." *Spectrochimica Acta Part B* **65** (2010) 1–14; the
intercept-borne concentration is Ciucci, A.; Corsi, M.; Palleschi, V.; Rastelli, S.; Salvetti, A.;
Tognoni, E. *Applied Spectroscopy* **53** (1999) 960–964. This module is the probabilistic tail
companion of the deterministic worst-case budget in `CflibsFormal.ErrorBudget`, feeding the exact
`Var` layer of `CflibsFormal.Alt.OLSVariance` into Chebyshev's inequality.
-/

namespace CflibsFormal.Alt

open CflibsFormal
open MeasureTheory ProbabilityTheory
open Finset Real
open scoped BigOperators ProbabilityTheory

variable {ι : Type*} [Fintype ι]
variable {Ω : Type*}

/-- **The OLS-intercept estimator as a random variable.** For the linear model
`yₖ(ω) = α + β·Eₖ + εₖ(ω)`, `alphaHat E α β ε ω` is the ordinary-least-squares intercept of the
realized Boltzmann-plot points `(Eₖ, yₖ(ω))`. Unlike the slope, the intercept does depend on `α`
(and on `Ē` through `olsIntercept = mean y − olsSlope·Ē`); see `alphaHat_estimator_eq`. The
intercept-borne species concentration is `N = exp(α̂)·U/Fcal` (`ErrorBudget.relDensity_le`). -/
noncomputable def alphaHat (E : ι → ℝ) (α β : ℝ) (ε : ι → Ω → ℝ) (ω : Ω) : ℝ :=
  olsIntercept E (fun k => α + β * E k + ε k ω)

/-- **Intercept estimator = truth + weighted noise (pure pointwise algebra, no probability).** For
every `ω`, `α̂(ω) = α + ∑ₖ aₖ·εₖ(ω)` with `aₖ = 1/n − wₖ·Ē`, `wₖ = olsWeight E k`, `Ē = mean E`,
`n = Fintype.card ι`. Derivation: `olsIntercept = mean y − olsSlope·Ē`; `mean y = α + β·Ē + mean
ε_ω`
(mean of the affine part plus the noise mean) and `olsSlope = β + ∑ₖ wₖ·εₖ`
(`Alt.OLSVariance.olsSlope_estimator_eq`), so the `β·Ē` terms cancel and
`α̂ = α + mean ε_ω − Ē·∑ₖ wₖ·εₖ = α + ∑ₖ (1/n − wₖ·Ē)·εₖ`. This is exactly the `c + ∑ₖ aₖ·εₖ` shape
of the two `OLSVariance` kernels, so expectation/variance follow with no new probability. -/
theorem alphaHat_estimator_eq [Nonempty ι] (E : ι → ℝ) (α β : ℝ) (ε : ι → Ω → ℝ)
    (hvar : 0 < ∑ k, (E k - mean E) ^ 2) (ω : Ω) :
    alphaHat E α β ε ω
      = α + ∑ k, (1 / (Fintype.card ι : ℝ) - olsWeight E k * mean E) * ε k ω := by
  have hcard : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hslope : olsSlope E (fun k => α + β * E k + ε k ω) = β + ∑ k, olsWeight E k * ε k ω :=
    olsSlope_estimator_eq E α β ε hvar ω
  have hmeany : mean (fun k => α + β * E k + ε k ω)
      = α + β * mean E + (∑ k, ε k ω) / (Fintype.card ι : ℝ) := by
    unfold mean
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, ← Finset.mul_sum]
    field_simp
  have hRHS : ∑ k, (1 / (Fintype.card ι : ℝ) - olsWeight E k * mean E) * ε k ω
      = (∑ k, ε k ω) / (Fintype.card ι : ℝ) - mean E * ∑ k, olsWeight E k * ε k ω := by
    rw [Finset.sum_div, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  unfold alphaHat olsIntercept
  rw [hslope, hmeany, hRHS]
  ring

variable [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **`L²` membership of the OLS slope estimator** `MemLp β̂ 2 μ`, the square-integrability that
Chebyshev's inequality (`meas_ge_le_variance_div_sq`) requires. By `olsSlope_estimator_eq`,
`β̂ = fun ω ↦ β + ∑ₖ wₖ·εₖ(ω)` is a constant plus a finite `Finset` sum of constant-scalings of the
`L²` noise `εₖ`, so it lands in `L²` by `memLp_const`, `memLp_finsetSum`, and `MemLp.const_mul` —
the same computation already inside `Alt.OLSVariance.variance_const_add_weightedNoise`. -/
lemma betaHat_memLp_two [Nonempty ι] (E : ι → ℝ) (α β : ℝ) (ε : ι → Ω → ℝ)
    (hvar : 0 < ∑ k, (E k - mean E) ^ 2) (hL2 : ∀ k, MemLp (ε k) 2 μ) :
    MemLp (betaHat E α β ε) 2 μ := by
  rw [funext (olsSlope_estimator_eq E α β ε hvar)]
  exact (memLp_const β).add
    (memLp_finsetSum Finset.univ (fun k _ => (hL2 k).const_mul (olsWeight E k)))

/-- **Slope concentration — Chebyshev's inequality on `β̂`.** The probability that the recovered
slope misses the truth by at least `δ` is controlled by the variance:
`μ {ω | δ ≤ |β̂(ω) − β|} ≤ σ²/(SS_E·δ²)` (as an `ENNReal.ofReal`, `SS_E = ∑ₖ (Eₖ − Ē)²`). Apply
`meas_ge_le_variance_div_sq` to `β̂` (with `betaHat_memLp_two`); `olsSlope_unbiased` (`𝔼[β̂] = β`,
using zero-mean noise `hmean0`) rewrites the centred event to `{δ ≤ |β̂ − β|}`, and
`olsSlope_variance_eq` (`Var(β̂) = σ²/SS_E`) rewrites the bound. **REDUCED**: a Chebyshev tail is a
slackened, non-attained bound — like `ErrorBudget.temp_rel_error_le`, not the exact identity
`olsSlope_variance_eq`. Physics: with `β = −1/(k_B T)` this is a probability that the recovered
inverse temperature misses by more than `δ`. -/
theorem olsSlope_chebyshev [Nonempty ι] (E : ι → ℝ) (α β σ δ : ℝ) (ε : ι → Ω → ℝ)
    (hvar : 0 < ∑ k, (E k - mean E) ^ 2) (hδ : 0 < δ)
    (hL2 : ∀ k, MemLp (ε k) 2 μ) (hmean0 : ∀ k, μ[ε k] = 0)
    (huncorr : ∀ i j, i ≠ j → covariance (ε i) (ε j) μ = 0)
    (hhom : ∀ k, variance (ε k) μ = σ ^ 2) :
    μ {ω | δ ≤ |betaHat E α β ε ω - β|}
      ≤ ENNReal.ofReal (σ ^ 2 / ((∑ k, (E k - mean E) ^ 2) * δ ^ 2)) := by
  have hexp : μ[betaHat E α β ε] = β := olsSlope_unbiased E α β ε hvar hL2 hmean0
  have hvareq : variance (betaHat E α β ε) μ = σ ^ 2 / (∑ k, (E k - mean E) ^ 2) :=
    olsSlope_variance_eq E α β σ ε hvar hL2 huncorr hhom
  have hcheb := meas_ge_le_variance_div_sq (betaHat_memLp_two E α β ε hvar hL2) hδ
  rw [hexp, hvareq] at hcheb
  refine hcheb.trans (le_of_eq ?_)
  congr 1
  rw [div_div]

/-- **Intercept unbiasedness** `𝔼[α̂] = α`. Linearity of expectation over the finite weighted-noise
sum `α + ∑ₖ (1/n − wₖ·Ē)·εₖ` (`alphaHat_estimator_eq`) plus zero-mean noise: the shared kernel
`Alt.OLSVariance.expectation_const_add_weightedNoise` at weights `aₖ = 1/n − wₖ·Ē` and constant `α`.
Needs neither independence nor homoscedasticity. -/
theorem alphaHat_unbiased [Nonempty ι] (E : ι → ℝ) (α β : ℝ) (ε : ι → Ω → ℝ)
    (hvar : 0 < ∑ k, (E k - mean E) ^ 2)
    (hL2 : ∀ k, MemLp (ε k) 2 μ) (hmean0 : ∀ k, μ[ε k] = 0) :
    μ[alphaHat E α β ε] = α := by
  simp_rw [alphaHat_estimator_eq E α β ε hvar]
  exact expectation_const_add_weightedNoise
    (fun k => 1 / (Fintype.card ι : ℝ) - olsWeight E k * mean E) α ε hL2 hmean0

/-- **THE classical intercept-variance law** `Var(α̂) = σ²·(1/n + Ē²/SS_E)`, with `n = Fintype.card
ι`,
`Ē = mean E`, `SS_E = ∑ₖ (Eₖ − Ē)²`. The `w = a` instance of
`Alt.OLSVariance.variance_const_add_weightedNoise` at weights `aₖ = 1/n − wₖ·Ē` gives
`Var(α̂) = σ²·∑ₖ aₖ²`; the closed form `∑ₖ aₖ² = 1/n + Ē²/SS_E` follows from `∑ₖ wₖ = 0`
(`OLS.centered_sum_zero`, scaled) and `∑ₖ wₖ² = 1/SS_E` (`OLS.olsSlope_noise_gain`) after expanding
`aₖ² = 1/n² − (2Ē/n)·wₖ + Ē²·wₖ²`. **EXACT**, not a slackened bound (a genuine identity, like
`olsSlope_variance_eq`). Collapses to the centered-convention value `σ²/n` when `Ē = 0` (the
standard
Boltzmann-plot normalization of `ErrorBudget.olsIntercept_stable_centered`). -/
theorem alphaHat_variance_eq [Nonempty ι] (E : ι → ℝ) (α β σ : ℝ) (ε : ι → Ω → ℝ)
    (hvar : 0 < ∑ k, (E k - mean E) ^ 2)
    (hL2 : ∀ k, MemLp (ε k) 2 μ)
    (huncorr : ∀ i j, i ≠ j → covariance (ε i) (ε j) μ = 0)
    (hhom : ∀ k, variance (ε k) μ = σ ^ 2) :
    variance (alphaHat E α β ε) μ
      = σ ^ 2 * (1 / (Fintype.card ι : ℝ) + (mean E) ^ 2 / (∑ k, (E k - mean E) ^ 2)) := by
  have hcard : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hS : (∑ k, (E k - mean E) ^ 2) ≠ 0 := hvar.ne'
  have hw0 : ∑ k, olsWeight E k = 0 := by
    simp only [olsWeight]
    rw [← Finset.sum_div, centered_sum_zero E, zero_div]
  have hw2 : ∑ k, (olsWeight E k) ^ 2 = 1 / (∑ k, (E k - mean E) ^ 2) := by
    simp only [olsWeight]; exact olsSlope_noise_gain E hvar
  have hsumsq : ∑ k, (1 / (Fintype.card ι : ℝ) - olsWeight E k * mean E) ^ 2
      = 1 / (Fintype.card ι : ℝ) + (mean E) ^ 2 / (∑ k, (E k - mean E) ^ 2) := by
    have key : ∑ k, (1 / (Fintype.card ι : ℝ) - olsWeight E k * mean E) ^ 2
        = ∑ k, ((1 / (Fintype.card ι : ℝ)) ^ 2
            - (2 * mean E / (Fintype.card ι : ℝ)) * olsWeight E k
            + (mean E) ^ 2 * (olsWeight E k) ^ 2) :=
      Finset.sum_congr rfl (fun k _ => by ring)
    rw [key, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      ← Finset.mul_sum, ← Finset.mul_sum, hw0, hw2, nsmul_eq_mul, mul_zero, sub_zero]
    field_simp
  rw [funext (alphaHat_estimator_eq E α β ε hvar),
    variance_const_add_weightedNoise
      (fun k => 1 / (Fintype.card ι : ℝ) - olsWeight E k * mean E) α σ ε hL2 huncorr hhom,
    hsumsq]

/-- **`L²` membership of the OLS intercept estimator** `MemLp α̂ 2 μ`, the intercept twin of
`betaHat_memLp_two`. By `alphaHat_estimator_eq`, `α̂ = fun ω ↦ α + ∑ₖ aₖ·εₖ(ω)` with
`aₖ = 1/n − wₖ·Ē` is a constant plus a finite sum of `L²` scalings of the `L²` noise. -/
lemma alphaHat_memLp_two [Nonempty ι] (E : ι → ℝ) (α β : ℝ) (ε : ι → Ω → ℝ)
    (hvar : 0 < ∑ k, (E k - mean E) ^ 2) (hL2 : ∀ k, MemLp (ε k) 2 μ) :
    MemLp (alphaHat E α β ε) 2 μ := by
  rw [funext (alphaHat_estimator_eq E α β ε hvar)]
  exact (memLp_const α).add
    (memLp_finsetSum Finset.univ (fun k _ =>
      (hL2 k).const_mul (1 / (Fintype.card ι : ℝ) - olsWeight E k * mean E)))

/-- **Intercept concentration — Chebyshev's inequality on `α̂`.** The intercept twin of
`olsSlope_chebyshev`: `μ {ω | δ ≤ |α̂(ω) − α|} ≤ σ²·(1/n + Ē²/SS_E)/δ²` (as an `ENNReal.ofReal`).
Apply `meas_ge_le_variance_div_sq` to `α̂` (with `alphaHat_memLp_two`); `alphaHat_unbiased`
(`𝔼[α̂] = α`, using zero-mean noise `hmean0`) centres the event and `alphaHat_variance_eq`
(`Var(α̂) = σ²(1/n + Ē²/SS_E)`) supplies the bound. **REDUCED**: a slackened, non-attained Chebyshev
tail, like `olsSlope_chebyshev`. The intercept carries the species concentration
(`ErrorBudget.relDensity_le`), so this is the probability that the log-concentration misses by more
than `δ`. -/
theorem alphaHat_chebyshev [Nonempty ι] (E : ι → ℝ) (α β σ δ : ℝ) (ε : ι → Ω → ℝ)
    (hvar : 0 < ∑ k, (E k - mean E) ^ 2) (hδ : 0 < δ)
    (hL2 : ∀ k, MemLp (ε k) 2 μ) (hmean0 : ∀ k, μ[ε k] = 0)
    (huncorr : ∀ i j, i ≠ j → covariance (ε i) (ε j) μ = 0)
    (hhom : ∀ k, variance (ε k) μ = σ ^ 2) :
    μ {ω | δ ≤ |alphaHat E α β ε ω - α|}
      ≤ ENNReal.ofReal
          (σ ^ 2 * (1 / (Fintype.card ι : ℝ) + (mean E) ^ 2 / (∑ k, (E k - mean E) ^ 2))
            / δ ^ 2) := by
  have hexp : μ[alphaHat E α β ε] = α := alphaHat_unbiased E α β ε hvar hL2 hmean0
  have hvareq := alphaHat_variance_eq E α β σ ε hvar hL2 huncorr hhom
  have hcheb := meas_ge_le_variance_div_sq (alphaHat_memLp_two E α β ε hvar hL2) hδ
  rw [hexp, hvareq] at hcheb
  exact hcheb

/-! ### Non-vacuity witnesses

The probabilistic hypotheses of the tail bounds are jointly satisfiable on a genuine
`IsProbabilityMeasure` (`Measure.dirac` on `Unit` with the zero-noise, `σ = 0` law, the tractable
deterministic instantiation — full mutual independence with `σ > 0` is a heavier construction, so
the *magnitude* of the bound is witnessed separately, in pure algebra, below), and the derived
formulae are non-degenerate on concrete Boltzmann-plot data with a nonzero mean energy. -/

/-- **Non-vacuity — the slope tail bound fires on a real probability measure.** All six hypotheses
of
`olsSlope_chebyshev` are jointly satisfiable: three lines at `E = (0,1,2)` (`SS_E = 2 > 0`) with the
zero-noise law (`σ = 0`) on `Measure.dirac` over `Unit`. (With `σ = 0` the bound is the tight
`0 ≤ 0`; the non-trivial *magnitude* of the bound is witnessed by the last `example` below.) -/
example :
    (Measure.dirac (α := Unit) Unit.unit)
        {ω | (1 : ℝ) ≤ |betaHat ![0, 1, 2] 0 0 (fun _ => 0) ω - 0|}
      ≤ ENNReal.ofReal
          ((0 : ℝ) ^ 2 / ((∑ k, (![0, 1, 2] k - mean ![0, 1, 2]) ^ 2) * (1 : ℝ) ^ 2)) := by
  refine olsSlope_chebyshev ![0, 1, 2] 0 0 0 1 (fun _ => 0) ?_ ?_ ?_ ?_ ?_ ?_
  · simp [mean, Fin.sum_univ_three]; norm_num
  · norm_num
  · intro k; exact MemLp.zero
  · intro k; simp
  · intro i j _; simp
  · intro k; rw [variance_zero]; norm_num

/-- **Non-vacuity — the intercept tail bound fires on a real probability measure.** The intercept
twin of the slope witness: all six hypotheses of `alphaHat_chebyshev` are jointly satisfiable on
`Measure.dirac` over `Unit` with `E = (0,1,2)` and the zero-noise (`σ = 0`) law. -/
example :
    (Measure.dirac (α := Unit) Unit.unit)
        {ω | (1 : ℝ) ≤ |alphaHat ![0, 1, 2] 0 0 (fun _ => 0) ω - 0|}
      ≤ ENNReal.ofReal
          ((0 : ℝ) ^ 2
            * (1 / (Fintype.card (Fin 3) : ℝ)
                + (mean ![0, 1, 2]) ^ 2 / (∑ k, (![0, 1, 2] k - mean ![0, 1, 2]) ^ 2))
            / (1 : ℝ) ^ 2) := by
  refine alphaHat_chebyshev ![0, 1, 2] 0 0 0 1 (fun _ => 0) ?_ ?_ ?_ ?_ ?_ ?_
  · simp [mean, Fin.sum_univ_three]; norm_num
  · norm_num
  · intro k; exact MemLp.zero
  · intro k; simp
  · intro i j _; simp
  · intro k; rw [variance_zero]; norm_num

/-- **Non-vacuity — the intercept variance is a genuine, non-degenerate identity.** On three lines
at
`E = (0,1,2)` the mean energy `Ē = 1 ≠ 0`, so `alphaHat_variance_eq`'s coefficient
`∑ₖ (1/n − wₖ·Ē)² = 1/n + Ē²/SS_E` is a real identity (both sides `= 5/6` here) whose non-centered
term `Ē²/SS_E > 0` is genuinely present: the intercept variance `σ²·(1/n + Ē²/SS_E)` STRICTLY
exceeds
the centered value `σ²/n`. So the law is neither vacuous nor the trivial `σ²/n`. -/
example :
    (0 < ∑ k, (![0, 1, 2] k - mean ![0, 1, 2]) ^ 2)
    ∧ ∑ k, ((1 : ℝ) / (Fintype.card (Fin 3) : ℝ) - olsWeight ![0, 1, 2] k * mean ![0, 1, 2]) ^ 2
        = 1 / (Fintype.card (Fin 3) : ℝ)
          + (mean ![0, 1, 2]) ^ 2 / (∑ k, (![0, 1, 2] k - mean ![0, 1, 2]) ^ 2)
    ∧ (1 : ℝ) / (Fintype.card (Fin 3) : ℝ)
        < 1 / (Fintype.card (Fin 3) : ℝ)
          + (mean ![0, 1, 2]) ^ 2 / (∑ k, (![0, 1, 2] k - mean ![0, 1, 2]) ^ 2) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [olsWeight, mean, Fin.sum_univ_three] <;> norm_num

/-- **Non-vacuity — the slope tail bound is a genuine probability bound.** At `σ = δ = 1` and
`E = (0,1,2)` the `olsSlope_chebyshev` bound argument `σ²/(SS_E·δ²) = 1/2` lies strictly in `(0,1)`:
when the theorem fires with real noise it yields a meaningful (non-trivial, `< 1`) tail probability,
not a vacuous `≤ ∞` or `≤ 0`. -/
example :
    0 < (1 : ℝ) ^ 2 / ((∑ k, (![0, 1, 2] k - mean ![0, 1, 2]) ^ 2) * (1 : ℝ) ^ 2)
    ∧ (1 : ℝ) ^ 2 / ((∑ k, (![0, 1, 2] k - mean ![0, 1, 2]) ^ 2) * (1 : ℝ) ^ 2) < 1 := by
  constructor <;> (simp [mean, Fin.sum_univ_three]; norm_num)

/-! ## Temperature tail transfer — the crown (`temp_tail_transfer`) -/

/-- **Slope→temperature reader** `T = 1/(k_B·x)`: the (sign-normalized) Boltzmann-plot
inverse-temperature map, the deterministic bridge the tail transfer routes through. -/
noncomputable def tempOfSlope (kB x : ℝ) : ℝ := 1 / (kB * x)

/-- **The recovered-temperature estimator as a random variable**: the temperature read off the
random OLS slope, `T̂ ω = tempOfSlope kB (β̂ ω)`. The stochastic twin of the deterministic
temperature reader; `temp_tail_transfer` bounds its tail around the true `T` on the
sign-normalized branch `β = 1/(k_B·T)`. -/
noncomputable def tempHat (kB : ℝ) (E : ι → ℝ) (α β : ℝ) (ε : ι → Ω → ℝ) (ω : Ω) : ℝ :=
  tempOfSlope kB (betaHat E α β ε ω)

theorem temp_slope_event_subset {kB T epsT x : ℝ}
    (hkB : 0 < kB) (hT : 0 < T) (hepsT : 0 < epsT)
    (hx : epsT ≤ |1 / (kB * x) - T|) :
    epsT / (kB * T * (T + epsT)) ≤ |x - 1 / (kB * T)| := by
  by_contra hlt
  rw [not_le, abs_lt] at hlt
  obtain ⟨hlo, hhi⟩ := hlt
  have hTe : 0 < T + epsT := by linarith
  have hkBne : kB ≠ 0 := hkB.ne'
  have hTne : T ≠ 0 := hT.ne'
  have hid_lo : 1 / (kB * T) - epsT / (kB * T * (T + epsT)) = 1 / (kB * (T + epsT)) := by
    field_simp
    ring
  have hid_hi : 1 / (kB * T) + epsT / (kB * T * (T + epsT))
      = (T + 2 * epsT) / (kB * T * (T + epsT)) := by
    field_simp
    ring
  have hxlb : 1 / (kB * (T + epsT)) < x := by linarith [hlo, hid_lo]
  have hxub : x < (T + 2 * epsT) / (kB * T * (T + epsT)) := by linarith [hhi, hid_hi]
  have hxpos : 0 < x := lt_trans (by positivity) hxlb
  have hkBx : 0 < kB * x := by positivity
  have hy : (1 / (kB * x)) * (kB * x) = 1 := one_div_mul_cancel hkBx.ne'
  have h1 : 1 < kB * x * (T + epsT) := by
    have h := (div_lt_iff₀ (show (0:ℝ) < kB * (T + epsT) by positivity)).mp hxlb
    nlinarith [h]
  have h2 : kB * x * (T - epsT) < 1 := by
    rcases le_or_gt T epsT with hle | hgt
    · have : kB * x * (T - epsT) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hkBx.le (by linarith)
      linarith
    · have hpc : (0:ℝ) < kB * T * (T + epsT) := by positivity
      have hc := (lt_div_iff₀ hpc).mp hxub
      nlinarith [hc, mul_pos hT hTe, show (0:ℝ) < T - epsT by linarith]
  have hfinal : |1 / (kB * x) - T| < epsT := by
    rw [abs_lt]
    refine ⟨?_, ?_⟩
    · nlinarith [hy, h2, hkBx]
    · nlinarith [hy, h1, hkBx]
  exact absurd hx (not_le.mpr hfinal)

theorem temp_tail_transfer [Nonempty ι] (E : ι → ℝ) (α β σ : ℝ) (ε : ι → Ω → ℝ)
    {kB T epsT : ℝ}
    (hvar : 0 < ∑ k, (E k - mean E) ^ 2) (hkB : 0 < kB) (hT : 0 < T) (hepsT : 0 < epsT)
    (hβ : β = 1 / (kB * T))
    (hL2 : ∀ k, MemLp (ε k) 2 μ) (hmean0 : ∀ k, μ[ε k] = 0)
    (huncorr : ∀ i j, i ≠ j → covariance (ε i) (ε j) μ = 0)
    (hhom : ∀ k, variance (ε k) μ = σ ^ 2) :
    μ {ω | epsT ≤ |tempHat kB E α β ε ω - T|}
      ≤ ENNReal.ofReal
          (σ ^ 2 * kB ^ 2 * T ^ 2 * (T + epsT) ^ 2
            / ((∑ k, (E k - mean E) ^ 2) * epsT ^ 2)) := by
  subst hβ
  have hkBne : kB ≠ 0 := hkB.ne'
  have hTne : T ≠ 0 := hT.ne'
  have hepsTne : epsT ≠ 0 := hepsT.ne'
  have hSne : (∑ k, (E k - mean E) ^ 2) ≠ 0 := hvar.ne'
  have hTene : T + epsT ≠ 0 := by positivity
  set δ := epsT / (kB * T * (T + epsT)) with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; positivity
  have hsub : {ω | epsT ≤ |tempHat kB E α (1 / (kB * T)) ε ω - T|}
      ⊆ {ω | δ ≤ |betaHat E α (1 / (kB * T)) ε ω - 1 / (kB * T)|} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    rw [hδdef]
    exact temp_slope_event_subset hkB hT hepsT
      (by simpa only [tempHat, tempOfSlope] using hω)
  refine (measure_mono hsub).trans ?_
  have hcheb := olsSlope_chebyshev E α (1 / (kB * T)) σ δ ε hvar hδpos hL2 hmean0 huncorr hhom
  refine hcheb.trans (le_of_eq ?_)
  congr 1
  rw [hδdef]
  field_simp

/-! ### Non-vacuity witnesses (temperature tail) -/

example : (1 : ℝ) / (1 * 1 * (1 + 1)) ≤ |(1 / 2 : ℝ) - 1 / (1 * 1)| :=
  temp_slope_event_subset (by norm_num) (by norm_num) (by norm_num) (by norm_num)

example :
    (Measure.dirac (α := Unit) Unit.unit)
        {ω | (1 : ℝ) ≤ |tempHat 1 ![0, 1, 2] 0 (1 / (1 * 1)) (fun _ => 0) ω - 1|}
      ≤ ENNReal.ofReal
          ((0 : ℝ) ^ 2 * (1 : ℝ) ^ 2 * (1 : ℝ) ^ 2 * ((1 : ℝ) + 1) ^ 2
            / ((∑ k, (![0, 1, 2] k - mean ![0, 1, 2]) ^ 2) * (1 : ℝ) ^ 2)) := by
  refine temp_tail_transfer ![0, 1, 2] 0 (1 / (1 * 1)) 0 (fun _ => 0) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simp [mean, Fin.sum_univ_three]; norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · intro k; exact MemLp.zero
  · intro k; simp
  · intro i j _; simp
  · intro k; rw [variance_zero]; norm_num

example :
    0 < (1 : ℝ) ^ 2 * (1 : ℝ) ^ 2 * (1 : ℝ) ^ 2 * ((1 : ℝ) + 10) ^ 2
          / ((∑ k, (![0, 1, 2] k - mean ![0, 1, 2]) ^ 2) * (10 : ℝ) ^ 2)
    ∧ (1 : ℝ) ^ 2 * (1 : ℝ) ^ 2 * (1 : ℝ) ^ 2 * ((1 : ℝ) + 10) ^ 2
          / ((∑ k, (![0, 1, 2] k - mean ![0, 1, 2]) ^ 2) * (10 : ℝ) ^ 2) < 1 := by
  constructor <;> (simp [mean, Fin.sum_univ_three]; norm_num)

/-! ## Composition tail — per-species density bound and the union over species -/

theorem density_event_subset {b bHat U Fcal τ : ℝ}
    (hU : 0 < U) (hFcal : 0 < Fcal) (hτ : 0 < τ)
    (h : τ ≤ |Real.exp bHat * U / Fcal - Real.exp b * U / Fcal|) :
    Real.log (1 + τ / (Real.exp b * U / Fcal)) ≤ |bHat - b| := by
  have hrel := relDensity_le hU.le hFcal (le_refl (|bHat - b|))
  set N := Real.exp b * U / Fcal with hN
  have hNpos : 0 < N := by rw [hN]; positivity
  by_contra hlt
  rw [not_le] at hlt
  have h1τN : 0 < 1 + τ / N := by have := div_pos hτ hNpos; linarith
  have hexp : Real.exp (|bHat - b|) < 1 + τ / N := by
    calc Real.exp (|bHat - b|) < Real.exp (Real.log (1 + τ / N)) := Real.exp_lt_exp.mpr hlt
      _ = 1 + τ / N := Real.exp_log h1τN
  have hbound : N * (Real.exp (|bHat - b|) - 1) < τ := by
    have hstep : N * (Real.exp (|bHat - b|) - 1) < N * (τ / N) :=
      mul_lt_mul_of_pos_left (by linarith [hexp]) hNpos
    have hNτ : N * (τ / N) = τ := by field_simp
    rwa [hNτ] at hstep
  linarith [h, hrel, hbound]

/-- **The recovered-density estimator as a random variable**: the CF-LIBS density read off the
random OLS intercept, `N̂ ω = exp(α̂ ω)·U/Fcal` (the intercept identity `b = log(Fcal·N/U)`
inverted at the realized intercept `alphaHat`). The stochastic twin of the deterministic
density reader; `density_tail_species` bounds its tail around the true `N = exp(α)·U/Fcal`. -/
noncomputable def densityHat (E : ι → ℝ) (α β U Fcal : ℝ) (ε : ι → Ω → ℝ) (ω : Ω) : ℝ :=
  Real.exp (alphaHat E α β ε ω) * U / Fcal

theorem density_tail_species [Nonempty ι] (E : ι → ℝ) (α β σ U Fcal τ : ℝ) (ε : ι → Ω → ℝ)
    (hvar : 0 < ∑ k, (E k - mean E) ^ 2) (hU : 0 < U) (hFcal : 0 < Fcal) (hτ : 0 < τ)
    (hL2 : ∀ k, MemLp (ε k) 2 μ) (hmean0 : ∀ k, μ[ε k] = 0)
    (huncorr : ∀ i j, i ≠ j → covariance (ε i) (ε j) μ = 0)
    (hhom : ∀ k, variance (ε k) μ = σ ^ 2) :
    μ {ω | τ ≤ |densityHat E α β U Fcal ε ω - Real.exp α * U / Fcal|}
      ≤ ENNReal.ofReal
          (σ ^ 2 * (1 / (Fintype.card ι : ℝ) + (mean E) ^ 2 / (∑ k, (E k - mean E) ^ 2))
            / (Real.log (1 + τ / (Real.exp α * U / Fcal))) ^ 2) := by
  have hNpos : 0 < Real.exp α * U / Fcal := by positivity
  have hδpos : 0 < Real.log (1 + τ / (Real.exp α * U / Fcal)) := by
    apply Real.log_pos
    have := div_pos hτ hNpos
    linarith
  have hsub : {ω | τ ≤ |densityHat E α β U Fcal ε ω - Real.exp α * U / Fcal|}
      ⊆ {ω | Real.log (1 + τ / (Real.exp α * U / Fcal)) ≤ |alphaHat E α β ε ω - α|} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    exact density_event_subset hU hFcal hτ (by simpa only [densityHat] using hω)
  refine (measure_mono hsub).trans ?_
  exact alphaHat_chebyshev E α β σ (Real.log (1 + τ / (Real.exp α * U / Fcal))) ε
    hvar hδpos hL2 hmean0 huncorr hhom

theorem composition_tail_union [Nonempty ι] {κ : Type*} [Fintype κ]
    (E : κ → ι → ℝ) (α β σ U Fcal : κ → ℝ) (τ : ℝ) (ε : κ → ι → Ω → ℝ)
    (hvar : ∀ s, 0 < ∑ k, (E s k - mean (E s)) ^ 2)
    (hU : ∀ s, 0 < U s) (hFcal : ∀ s, 0 < Fcal s) (hτ : 0 < τ)
    (hL2 : ∀ s k, MemLp (ε s k) 2 μ) (hmean0 : ∀ s k, μ[ε s k] = 0)
    (huncorr : ∀ s i j, i ≠ j → covariance (ε s i) (ε s j) μ = 0)
    (hhom : ∀ s k, variance (ε s k) μ = (σ s) ^ 2) :
    μ (⋃ s, {ω | τ ≤ |densityHat (E s) (α s) (β s) (U s) (Fcal s) (ε s) ω
                        - Real.exp (α s) * U s / Fcal s|})
      ≤ ∑ s, ENNReal.ofReal
          ((σ s) ^ 2 * (1 / (Fintype.card ι : ℝ)
              + (mean (E s)) ^ 2 / (∑ k, (E s k - mean (E s)) ^ 2))
            / (Real.log (1 + τ / (Real.exp (α s) * U s / Fcal s))) ^ 2) := by
  have hbi : (⋃ s, {ω | τ ≤ |densityHat (E s) (α s) (β s) (U s) (Fcal s) (ε s) ω
                        - Real.exp (α s) * U s / Fcal s|})
      = ⋃ s ∈ (Finset.univ : Finset κ),
          {ω | τ ≤ |densityHat (E s) (α s) (β s) (U s) (Fcal s) (ε s) ω
                    - Real.exp (α s) * U s / Fcal s|} := by
    simp
  rw [hbi]
  refine (measure_biUnion_finset_le Finset.univ _).trans ?_
  refine Finset.sum_le_sum (fun s _ => ?_)
  exact density_tail_species (E s) (α s) (β s) (σ s) (U s) (Fcal s) τ (ε s)
    (hvar s) (hU s) (hFcal s) hτ (hL2 s) (hmean0 s) (huncorr s) (hhom s)

/-! ### Non-vacuity witnesses (composition tail) -/

example : Real.log (1 + (1 : ℝ) / (Real.exp 0 * 1 / 1)) ≤ |Real.log 3 - 0| :=
  density_event_subset (by norm_num) (by norm_num) (by norm_num)
    (by rw [Real.exp_log (by norm_num), Real.exp_zero]; norm_num)

example :
    (Measure.dirac (α := Unit) Unit.unit)
        {ω | (1 : ℝ) ≤ |densityHat ![0, 1, 2] 0 0 1 1 (fun _ => 0) ω
                        - Real.exp 0 * 1 / 1|}
      ≤ ENNReal.ofReal
          ((0 : ℝ) ^ 2 * (1 / (Fintype.card (Fin 3) : ℝ)
              + (mean ![0, 1, 2]) ^ 2 / (∑ k, (![0, 1, 2] k - mean ![0, 1, 2]) ^ 2))
            / (Real.log (1 + (1 : ℝ) / (Real.exp 0 * 1 / 1))) ^ 2) := by
  refine density_tail_species ![0, 1, 2] 0 0 0 1 1 1 (fun _ => 0)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simp [mean, Fin.sum_univ_three]; norm_num
  · norm_num
  · norm_num
  · norm_num
  · intro k; exact MemLp.zero
  · intro k; simp
  · intro i j _; simp
  · intro k; rw [variance_zero]; norm_num

example :
    (Measure.dirac (α := Unit) Unit.unit)
        (⋃ _s : Fin 1, {ω | (1 : ℝ) ≤ |densityHat ![0, 1, 2] 0 0 1 1 (fun _ => 0) ω
                        - Real.exp 0 * 1 / 1|})
      ≤ ∑ _s : Fin 1, ENNReal.ofReal
          ((0 : ℝ) ^ 2 * (1 / (Fintype.card (Fin 3) : ℝ)
              + (mean (![0, 1, 2] : Fin 3 → ℝ)) ^ 2
                / (∑ k, ((![0, 1, 2] : Fin 3 → ℝ) k - mean (![0, 1, 2] : Fin 3 → ℝ)) ^ 2))
            / (Real.log (1 + (1 : ℝ) / (Real.exp 0 * 1 / 1))) ^ 2) := by
  refine composition_tail_union (fun _ => ![0, 1, 2]) (fun _ => 0) (fun _ => 0) (fun _ => 0)
    (fun _ => 1) (fun _ => 1) 1 (fun _ _ => 0) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro s; simp [mean, Fin.sum_univ_three]; norm_num
  · intro s; norm_num
  · intro s; norm_num
  · norm_num
  · intro s k; exact MemLp.zero
  · intro s k; simp
  · intro s i j _; simp
  · intro s k; rw [variance_zero]; norm_num

/-! ## Sub-Gaussian upgrade of the slope tail (`olsSlope_subGaussian_tail`) -/

omit [IsProbabilityMeasure μ] in
theorem olsSlope_subGaussian_tail [Nonempty ι] (E : ι → ℝ) (α β : ℝ) (ε : ι → Ω → ℝ)
    {c : NNReal} {δ : ℝ}
    (hvar : 0 < ∑ k, (E k - mean E) ^ 2) (hδ : 0 ≤ δ) (hc : 0 < c)
    (hindep : iIndepFun ε μ)
    (hsubG : ∀ k, HasSubgaussianMGF (ε k) c μ) :
    μ.real {ω | δ ≤ |betaHat E α β ε ω - β|}
      ≤ 2 * Real.exp (-(δ ^ 2 * (∑ k, (E k - mean E) ^ 2)) / (2 * (c : ℝ))) := by
  have hcpos : (0 : ℝ) < (c : ℝ) := hc
  have hcR : (c : ℝ) ≠ 0 := hcpos.ne'
  have hSSne : (∑ k, (E k - mean E) ^ 2) ≠ 0 := hvar.ne'
  have hindep' : iIndepFun (fun k => (fun x : ℝ => olsWeight E k * x) ∘ ε k) μ :=
    hindep.comp (fun k x => olsWeight E k * x) (fun k => measurable_id.const_mul (olsWeight E k))
  have hsum : HasSubgaussianMGF (fun ω => ∑ k, olsWeight E k * ε k ω)
      (∑ k, (⟨(olsWeight E k) ^ 2, sq_nonneg _⟩ * c : NNReal)) μ :=
    HasSubgaussianMGF.sum_of_iIndepFun hindep'
      (fun k _ => (hsubG k).const_mul (olsWeight E k))
  have hw2 : ∑ k, (olsWeight E k) ^ 2 = 1 / (∑ k, (E k - mean E) ^ 2) := by
    simp only [olsWeight]; exact olsSlope_noise_gain E hvar
  have hterm : ∀ k, ((⟨(olsWeight E k) ^ 2, sq_nonneg _⟩ * c : NNReal) : ℝ)
      = (olsWeight E k) ^ 2 * (c : ℝ) := fun k => by rw [NNReal.coe_mul]; rfl
  have hCcoe : ((∑ k, (⟨(olsWeight E k) ^ 2, sq_nonneg _⟩ * c : NNReal)) : ℝ)
      = (c : ℝ) / (∑ k, (E k - mean E) ^ 2) := by
    push_cast [hterm]; rw [← Finset.sum_mul, hw2]; ring
  have hexp_eq : -δ ^ 2 / (2 * (∑ k, ((⟨(olsWeight E k) ^ 2, sq_nonneg _⟩ * c : NNReal) : ℝ)))
      = -(δ ^ 2 * (∑ k, (E k - mean E) ^ 2)) / (2 * (c : ℝ)) := by
    rw [hCcoe]; field_simp
  have hpos := hsum.measure_ge_le hδ
  have hneg := hsum.neg.measure_ge_le hδ
  simp only [NNReal.coe_sum, Pi.neg_apply] at hpos hneg
  rw [hexp_eq] at hpos hneg
  have hset : {ω | δ ≤ |betaHat E α β ε ω - β|}
      = {ω | δ ≤ ∑ k, olsWeight E k * ε k ω}
          ∪ {ω | δ ≤ -(∑ k, olsWeight E k * ε k ω)} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_union]
    rw [olsSlope_estimator_eq E α β ε hvar,
      show β + (∑ k, olsWeight E k * ε k ω) - β = ∑ k, olsWeight E k * ε k ω from by ring]
    exact le_abs
  rw [hset]
  calc μ.real ({ω | δ ≤ ∑ k, olsWeight E k * ε k ω}
          ∪ {ω | δ ≤ -(∑ k, olsWeight E k * ε k ω)})
      ≤ μ.real {ω | δ ≤ ∑ k, olsWeight E k * ε k ω}
          + μ.real {ω | δ ≤ -(∑ k, olsWeight E k * ε k ω)} := measureReal_union_le _ _
    _ ≤ Real.exp (-(δ ^ 2 * (∑ k, (E k - mean E) ^ 2)) / (2 * (c : ℝ)))
          + Real.exp (-(δ ^ 2 * (∑ k, (E k - mean E) ^ 2)) / (2 * (c : ℝ))) :=
        add_le_add hpos hneg
    _ = 2 * Real.exp (-(δ ^ 2 * (∑ k, (E k - mean E) ^ 2)) / (2 * (c : ℝ))) := by ring

/-! ### Non-vacuity witness (sub-Gaussian tail) -/

example :
    0 < 2 * Real.exp (-((3 : ℝ) ^ 2 * (∑ k, (![0, 1, 2] k - mean ![0, 1, 2]) ^ 2)) / (2 * (1 : ℝ)))
    ∧ 2 * Real.exp (-((3 : ℝ) ^ 2 * (∑ k, (![0, 1, 2] k - mean ![0, 1, 2]) ^ 2)) / (2 * (1 : ℝ)))
        < 1 := by
  have hSS : (∑ k, (![0, 1, 2] k - mean ![0, 1, 2]) ^ 2) = 2 := by
    simp [mean, Fin.sum_univ_three]; norm_num
  rw [hSS]
  refine ⟨by positivity, ?_⟩
  have h : (10 : ℝ) ≤ Real.exp 9 := by have := Real.add_one_le_exp (9 : ℝ); linarith
  have hpos : (0 : ℝ) < Real.exp 9 := Real.exp_pos 9
  rw [show -((3 : ℝ) ^ 2 * 2) / (2 * 1) = -9 by norm_num, Real.exp_neg,
    mul_inv_lt_iff₀ hpos, one_mul]
  linarith

end CflibsFormal.Alt
