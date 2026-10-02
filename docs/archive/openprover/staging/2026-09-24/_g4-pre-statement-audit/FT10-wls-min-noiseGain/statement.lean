import Mathlib

/-!
# FT-10 (items 1-3): the weighted-least-squares slope attains the linear-unbiased noise floor

Staged queue target, 2026-09-24 audit, frontier FT-10. Deterministic Finset algebra (the
heteroscedastic Aitken core); the probabilistic variance statement is a separate target.
-/

open Finset

namespace Plan.FT10

variable {ι : Type*} [Fintype ι]

/-- **Weighted mean** `Ē_w = (∑_k w k * E k) / ∑_k w k` of the upper-level energies `E` with line
weights `w` (in the noise reading, `w k = 1/σ_k²`, the inverse variance of line `k`'s ordinate).
Totalized division: `0` when `∑ w = 0`, which positive weights on a non-empty line set exclude. -/
noncomputable def wMean (w E : ι → ℝ) : ℝ := (∑ k, w k * E k) / ∑ k, w k

/-- **Weighted centred sum of squares** `wSS = ∑_k w k * (E k − Ē_w)²`, the weighted energy
spread of the Boltzmann plot. With `w k = 1/σ_k²` it is the information about the slope
carried by the line set; for unit weights it is the usual `SS_E`. -/
noncomputable def wSS (w E : ι → ℝ) : ℝ := ∑ k, w k * (E k - wMean w E) ^ 2

/-- **Weighted-least-squares slope weight** `ω_k = w k * (E k − Ē_w) / wSS`: the WLS slope of the
Boltzmann plot is the linear estimator `β̂ = ∑_k ω_k * y k`. For unit weights this is the OLS
weight `(E k − Ē)/SS_E` (`CflibsFormal.olsWeight`). Totalized division: `0` when `wSS = 0`. -/
noncomputable def wlsWeight (w E : ι → ℝ) (k : ι) : ℝ := w k * (E k - wMean w E) / wSS w E

/-- **FT-10: WLS attains the minimum noise gain among linear unbiased slope estimators.**
Let `a : ι → ℝ` be the weights of any linear slope estimator `∑_k a k * y k` that is unbiased for
every straight line `y k = α + β * E k`, i.e. `∑_k a k = 0` and `∑_k a k * E k = 1`. Its noise
gain under per-line variances `σ_k² = 1/w k` is `∑_k a k² / w k`. The theorem says:
1. the WLS weights `wlsWeight w E` have noise gain exactly `1 / wSS w E`, and
2. every unbiased `a` has noise gain at least `1 / wSS w E`.
So `1 / wSS` is the floor, and WLS attains it. Under uncorrelated ordinate noise with
`Var ε_k = 1/w k` this is the deterministic core of "WLS is the best linear unbiased slope
estimator" (Aitken); the variance statement itself is a separate target.

This is a BLUE floor, not a Cramér–Rao bound: it compares linear unbiased estimators only, and
no Fisher information is involved.

Hypotheses.
* `hw : ∀ k, 0 < w k`: finite positive variances `1/w k`; the noise gain divides by `w k`, and
  both the equality and the inequality use `w k > 0`.
* `ha0 : ∑ a = 0`, `ha1 : ∑ a E = 1`: unbiasedness for every intercept and slope.
* `hSS : 0 < wSS w E`: the slope is identifiable. Given `hw`, `ha0` and `ha1` it is in fact
  implied (if `wSS = 0` then every `E k = Ē_w`, so `∑ a E = Ē_w * ∑ a = 0 ≠ 1`); it is kept to
  name the identifiability condition and to save the prover that derivation.

Scope, two-axis prediction: relation PURE-MATH; the definitions used are PURE-MATH regression
objects; published tag PURE-MATH. The physics reading (Boltzmann-plot ordinates with uncorrelated
additive noise of known variance `σ_k²`) is REDUCED and belongs in the landing docstring.
Atomic-data (`gA`) uncertainties are a bias, not noise, and should not enter `w`.

Literature: Aitken 1935 (Proc. Roy. Soc. Edinburgh 55, 42) for generalized least squares;
Tognoni et al. 2010 (Spectrochim. Acta B 65, 1) for the CF-LIBS uncertainty context. -/
theorem wls_min_noiseGain {w E a : ι → ℝ} (hw : ∀ k, 0 < w k) (hSS : 0 < wSS w E)
    (ha0 : ∑ k, a k = 0) (ha1 : ∑ k, a k * E k = 1) :
    ∑ k, wlsWeight w E k ^ 2 / w k = 1 / wSS w E ∧ 1 / wSS w E ≤ ∑ k, a k ^ 2 / w k := by
  sorry

end Plan.FT10
