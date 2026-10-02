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

/-- **Weighted-least-squares slope weight** `ω_k = w k * (E k − Ē_w) / wSS`. The linear estimator
`∑_k ω_k * y k` is the weighted-RSS-minimizing slope (the one-group case of FT-04 `feSlope` /
`feSlope_isMin`); that identification is not proved in this file. For unit weights this is the
OLS weight `(E k − Ē)/SS_E` (`CflibsFormal.olsWeight`). Totalized division: `0` when
`wSS = 0`. -/
noncomputable def wlsWeight (w E : ι → ℝ) (k : ι) : ℝ := w k * (E k - wMean w E) / wSS w E

/-- The WLS weights are linear-unbiased: `∑ ω = 0` and `∑ ω E = 1`. -/
theorem wlsWeight_unbiased {w E : ι → ℝ} (hw : ∀ k, 0 < w k) (hSS : 0 < wSS w E) :
    ∑ k, wlsWeight w E k = 0 ∧ ∑ k, wlsWeight w E k * E k = 1 := by
  have hSne : wSS w E ≠ 0 := hSS.ne'
  obtain ⟨k0, -, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero
    (show ∑ k, w k * (E k - wMean w E) ^ 2 ≠ 0 from hSne)
  have hW : 0 < ∑ k, w k := Finset.sum_pos (fun k _ => hw k) ⟨k0, Finset.mem_univ _⟩
  have hc : ∑ k, w k * (E k - wMean w E) = 0 := by
    have : ∑ k, w k * (E k - wMean w E) = ∑ k, w k * E k - wMean w E * ∑ k, w k := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun k _ => by ring)
    rw [this, wMean, div_mul_cancel₀ _ hW.ne', sub_self]
  constructor
  · simp only [wlsWeight]; rw [← Finset.sum_div, hc, zero_div]
  · have : ∑ k, wlsWeight w E k * E k
        = (∑ k, w k * (E k - wMean w E) ^ 2 + wMean w E * ∑ k, w k * (E k - wMean w E))
          / wSS w E := by
      simp only [wlsWeight]
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_div]
      exact Finset.sum_congr rfl (fun k _ => by ring)
    rw [this, hc, mul_zero, add_zero]
    exact div_self hSne

/-- **FT-10: WLS attains the minimum noise gain among linear unbiased slope estimators.**
Let `a : ι → ℝ` be the weights of any linear slope estimator `∑_k a k * y k` that is unbiased for
every straight line `y k = α + β * E k`, i.e. `∑_k a k = 0` and `∑_k a k * E k = 1`. Its noise
gain under per-line variances `σ_k² = 1/w k` is `∑_k a k² / w k`. The theorem says:
0. the WLS weights are themselves linear-unbiased (`∑ ω = 0`, `∑ ω E = 1`),
1. the WLS weights `wlsWeight w E` have noise gain exactly `1 / wSS w E`, and
2. every unbiased `a` has noise gain at least `1 / wSS w E`.
So `1 / wSS` is the floor, and WLS attains it. Under uncorrelated ordinate noise with
`Var ε_k = 1/w k` this is the deterministic core of "WLS is the best linear unbiased slope
estimator" (Aitken); the variance statement itself is a separate target.

This is a BLUE floor, not a Cramér–Rao bound: it compares linear unbiased estimators only, and
no Fisher information is involved.

Hypotheses.
* `hw : ∀ k, 0 < w k`: finite positive variances `1/w k`; the noise gain divides by `w k`, and
  both the equality and the inequality use `w k > 0`. Item 0 uses it for `∑ w > 0`, so that
  the weighted deviations `w k * (E k − Ē_w)` sum to zero.
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
    (∑ k, wlsWeight w E k = 0 ∧ ∑ k, wlsWeight w E k * E k = 1) ∧
      ∑ k, wlsWeight w E k ^ 2 / w k = 1 / wSS w E ∧ 1 / wSS w E ≤ ∑ k, a k ^ 2 / w k := by
  refine ⟨wlsWeight_unbiased hw hSS, ?_, ?_⟩
  · have hterm : ∀ k, wlsWeight w E k ^ 2 / w k
        = w k * (E k - wMean w E) ^ 2 / wSS w E ^ 2 := by
      intro k
      have hwk := (hw k).ne'
      unfold wlsWeight
      field_simp
    simp only [hterm]
    rw [← Finset.sum_div]
    change wSS w E / wSS w E ^ 2 = 1 / wSS w E
    field_simp
  · -- Σ a (E - Ē) = 1
    have hd : ∑ k, a k * (E k - wMean w E) = 1 := by
      have : ∑ k, a k * (E k - wMean w E) = ∑ k, a k * E k - (∑ k, a k) * wMean w E := by
        rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl (fun k _ => by ring)
      rw [this, ha1, ha0]; ring
    have hCS : (∑ k, a k * (E k - wMean w E)) ^ 2
        ≤ (∑ k, a k ^ 2 / w k) * ∑ k, w k * (E k - wMean w E) ^ 2 := by
      apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
      · intro k _; exact div_nonneg (sq_nonneg _) (hw k).le
      · intro k _; exact mul_nonneg (hw k).le (sq_nonneg _)
      · intro k _
        have hwk := (hw k).ne'
        apply le_of_eq
        field_simp
    rw [hd, one_pow] at hCS
    change 1 ≤ (∑ k, a k ^ 2 / w k) * wSS w E at hCS
    rw [div_le_iff₀ hSS]
    linarith

end Plan.FT10
