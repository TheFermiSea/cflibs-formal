/-
Copyright (c) 2026 Brian Squires. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Squires
-/
import Mathlib
import CflibsFormal.OLS
import CflibsFormal.FixedEffectsDesign

/-!
# CF-LIBS formalization — noise-gain floors for the Boltzmann slope and intercept difference

Deterministic Finset algebra behind the precision limits of a Boltzmann-plot fit (frontier FT-10
of the 2026-09-24 audit). A linear estimator `∑_k a k * y k` of a Boltzmann-plot parameter has,
under uncorrelated ordinate noise of variance `σ_k² = 1/w k`, the variance `∑_k a k² / w k`; that
sum is called its *noise gain* here. The variance statements themselves are not proved here.

## Main definitions

* `wMean`, `wSS`: the weighted mean and weighted centred sum of squares of the energies.
* `wlsWeight`: the weighted-least-squares slope weights `w k (E k − Ē_w) / wSS`.
* `pooledSS`, `commonSlope`, `interceptDiff`, `idWeightA`, `idWeightB`: the two-species
  common-slope fit, the difference of its two fitted intercepts, and that difference's weights.

## Main results

* `gMean_const_eq_wMean`: `wMean` is the one-group case of `FixedEffectsDesign.gMean`.
* `wls_min_noiseGain`: the WLS slope weights are linear-unbiased with noise gain `1/wSS`, and
  every linear unbiased slope estimator has noise gain at least `1/wSS` (the heteroscedastic
  Aitken floor; the homoscedastic twin is `Alt.weight_sq_ge_noiseGain`). This is a floor among
  linear unbiased estimators, not a Cramér–Rao bound.
* `interceptDiff_noiseGain`: the common-slope intercept difference is linear in the ordinates,
  with noise gain `1/n_a + 1/n_b + (Ē_a − Ē_b)²/(SS_a + SS_b)` (unit weights).

## Scope

All results are `PURE-MATH`. The physics reading (Boltzmann-plot ordinates with uncorrelated
additive noise of known variance) is a reduced model and is not part of any statement. The
intercept difference estimates `ln (F N_a/U_a) − ln (F N_b/U_b)`; the log abundance ratio
`ln (N_a/N_b)` also carries the temperature-dependent `ln (U_a/U_b)`, which is not bounded here.

## Literature

Aitken 1935 (Proc. Roy. Soc. Edinburgh 55, 42) for generalized (weighted) least squares;
Tognoni 2010 (Spectrochim. Acta B 65, 1) for the CF-LIBS uncertainty context.
-/

open Finset

namespace CflibsFormal

section WeightedSlope

variable {ι : Type*} [Fintype ι]

/-- **Weighted mean** `Ē_w = (∑_k w k * E k) / ∑_k w k` of the upper-level energies `E` with line
weights `w` (in the noise reading, `w k = 1/σ_k²`, the inverse variance of line `k`'s ordinate).
Totalized division: `0` when `∑ w = 0`, which positive weights on a non-empty line set exclude. -/
noncomputable def wMean (w E : ι → ℝ) : ℝ := (∑ k, w k * E k) / ∑ k, w k

/-- **The weighted mean is the one-group `gMean`.** With every line in one group `e`,
`gMean (fun _ => e) w f e = wMean w f`: the weighted group mean of `FixedEffectsDesign`,
restricted to a single group, is the weighted mean used here. -/
theorem gMean_const_eq_wMean {κ : Type*} [DecidableEq κ] (w f : ι → ℝ) (e : κ) :
    gMean (fun _ => e) w f e = wMean w f := by
  simp [gMean, wMean]

/-- **Weighted centred sum of squares** `wSS = ∑_k w k * (E k − Ē_w)²`, the weighted energy
spread of the Boltzmann plot. With `w k = 1/σ_k²` it is the information about the slope
carried by the line set; for unit weights it is the usual `SS_E`. -/
noncomputable def wSS (w E : ι → ℝ) : ℝ := ∑ k, w k * (E k - wMean w E) ^ 2

/-- **Weighted-least-squares slope weight** `ω_k = w k * (E k − Ē_w) / wSS`. The linear estimator
`∑_k ω_k * y k` is the weighted-RSS-minimizing slope (the one-group case of `feSlope` /
`feSlope_isMin`, whose group mean `gMean` reduces to `wMean` by `gMean_const_eq_wMean`); the
identification of the slopes is not proved in this file. For unit weights this is the
OLS weight `(E k − Ē)/SS_E` (`CflibsFormal.olsWeight`). Totalized division: `0` when
`wSS = 0`. -/
noncomputable def wlsWeight (w E : ι → ℝ) (k : ι) : ℝ := w k * (E k - wMean w E) / wSS w E

/-- The WLS weights are linear-unbiased: `∑ ω = 0` and `∑ ω E = 1`. -/
private theorem wlsWeight_unbiased {w E : ι → ℝ} (hw : ∀ k, 0 < w k) (hSS : 0 < wSS w E) :
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

/-- **WLS attains the minimum noise gain among linear unbiased slope estimators.**
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

Scope: relation PURE-MATH; no physics definition is used; published PURE-MATH. Physics reading
(REDUCED, not part of the statement): Boltzmann-plot ordinates `y k = log (I k/(g k A k))` with
uncorrelated additive noise of known variance `σ_k² = 1/w k`. Atomic-data (`gA`) uncertainties
are a bias, not noise, and should not enter `w`.

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


end WeightedSlope

section CommonSlope

variable {ιa ιb : Type*} [Fintype ιa] [Fintype ιb]

/-- **Pooled within-species energy spread** `SS = SS_a + SS_b`, with
`SS_a = ∑_k (Ea k − mean Ea)²` over the lines of species `a` and `SS_b` likewise for species `b`
(unit weights). It is the denominator of the shared slope. -/
noncomputable def pooledSS (Ea : ιa → ℝ) (Eb : ιb → ℝ) : ℝ :=
  ∑ k, (Ea k - mean Ea) ^ 2 + ∑ k, (Eb k - mean Eb) ^ 2

/-- **Common (shared) slope** of two Boltzmann plots with separate intercepts: each species'
energies and ordinates are centred on that species' own means and one slope is fitted to the
pooled centred points, `β̂ = (∑_a (E − Ē_a)(y − ȳ_a) + ∑_b (E − Ē_b)(y − ȳ_b)) / SS`.
Totalized division: `β̂ = 0` when `SS = 0`. -/
noncomputable def commonSlope (Ea ya : ιa → ℝ) (Eb yb : ιb → ℝ) : ℝ :=
  (∑ k, (Ea k - mean Ea) * (ya k - mean ya) + ∑ k, (Eb k - mean Eb) * (yb k - mean yb))
    / pooledSS Ea Eb

/-- **Intercept difference** `d̂ = (ȳ_a − β̂ Ē_a) − (ȳ_b − β̂ Ē_b)` of the common-slope fit: the
fitted intercept of species `a` minus that of species `b`. In the Boltzmann-plot reading the
intercepts are `b_s = ln (F N_s / U_s)`, so `d̂` estimates `b_a − b_b`; the log abundance ratio
`ln (N_a / N_b)` additionally needs the temperature-dependent term `ln (U_a / U_b)`. -/
noncomputable def interceptDiff (Ea ya : ιa → ℝ) (Eb yb : ιb → ℝ) : ℝ :=
  (mean ya - commonSlope Ea ya Eb yb * mean Ea) - (mean yb - commonSlope Ea ya Eb yb * mean Eb)

/-- **Weight of species-`a` line `k` in `d̂`**:
`1/n_a − (Ē_a − Ē_b)(Ea k − Ē_a)/SS`, where `n_a = card ιa`. -/
noncomputable def idWeightA (Ea : ιa → ℝ) (Eb : ιb → ℝ) (k : ιa) : ℝ :=
  (1 : ℝ) / (Fintype.card ιa : ℝ) - (mean Ea - mean Eb) * (Ea k - mean Ea) / pooledSS Ea Eb

/-- **Weight of species-`b` line `k` in `d̂`**:
`−1/n_b − (Ē_a − Ē_b)(Eb k − Ē_b)/SS`, where `n_b = card ιb`. -/
noncomputable def idWeightB (Ea : ιa → ℝ) (Eb : ιb → ℝ) (k : ιb) : ℝ :=
  -((1 : ℝ) / (Fintype.card ιb : ℝ)) - (mean Ea - mean Eb) * (Eb k - mean Eb) / pooledSS Ea Eb

/-- helper: centring the ordinate does not change the centred cross sum. -/
private theorem centered_cross [Nonempty ιa] (E y : ιa → ℝ) :
    ∑ k, (E k - mean E) * (y k - mean y) = ∑ k, (E k - mean E) * y k := by
  have h0 := centered_sum_zero E
  have : ∑ k, (E k - mean E) * (y k - mean y)
      = ∑ k, (E k - mean E) * y k - (∑ k, (E k - mean E)) * mean y := by
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  rw [this, h0, zero_mul, sub_zero]

/-- helper: sum of squares of `c0 + c1 * (E k - mean E)`. -/
private theorem sum_sq_affine_centered [Nonempty ιa] (E : ιa → ℝ) (c0 c1 : ℝ) :
    ∑ k, (c0 + c1 * (E k - mean E)) ^ 2
      = (Fintype.card ιa : ℝ) * c0 ^ 2 + c1 ^ 2 * ∑ k, (E k - mean E) ^ 2 := by
  have h0 := centered_sum_zero E
  have : ∑ k, (c0 + c1 * (E k - mean E)) ^ 2
      = ∑ k, (c0 ^ 2 + (2 * c0 * c1) * (E k - mean E) + c1 ^ 2 * (E k - mean E) ^ 2) :=
    Finset.sum_congr rfl (fun k _ => by ring)
  rw [this, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    h0, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

/-- **The common-slope intercept difference is linear with noise gain
`1/n_a + 1/n_b + (Ē_a − Ē_b)²/(SS_a + SS_b)`.**
Two species `a`, `b` have `n_a`, `n_b` lines with upper-level energies `Ea`, `Eb`. Their
Boltzmann plots are fitted with separate intercepts and one shared slope (`commonSlope`), and
`d̂ = interceptDiff` is the difference of the fitted intercepts. The theorem proves:
1. `d̂` is the linear estimator `∑_k idWeightA k * ya k + ∑_k idWeightB k * yb k` for all
   ordinates `ya`, `yb`, so the weights are exactly its coefficients; and
2. the squared weights sum to `1/n_a + 1/n_b + (Ē_a − Ē_b)²/(SS_a + SS_b)`.
Under uncorrelated homoscedastic ordinate noise of variance `σ²`, (1) and (2) give
`Var d̂ = σ² (1/n_a + 1/n_b + (Ē_a − Ē_b)²/SS)`; that variance statement is a separate target.
The line-level precision of the intercept difference is therefore limited by the mismatch of the
two species' mean upper energies, not only by the line counts.

Reading: `d̂` estimates `b_a − b_b = ln (F N_a / U_a) − ln (F N_b / U_b)`. The log abundance
ratio `ln (N_a / N_b)` also carries `ln (U_a / U_b)`, which depends on temperature; this theorem
bounds only the intercept-difference part.

Hypotheses.
* `[Nonempty ιa] [Nonempty ιb]`: each species has at least one line, so `1/n_a`, `1/n_b` and
  the means are genuine.
* `hSS : 0 < pooledSS Ea Eb`: the shared slope is identifiable (some species has two distinct
  energies). On paper both conjuncts also hold when `SS = 0` (every `… / SS` term is `0` by
  totalized division), but that case is not claimed: there `d̂` is just the difference of mean
  ordinates, not a common-slope estimator.

Scope: relation PURE-MATH; the definitions used (`mean`, `pooledSS`, `commonSlope`,
`interceptDiff`, the weights) are regression objects with no model tag; published PURE-MATH.
The noise model (uncorrelated homoscedastic ordinate noise) and the intercept-difference reading
above are REDUCED and are not part of the statement.

Literature: Aitken 1935 (Proc. Roy. Soc. Edinburgh 55, 42) for generalized least squares;
Tognoni et al. 2010 (Spectrochim. Acta B 65, 1) for the CF-LIBS context. -/
theorem interceptDiff_noiseGain [Nonempty ιa] [Nonempty ιb] (Ea : ιa → ℝ) (Eb : ιb → ℝ)
    (hSS : 0 < pooledSS Ea Eb) :
    (∀ (ya : ιa → ℝ) (yb : ιb → ℝ),
        interceptDiff Ea ya Eb yb
          = ∑ k, idWeightA Ea Eb k * ya k + ∑ k, idWeightB Ea Eb k * yb k) ∧
      ∑ k, idWeightA Ea Eb k ^ 2 + ∑ k, idWeightB Ea Eb k ^ 2
        = (1 : ℝ) / (Fintype.card ιa : ℝ) + (1 : ℝ) / (Fintype.card ιb : ℝ)
            + (mean Ea - mean Eb) ^ 2 / pooledSS Ea Eb := by
  have hna : (Fintype.card ιa : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hnb : (Fintype.card ιb : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hS : pooledSS Ea Eb ≠ 0 := hSS.ne'
  constructor
  · intro ya yb
    have hA : ∑ k, idWeightA Ea Eb k * ya k
        = mean ya - (mean Ea - mean Eb) * (∑ k, (Ea k - mean Ea) * ya k) / pooledSS Ea Eb := by
      unfold idWeightA
      have : ∑ k, ((1 : ℝ) / (Fintype.card ιa : ℝ)
            - (mean Ea - mean Eb) * (Ea k - mean Ea) / pooledSS Ea Eb) * ya k
          = ∑ k, ((1 : ℝ) / (Fintype.card ιa : ℝ) * ya k
            - (mean Ea - mean Eb) / pooledSS Ea Eb * ((Ea k - mean Ea) * ya k)) :=
        Finset.sum_congr rfl (fun k _ => by ring)
      have hm : mean ya = (∑ k, ya k) / (Fintype.card ιa : ℝ) := rfl
      rw [this, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hm]
      ring
    have hB : ∑ k, idWeightB Ea Eb k * yb k
        = -mean yb - (mean Ea - mean Eb) * (∑ k, (Eb k - mean Eb) * yb k) / pooledSS Ea Eb := by
      unfold idWeightB
      have : ∑ k, (-((1 : ℝ) / (Fintype.card ιb : ℝ))
            - (mean Ea - mean Eb) * (Eb k - mean Eb) / pooledSS Ea Eb) * yb k
          = ∑ k, (-((1 : ℝ) / (Fintype.card ιb : ℝ)) * yb k
            - (mean Ea - mean Eb) / pooledSS Ea Eb * ((Eb k - mean Eb) * yb k)) :=
        Finset.sum_congr rfl (fun k _ => by ring)
      have hm : mean yb = (∑ k, yb k) / (Fintype.card ιb : ℝ) := rfl
      rw [this, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hm]
      ring
    rw [hA, hB]
    unfold interceptDiff commonSlope
    rw [centered_cross Ea ya, centered_cross Eb yb]
    ring
  · have hA : ∑ k, idWeightA Ea Eb k ^ 2
        = (Fintype.card ιa : ℝ) * ((1 : ℝ) / (Fintype.card ιa : ℝ)) ^ 2
          + (-((mean Ea - mean Eb) / pooledSS Ea Eb)) ^ 2 * ∑ k, (Ea k - mean Ea) ^ 2 := by
      rw [← sum_sq_affine_centered]
      exact Finset.sum_congr rfl (fun k _ => by unfold idWeightA; ring)
    have hB : ∑ k, idWeightB Ea Eb k ^ 2
        = (Fintype.card ιb : ℝ) * (-((1 : ℝ) / (Fintype.card ιb : ℝ))) ^ 2
          + (-((mean Ea - mean Eb) / pooledSS Ea Eb)) ^ 2 * ∑ k, (Eb k - mean Eb) ^ 2 := by
      rw [← sum_sq_affine_centered]
      exact Finset.sum_congr rfl (fun k _ => by unfold idWeightB; ring)
    rw [hA, hB]
    have hSSdef : pooledSS Ea Eb = ∑ k, (Ea k - mean Ea) ^ 2 + ∑ k, (Eb k - mean Eb) ^ 2 := rfl
    field_simp
    rw [hSSdef]
    ring


end CommonSlope

end CflibsFormal
