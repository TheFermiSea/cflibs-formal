import Mathlib
import CflibsFormal.OLS

/-!
# FT-10 (item 6): noise gain of the common-slope intercept difference

Staged queue target, 2026-09-24 audit, frontier FT-10. Deterministic Finset algebra for two
species' Boltzmann plots fitted with separate intercepts and one shared slope. Uses
`CflibsFormal.mean` (`OLS.lean`) verbatim.
-/

open Finset CflibsFormal

namespace Plan.FT10

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
theorem centered_cross [Nonempty ιa] (E y : ιa → ℝ) :
    ∑ k, (E k - mean E) * (y k - mean y) = ∑ k, (E k - mean E) * y k := by
  have h0 := centered_sum_zero E
  have : ∑ k, (E k - mean E) * (y k - mean y)
      = ∑ k, (E k - mean E) * y k - (∑ k, (E k - mean E)) * mean y := by
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  rw [this, h0, zero_mul, sub_zero]

/-- helper: sum of squares of `c0 + c1 * (E k - mean E)`. -/
theorem sum_sq_affine_centered [Nonempty ιa] (E : ιa → ℝ) (c0 c1 : ℝ) :
    ∑ k, (c0 + c1 * (E k - mean E)) ^ 2
      = (Fintype.card ιa : ℝ) * c0 ^ 2 + c1 ^ 2 * ∑ k, (E k - mean E) ^ 2 := by
  have h0 := centered_sum_zero E
  have : ∑ k, (c0 + c1 * (E k - mean E)) ^ 2
      = ∑ k, (c0 ^ 2 + (2 * c0 * c1) * (E k - mean E) + c1 ^ 2 * (E k - mean E) ^ 2) :=
    Finset.sum_congr rfl (fun k _ => by ring)
  rw [this, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    h0, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

/-- **FT-10(c): the common-slope intercept difference is linear with noise gain
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

Scope, two-axis prediction: relation PURE-MATH; the definitions used (`mean`, `pooledSS`,
`commonSlope`, `interceptDiff`, the weights) are PURE-MATH regression objects; published tag
PURE-MATH. The noise model and the `ln (N_a/N_b)` reading are REDUCED and belong in the landing
docstring.

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

end Plan.FT10

