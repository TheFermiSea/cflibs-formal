/-
Copyright (c) 2026 Brian Squires. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Squires
-/
import Mathlib
import CflibsFormal.AtomicDataPerturbation
import CflibsFormal.ErrorBudget

/-!
# CF-LIBS formalization — the end-to-end noise → composition chain (gap #5, the composed bound)

Every earlier module bounds ONE link of the CF-LIBS error budget. `ErrorBudget.lean` maps per-line
ordinate noise to a recovered-temperature error; `PartitionLipschitz.lean` maps a temperature error
to a relative partition-function error; `AtomicDataPerturbation.lean` maps a temperature error to a
recovered-density error and (via the verbatim `CompositionRobustness` bound) to a composition error.
This module **composes** those links into a single statement: a bound on the recovered composition
error `|Ĉ_s − C_s|` as an explicit function of the *measurement* noise, assembled strictly from the
existing theorems — none reproven.

The chain, as three reused legs joined at the recovered-temperature gap `|T̂ − T|`:

```
  per-line ordinate noise εₖ  (on the Boltzmann-plot ordinates)
        │  ErrorBudget.temp_rel_error_hetero        (noise → relative T error, REDUCED)
        ▼
  relative temperature error |T̂ − T|/T
        │  × T, then T, T̂ ≤ Tmax                     (noise_to_temperatureGap, this file)
        ▼
  temperature gap  |T̂ − T| ≤ dmax(ε, SS_E, kB, Tmax)
        │  AtomicDataPerturbation.classicDensity_temperature_aliasing_error   (T → density, REDUCED)
        │  + tempResponseErrorBoundOfGap_mono (monotone substitution of dmax for |T̂ − T|)
        ▼
  per-species density error  |N̂_s − N_s| ≤ N_s · Φ
        │  AtomicDataPerturbation.classicComposition_temperature_error     (density → C, REDUCED)
        │  (which is CompositionRobustness.composition_abs_sub_le_bound, verbatim)
        ▼
  composition error  |Ĉ_s − C_s| ≤ compositionErrorBound N Ŝ (Nmax·Φ) s
```

The three physics legs are reused verbatim. The ONLY new mathematics this module adds to make the
join is `tempResponseErrorBoundOfGap_mono` (a pure-analysis monotonicity of the
temperature-response error bound in the gap `|T̂ − T|`), which lets the noise-derived upper bound
`dmax` replace the exact gap inside the envelope, so the final constant is an explicit function of
the noise inputs
(`ε`, `SS_E`, `∑ gₖEₖ`, `kB`, `Tmin`, `Tmax`, `Nmax`) rather than of `|T̂ − T|`.

## Literature

Tognoni et al. 2010 (the CF-LIBS review) presents exactly this error budget: measurement noise on
the Boltzmann-plot ordinates sets the temperature uncertainty, and that uncertainty propagates
— through the partition functions and the Boltzmann factors — into the recovered densities and hence
the composition. This module is the machine-checked assembly of that budget into one inequality;
each
constituent leg carries its own peer-reviewed grounding (`ErrorBudget`, `PartitionLipschitz`,
`AtomicDataPerturbation`, all Tognoni 2010).

## Honest scope

Every result here is `REDUCED` (Tognoni 2010): **a composed chain of REDUCED links is REDUCED, and
the reductions compound.** Restating them, because they must all be carried simultaneously:

* *Temperature leg* (`ErrorBudget.temp_rel_error_hetero`): the recovered temperature is identified
  with the OLS Boltzmann-plot slope (`olsSlope E y = 1/(kB T)`, `olsSlope E ŷ = 1/(kB T̂)` — the
  sign-normalized slope), and the slope error is bounded by the *deterministic worst-case* ℓ¹ bound
  (adversarial, perfectly-correlated ordinate errors); the statistical Gauss–Markov improvement with
  line count is NOT used.
* *Gap scaling* (`noise_to_temperatureGap`): `|T̂ − T| = T·(|T̂ − T|/T)` is over-estimated
  by `T, T̂ ≤ Tmax`, giving the over-estimate `|T̂ − T| ≤ kB·Tmax²·(∑ₖ|Eₖ − Ē|·εₖ)/SS_E`. The
  box
  `Tmin ≤ T, T̂ ≤ Tmax` is a modeling assumption (the plasma temperature is a-priori bracketed).
* *Density leg* (`AtomicDataPerturbation.classicDensity_temperature_aliasing_error`): the
  temperature-response error bound uses honest over-estimates (`exp ≤ 1`, `T₁T₂ ≥ Tmin²`, a
  single-term partition-function floor). The exp-channel smallness `delta_exp < 1` at the WORST-case
  gap `dmax` is a hypothesis (`hsmallmax`); the aliasing algebra itself is exact.
* *Composition leg* (`AtomicDataPerturbation.classicComposition_temperature_error`, i.e.
  `CompositionRobustness.composition_abs_sub_le_bound`): the per-species density errors are
  collapsed into a single uniform envelope `Φ` and a density cap `Nmax`.

The forward model is never linearized: all reductions live in the hypotheses (stronger, lumped) and
in explicit non-sharp constants, not in the algebra. What is delivered:

* `noise_to_temperatureGap` — noise ⇒ temperature gap (`ErrorBudget` + Tmax scaling).
* `noise_to_density` — noise ⇒ per-species recovered-density error (single species).
* `noise_to_composition` — **HEADLINE**: noise ⇒ recovered-composition error, the composed
  end-to-end bound with constant explicit in the noise inputs.

What remains open (unchanged from the constituent modules): the temperature leg's
density/composition coupling is threaded here through the *temperature* channel only (the same-`g`
`U`-shift and Boltzmann shift at `T̂ ≠ T`); an independent atomic-data (`g, A, E`) error channel
exists (`classicComposition_atomicData_error`) but is NOT jointly composed with the temperature
channel in a single constant here — the two error budgets are still to be added by the caller.
-/

namespace CflibsFormal

open Finset Real
open scoped BigOperators

variable {ι : Type*} [Fintype ι]
variable {κ : Type*} [Fintype κ]
variable {ιT : Type*} [Fintype ιT]

/-- **Noise-derived temperature-gap bound.** The explicit upper bound on the recovered-temperature
gap `|T̂ − T|` produced by the temperature leg after over-estimating `T, T̂ ≤ Tmax`:
`dmax = kB·Tmax²·(∑ₖ |Eₖ − Ē|·εₖ)/SS_E`, with `SS_E = ∑ₖ (Eₖ − Ē)²`. Pure algebraic packaging of the
composed bound's temperature-gap term; not an estimator. -/
noncomputable def noiseTempGapBound (kB Tmax : ℝ) (ET epsT : ιT → ℝ) : ℝ :=
  kB * Tmax ^ 2 * ((∑ k, |ET k - mean ET| * epsT k) / (∑ k, (ET k - mean ET) ^ 2))

/-- **Gap-form temperature-response error bound.** Identical to
`AtomicDataPerturbation.tempResponseErrorBound` but parametrized by the temperature gap `d` directly
(rather than by `|T̂ − T|`), so it can be evaluated at the worst-case gap `dmax` and its
monotonicity in `d` can be stated. Pure algebraic packaging; not an estimator. -/
noncomputable def tempResponseErrorBoundOfGap (kB Tmin d : ℝ) (g E : ι → ℝ) (u k0 : ι) : ℝ :=
  ((Real.exp (E u * d / (kB * Tmin ^ 2)) - 1)
      + (∑ k, g k * E k) * d / (kB * Tmin ^ 2)
          / (g k0 * Real.exp (-E k0 / (kB * Tmin))))
    / (1 - (Real.exp (E u * d / (kB * Tmin ^ 2)) - 1))

/-- **The named temperature-response bound is the gap-form bound at the actual gap.** A definitional
identity: `tempResponseErrorBound kB Tmin T T̂ … = tempResponseErrorBoundOfGap kB Tmin |T̂ − T| …`.
Pure packaging bridge (`rfl`). -/
theorem tempResponseErrorBound_eq_ofGap {kB Tmin T That : ℝ} {g E : ι → ℝ} {u k0 : ι} :
    tempResponseErrorBound kB Tmin T That g E u k0
      = tempResponseErrorBoundOfGap kB Tmin |That - T| g E u k0 := rfl

/-- **Elementary monotone-fraction bound.** For `a₁ ≤ a₂ < 1`, `0 ≤ a₁`, `0 ≤ t₁ ≤ t₂`,
`(a₁ + t₁)/(1 − a₁) ≤ (a₂ + t₂)/(1 − a₂)`: the numerator grows and the positive denominator shrinks.
Private helper; pure real algebra. -/
private lemma frac_mono {a1 a2 t1 t2 : ℝ}
    (ha1 : 0 ≤ a1) (ha12 : a1 ≤ a2) (ht1 : 0 ≤ t1) (ht12 : t1 ≤ t2) (ha2 : a2 < 1) :
    (a1 + t1) / (1 - a1) ≤ (a2 + t2) / (1 - a2) := by
  have hq2 : 0 < 1 - a2 := by linarith
  have hq1 : 0 < 1 - a1 := by linarith
  have hp2 : 0 ≤ a2 + t2 := by linarith
  have hp12 : a1 + t1 ≤ a2 + t2 := by linarith
  have hq21 : 1 - a2 ≤ 1 - a1 := by linarith
  rw [div_le_div_iff₀ hq1 hq2]
  linarith [mul_le_mul_of_nonneg_right hp12 hq2.le, mul_le_mul_of_nonneg_left hq21 hp2]

/-- **Temperature-response error bound is monotone in the gap (PURE-MATH).** For `gₖ > 0`, `Eₖ ≥ 0`,
`0 < kB, Tmin`, and gaps `0 ≤ d₁ ≤ d₂` with the exp-channel smallness holding at the larger gap
(`exp(E_u·d₂/(kB·Tmin²)) − 1 < 1`),
`tempResponseErrorBoundOfGap … d₁ … ≤ tempResponseErrorBoundOfGap … d₂ …`. Both numerator channels
(the exp channel and `U` channel) grow in `d`, while the denominator `2 − exp(…)` decreases
but stays positive, so the ratio increases; `frac_mono` closes it. This is the lever that lets a
noise-derived UPPER bound `dmax` on the gap replace the exact gap inside the envelope. -/
theorem tempResponseErrorBoundOfGap_mono {kB Tmin d1 d2 : ℝ} {g E : ι → ℝ} {u k0 : ι}
    (hd1 : 0 ≤ d1) (hd12 : d1 ≤ d2) (hkB : 0 < kB) (hTmin : 0 < Tmin)
    (hg : ∀ k, 0 < g k) (hE : ∀ k, 0 ≤ E k)
    (hsmall : Real.exp (E u * d2 / (kB * Tmin ^ 2)) - 1 < 1) :
    tempResponseErrorBoundOfGap kB Tmin d1 g E u k0
      ≤ tempResponseErrorBoundOfGap kB Tmin d2 g E u k0 := by
  have hD : 0 < kB * Tmin ^ 2 := by positivity
  have hW : 0 < g k0 * Real.exp (-E k0 / (kB * Tmin)) := mul_pos (hg k0) (Real.exp_pos _)
  have hSsum : 0 ≤ ∑ k, g k * E k := Finset.sum_nonneg (fun k _ => mul_nonneg (hg k).le (hE k))
  have harg1 : 0 ≤ E u * d1 / (kB * Tmin ^ 2) := div_nonneg (mul_nonneg (hE u) hd1) hD.le
  have ha1 : 0 ≤ Real.exp (E u * d1 / (kB * Tmin ^ 2)) - 1 := by
    linarith [Real.add_one_le_exp (E u * d1 / (kB * Tmin ^ 2)), harg1]
  have harg12 : E u * d1 / (kB * Tmin ^ 2) ≤ E u * d2 / (kB * Tmin ^ 2) := by
    rw [div_le_div_iff₀ hD hD]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hd12 (hE u)) hD.le
  have ha12 : Real.exp (E u * d1 / (kB * Tmin ^ 2)) - 1
      ≤ Real.exp (E u * d2 / (kB * Tmin ^ 2)) - 1 := by
    linarith [Real.exp_le_exp.mpr harg12]
  have ht1 : 0 ≤ (∑ k, g k * E k) * d1 / (kB * Tmin ^ 2)
      / (g k0 * Real.exp (-E k0 / (kB * Tmin))) :=
    div_nonneg (div_nonneg (mul_nonneg hSsum hd1) hD.le) hW.le
  have ht12 : (∑ k, g k * E k) * d1 / (kB * Tmin ^ 2)
        / (g k0 * Real.exp (-E k0 / (kB * Tmin)))
      ≤ (∑ k, g k * E k) * d2 / (kB * Tmin ^ 2)
        / (g k0 * Real.exp (-E k0 / (kB * Tmin))) := by
    have hb : (∑ k, g k * E k) * d1 ≤ (∑ k, g k * E k) * d2 :=
      mul_le_mul_of_nonneg_left hd12 hSsum
    have hDW : 0 < (kB * Tmin ^ 2) * (g k0 * Real.exp (-E k0 / (kB * Tmin))) := mul_pos hD hW
    rw [div_div, div_div, div_le_div_iff₀ hDW hDW]
    exact mul_le_mul_of_nonneg_right hb hDW.le
  unfold tempResponseErrorBoundOfGap
  exact frac_mono ha1 ha12 ht1 ht12 hsmall

/-- **Noise ⇒ temperature gap (REDUCED, Tognoni 2010).** Composing the heteroscedastic temperature
identity `ErrorBudget.temp_rel_error_hetero` (per-line ordinate budgets `εₖ` ⇒ relative temperature
error) with the box `Tmin ≤ T, T̂ ≤ Tmax`, the recovered-temperature gap is bounded by the
noise:
  `|T̂ − T| ≤ kB·Tmax²·(∑ₖ |Eₖ − Ē|·εₖ)/SS_E = noiseTempGapBound kB Tmax E ε`.
Derivation: `|T̂ − T| = T·(|T̂ − T|/T) ≤ T·kB·T̂·S` (the temperature identity), then `T, T̂ ≤ Tmax`
gives `T·T̂ ≤ Tmax²`. Reduction: the deterministic worst-case slope bound of `temp_rel_error_hetero`
plus the `Tmax` over-estimate; the Boltzmann-plot slope/temperature identification is inherited as a
hypothesis (`hβ`, `hβHat`). -/
theorem noise_to_temperatureGap [Nonempty ιT]
    {kB Tmin Tmax T That : ℝ} {ET yT yHatT epsT : ιT → ℝ}
    (hkB : 0 < kB) (hTmin : 0 < Tmin)
    (hT : Tmin ≤ T) (hThat : Tmin ≤ That)
    (hTmaxT : T ≤ Tmax) (hTmaxThat : That ≤ Tmax)
    (hvarT : 0 < ∑ k, (ET k - mean ET) ^ 2)
    (hδT : ∀ k, |yHatT k - yT k| ≤ epsT k)
    (hβ : olsSlope ET yT = 1 / (kB * T))
    (hβHat : olsSlope ET yHatT = 1 / (kB * That)) :
    |That - T| ≤ noiseTempGapBound kB Tmax ET epsT := by
  have hTpos : 0 < T := lt_of_lt_of_le hTmin hT
  have hThatpos : 0 < That := lt_of_lt_of_le hTmin hThat
  have hrel : |That - T| / T
      ≤ kB * That * ((∑ k, |ET k - mean ET| * epsT k) / (∑ k, (ET k - mean ET) ^ 2)) :=
    temp_rel_error_hetero hkB hTpos hThatpos hvarT hδT hβ hβHat
  set S := (∑ k, |ET k - mean ET| * epsT k) / (∑ k, (ET k - mean ET) ^ 2) with hSdef
  have hSnn : 0 ≤ S := by
    rw [hSdef]
    exact div_nonneg
      (Finset.sum_nonneg (fun k _ => mul_nonneg (abs_nonneg _) ((abs_nonneg _).trans (hδT k))))
      hvarT.le
  have hkS : 0 ≤ kB * S := mul_nonneg hkB.le hSnn
  rw [div_le_iff₀ hTpos] at hrel
  have hTT : T * That ≤ Tmax * Tmax :=
    mul_le_mul hTmaxT hTmaxThat hThatpos.le (le_trans hTpos.le hTmaxT)
  have h2 : kB * That * S * T ≤ kB * Tmax ^ 2 * S := by
    have hrw : kB * That * S * T = kB * S * (T * That) := by ring
    rw [hrw]
    calc kB * S * (T * That) ≤ kB * S * (Tmax * Tmax) := mul_le_mul_of_nonneg_left hTT hkS
      _ = kB * Tmax ^ 2 * S := by ring
  unfold noiseTempGapBound
  rw [← hSdef]
  linarith [hrel, h2]

/-- **Noise ⇒ per-species recovered-density error (REDUCED, Tognoni 2010).** The single-species
composition of two reused legs. The temperature gap is bounded by the noise
(`noise_to_temperatureGap`), fed into the temperature-density bound
`AtomicDataPerturbation.classicDensity_temperature_aliasing_error`, and the exact gap `|T̂ − T|` is
replaced by the noise-derived worst-case gap `dmax = noiseTempGapBound kB Tmax E ε` via
`tempResponseErrorBoundOfGap_mono`:
  `|N̂ − N| ≤ N · tempResponseErrorBoundOfGap kB Tmin dmax g E u k0`.
The exp-channel smallness `hsmall` is required at `dmax` (the worst case), whence it holds at the
actual gap. Reduction: inherits the temperature and density legs' reductions (worst-case slope,
`Tmax` over-estimate, non-sharp response constants). -/
theorem noise_to_density [Nonempty ι] [Nonempty ιT]
    {kB Tmin Tmax T That Fcal N : ℝ} {ET yT yHatT epsT : ιT → ℝ}
    {g E A : ι → ℝ} {u k0 : ι}
    (hkB : 0 < kB) (hTmin : 0 < Tmin)
    (hT : Tmin ≤ T) (hThat : Tmin ≤ That)
    (hTmaxT : T ≤ Tmax) (hTmaxThat : That ≤ Tmax)
    (hg : ∀ k, 0 < g k) (hE : ∀ k, 0 ≤ E k)
    (hFcal : 0 < Fcal) (hA : 0 < A u) (hN : 0 < N)
    (hvarT : 0 < ∑ k, (ET k - mean ET) ^ 2)
    (hδT : ∀ k, |yHatT k - yT k| ≤ epsT k)
    (hβ : olsSlope ET yT = 1 / (kB * T))
    (hβHat : olsSlope ET yHatT = 1 / (kB * That))
    (hsmall : Real.exp (E u * noiseTempGapBound kB Tmax ET epsT / (kB * Tmin ^ 2)) - 1 < 1) :
    |Classic.classicDensity kB That Fcal g E A u (lineIntensity kB T N Fcal g E A u) - N|
      ≤ N * tempResponseErrorBoundOfGap kB Tmin (noiseTempGapBound kB Tmax ET epsT) g E u k0 := by
  have hgap : |That - T| ≤ noiseTempGapBound kB Tmax ET epsT :=
    noise_to_temperatureGap hkB hTmin hT hThat hTmaxT hTmaxThat hvarT hδT hβ hβHat
  have hgap0 : 0 ≤ |That - T| := abs_nonneg _
  have hD : 0 < kB * Tmin ^ 2 := by positivity
  have harg : E u * |That - T| / (kB * Tmin ^ 2)
      ≤ E u * noiseTempGapBound kB Tmax ET epsT / (kB * Tmin ^ 2) := by
    rw [div_le_div_iff₀ hD hD]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hgap (hE u)) hD.le
  have hsmall' : Real.exp (E u * |That - T| / (kB * Tmin ^ 2)) - 1 < 1 := by
    linarith [Real.exp_le_exp.mpr harg, hsmall]
  have hbound := classicDensity_temperature_aliasing_error hkB hTmin hT hThat hg hE
    hFcal u k0 hA hN hsmall'
  rw [tempResponseErrorBound_eq_ofGap] at hbound
  refine hbound.trans (mul_le_mul_of_nonneg_left ?_ hN.le)
  exact tempResponseErrorBoundOfGap_mono hgap0 hgap hkB hTmin hg hE hsmall

/-- **HEADLINE — noise ⇒ recovered-composition error (REDUCED, Tognoni 2010).** The composed
end-to-end bound. Given per-line ordinate noise `εₖ` on the temperature-diagnostic Boltzmann plot
(index `ιT`), a positive energy spread `SS_E = ∑ (ET_k − Ē)² > 0`, a temperature box
`Tmin ≤ T, T̂ ≤ Tmax`, positive nondegenerate per-species atomic data (`g`, `A`), `E ≥ 0`, a uniform
temperature-response envelope `Φ` at the worst-case gap and a density cap `Nmax`, the recovered
composition error is bounded by an EXPLICIT function of the noise:
  `|Ĉ_s − C_s| ≤ compositionErrorBound N Ŝ (Nmax·Φ) s`,
where the worst-case gap `dmax = noiseTempGapBound kB Tmax ET ε` and `Φ` envelopes
`tempResponseErrorBoundOfGap kB Tmin dmax …` across species. Assembled strictly from
`noise_to_temperatureGap` (⇒ `|T̂ − T| ≤ dmax`), `tempResponseErrorBoundOfGap_mono` (⇒ the
per-species smallness `hδp1` and envelope `henv` at the actual gap from those at `dmax`), and
`AtomicDataPerturbation.classicComposition_temperature_error` (the verbatim density → composition
leg, i.e. `CompositionRobustness.composition_abs_sub_le_bound`). Reduction: the reductions
of all three legs (see the module Honest-scope note); `hsmallmax`/`henvmax` are stated at the
worst-case gap. -/
theorem noise_to_composition [Nonempty ι] [Nonempty κ] [Nonempty ιT]
    {kB Tmin Tmax T That Fcal Φ Nmax : ℝ} {ET yT yHatT epsT : ιT → ℝ}
    {N : κ → ℝ} {g E A : κ → ι → ℝ} {u k0 : κ → ι}
    (hkB : 0 < kB) (hTmin : 0 < Tmin)
    (hT : Tmin ≤ T) (hThat : Tmin ≤ That)
    (hTmaxT : T ≤ Tmax) (hTmaxThat : That ≤ Tmax)
    (hg : ∀ s k, 0 < g s k) (hE : ∀ s k, 0 ≤ E s k)
    (hFcal : 0 < Fcal) (hA : ∀ s, 0 < A s (u s))
    (hN : ∀ s, 0 < N s) (hNmax : ∀ s, N s ≤ Nmax) (hΦ0 : 0 ≤ Φ)
    (hvarT : 0 < ∑ k, (ET k - mean ET) ^ 2)
    (hδT : ∀ k, |yHatT k - yT k| ≤ epsT k)
    (hβ : olsSlope ET yT = 1 / (kB * T))
    (hβHat : olsSlope ET yHatT = 1 / (kB * That))
    (hsmallmax : ∀ s, Real.exp (E s (u s) * noiseTempGapBound kB Tmax ET epsT
        / (kB * Tmin ^ 2)) - 1 < 1)
    (henvmax : ∀ s, tempResponseErrorBoundOfGap kB Tmin (noiseTempGapBound kB Tmax ET epsT)
        (g s) (E s) (u s) (k0 s) ≤ Φ)
    (s : κ) :
    |composition (recoveredDensityAtT kB T That Fcal g E A u N) s - composition N s|
      ≤ compositionErrorBound N
          (totalDensity (recoveredDensityAtT kB T That Fcal g E A u N)) (Nmax * Φ) s := by
  have hgap : |That - T| ≤ noiseTempGapBound kB Tmax ET epsT :=
    noise_to_temperatureGap hkB hTmin hT hThat hTmaxT hTmaxThat hvarT hδT hβ hβHat
  have hgap0 : 0 ≤ |That - T| := abs_nonneg _
  have hD : 0 < kB * Tmin ^ 2 := by positivity
  have hδp1 : ∀ t, Real.exp (E t (u t) * |That - T| / (kB * Tmin ^ 2)) - 1 < 1 := by
    intro t
    have harg : E t (u t) * |That - T| / (kB * Tmin ^ 2)
        ≤ E t (u t) * noiseTempGapBound kB Tmax ET epsT / (kB * Tmin ^ 2) := by
      rw [div_le_div_iff₀ hD hD]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hgap (hE t (u t))) hD.le
    linarith [Real.exp_le_exp.mpr harg, hsmallmax t]
  have henv : ∀ t, tempResponseErrorBound kB Tmin T That (g t) (E t) (u t) (k0 t) ≤ Φ := by
    intro t
    rw [tempResponseErrorBound_eq_ofGap]
    exact le_trans
      (tempResponseErrorBoundOfGap_mono hgap0 hgap hkB hTmin (hg t) (hE t) (hsmallmax t))
      (henvmax t)
  exact classicComposition_temperature_error hkB hTmin hT hThat hg hE hFcal hA hN hNmax hΦ0
    hδp1 henv s

/-! ### Non-vacuity witnesses

The `nvN2c*` data instantiate the chain on temperature-diagnostic lines `ιT = Fin 2` and a single
species / single atomic line (`κ = ι = Fin 1`) with `kB = Fcal = 1`, `Tmin = 1/2`, `Tmax = 2`. The
Boltzmann plot `ET = (0, 1)`, `yT = (0, 1)`, `ŷT = (0, 3/2)` fixes a genuine `T = 1 ≠ T̂ = 2/3` (the
recovered temperature is really wrong), with per-line budget `ε = (0, 1/2)` — all hypotheses jointly
satisfiable. -/

private def nvN2cET : Fin 2 → ℝ := ![0, 1]
private def nvN2cYt : Fin 2 → ℝ := ![0, 1]
private noncomputable def nvN2cYhat : Fin 2 → ℝ := ![0, 3 / 2]
private noncomputable def nvN2cEps : Fin 2 → ℝ := ![0, 1 / 2]
private def nvN2cN : Fin 1 → ℝ := fun _ => 4
private def nvN2cg : Fin 1 → Fin 1 → ℝ := fun _ _ => 1
private def nvN2cE : Fin 1 → Fin 1 → ℝ := fun _ _ => 0
private def nvN2cA : Fin 1 → Fin 1 → ℝ := fun _ _ => 1
private def nvN2cu : Fin 1 → Fin 1 := fun _ => 0
private def nvN2ck0 : Fin 1 → Fin 1 := fun _ => 0

/-- The noise ⇒ temperature-gap bound applies with a genuine wrong temperature (`T = 1`, `T̂ = 2/3`,
slopes `1` and `3/2`): all hypotheses of `noise_to_temperatureGap` are jointly satisfiable, and the
gap `|2/3 − 1| = 1/3` is bounded by the noise-derived `noiseTempGapBound 1 2 ET ε`. -/
example :
    |(2 / 3 : ℝ) - 1| ≤ noiseTempGapBound 1 2 nvN2cET nvN2cEps :=
  noise_to_temperatureGap (T := 1) (That := 2 / 3) (Tmin := 1 / 2)
    (yT := nvN2cYt) (yHatT := nvN2cYhat)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [nvN2cET, mean, Fin.sum_univ_two])
    (by intro k; fin_cases k <;> norm_num [nvN2cYt, nvN2cYhat, nvN2cEps])
    (by norm_num [olsSlope, nvN2cET, nvN2cYt, mean, Fin.sum_univ_two])
    (by norm_num [olsSlope, nvN2cET, nvN2cYhat, mean, Fin.sum_univ_two])

/-- The headline `noise_to_composition` applies: all its hypotheses — the Boltzmann-plot slope
identifications fixing `T = 1 ≠ T̂ = 2/3`, the temperature box, positive nondegenerate atomic data,
the worst-case exp-channel smallness, and the uniform envelope `Φ = 0` — are jointly satisfiable, so
the
composed end-to-end bound is non-vacuously instantiable. -/
example : True := by
  have _h := noise_to_composition (kB := 1) (Tmin := 1 / 2) (Tmax := 2) (T := 1) (That := 2 / 3)
    (Fcal := 1) (Φ := 0) (Nmax := 4) (ET := nvN2cET) (yT := nvN2cYt) (yHatT := nvN2cYhat)
    (epsT := nvN2cEps) (N := nvN2cN) (g := nvN2cg) (E := nvN2cE) (A := nvN2cA)
    (u := nvN2cu) (k0 := nvN2ck0)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by intro t k; norm_num [nvN2cg]) (by intro t k; norm_num [nvN2cE]) (by norm_num)
    (by intro t; norm_num [nvN2cA]) (by intro t; norm_num [nvN2cN])
    (by intro t; norm_num [nvN2cN]) (by norm_num)
    (by norm_num [nvN2cET, mean, Fin.sum_univ_two])
    (by intro k; fin_cases k <;> norm_num [nvN2cYt, nvN2cYhat, nvN2cEps])
    (by norm_num [olsSlope, nvN2cET, nvN2cYt, mean, Fin.sum_univ_two])
    (by norm_num [olsSlope, nvN2cET, nvN2cYhat, mean, Fin.sum_univ_two])
    (by intro t; simp [nvN2cE, Real.exp_zero])
    (by
      intro t
      simp [tempResponseErrorBoundOfGap, nvN2cE, nvN2cg, Real.exp_zero])
    (0 : Fin 1)
  trivial

end CflibsFormal
