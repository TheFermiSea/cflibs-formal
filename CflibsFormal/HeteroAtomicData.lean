/-
Copyright (c) 2026 Brian Squires. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Squires
-/
import Mathlib
import CflibsFormal.ForwardMap
import CflibsFormal.OLS
import CflibsFormal.ErrorBudget
import CflibsFormal.Analysis

/-!
# CF-LIBS formalization — PER-LINE heterogeneous atomic-data error in the Boltzmann-plot SLOPE

`AtomicDataPerturbation.lean` closes the single-line reader under a **single lumped** relative
data error `δ` (`classicDensity_aliasing_error`, `..._error_channels`, `..._error_energy`), and
`Alt/OLSAtomicDataPerturbation.lean` closes the multi-line OLS **intercept/density** leg under a
per-line `δₖ` (`olsDensity_aliasing_A`, `olsDensity_aliasing_A_error`). What neither closes is the
**slope leg**: a per-line transition-probability error `δₖ` does not only shift the Boltzmann-plot
intercept, it *tilts* the fitted line, so it biases the recovered **temperature** — the quantity
every downstream CF-LIBS step (partition functions, Saha, composition) consumes. This module
closes that leg with a genuinely per-line budget.

Real atomic data is not uniformly wrong: some `gA` values are measured to a few percent, others
are order-of-magnitude estimates. A single global `δ` is therefore the wrong model and is
needlessly pessimistic — it must be set by the *worst* line even when most lines are excellent.

## The chain

```
  per-line relative transition-probability error  |A'ₖ − Aₖ| ≤ δₖ·Aₖ
        │  abs_log_ratio_le  (Analysis.lean)                    [PURE-MATH]
        ▼
  per-line ordinate error   |log(Aₖ/A'ₖ)| ≤ δₖ/(1 − δₖ)
        │  olsSlope_aliasing_A  (EXACT split of the fitted slope)
        │  olsSlope_stable_hetero  (ErrorBudget.lean)
        ▼
  slope (inverse-temperature) bias  ≤  heteroSlopeBound E δ
        │  temp_rel_error_le  (ErrorBudget.lean)
        ▼
  relative temperature error  |T̂ − T|/T
```

The precedent mirrored here is `ErrorBudget.olsSlope_stable_hetero` /
`olsSlope_stable_l1_of_hetero` (per-line NOISE budgets, with the global bound recovered as the
constant special case). The three required pieces are supplied for atomic data:

* the heterogeneous bound — `olsSlope_aliasing_A_hetero`, `temp_rel_error_atomicData_hetero`;
* the global bound recovered as the constant-`δ` special case — `heteroSlopeBound_const`
  (an EQUALITY, so the new bound is the same quantity, not a different one) plus the
  domination `heteroSlopeBound_le_global` and its composed form `olsSlope_aliasing_A_global`;
* a NUMERICAL strict-improvement witness — `heteroSlopeBound_lt_global_witness`:
  on two lines with `E = (0, 1)` and `δ = (0, 1/2)` (line 0 exact) the heterogeneous constant is
  `1` while the global constant at `δmax = 1/2` is `2`. Factor two, exhibited, not asserted.

Anti-vacuity is machine-checked on the physical witness at the end of the module from both sides:
`nvP_slope_bias_eq_log` computes the slope bias there to be EXACTLY `log (2/3) < 0` (so the bound
is applied to a genuine, non-zero perturbation, not a `0 ≤ 3/2` collapse) and
`nvP_heteroSlopeBound_value` computes the bound to be `3/2 ≠ 0`; a closing `example` discharges
`temp_rel_error_atomicData_hetero`'s hypotheses — `hslopeHat` included — with the explicit
`T̂ = 1/(1 − log (2/3)) > 0`, certifying that hypothesis set is SATISFIABLE, not contradictory.

## Literature and scope

Tognoni, Cristoforetti, Legnaioli, Palleschi, "Calibration-Free LIBS: State of the art,"
*Spectrochim. Acta B* **65** (2010) 1–14 — transition-probability (`A`) uncertainty is the
dominant CF-LIBS accuracy contributor once the plasma is characterized, and it is *line-specific*
(NIST-grade lines alongside estimated ones in the same fit). This is the citation already carried
by `AtomicDataPerturbation.classicDensity_aliasing` and by the OLS intercept mirror
`Alt.olsDensity_aliasing_A`; nothing new is claimed of the literature here. The Boltzmann-plot
fit itself is Ciucci et al. (1999) as carried by `ForwardMap.boltzmann_plot_intensity`.

The "a per-line atomic-data error is exactly an additive per-line ordinate error, so the OLS
slope picks up exactly `olsSlope E (log(A/A'))`" reading is a *derived* algebraic consequence of
the affine structure of the Boltzmann plot, not a literature claim.

Scope tags: `relTransfer_mono`, `heteroSlopeBound_le_global`, `heteroSlopeBound_const`,
`heteroSlopeBound_lt_global_witness`, `nvP_heteroSlopeBound_value` are PURE-MATH (real-number
algebra on explicit data, no physics).
`olsSlope_aliasing_A` is EXACT (a cancellation identity, no approximation), and
`nvP_slope_bias_eq_log` is EXACT with it — a numerical instance of that same identity, exact
*within* the forward map it inherits (which is itself REDUCED; this follows the tagging precedent
of `Alt.olsDensity_aliasing_A`, its intercept twin).
`olsSlope_aliasing_A_hetero`, `olsSlope_aliasing_A_global` and
`temp_rel_error_atomicData_hetero` are REDUCED (they inherit the optically-thin, single-`T`
LTE forward map and lump the per-line log-ratios through the two-sided transfer bound).

## Honest limitations

* **A-channel only.** `g` and `E` are assumed correct; only the transition probabilities `A` are
  wrong. A wrong `g` also perturbs the partition function `U(T)`, and a wrong `E` perturbs the
  fit *abscissa* (a projection artifact, handled separately and only partially by
  `Alt.olsDensity_aliasing_E_error`). Neither is covered here.
* **Bias, not variance.** `δₖ = log(Aₖ/A'ₖ)` is a fixed SYSTEMATIC error, not zero-mean noise.
  Nothing here says "more lines ⇒ better": if the tabulated `A'ₖ` are biased in a common
  direction, the slope bias does **not** average away. The `olsSlope_noise_gain` /
  `Alt.OLSVariance` statistical machinery does not apply to this channel.
* **`T̂` is a hypothesis, not a construction.** `temp_rel_error_atomicData_hetero` takes
  `hslopeHat : olsSlope E ŷ = −1/(k_B T̂)` as a hypothesis identifying the analyst's recovered
  temperature with the fitted slope. It does not *construct* `T̂` in general or prove such a `T̂`
  exists in general; it bounds the error of whatever temperature the analyst reads off that
  slope. (What IS certified is that the hypothesis set is satisfiable: the closing `example`
  exhibits one explicit `T̂` on the witness spectrum. That is one instance, not a construction.)
* **Worst case, not attained.** `heteroSlopeBound` is an upper envelope (triangle inequality plus
  the one-sided-worse `δ/(1−δ)` transfer constant). Sharpness is not claimed and not proven.
* **The temperature error is not fed back.** A biased `T̂` re-enters the density channel through
  `U(T̂)`; that cross-channel coupling is the same open residual already recorded in
  `ErrorBudget.lean`, and this module does not close it.
-/

namespace CflibsFormal

open Finset Real
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-! ## Additivity of the OLS slope in the ordinate (private algebra)

The lever behind the EXACT slope split: `olsSlope` is linear in the ordinate, via its centered
representation `olsSlope_eq_centered` (a common denominator `SS_E`, so the numerator sum
splits). Proved locally rather than imported, since the `Alt` mirror keeps its copy private. -/

private theorem hetero_olsSlope_add [Nonempty ι] (E f h : ι → ℝ) :
    olsSlope E (fun k => f k + h k) = olsSlope E f + olsSlope E h := by
  rw [olsSlope_eq_centered, olsSlope_eq_centered, olsSlope_eq_centered, ← add_div]
  congr 1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  ring

private theorem hetero_olsSlope_zero [Nonempty ι] (E : ι → ℝ) :
    olsSlope E (fun _ : ι => (0 : ℝ)) = 0 := by
  rw [olsSlope_eq_centered]
  simp only [mul_zero, Finset.sum_const_zero, zero_div]

/-! ## The two error constants -/

/-- **Heterogeneous (per-line) slope-error constant.** With a per-line relative
transition-probability budget `δₖ`, the Boltzmann-plot slope bias is bounded by
`(∑ₖ |Eₖ − Ē|·δₖ/(1 − δₖ)) / SS_E`. Each line contributes its OWN budget, weighted by its own
leverage `|Eₖ − Ē|`; a line with `δₖ = 0` (an exactly-known `A`) contributes exactly nothing. -/
noncomputable def heteroSlopeBound (E δ : ι → ℝ) : ℝ :=
  (∑ k, |E k - mean E| * (δ k / (1 - δ k))) / (∑ k, (E k - mean E) ^ 2)

/-- **Global (single-`δ`) slope-error constant.** The constant the existing lumped-`δ` model
produces: one worst-case relative budget `δmax` for every line,
`(δmax/(1 − δmax))·(∑ₖ |Eₖ − Ē|) / SS_E`. This is the shape of `ErrorBudget.olsSlope_stable_l1`
with `ε = δmax/(1 − δmax)`. -/
noncomputable def globalSlopeBound (E : ι → ℝ) (dmax : ℝ) : ℝ :=
  (dmax / (1 - dmax)) * (∑ k, |E k - mean E|) / (∑ k, (E k - mean E) ^ 2)

/-- **The relative-error transfer `δ ↦ δ/(1 − δ)` is monotone below `1`.** The elementary fact
that lets a per-line budget be dominated by a global one: `a ≤ b < 1 ⇒ a/(1−a) ≤ b/(1−b)`.
Non-negativity of `a` is NOT needed (both denominators are positive once `a ≤ b < 1`, and
cross-multiplying collapses to `a ≤ b`), so the lemma is stated without it even though the
physical budgets it is applied to are of course non-negative. Pure real algebra, no physics. -/
theorem relTransfer_mono {a b : ℝ} (hab : a ≤ b) (hb : b < 1) :
    a / (1 - a) ≤ b / (1 - b) := by
  have h1 : (0 : ℝ) < 1 - a := sub_pos.mpr (lt_of_le_of_lt hab hb)
  have h2 : (0 : ℝ) < 1 - b := sub_pos.mpr hb
  rw [div_le_div_iff₀ h1 h2]
  nlinarith [hab, h1, h2]

/-- **The heterogeneous constant is never worse than the global one.** If every per-line budget
satisfies `δₖ ≤ δmax < 1`, then `heteroSlopeBound E δ ≤ globalSlopeBound E δmax`. Pure
algebra: monotonicity of the transfer (`relTransfer_mono`) termwise, then the common positive
denominator `SS_E`. This is the domination half of "genuine generalization"; the equality half is
`heteroSlopeBound_const`. (No `0 ≤ δₖ` hypothesis is needed — see `relTransfer_mono`.) -/
theorem heteroSlopeBound_le_global {E δ : ι → ℝ} {dmax : ℝ}
    (hvar : 0 < ∑ k, (E k - mean E) ^ 2)
    (hδmax : ∀ k, δ k ≤ dmax) (hmax1 : dmax < 1) :
    heteroSlopeBound E δ ≤ globalSlopeBound E dmax := by
  have hnum : ∑ k, |E k - mean E| * (δ k / (1 - δ k))
      ≤ ∑ k, |E k - mean E| * (dmax / (1 - dmax)) := by
    refine Finset.sum_le_sum (fun k _ => ?_)
    exact mul_le_mul_of_nonneg_left (relTransfer_mono (hδmax k) hmax1) (abs_nonneg _)
  have hfac : ∑ k, |E k - mean E| * (dmax / (1 - dmax))
      = dmax / (1 - dmax) * ∑ k, |E k - mean E| := by
    rw [← Finset.sum_mul]; ring
  unfold heteroSlopeBound globalSlopeBound
  rw [← hfac, div_le_div_iff_of_pos_right hvar]
  exact hnum

/-- **The global constant is EXACTLY the constant-`δ` special case.** Feeding the constant budget
`δₖ := d` into `heteroSlopeBound` returns `globalSlopeBound E d` on the nose — an equality, not a
bound. This is the check that the heterogeneous constant is a genuine *generalization* of the
existing lumped-`δ` constant rather than a different quantity: the whole lumped-`δ` chain is the
special case `δ ≡ d`. Pure algebra (`∑ₖ |Eₖ − Ē|·c = c·∑ₖ |Eₖ − Ē|`). -/
theorem heteroSlopeBound_const (E : ι → ℝ) (d : ℝ) :
    heteroSlopeBound E (fun _ => d) = globalSlopeBound E d := by
  have h : ∑ k, |E k - mean E| * (d / (1 - d)) = d / (1 - d) * ∑ k, |E k - mean E| := by
    rw [← Finset.sum_mul]; ring
  simp only [heteroSlopeBound, globalSlopeBound]
  rw [h]

/-! ## The EXACT slope split under wrong transition probabilities -/

/-- **EXACT aliasing identity for the fitted SLOPE (A-channel).** The spectrum is emitted with the
TRUE transition probabilities `A` (correct `g`, `E`) at density `N`; the analyst builds the
Boltzmann-plot ordinate with the WRONG `A'`. Then the fitted slope is EXACTLY the true slope plus
the OLS slope of the per-line log data-ratios:
  `olsSlope E (log(Iₖ/(gₖA'ₖ))) = −1/(k_B T) + olsSlope E (log(Aₖ/A'ₖ))`.
Proof: the observed ordinate splits additively, `ŷₖ = yₖ^true + log(Aₖ/A'ₖ)` (`Real.log_mul` on
`Iₖ/(gₖA'ₖ) = (Iₖ/(gₖAₖ))·(Aₖ/A'ₖ)`, all factors positive); `olsSlope` is linear in the ordinate;
and the true ordinate is affine in `Eₖ` with slope `−1/(k_B T)`
(`ForwardMap.boltzmann_plot_intensity` + `OLS.ols_recovers_line`).
EXACT: a cancellation identity, no approximation, no centering hypothesis. It is the SLOPE twin
of `Alt.olsDensity_aliasing_A` (which is the intercept/density statement), and it is what makes
the atomic-data error a *temperature* error, not only a density error. -/
theorem olsSlope_aliasing_A [Nonempty ι] {kB T N Fcal : ℝ} {g E A A' : ι → ℝ}
    (hg : ∀ k, 0 < g k) (hN : 0 < N) (hFcal : 0 < Fcal)
    (hA : ∀ k, 0 < A k) (hA' : ∀ k, 0 < A' k)
    (hvar : 0 < ∑ k, (E k - mean E) ^ 2) :
    olsSlope E (fun k => Real.log (lineIntensity kB T N Fcal g E A k / (g k * A' k)))
      = -(1 / (kB * T)) + olsSlope E (fun k => Real.log (A k / A' k)) := by
  have hsplit : (fun k => Real.log (lineIntensity kB T N Fcal g E A k / (g k * A' k)))
      = (fun k => Real.log (lineIntensity kB T N Fcal g E A k / (g k * A k))
          + Real.log (A k / A' k)) := by
    funext k
    have hI : 0 < lineIntensity kB T N Fcal g E A k := lineIntensity_pos hg hN hFcal hA k
    have hgk : 0 < g k := hg k
    have hAk : 0 < A k := hA k
    have hA'k : 0 < A' k := hA' k
    have hrw : lineIntensity kB T N Fcal g E A k / (g k * A' k)
        = (lineIntensity kB T N Fcal g E A k / (g k * A k)) * (A k / A' k) := by
      field_simp
    rw [hrw, Real.log_mul (by positivity) (by positivity)]
  rw [hsplit,
    hetero_olsSlope_add E (fun k => Real.log (lineIntensity kB T N Fcal g E A k / (g k * A k)))
      (fun k => Real.log (A k / A' k))]
  congr 1
  exact (ols_recovers_line
    (m0 := -(1 / (kB * T))) (b0 := Real.log (Fcal * N / partitionFunction kB T g E))
    (fun k => by rw [boltzmann_plot_intensity hg hN hFcal hA k]; ring) hvar).1

/-! ## The heterogeneous bound and its global specialization -/

/-- **HETEROGENEOUS atomic-data slope bound (the main result).** With a genuinely PER-LINE
relative transition-probability error `|A'ₖ − Aₖ| ≤ δₖ·Aₖ` (`δₖ < 1`), the Boltzmann-plot slope
recovered from the true spectrum with the wrong `A'` deviates from the true inverse temperature
by at most `heteroSlopeBound E δ = (∑ₖ |Eₖ − Ē|·δₖ/(1−δₖ)) / SS_E`.
Each line is charged its OWN budget, weighted by its OWN leverage: a line whose `A` is exact
(`δₖ = 0`) contributes nothing at all, which no single-`δ` bound can express.
Proof: the EXACT split `olsSlope_aliasing_A` reduces the claim to `|olsSlope E (log(A/A'))|`;
`Analysis.abs_log_ratio_le` turns each relative data error into an ordinate budget
`δₖ/(1−δₖ)`; `ErrorBudget.olsSlope_stable_hetero` (the per-line NOISE precedent, reused verbatim)
closes it against the zero ordinate.
REDUCED: it inherits the optically-thin single-temperature LTE forward map, and the two-sided
`δ/(1−δ)` transfer constant is the worse of the two log sides. -/
theorem olsSlope_aliasing_A_hetero [Nonempty ι] {kB T N Fcal : ℝ} {g E A A' δ : ι → ℝ}
    (hg : ∀ k, 0 < g k) (hN : 0 < N) (hFcal : 0 < Fcal)
    (hA : ∀ k, 0 < A k) (hA' : ∀ k, 0 < A' k)
    (hvar : 0 < ∑ k, (E k - mean E) ^ 2)
    (hδ1 : ∀ k, δ k < 1) (hpert : ∀ k, |A' k - A k| ≤ δ k * A k) :
    |olsSlope E (fun k => Real.log (lineIntensity kB T N Fcal g E A k / (g k * A' k)))
        - -(1 / (kB * T))|
      ≤ heteroSlopeBound E δ := by
  rw [olsSlope_aliasing_A hg hN hFcal hA hA' hvar]
  have hb := olsSlope_stable_hetero (E := E) (y := fun _ : ι => (0 : ℝ))
    (yHat := fun k => Real.log (A k / A' k)) (eps := fun k => δ k / (1 - δ k)) hvar
    (fun k => by
      rw [sub_zero]
      exact abs_log_ratio_le (hA k) (hA' k) (hδ1 k) (hpert k))
  rw [hetero_olsSlope_zero E, sub_zero] at hb
  have hsimp : -(1 / (kB * T)) + olsSlope E (fun k => Real.log (A k / A' k)) - -(1 / (kB * T))
      = olsSlope E (fun k => Real.log (A k / A' k)) := by ring
  rw [hsimp]
  simpa only [heteroSlopeBound] using hb

/-- **The GLOBAL lumped-`δ` bound, recovered as a corollary.** If every per-line budget is capped
by one worst-case `δmax < 1`, the heterogeneous bound implies the familiar single-`δ` bound
`|Δβ| ≤ (δmax/(1−δmax))·(∑ₖ |Eₖ − Ē|)/SS_E`. Together with the EQUALITY
`heteroSlopeBound_const` (constant `δ` gives exactly `globalSlopeBound`), this certifies that the
heterogeneous statement is a strict generalization of the lumped-`δ` model rather than a
different quantity.
REDUCED, for the same reasons as `olsSlope_aliasing_A_hetero`. -/
theorem olsSlope_aliasing_A_global [Nonempty ι] {kB T N Fcal dmax : ℝ} {g E A A' δ : ι → ℝ}
    (hg : ∀ k, 0 < g k) (hN : 0 < N) (hFcal : 0 < Fcal)
    (hA : ∀ k, 0 < A k) (hA' : ∀ k, 0 < A' k)
    (hvar : 0 < ∑ k, (E k - mean E) ^ 2)
    (hδ1 : ∀ k, δ k < 1) (hpert : ∀ k, |A' k - A k| ≤ δ k * A k)
    (hδmax : ∀ k, δ k ≤ dmax) (hmax1 : dmax < 1) :
    |olsSlope E (fun k => Real.log (lineIntensity kB T N Fcal g E A k / (g k * A' k)))
        - -(1 / (kB * T))|
      ≤ globalSlopeBound E dmax :=
  (olsSlope_aliasing_A_hetero hg hN hFcal hA hA' hvar hδ1 hpert).trans
    (heteroSlopeBound_le_global hvar hδmax hmax1)

/-- **Per-line atomic-data error ⇒ relative TEMPERATURE error.** The physics payload: composing
the heterogeneous slope bound with the exact temperature identity
(`ErrorBudget.temp_rel_error_le`), a per-line transition-probability budget `δₖ` propagates to
  `|T̂ − T|/T ≤ k_B·T̂·heteroSlopeBound E δ`.
`hslopeHat` identifies the analyst's recovered temperature `T̂` with the fitted (wrong-`A'`) slope
in the physical Boltzmann sign convention `slope = −1/(k_B T)`.
REDUCED, and honestly partial: `T̂` is a HYPOTHESIS (this bounds the error of whatever temperature
the analyst reads off the fitted slope; it does not construct `T̂` or prove one exists), the
`g`/`E` channels are excluded, and the resulting temperature error is NOT fed back into the
partition functions `U(T̂)` — that cross-channel coupling remains open (see `ErrorBudget.lean`). -/
theorem temp_rel_error_atomicData_hetero [Nonempty ι] {kB T THat N Fcal : ℝ}
    {g E A A' δ : ι → ℝ}
    (hkB : 0 < kB) (hT : 0 < T) (hTHat : 0 < THat)
    (hg : ∀ k, 0 < g k) (hN : 0 < N) (hFcal : 0 < Fcal)
    (hA : ∀ k, 0 < A k) (hA' : ∀ k, 0 < A' k)
    (hvar : 0 < ∑ k, (E k - mean E) ^ 2)
    (hδ1 : ∀ k, δ k < 1) (hpert : ∀ k, |A' k - A k| ≤ δ k * A k)
    (hslopeHat :
      olsSlope E (fun k => Real.log (lineIntensity kB T N Fcal g E A k / (g k * A' k)))
        = -(1 / (kB * THat))) :
    |THat - T| / T ≤ kB * THat * heteroSlopeBound E δ := by
  have hb := olsSlope_aliasing_A_hetero (kB := kB) (T := T) (N := N) (Fcal := Fcal)
    hg hN hFcal hA hA' hvar hδ1 hpert
  rw [hslopeHat] at hb
  have heq : -(1 / (kB * THat)) - -(1 / (kB * T)) = -(1 / (kB * THat) - 1 / (kB * T)) := by
    ring
  rw [heq, abs_neg] at hb
  exact temp_rel_error_le hkB hT hTHat hb

/-! ## Numerical witness — the heterogeneous bound is STRICTLY better

Two lines at energies `E = (0, 1)` (so `Ē = 1/2`, `SS_E = 1/2 > 0`) with per-line budgets
`δ = (0, 1/2)`: line 0's transition probability is EXACT, line 1 carries a 50% budget. The
worst-case global cap is `δmax = 1/2`. -/

private def nvHE : Fin 2 → ℝ := ![0, 1]
private noncomputable def nvHDelta : Fin 2 → ℝ := ![0, 1 / 2]

private theorem nvHE_mean : mean nvHE = 1 / 2 := by
  simp only [mean, nvHE, Fin.sum_univ_two, Fintype.card_fin]
  norm_num

private theorem nvHE_ss : ∑ k, (nvHE k - mean nvHE) ^ 2 = 1 / 2 := by
  rw [Fin.sum_univ_two, nvHE_mean]
  norm_num [nvHE]

private theorem nvHE_leverage0 : |nvHE 0 - mean nvHE| = 1 / 2 := by
  rw [nvHE_mean]
  have h : nvHE 0 - 1 / 2 = -(1 / 2) := by norm_num [nvHE]
  rw [h, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]

private theorem nvHE_leverage1 : |nvHE 1 - mean nvHE| = 1 / 2 := by
  rw [nvHE_mean]
  have h : nvHE 1 - 1 / 2 = 1 / 2 := by norm_num [nvHE]
  rw [h, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]

private theorem nvHE_abssum : ∑ k, |nvHE k - mean nvHE| = 1 := by
  rw [Fin.sum_univ_two, nvHE_leverage0, nvHE_leverage1]
  norm_num

private theorem nvH_heteroNum :
    ∑ k, |nvHE k - mean nvHE| * (nvHDelta k / (1 - nvHDelta k)) = 1 / 2 := by
  rw [Fin.sum_univ_two, nvHE_leverage0, nvHE_leverage1]
  norm_num [nvHDelta]

/-- **NON-VACUITY / strict-improvement witness (the point of the whole module).** On two lines at
`E = (0, 1)` with per-line budgets `δ = (0, 1/2)` — line 0's transition probability EXACT, line 1
at a 50% budget — the heterogeneous slope constant is `1` while the global constant at the same
worst-case cap `δmax = 1/2` is `2`. The heterogeneous bound is therefore **strictly** better here,
by a factor of two, and the numbers are exhibited rather than asserted. Both constants are
non-zero, so this is not a degenerate `0 ≤ 0` comparison; the improvement comes exactly from the
noiseless line, whose leverage `|E₀ − Ē| = 1/2` the global bound must still pay for. -/
theorem heteroSlopeBound_lt_global_witness :
    heteroSlopeBound nvHE nvHDelta = 1 ∧ globalSlopeBound nvHE (1 / 2) = 2
      ∧ heteroSlopeBound nvHE nvHDelta < globalSlopeBound nvHE (1 / 2) := by
  have hh : heteroSlopeBound nvHE nvHDelta = 1 := by
    rw [heteroSlopeBound, nvH_heteroNum, nvHE_ss]
    norm_num
  have hgl : globalSlopeBound nvHE (1 / 2) = 2 := by
    rw [globalSlopeBound, nvHE_abssum, nvHE_ss]
    norm_num
  refine ⟨hh, hgl, ?_⟩
  rw [hh, hgl]
  norm_num

/-- The witness data really does satisfy the hypotheses of `heteroSlopeBound_le_global`
(`δₖ ≤ 1/2 < 1`, `SS_E > 0`), so the two constants above are being compared on the SAME
scenario — the strict inequality is a genuine improvement, not a comparison of different setups. -/
example : heteroSlopeBound nvHE nvHDelta ≤ globalSlopeBound nvHE (1 / 2) :=
  heteroSlopeBound_le_global
    (by rw [nvHE_ss]; norm_num)
    (by intro k; fin_cases k <;> norm_num [nvHDelta])
    (by norm_num)

/-! ### Non-vacuity witness on a genuine physical spectrum

Two lines, `k_B = T = Fcal = 1`, `g = (1, 1)`, `E = (0, 1)`, TRUE transition probabilities
`A = (1, 2)`, tabulated (WRONG) `A' = (1, 3)` — line 0 EXACT, line 1 off by 50% — density `N = 2`,
and the genuinely per-line budget `δ = (0, 3/5)` (`|A'₁ − A₁| = 1 ≤ (3/5)·2 = 6/5`). All
positivity and `hvar` hypotheses hold, `A ≠ A'` so the perturbation is real, and the bound is
non-degenerate: `heteroSlopeBound nvHE nvPDelta = 3/2 ≠ 0`. -/

private def nvPg : Fin 2 → ℝ := ![1, 1]
private def nvPA : Fin 2 → ℝ := ![1, 2]
private def nvPA' : Fin 2 → ℝ := ![1, 3]
private noncomputable def nvPDelta : Fin 2 → ℝ := ![0, 3 / 5]

example :
    |olsSlope nvHE
        (fun k => Real.log (lineIntensity 1 1 2 1 nvPg nvHE nvPA k / (nvPg k * nvPA' k)))
      - -(1 / ((1 : ℝ) * 1))|
      ≤ heteroSlopeBound nvHE nvPDelta :=
  olsSlope_aliasing_A_hetero
    (kB := 1) (T := 1) (N := 2) (Fcal := 1)
    (g := nvPg) (E := nvHE) (A := nvPA) (A' := nvPA') (δ := nvPDelta)
    (by intro k; fin_cases k <;> norm_num [nvPg])
    (by norm_num) (by norm_num)
    (by intro k; fin_cases k <;> norm_num [nvPA])
    (by intro k; fin_cases k <;> norm_num [nvPA'])
    (by rw [nvHE_ss]; norm_num)
    (by intro k; fin_cases k <;> norm_num [nvPDelta])
    (by intro k; fin_cases k <;> norm_num [nvPA, nvPA', nvPDelta])

/-- The physical witness's bound is genuinely non-zero: `heteroSlopeBound = 3/2`, so the
preceding `example` is not a vacuous `|·| ≤ 0` statement. -/
theorem nvP_heteroSlopeBound_value : heteroSlopeBound nvHE nvPDelta = 3 / 2 := by
  have hnum : ∑ k, |nvHE k - mean nvHE| * (nvPDelta k / (1 - nvPDelta k)) = 3 / 4 := by
    rw [Fin.sum_univ_two, nvHE_leverage0, nvHE_leverage1]
    norm_num [nvPDelta]
  rw [heteroSlopeBound, hnum, nvHE_ss]
  norm_num

/-- The witness's per-line log-data-ratio slope, computed: line 0 contributes nothing
(`A₀ = A'₀`, so `log 1 = 0`) and the whole tilt comes from line 1, giving `log (2/3)`. -/
private theorem nvP_slope_shift :
    olsSlope nvHE (fun k => Real.log (nvPA k / nvPA' k)) = Real.log (2 / 3) := by
  rw [olsSlope_eq_centered, nvHE_ss, Fin.sum_univ_two, nvHE_mean]
  norm_num [nvHE, nvPA, nvPA']

/-- **The physical witness's slope bias is NOT zero** — the `example` above is bracketed by two
non-zero numbers, `0 < |Δβ| = |log (2/3)| ≤ 3/2`, not a `0 ≤ 3/2` collapse. On the witness data
the fitted slope is displaced from the true `−1/(k_B T) = −1` by EXACTLY `log (2/3) < 0`: the
wrong `A'₁ = 3` in place of `A₁ = 2` really does tilt the Boltzmann plot, so the recovered
temperature really is biased. Together with `nvP_heteroSlopeBound_value` this certifies that
`olsSlope_aliasing_A_hetero` is being exercised on a genuine perturbation. -/
theorem nvP_slope_bias_eq_log :
    olsSlope nvHE
        (fun k => Real.log (lineIntensity 1 1 2 1 nvPg nvHE nvPA k / (nvPg k * nvPA' k)))
        - -(1 / ((1 : ℝ) * 1)) = Real.log (2 / 3)
      ∧ Real.log (2 / 3) < 0 := by
  refine ⟨?_, Real.log_neg (by norm_num) (by norm_num)⟩
  rw [olsSlope_aliasing_A (kB := 1) (T := 1) (N := 2) (Fcal := 1)
      (g := nvPg) (E := nvHE) (A := nvPA) (A' := nvPA')
      (by intro k; fin_cases k <;> norm_num [nvPg]) (by norm_num) (by norm_num)
      (by intro k; fin_cases k <;> norm_num [nvPA])
      (by intro k; fin_cases k <;> norm_num [nvPA'])
      (by rw [nvHE_ss]; norm_num), nvP_slope_shift]
  ring

/-- The temperature the analyst reads off the biased witness fit: `T̂ = 1/(1 − log(2/3))`, the
unique positive solution of `−1/(k_B T̂) = fitted slope` at `k_B = 1`. -/
private noncomputable def nvPTHat : ℝ := 1 / (1 - Real.log (2 / 3))

private theorem nvPTHat_pos : 0 < nvPTHat := by
  have h : Real.log (2 / 3) < 0 := Real.log_neg (by norm_num) (by norm_num)
  exact div_pos one_pos (by linarith)

/-- **The hypotheses of `temp_rel_error_atomicData_hetero` are JOINTLY SATISFIABLE.** The
`hslopeHat` hypothesis is not idle decoration and not contradictory: on the physical witness it is
discharged by the explicit `T̂ = 1/(1 − log(2/3)) > 0` (true `T = 1`), so the composed temperature
statement is instantiated on data, not merely stated. This is the anti-vacuity check against a
conclusion that would otherwise be reachable from an unsatisfiable hypothesis set. -/
example : |nvPTHat - 1| / 1 ≤ 1 * nvPTHat * heteroSlopeBound nvHE nvPDelta :=
  temp_rel_error_atomicData_hetero
    (kB := 1) (T := 1) (THat := nvPTHat) (N := 2) (Fcal := 1)
    (g := nvPg) (E := nvHE) (A := nvPA) (A' := nvPA') (δ := nvPDelta)
    one_pos one_pos nvPTHat_pos
    (by intro k; fin_cases k <;> norm_num [nvPg])
    (by norm_num) (by norm_num)
    (by intro k; fin_cases k <;> norm_num [nvPA])
    (by intro k; fin_cases k <;> norm_num [nvPA'])
    (by rw [nvHE_ss]; norm_num)
    (by intro k; fin_cases k <;> norm_num [nvPDelta])
    (by intro k; fin_cases k <;> norm_num [nvPA, nvPA', nvPDelta])
    (by
      have hlog : Real.log (2 / 3) < 0 := Real.log_neg (by norm_num) (by norm_num)
      have h := nvP_slope_bias_eq_log.1
      change _ = -(1 / (1 * nvPTHat))
      rw [show nvPTHat = 1 / (1 - Real.log (2 / 3)) from rfl, one_mul, one_div_one_div]
      norm_num at h ⊢
      linarith)

end CflibsFormal
