/-
Copyright (c) 2026 Brian Squires. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Squires
-/
import Mathlib
import CflibsFormal.ForwardMap
import CflibsFormal.Closure
import CflibsFormal.OLS
import CflibsFormal.Analysis
import CflibsFormal.SelfAbsorption
import CflibsFormal.PartitionLipschitz
import CflibsFormal.SahaStability
import CflibsFormal.AtomicDataPerturbation

/-!
# CF-LIBS formalization — the reference-differenced (line-by-line) estimator

Measure a sample `s` and a matrix-similar **reference** `r` of *known* composition under
identical conditions (same temperature `T`, same calibration `Fcal`, same optical depth per line).
For every emission line `k` of a species, form the **per-line intensity ratio**

  `differentialRatio Is Ir k := Is k / Ir k`.

Substituting the optically-thin forward model `lineIntensity = Fcal · A_k · population` for
both spectra, *every* line-dependent and atomic-data factor cancels **line by line**:

  `Is k / Ir k = (Fcal·A_k·N_s·g_k·bf_k/U) / (Fcal·A_k·N_r·g_k·bf_k/U) = N_s / N_r`.

The estimator takes NO atomic-data inputs — no `A`, no `g`, no `E`, no `U(T)` — and that is the
entire point. `AtomicDataPerturbation.classicDensity_aliasing` proves that the classic single-line
reader, inverting a spectrum emitted with the true data `(g, E, A)` while *believing* the wrong
data `(g', E', A')`, returns `N · ρ_true/ρ_wrong` — a multiplicative bias with no self-diagnosing
signature. The differential ratio never consults the believed data, so that aliasing term is
identically absent (`differentialRatio_immune_to_atomicData` states the two side by side on the
*same* emitted spectrum and the *same* wrong belief).

Results:

* `differentialRatio_eq_density_ratio` — **EXACT.** Matched `(T, Fcal)`: the ratio is `N_s/N_r`
  for *every* line, with `Fcal`, `A_k`, `g_k`, the Boltzmann factor and `U(T)` all cancelling.
* `differentialRatio_immune_to_atomicData` — **EXACT.** The contrast: on one emitted spectrum
  and one wrong belief `(g', E', A')`, the classic reader is aliased while the differential
  ratio is `N_s/N_r`; the differential conjunct mentions no believed datum at all.
  `classic_biased_differential_exact` sharpens this to `N̂_classic ≠ N_s` whenever the believed
  response factor differs from the true one.
* `logDifferentialRatio_affine_in_E` — **EXACT, unmatched `T`.** With `β := 1/(k_B T)`,
  `log (I_s k / I_r k) = log (N_s/N_r) + log (U_r/U_s) − E_k·(β_s − β_r)`: affine in `E_k` with
  slope `−(β_s − β_r)`. Still no `A`, `g`, `Fcal`. Hence a *differential Boltzmann plot*:
  `differentialSlope_eq_neg_dbeta` (OLS over any line set with positive energy spread) and
  `differentialSlope_two_lines` (two lines, `E 0 ≠ E 1`) recover `Δβ` from the slope.
* `differentialRatio_error_bound` — **REDUCED, first order in `|T_s − T_r|`.** On a temperature
  floor `Tmin`, `|log (I_s k/I_r k) − log (N_s/N_r)| ≤ (|E_k| + (∑ g_j E_j)/U(Tmin))·δ/(k_B Tmin²)`
  whenever `|T_s − T_r| ≤ δ`. Explicit constants only: the inverse-temperature leg uses
  `Analysis.inv_kT_sub_le`, the partition-function leg uses
  `PartitionLipschitz.partitionFunction_lipschitz_temp` and the floor `U(Tmin) ≤ U(T)`.
* `differentialRatio_selfAbsorption_residual` — **EXACT, honest non-cancellation.** With
  measured intensities `I · SA(τ)`, the ratio is `N_s/N_r · SA(τ_s k)/SA(τ_r k)`;
  `differentialRatio_selfAbsorption_cancels_iff` shows the residual is `1` **iff**
  `τ_s k = τ_r k`. Matched optical depth is a *hypothesis*, not a consequence.
* `differentialComposition` / `differentialComposition_exact_of_matched` — **EXACT.** Feeding
  the per-element ratios and the reference's known composition through the closure recovers
  the sample composition exactly under matched `(T, Fcal, τ)`.

## Literature and scope

**This is NOT calibration-free.** The estimator requires one reference sample of *known*
composition measured under the same conditions — exactly as one-point-calibration (OPC) schemes
do. Its claim is **immunity to atomic-data error**, not standardlessness: what cancels is the
atomic data `(A, g, E, U)` and the instrument factor `Fcal`, and it cancels *because* the same
factors multiply both spectra, not because they are known. Anything that differs between the two
measurements — temperature, optical depth, matrix — does **not** cancel, and the results above
say so explicitly (`logDifferentialRatio_affine_in_E`, `differentialRatio_error_bound`,
`differentialRatio_selfAbsorption_residual`).

The idea is the LIBS transcription of *differential* stellar abundance analysis, where a target
star is analysed line-by-line relative to a reference star of similar parameters so that model
and atomic-data systematics cancel to first order:

* Meléndez, Asplund, Gustafsson & Yong (2009), ApJ 704, L66 — DOI 10.1088/0004-637X/704/1/L66
  (verified via Crossref).
* Bedell, Meléndez, Bean, Ramírez, Leite & Asplund (2014), ApJ 795, 23 —
  DOI 10.1088/0004-637X/795/1/23 (verified via Crossref).
* Nissen & Gustafsson (2018), A&ARv 26, 6 — DOI 10.1007/s00159-018-0111-3 (verified via
  Crossref / Springer).

Those papers report *empirical* precision gains; nothing of that kind is formalized here. What is
proven is the algebraic cancellation (and its precise failure modes) in the CF-LIBS forward model
of Ciucci et al. 1999 (`ForwardMap.lineIntensity`), so the `EXACT` rows cite "Ciucci 1999" (the
forward model) or "—" (pure algebra), and the `REDUCED` first-order bound cites the repo-wide
string "Aguilera & Aragón 2007" (multi-element Saha–Boltzmann error budgets), as the scope-tag
table does for `combinedSahaBoltzmannSlope`; no bibliographic detail is re-asserted for it here.

Scope: single-zone LTE, optically thin or curve-of-growth-corrected lines, one species per
`ι`, the reference and sample sharing the *same* level set and Einstein coefficients (the same
species). No noise model is attached; the noise transfer of a two-spectrum ratio is out of scope.
-/

namespace CflibsFormal

open Finset Real
open scoped BigOperators

variable {ι : Type*} [Fintype ι]
variable {κ : Type*} [Fintype κ]

/-- **The differential (reference-differenced) estimator.** The per-line ratio of the sample
intensity to the reference intensity, `Is k / Ir k`. It takes NO atomic-data inputs — no `A`,
`g`, `E`, or `U(T)` — and no calibration constant: it is a function of the two spectra alone.
That absence is the whole content of the immunity results below. -/
noncomputable def differentialRatio (Is Ir : ι → ℝ) (k : ι) : ℝ := Is k / Ir k

/-- **EXACT line-by-line cancellation (matched `T`, `Fcal`).** For a sample of density `N_s` and
a reference of density `N_r` of the same species, emitted at the same temperature with the same
calibration and the same (true) atomic data, the differential ratio of EVERY line is `N_s / N_r`:
  `(Fcal·A_k·N_s·g_k·bf_k/U) / (Fcal·A_k·N_r·g_k·bf_k/U) = N_s/N_r`.
`Fcal`, `A_k`, `g_k`, the Boltzmann factor and the partition function all cancel *per line*
(contrast `Identifiability.lineIntensity_ratio_closed_form`, the ratio *across* lines of one
spectrum, where `g_j A_j/(g_i A_i)` survives). No positivity of `N_s` is needed; `N_r > 0` keeps
the reference line nonzero. The forward model is that of Ciucci et al. 1999. -/
theorem differentialRatio_eq_density_ratio [Nonempty ι] {kB T Ns Nr Fcal : ℝ} {g E A : ι → ℝ}
    (hg : ∀ k, 0 < g k) (hNr : 0 < Nr) (hFcal : 0 < Fcal) (hA : ∀ k, 0 < A k) (k : ι) :
    differentialRatio (lineIntensity kB T Ns Fcal g E A) (lineIntensity kB T Nr Fcal g E A) k
      = Ns / Nr := by
  have hU : partitionFunction kB T g E ≠ 0 := (partitionFunction_pos hg).ne'
  have hgk : g k ≠ 0 := (hg k).ne'
  have hAk : A k ≠ 0 := (hA k).ne'
  have hF : Fcal ≠ 0 := hFcal.ne'
  have hbf : boltzmannFactor kB T (E k) ≠ 0 := (boltzmannFactor_pos _ _ _).ne'
  have hNrne : Nr ≠ 0 := hNr.ne'
  unfold differentialRatio lineIntensity population
  field_simp

/-- **EXACT immunity to atomic-data error — the contrast with `classicDensity_aliasing`.**
One spectrum, emitted with the TRUE data `(g, E, A)` at density `N_s`; one analyst who BELIEVES
the wrong data `(g', E', A')`. The classic single-line reader returns the aliased
`N_s · ρ_true/ρ_wrong` (first conjunct — verbatim `classicDensity_aliasing`), while the
differential ratio against a reference of density `N_r` returns `N_s/N_r` (second conjunct).

Why this is the whole result and not a triviality: the second conjunct literally does not
mention `g'`, `E'`, or `A'`. The differential estimator has no slot for the believed data, so the
aliasing factor `ρ_true/ρ_wrong` — an *arbitrary* multiplicative bias with no self-diagnosing
signature in the classic method — cannot enter it at all. The immunity is structural (a property
of the estimator's *inputs*), not a cancellation that happens to hold for correct data. What it
does NOT buy is standardlessness: `N_r` must be known independently. -/
theorem differentialRatio_immune_to_atomicData [Nonempty ι]
    {kB T Ns Nr Fcal : ℝ} {g E A g' E' A' : ι → ℝ}
    (hg : ∀ k, 0 < g k) (hg' : ∀ k, 0 < g' k) (hNr : 0 < Nr) (hFcal : 0 < Fcal)
    (hA : ∀ k, 0 < A k) (k : ι) (hA' : 0 < A' k) :
    Classic.classicDensity kB T Fcal g' E' A' k (lineIntensity kB T Ns Fcal g E A k)
        = Ns * responseFactor kB T g E A k / responseFactor kB T g' E' A' k
      ∧ differentialRatio (lineIntensity kB T Ns Fcal g E A)
          (lineIntensity kB T Nr Fcal g E A) k = Ns / Nr :=
  ⟨classicDensity_aliasing hg hg' hFcal k hA',
    differentialRatio_eq_density_ratio hg hNr hFcal hA k⟩

/-- **EXACT: the classic reader is actually biased, the differential one is not.** Sharpening of
`differentialRatio_immune_to_atomicData`: whenever the believed response factor differs from the
true one (`ρ_wrong ≠ ρ_true` — e.g. any wrong `A'_k`), the classic recovered density is *not*
`N_s`, while on the same spectrum the differential ratio is exactly `N_s/N_r`. -/
theorem classic_biased_differential_exact [Nonempty ι]
    {kB T Ns Nr Fcal : ℝ} {g E A g' E' A' : ι → ℝ}
    (hg : ∀ k, 0 < g k) (hg' : ∀ k, 0 < g' k) (hNs : 0 < Ns) (hNr : 0 < Nr) (hFcal : 0 < Fcal)
    (hA : ∀ k, 0 < A k) (k : ι) (hA' : 0 < A' k)
    (hρ : responseFactor kB T g' E' A' k ≠ responseFactor kB T g E A k) :
    Classic.classicDensity kB T Fcal g' E' A' k (lineIntensity kB T Ns Fcal g E A k) ≠ Ns
      ∧ differentialRatio (lineIntensity kB T Ns Fcal g E A)
          (lineIntensity kB T Nr Fcal g E A) k = Ns / Nr := by
  refine ⟨?_, differentialRatio_eq_density_ratio hg hNr hFcal hA k⟩
  have hρ'pos : 0 < responseFactor kB T g' E' A' k := by
    unfold responseFactor
    exact div_pos (mul_pos (mul_pos (hg' k) hA') (boltzmannFactor_pos _ _ _))
      (partitionFunction_pos hg')
  rw [classicDensity_aliasing hg hg' hFcal k hA', mul_div_assoc, Ne, mul_eq_left₀ hNs.ne',
    div_eq_one_iff_eq hρ'pos.ne']
  exact fun h => hρ h.symm

/-- **EXACT: the differential Boltzmann plot (unmatched temperatures).** With sample and
reference at temperatures `T_s`, `T_r` and inverse temperatures `β_x := 1/(k_B T_x)`,
  `log (I_s k / I_r k) = log (N_s/N_r) + log (U_r/U_s) − E_k · (β_s − β_r)`,
where `U_x = partitionFunction kB T_x g E`. The log-ratio is *affine in the level energy* with
slope `−(β_s − β_r)` and an intercept carrying the density ratio and the partition-function
ratio. Still no `A_k`, `g_k`, or `Fcal` — those cancel line by line regardless of `T`. So a
two-spectrum Boltzmann plot of `log (I_s/I_r)` against `E_k` reads off the temperature
*mismatch*; at `T_s = T_r` the slope is `0` and the intercept collapses to `log (N_s/N_r)`
(`differentialRatio_eq_density_ratio`). Forward model: Ciucci et al. 1999. -/
theorem logDifferentialRatio_affine_in_E [Nonempty ι]
    {kB Ts Tr Ns Nr Fcal : ℝ} {g E A : ι → ℝ}
    (hg : ∀ k, 0 < g k) (hNs : 0 < Ns) (hNr : 0 < Nr) (hFcal : 0 < Fcal) (hA : ∀ k, 0 < A k)
    (k : ι) :
    Real.log (differentialRatio (lineIntensity kB Ts Ns Fcal g E A)
        (lineIntensity kB Tr Nr Fcal g E A) k)
      = Real.log (Ns / Nr)
        + Real.log (partitionFunction kB Tr g E / partitionFunction kB Ts g E)
        - E k * (1 / (kB * Ts) - 1 / (kB * Tr)) := by
  have hUs : 0 < partitionFunction kB Ts g E := partitionFunction_pos hg
  have hUr : 0 < partitionFunction kB Tr g E := partitionFunction_pos hg
  have hgk : g k ≠ 0 := (hg k).ne'
  have hAk : A k ≠ 0 := (hA k).ne'
  have hF : Fcal ≠ 0 := hFcal.ne'
  have hexp : Real.exp (-(E k * (1 / (kB * Ts) - 1 / (kB * Tr))))
      = Real.exp (-E k / (kB * Ts)) / Real.exp (-E k / (kB * Tr)) := by
    rw [← Real.exp_sub]; congr 1; ring
  have hsplit : differentialRatio (lineIntensity kB Ts Ns Fcal g E A)
        (lineIntensity kB Tr Nr Fcal g E A) k
      = (Ns / Nr) * (partitionFunction kB Tr g E / partitionFunction kB Ts g E)
          * Real.exp (-(E k * (1 / (kB * Ts) - 1 / (kB * Tr)))) := by
    rw [hexp]
    simp only [differentialRatio, lineIntensity, population, boltzmannFactor]
    field_simp
  rw [hsplit,
    Real.log_mul (mul_pos (div_pos hNs hNr) (div_pos hUr hUs)).ne' (Real.exp_ne_zero _),
    Real.log_mul (div_pos hNs hNr).ne' (div_pos hUr hUs).ne', Real.log_exp]
  ring

/-- **EXACT: OLS on the differential Boltzmann plot recovers `−Δβ`.** Fitting
`y_k := log (I_s k / I_r k)` against `E_k` by ordinary least squares over any line set with
positive energy spread (`OLS.olsSlope`, `OLS.ols_recovers_line`) returns the slope
`−(β_s − β_r) = −(1/(k_B T_s) − 1/(k_B T_r))` and the intercept
`log (N_s/N_r) + log (U_r/U_s)` exactly — because `logDifferentialRatio_affine_in_E` makes the
ordinates exactly collinear. No atomic data enter the ordinates. -/
theorem differentialSlope_eq_neg_dbeta [Nonempty ι]
    {kB Ts Tr Ns Nr Fcal : ℝ} {g E A : ι → ℝ}
    (hg : ∀ k, 0 < g k) (hNs : 0 < Ns) (hNr : 0 < Nr) (hFcal : 0 < Fcal) (hA : ∀ k, 0 < A k)
    (hvar : 0 < ∑ k, (E k - mean E) ^ 2) :
    olsSlope E (fun k => Real.log (differentialRatio (lineIntensity kB Ts Ns Fcal g E A)
          (lineIntensity kB Tr Nr Fcal g E A) k))
        = -(1 / (kB * Ts) - 1 / (kB * Tr))
      ∧ olsIntercept E (fun k => Real.log (differentialRatio (lineIntensity kB Ts Ns Fcal g E A)
          (lineIntensity kB Tr Nr Fcal g E A) k))
        = Real.log (Ns / Nr)
          + Real.log (partitionFunction kB Tr g E / partitionFunction kB Ts g E) := by
  refine ols_recovers_line (fun k => ?_) hvar
  rw [logDifferentialRatio_affine_in_E hg hNs hNr hFcal hA k]
  ring

/-- **EXACT two-line differential slope.** The two-line specialization of
`differentialSlope_eq_neg_dbeta`: with exactly two lines of distinct energy (`E 0 ≠ E 1`, which
is precisely the positive-spread condition for `Fin 2`), the OLS slope of the differential
Boltzmann plot is `−(β_s − β_r)`. This is the differential analogue of
`ForwardMap.temperature_from_two_lines`, with `Δβ` in place of `β`. -/
theorem differentialSlope_two_lines {kB Ts Tr Ns Nr Fcal : ℝ} {g E A : Fin 2 → ℝ}
    (hg : ∀ k, 0 < g k) (hNs : 0 < Ns) (hNr : 0 < Nr) (hFcal : 0 < Fcal) (hA : ∀ k, 0 < A k)
    (hE : E 0 ≠ E 1) :
    olsSlope E (fun k => Real.log (differentialRatio (lineIntensity kB Ts Ns Fcal g E A)
          (lineIntensity kB Tr Nr Fcal g E A) k))
      = -(1 / (kB * Ts) - 1 / (kB * Tr)) := by
  have hmean : mean E = (E 0 + E 1) / 2 := by
    unfold mean; rw [show (Fintype.card (Fin 2) : ℝ) = 2 by simp, Fin.sum_univ_two]
  have hvar : 0 < ∑ k, (E k - mean E) ^ 2 := by
    have hd : E 0 - E 1 ≠ 0 := sub_ne_zero.mpr hE
    have hsq : (∑ k, (E k - mean E) ^ 2) = (E 0 - E 1) ^ 2 / 2 := by
      rw [Fin.sum_univ_two, hmean]; ring
    rw [hsq]; positivity
  exact (differentialSlope_eq_neg_dbeta hg hNs hNr hFcal hA hvar).1

/-- **Two-sided log floor bound (PURE-MATH).** For `a, b ≥ m > 0`,
`|log a − log b| ≤ |a − b| / m`. Each side is `log (x/y) ≤ x/y − 1 = (x − y)/y ≤ |x − y|/m`
(`Real.log_le_sub_one_of_pos`), the floor `m` replacing the denominator `y ≥ m`. -/
private lemma abs_log_sub_log_le_of_floor {a b m : ℝ} (hm : 0 < m) (ha : m ≤ a) (hb : m ≤ b) :
    |Real.log a - Real.log b| ≤ |a - b| / m := by
  have key : ∀ {x y : ℝ}, m ≤ x → m ≤ y → Real.log x - Real.log y ≤ |x - y| / m := by
    intro x y hx hy
    have hx0 : 0 < x := lt_of_lt_of_le hm hx
    have hy0 : 0 < y := lt_of_lt_of_le hm hy
    rw [← Real.log_div hx0.ne' hy0.ne']
    calc Real.log (x / y) ≤ x / y - 1 := Real.log_le_sub_one_of_pos (div_pos hx0 hy0)
      _ = (x - y) / y := by field_simp
      _ ≤ |x - y| / y := div_le_div_of_nonneg_right (le_abs_self _) hy0.le
      _ ≤ |x - y| / m := div_le_div_of_nonneg_left (abs_nonneg _) hm hy
  rw [abs_sub_le_iff]
  refine ⟨key ha hb, ?_⟩
  rw [abs_sub_comm]
  exact key hb ha

/-- **REDUCED first-order error bound for an unmatched temperature.** On a temperature floor
`0 < Tmin ≤ T_s, T_r`, with `k_B > 0`, `g_k > 0`, level energies `E_k ≥ 0` and
`|T_s − T_r| ≤ δ`, the differential log-ratio deviates from `log (N_s/N_r)` by at most
  `(|E_k| + (∑_j g_j E_j) / U(Tmin)) · δ / (k_B Tmin²)`.
Derivation (all constants explicit): by `logDifferentialRatio_affine_in_E` the deviation is
`log (U_r/U_s) − E_k (β_s − β_r)`; the inverse-temperature leg is `|β_s − β_r| ≤ δ/(k_B Tmin²)`
(`Analysis.inv_kT_sub_le`, the mean-value bound on `1/(k_B T)`); the partition-function leg is
`|log U_r − log U_s| ≤ |U_r − U_s|/U(Tmin) ≤ (∑ g_j E_j)/(k_B Tmin²) · δ / U(Tmin)`, using the
Lipschitz constant of `PartitionLipschitz.partitionFunction_lipschitz_temp` and the floor
`U(Tmin) ≤ U(T)` for `T ≥ Tmin` (`SahaStability.partitionFunction_mono_temp`, valid because
`E_k ≥ 0`). Reduction: the bound is a first-order (Lipschitz) envelope in `|T_s − T_r|` with
`Tmin`-floor over-estimates in both legs; the identity it starts from is exact. -/
theorem differentialRatio_error_bound [Nonempty ι]
    {kB Tmin Ts Tr Ns Nr Fcal δ : ℝ} {g E A : ι → ℝ}
    (hkB : 0 < kB) (hTmin : 0 < Tmin) (hTs : Tmin ≤ Ts) (hTr : Tmin ≤ Tr)
    (hg : ∀ k, 0 < g k) (hE : ∀ k, 0 ≤ E k) (hNs : 0 < Ns) (hNr : 0 < Nr)
    (hFcal : 0 < Fcal) (hA : ∀ k, 0 < A k) (hδ : |Ts - Tr| ≤ δ) (k : ι) :
    |Real.log (differentialRatio (lineIntensity kB Ts Ns Fcal g E A)
          (lineIntensity kB Tr Nr Fcal g E A) k) - Real.log (Ns / Nr)|
      ≤ (|E k| + (∑ j, g j * E j) / partitionFunction kB Tmin g E) / (kB * Tmin ^ 2) * δ := by
  have hUmin : 0 < partitionFunction kB Tmin g E := partitionFunction_pos hg
  have hUs : partitionFunction kB Tmin g E ≤ partitionFunction kB Ts g E :=
    partitionFunction_mono_temp hkB hTmin hTs hg hE
  have hUr : partitionFunction kB Tmin g E ≤ partitionFunction kB Tr g E :=
    partitionFunction_mono_temp hkB hTmin hTr hg hE
  have hUspos : 0 < partitionFunction kB Ts g E := lt_of_lt_of_le hUmin hUs
  have hUrpos : 0 < partitionFunction kB Tr g E := lt_of_lt_of_le hUmin hUr
  have hden : 0 < kB * Tmin ^ 2 := mul_pos hkB (pow_pos hTmin 2)
  have hsum : 0 ≤ ∑ j, g j * E j :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (hg j).le (hE j))
  rw [logDifferentialRatio_affine_in_E hg hNs hNr hFcal hA k]
  have hrw : Real.log (Ns / Nr)
        + Real.log (partitionFunction kB Tr g E / partitionFunction kB Ts g E)
        - E k * (1 / (kB * Ts) - 1 / (kB * Tr)) - Real.log (Ns / Nr)
      = (Real.log (partitionFunction kB Tr g E) - Real.log (partitionFunction kB Ts g E))
        + (-(E k * (1 / (kB * Ts) - 1 / (kB * Tr)))) := by
    rw [Real.log_div hUrpos.ne' hUspos.ne']; ring
  rw [hrw]
  -- inverse-temperature leg
  have hβ : |E k * (1 / (kB * Ts) - 1 / (kB * Tr))| ≤ |E k| * (δ / (kB * Tmin ^ 2)) := by
    rw [abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    calc |1 / (kB * Ts) - 1 / (kB * Tr)| ≤ |Ts - Tr| / (kB * Tmin ^ 2) :=
          inv_kT_sub_le hkB hTmin hTs hTr
      _ ≤ δ / (kB * Tmin ^ 2) := div_le_div_of_nonneg_right hδ hden.le
  -- partition-function leg
  have hU : |Real.log (partitionFunction kB Tr g E) - Real.log (partitionFunction kB Ts g E)|
      ≤ (∑ j, g j * E j) / (kB * Tmin ^ 2) * δ / partitionFunction kB Tmin g E := by
    calc |Real.log (partitionFunction kB Tr g E) - Real.log (partitionFunction kB Ts g E)|
        ≤ |partitionFunction kB Tr g E - partitionFunction kB Ts g E|
            / partitionFunction kB Tmin g E :=
          abs_log_sub_log_le_of_floor hUmin hUr hUs
      _ ≤ (∑ j, g j * E j) / (kB * Tmin ^ 2) * |Tr - Ts| / partitionFunction kB Tmin g E :=
          div_le_div_of_nonneg_right
            (partitionFunction_lipschitz_temp hkB hTmin hTr hTs hg hE) hUmin.le
      _ ≤ (∑ j, g j * E j) / (kB * Tmin ^ 2) * δ / partitionFunction kB Tmin g E := by
          refine div_le_div_of_nonneg_right ?_ hUmin.le
          refine mul_le_mul_of_nonneg_left ?_ (div_nonneg hsum hden.le)
          rw [abs_sub_comm]; exact hδ
  calc |(Real.log (partitionFunction kB Tr g E) - Real.log (partitionFunction kB Ts g E))
        + (-(E k * (1 / (kB * Ts) - 1 / (kB * Tr))))|
      ≤ |Real.log (partitionFunction kB Tr g E) - Real.log (partitionFunction kB Ts g E)|
          + |-(E k * (1 / (kB * Ts) - 1 / (kB * Tr)))| := abs_add_le _ _
    _ = |Real.log (partitionFunction kB Tr g E) - Real.log (partitionFunction kB Ts g E)|
          + |E k * (1 / (kB * Ts) - 1 / (kB * Tr))| := by rw [abs_neg]
    _ ≤ (∑ j, g j * E j) / (kB * Tmin ^ 2) * δ / partitionFunction kB Tmin g E
          + |E k| * (δ / (kB * Tmin ^ 2)) := add_le_add hU hβ
    _ = (|E k| + (∑ j, g j * E j) / partitionFunction kB Tmin g E) / (kB * Tmin ^ 2) * δ := by
          ring

/-- **EXACT self-absorption residual — the honest non-cancellation.** If the measured
intensities are the curve-of-growth-corrected `I · SA(τ)` (`SelfAbsorption.selfAbsorbedIntensity`)
with per-line optical depths `τ_s k` (sample) and `τ_r k` (reference), then at matched `(T, Fcal)`
  `I_s k / I_r k = N_s/N_r · SA(τ_s k) / SA(τ_r k)`.
The optical-depth factor does NOT cancel: unlike `A_k`, `g_k`, `U`, it is a property of each
*sample*, not of the species. Matched optical depth is a hypothesis to be certified, not a
consequence of using a reference. (No sign hypothesis on `τ` is needed for the identity itself —
it is a pure regrouping of the two products.) -/
theorem differentialRatio_selfAbsorption_residual [Nonempty ι]
    {kB T Ns Nr Fcal : ℝ} {g E A τs τr : ι → ℝ}
    (hg : ∀ k, 0 < g k) (hNr : 0 < Nr) (hFcal : 0 < Fcal) (hA : ∀ k, 0 < A k) (k : ι) :
    differentialRatio (fun j => selfAbsorbedIntensity kB T Ns Fcal g E A j (τs j))
        (fun j => selfAbsorbedIntensity kB T Nr Fcal g E A j (τr j)) k
      = Ns / Nr * (selfAbsorptionFactor (τs k) / selfAbsorptionFactor (τr k)) := by
  have h := differentialRatio_eq_density_ratio (kB := kB) (T := T) (Ns := Ns) (E := E)
    hg hNr hFcal hA k
  simp only [differentialRatio] at h
  simp only [differentialRatio, selfAbsorbedIntensity]
  rw [mul_div_mul_comm, h]

/-- `SA(τ) < 1` strictly for `τ > 0` (`Real.add_one_lt_exp`). Private helper for injectivity
of the escape factor on `[0, ∞)`. -/
private lemma selfAbsorptionFactor_lt_one_of_pos {tau : ℝ} (h : 0 < tau) :
    selfAbsorptionFactor tau < 1 := by
  unfold selfAbsorptionFactor
  rw [if_neg h.ne', div_lt_one h]
  have := Real.add_one_lt_exp (neg_ne_zero.mpr h.ne')
  linarith

/-- The escape factor is injective on `[0, ∞)`: strict antitonicity on `(0, ∞)`
(`selfAbsorptionFactor_strictAntiOn`) plus `SA 0 = 1 > SA τ` for `τ > 0`. Private helper. -/
private lemma selfAbsorptionFactor_injOn_nonneg :
    Set.InjOn selfAbsorptionFactor (Set.Ici 0) := by
  intro a ha b hb hab
  rcases (Set.mem_Ici.mp ha).eq_or_lt with ha0 | ha0
  · rcases (Set.mem_Ici.mp hb).eq_or_lt with hb0 | hb0
    · rw [← ha0, ← hb0]
    · exfalso
      have h1 : selfAbsorptionFactor a = 1 := by
        rw [← ha0, selfAbsorptionFactor, if_pos rfl]
      have h2 := selfAbsorptionFactor_lt_one_of_pos hb0
      rw [hab] at h1
      linarith
  · rcases (Set.mem_Ici.mp hb).eq_or_lt with hb0 | hb0
    · exfalso
      have h1 : selfAbsorptionFactor b = 1 := by
        rw [← hb0, selfAbsorptionFactor, if_pos rfl]
      have h2 := selfAbsorptionFactor_lt_one_of_pos ha0
      rw [← hab] at h1
      linarith
    · exact selfAbsorptionFactor_strictAntiOn.injOn (Set.mem_Ioi.mpr ha0)
        (Set.mem_Ioi.mpr hb0) hab

/-- **EXACT: the residual cancels iff the optical depths match.** With non-negative optical
depths on line `k`, the self-absorbed differential ratio equals `N_s/N_r` **if and only if**
`τ_s k = τ_r k`. The "if" is the trivial `SA(τ)/SA(τ) = 1`; the "only if" is the strict
monotonicity of the escape factor (`selfAbsorptionFactor_strictAntiOn`), so no *other* pair of
optical depths can hide inside a clean-looking ratio. This is what makes matched optical depth
a genuine hypothesis of `differentialComposition_exact_of_matched`. -/
theorem differentialRatio_selfAbsorption_cancels_iff [Nonempty ι]
    {kB T Ns Nr Fcal : ℝ} {g E A τs τr : ι → ℝ}
    (hg : ∀ k, 0 < g k) (hNs : 0 < Ns) (hNr : 0 < Nr) (hFcal : 0 < Fcal) (hA : ∀ k, 0 < A k)
    (k : ι) (hτs : 0 ≤ τs k) (hτr : 0 ≤ τr k) :
    differentialRatio (fun j => selfAbsorbedIntensity kB T Ns Fcal g E A j (τs j))
        (fun j => selfAbsorbedIntensity kB T Nr Fcal g E A j (τr j)) k = Ns / Nr
      ↔ τs k = τr k := by
  rw [differentialRatio_selfAbsorption_residual hg hNr hFcal hA k,
    mul_eq_left₀ (div_pos hNs hNr).ne',
    div_eq_one_iff_eq (selfAbsorptionFactor_pos hτr).ne']
  exact ⟨fun h => selfAbsorptionFactor_injOn_nonneg (Set.mem_Ici.mpr hτs)
    (Set.mem_Ici.mpr hτr) h, fun h => by rw [h]⟩

/-- **EXACT: matched optical depth restores the clean ratio.** If sample and reference share the
same per-line optical depth `τ k ≥ 0` (in particular `τ = 0`, the optically-thin case), the
self-absorbed differential ratio is `N_s/N_r` on every line. -/
theorem differentialRatio_selfAbsorbed_matched [Nonempty ι]
    {kB T Ns Nr Fcal : ℝ} {g E A τ : ι → ℝ}
    (hg : ∀ k, 0 < g k) (hNr : 0 < Nr) (hFcal : 0 < Fcal) (hA : ∀ k, 0 < A k)
    (hτ : ∀ k, 0 ≤ τ k) (k : ι) :
    differentialRatio (fun j => selfAbsorbedIntensity kB T Ns Fcal g E A j (τ j))
        (fun j => selfAbsorbedIntensity kB T Nr Fcal g E A j (τ j)) k = Ns / Nr := by
  rw [differentialRatio_selfAbsorption_residual hg hNr hFcal hA k,
    div_self (selfAbsorptionFactor_pos (hτ k)).ne', mul_one]

/-- **Differential composition from a reference of KNOWN composition.** Given the reference's
number fractions `Cr` and the per-element differential ratios `R s = N_s(s)/N_r(s)`, the sample
composition is the closure of `Cr s · R s`:
  `C_s(sample) = Cr s · R s / ∑_t Cr t · R t`
(`Closure.composition` applied to the rescaled reference). This is NOT calibration-free: `Cr`
is an external input — one reference of known composition, as in one-point calibration. The
claim is immunity to atomic-data error (no `A`, `g`, `E`, `U` anywhere in `R`), not
standardlessness. -/
noncomputable def differentialComposition (Cr R : κ → ℝ) (s : κ) : ℝ :=
  composition (fun t => Cr t * R t) s

/-- **EXACT composition recovery under matched `(T, Fcal, τ)`.** Each species `s` is read on
its chosen line `u s`, emitted at the same `T`, `Fcal`, and per-line optical depth `τ s` in both
spectra; the reference densities `Nr` are unknown *individually* but their composition
`composition Nr` is known. Then the differential composition equals the true sample composition
`composition Ns s` exactly. Proof: every ratio is `Ns s / Nr s`
(`differentialRatio_selfAbsorbed_matched`), so `Cr s · R s = Ns s / N_tot(r)`, a common rescaling
that `composition_smul_invariant` removes. Matched `τ` is a hypothesis
(`differentialRatio_selfAbsorption_cancels_iff` shows it cannot be dropped), and so is a matched
temperature (`logDifferentialRatio_affine_in_E` shows the slope `−Δβ` that otherwise appears). -/
theorem differentialComposition_exact_of_matched [Nonempty ι] [Nonempty κ]
    {kB T Fcal : ℝ} {Ns Nr : κ → ℝ} {g E A τ : κ → ι → ℝ} {u : κ → ι}
    (hg : ∀ s k, 0 < g s k) (hNr : ∀ s, 0 < Nr s) (hFcal : 0 < Fcal)
    (hA : ∀ s k, 0 < A s k) (hτ : ∀ s k, 0 ≤ τ s k) (s : κ) :
    differentialComposition (composition Nr)
        (fun t => differentialRatio
          (fun j => selfAbsorbedIntensity kB T (Ns t) Fcal (g t) (E t) (A t) j (τ t j))
          (fun j => selfAbsorbedIntensity kB T (Nr t) Fcal (g t) (E t) (A t) j (τ t j))
          (u t)) s
      = composition Ns s := by
  have hR : ∀ t, differentialRatio
      (fun j => selfAbsorbedIntensity kB T (Ns t) Fcal (g t) (E t) (A t) j (τ t j))
      (fun j => selfAbsorbedIntensity kB T (Nr t) Fcal (g t) (E t) (A t) j (τ t j)) (u t)
      = Ns t / Nr t :=
    fun t => differentialRatio_selfAbsorbed_matched (hg t) (hNr t) hFcal (hA t) (hτ t) (u t)
  have hStot : 0 < totalDensity Nr := totalDensity_pos hNr
  simp only [differentialComposition, hR]
  have hfun : (fun t => composition Nr t * (Ns t / Nr t))
      = fun t => (totalDensity Nr)⁻¹ * Ns t := by
    funext t
    have hNrt : Nr t ≠ 0 := (hNr t).ne'
    unfold composition
    field_simp
  rw [hfun]
  exact composition_smul_invariant (inv_ne_zero hStot.ne') s

/-! ### Non-vacuity witnesses

Explicit `Fin 2` data: `k_B = 1`, `g = A = 1`, `E = ![0, 1]` (distinct energies), `Fcal = 1`,
sample density `N_s = 2`, reference density `N_r = 1`. Matched (`T_s = T_r = 1`): the
differential ratio on line `0` is `2 = N_s/N_r`. Unmatched (`T_s = 1`, `T_r = 2`): the two-line
differential Boltzmann slope is `−(1 − 1/2) = −1/2 ≠ 0`, so the affine relation of
`logDifferentialRatio_affine_in_E` has a genuinely nonzero slope. Self-absorption
(`τ_s = 1`, `τ_r = 0`): the ratio is NOT `N_s/N_r`, so the residual is a real effect. -/

private def nvDeOne : Fin 2 → ℝ := fun _ => 1
private def nvDeE : Fin 2 → ℝ := ![0, 1]
private def nvDeTauS : Fin 2 → ℝ := fun _ => 1
private def nvDeTauR : Fin 2 → ℝ := fun _ => 0

private lemma nvDeOne_pos : ∀ k, 0 < nvDeOne k := fun _ => by norm_num [nvDeOne]

/-- Matched conditions: the ratio on line `0` equals `N_s/N_r = 2`. -/
example : differentialRatio (lineIntensity 1 1 2 1 nvDeOne nvDeE nvDeOne)
    (lineIntensity 1 1 1 1 nvDeOne nvDeE nvDeOne) 0 = 2 := by
  rw [differentialRatio_eq_density_ratio nvDeOne_pos one_pos one_pos nvDeOne_pos 0]
  norm_num

/-- The two witness energies are distinct (the `Fin 2` positive-spread condition). -/
private lemma nvDeE_ne : nvDeE 0 ≠ nvDeE 1 := by norm_num [nvDeE]

/-- Unmatched temperatures `T_s = 1`, `T_r = 2`: the differential Boltzmann slope is `−1/2`,
a genuinely nonzero slope. -/
example : olsSlope nvDeE (fun k => Real.log (differentialRatio
      (lineIntensity 1 1 2 1 nvDeOne nvDeE nvDeOne)
      (lineIntensity 1 2 1 1 nvDeOne nvDeE nvDeOne) k)) = -1 / 2
    ∧ (-1 / 2 : ℝ) ≠ 0 := by
  refine ⟨?_, by norm_num⟩
  rw [differentialSlope_two_lines nvDeOne_pos two_pos one_pos one_pos nvDeOne_pos nvDeE_ne]
  norm_num

/-- The witness energies are non-negative (the `E_k ≥ 0` hypothesis of the error bound). -/
private lemma nvDeE_nonneg : ∀ k, 0 ≤ nvDeE k := fun k => by
  fin_cases k <;> norm_num [nvDeE]

/-- The REDUCED bound applies on the witness data with floor `Tmin = 1 ≤ T_s = 1, T_r = 2` and
`δ = 1 ≥ |1 − 2|`: all hypotheses are jointly satisfiable, so the bound is not vacuous. -/
example : |Real.log (differentialRatio (lineIntensity 1 1 2 1 nvDeOne nvDeE nvDeOne)
        (lineIntensity 1 2 1 1 nvDeOne nvDeE nvDeOne) 0) - Real.log ((2 : ℝ) / 1)|
      ≤ (|nvDeE 0| + (∑ j, nvDeOne j * nvDeE j) / partitionFunction 1 1 nvDeOne nvDeE)
          / ((1 : ℝ) * 1 ^ 2) * 1 :=
  differentialRatio_error_bound one_pos one_pos le_rfl one_le_two nvDeOne_pos nvDeE_nonneg
    two_pos one_pos one_pos nvDeOne_pos (by norm_num) 0

/-- Mismatched optical depths `τ_s = 1`, `τ_r = 0`: the self-absorbed ratio is NOT `N_s/N_r`. -/
example : differentialRatio
      (fun j => selfAbsorbedIntensity 1 1 2 1 nvDeOne nvDeE nvDeOne j (nvDeTauS j))
      (fun j => selfAbsorbedIntensity 1 1 1 1 nvDeOne nvDeE nvDeOne j (nvDeTauR j)) 0
    ≠ 2 / 1 := by
  intro h
  have := (differentialRatio_selfAbsorption_cancels_iff nvDeOne_pos two_pos one_pos one_pos
    nvDeOne_pos 0 (by norm_num [nvDeTauS]) (by norm_num [nvDeTauR])).mp h
  norm_num [nvDeTauS, nvDeTauR] at this

end CflibsFormal
