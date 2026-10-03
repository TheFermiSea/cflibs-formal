/-
Copyright (c) 2026 Brian Squires. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Squires
-/
import Mathlib
import CflibsFormal.Boltzmann
import CflibsFormal.ForwardMap
import CflibsFormal.Classic
import CflibsFormal.CompositionRobustness
import CflibsFormal.PartitionLipschitz
import CflibsFormal.Analysis

/-!
# CF-LIBS formalization — the atomic-data perturbation channel

The identifiability results (`Identifiability.lean`, `CompositionRobustness.lean`) assume
that the analyst inverts a measured spectrum with the *same, correct* atomic data
`(g, A, E, U)` that produced it. Real CF-LIBS never has this luxury: transition
probabilities `A`, statistical weights `g`, level energies `E`, and partition functions
`U(T)` are read from tabulations that carry their own uncertainty (and are sometimes
missing entirely). The documented real-data accuracy floor of CF-LIBS *is* this
atomic-data error. This module formalizes the perturbation channel for the single-line
density reader `Classic.classicDensity`.

The chain is:

* `responseFactor` — the per-line "response" `ρ = g_u · A_u · exp(−E_u/(k_B T)) / U(T)`;
  the forward line intensity is `I = Fcal · N · ρ` and the classic inverse divides it back
  out. Packaging it makes the aliasing algebra a one-line cancellation.
* `classicDensity_aliasing` — **EXACT.** If the spectrum was emitted with TRUE data
  `(g, A, E)` (hence true `U`) at density `N`, but the analyst inverts the line with WRONG
  data `(g', A', E')` (hence wrong `U'`), the recovered density is exactly
  `N̂ = N · ρ_true / ρ_wrong`. Pure cancellation on `classicDensity ∘ lineIntensity`; the
  shared calibration `Fcal` cancels.
* `classicDensity_aliasing_error` — **REDUCED.** Lumping all atomic-data error into a single
  relative response error `|ρ' − ρ| ≤ δ·ρ` (`0 ≤ δ < 1`), the recovered density obeys
  `|N̂ − N| ≤ N · δ/(1 − δ)`. This channel absorbs an `E`-channel automatically, since `ρ`
  carries `exp(−E_u/(k_B T))`.
* `classicDensity_aliasing_error_channels` — **REDUCED.** The explicit two-channel form for
  `E' = E`: with `|g'A' − gA| ≤ δ_gA·(gA)` and `|U' − U| ≤ δ_U·U`,
  `|N̂ − N| ≤ N · (δ_gA + δ_U)/(1 − δ_gA)`. Simple monotone ratio algebra.
* `classicComposition_atomicData_error` — **REDUCED.** Feeding the per-species density bound
  into `composition_abs_sub_le_bound` (reused verbatim from `CompositionRobustness.lean`)
  bounds the recovered *composition* error `|Ĉ_s − C_s|` by the atomic-data error, via the
  named `compositionErrorBound`.
* `classicComposition_atomicData_error_rel` — **REDUCED.** The abundance-scaled twin: a relative
  response error `δ < 1` on every species gives `|Ĉ_s − C_s| ≤ (2δ/(1 − δ))·C_s`, a bound that
  shrinks with the true fraction and so stays informative for minor elements.

## Literature

Tognoni et al. 2010 (the CF-LIBS review) identifies atomic-parameter uncertainty — chiefly
transition-probability (`A`) error, but also `g`, `E`, and partition-function error — as the
dominant contribution to the CF-LIBS accuracy budget once the plasma is well-characterized.
The `EXACT` aliasing identity is the algebraic substrate of that discussion: it exhibits the
recovered density as the true density multiplied by a *ratio of response factors*, so any
mismatch between the tabulated and the true atomic data biases the result multiplicatively.
The `REDUCED` bounds turn that identity into exact (non-linearized) error envelopes.

## Honest scope

`classicDensity_aliasing` is `EXACT`: a faithful identity, no approximation, `Fcal` and every
partition-function/Boltzmann factor cancels as it does physically. The error results are
`REDUCED`: the first three replace the full per-symbol atomic-data error by *lumped* relative
bounds — a
single `δ` on the response factor (`classicDensity_aliasing_error`), a `δ_gA`/`δ_U` split with
`E' = E` (`classicDensity_aliasing_error_channels`), or a *uniform* `δ` and a density cap
`Nmax` across species (`classicComposition_atomicData_error`). No linearization of the forward
map is used — the reductions are only in the *hypotheses* (stronger, lumped) not in the
algebra, which stays exact.

This grounds the runtime hard-FAIL on missing / NULL atomic data: `classicDensity_aliasing`
shows that inverting with wrong data returns `N · ρ_true/ρ_wrong`, an *arbitrary* multiplicative
bias with no self-diagnosing signature. A solver handed NULL or unvalidated `(g, A, E, U)` can
therefore emit a perfectly finite, perfectly wrong number; the only sound response is to refuse.

### T-split aliasing bridge (gap #5 handoff, gap #2 residual — now closed here)

`PartitionLipschitz.lean` closed the `U_s(T)` Lipschitz leg but flagged that the *literal* wiring
into this module's density channel was missing: its `δ_U` slot models a same-`T` atomic-data
`U`-mismatch, whereas a recovered-temperature error is a same-`g` `U`-shift `|U(T̂) − U(T)|`, and no
forward/inverse-`T`-split aliasing identity was exposed. That bridge now EXISTS here:

* `classicDensity_temperature_aliasing` (`EXACT`): inverting at `T̂` a spectrum emitted at `T` with
  the SAME atomic data returns `N̂ = N · ρ(T)/ρ(T̂)`. Same cancellation as `classicDensity_aliasing`
  but with the response factor evaluated at two temperatures.
* `classicDensity_temperature_aliasing_error` (`REDUCED`): above a floor `Tmin ≤ T, T̂`, bounds
  `|N̂ − N| ≤ N · tempResponseErrorBound` by splitting the response ratio into an exp channel
  (two-point `|exp − 1|` bound, exponents ≤ 0) and a `U` channel
  (`PartitionLipschitz.partitionFunction_two_point_bound` + a single-term `U`-floor), through the
  two-factor ratio helper. The constants are honest over-estimates (not sharp).
* `classicDensity_aliasing_error_energy` (`REDUCED`): the gap #2 residual — with `g'A' = gA`,
  `U' = U` but `E' ≠ E`, isolates the pure energy channel, bounding `|N̂ − N|` by
  `N·(exp(|E'−E|/(k_B·Tmin)) − 1)`.
* `classicComposition_temperature_error` (`REDUCED`): feeds the per-species temperature-density
  bound through the verbatim `composition_abs_sub_le_bound`, so a recovered-temperature error now
  bounds `|Ĉ_s − C_s|`. This is the bridge the end-to-end module consumes.

The single composed noise→composition statement (temperature recovery error → this T-channel
density bound → composition error) is assembled in `NoiseToComposition.lean`.
-/

namespace CflibsFormal

open Finset Real
open scoped BigOperators

variable {ι : Type*} [Fintype ι]
variable {κ : Type*} [Fintype κ]

/-- **Per-line response factor** `ρ = g_u · A_u · exp(−E_u/(k_B T)) / U(T)`. The optically-thin
forward map is `lineIntensity kB T N Fcal g E A u = Fcal · N · ρ`, and `classicDensity` divides
`ρ` (with the analyst's atomic data) back out. Isolating `ρ` makes the aliasing identity a single
cancellation and the response-error hypotheses of the `REDUCED` bounds a single scalar. Pure
packaging of atomic data; not an estimator. -/
noncomputable def responseFactor (kB T : ℝ) (g E A : ι → ℝ) (u : ι) : ℝ :=
  g u * A u * boltzmannFactor kB T (E u) / partitionFunction kB T g E

/-- The response factor is positive given positive degeneracies and a positive line `A_u`
(`g u > 0`, `A u > 0`; `Fcal` and `N` do not enter). Private positivity helper. -/
private lemma responseFactor_pos [Nonempty ι] {kB T : ℝ} {g E A : ι → ℝ}
    (hg : ∀ k, 0 < g k) {u : ι} (hA : 0 < A u) :
    0 < responseFactor kB T g E A u := by
  unfold responseFactor
  exact div_pos (mul_pos (mul_pos (hg u) hA) (boltzmannFactor_pos _ _ _))
    (partitionFunction_pos hg)

/-- **Elementary scaled-ratio bound.** For `N, ρ, ρ' > 0`, `0 ≤ δ < 1`, and
`|ρ' − ρ| ≤ δ·ρ`: `|N·ρ/ρ' − N| ≤ N·(δ/(1 − δ))`. Since `N·ρ/ρ' − N = N·(ρ − ρ')/ρ'` and
`ρ' ≥ ρ·(1 − δ) > 0`, the deviation is `N·|ρ − ρ'|/ρ' ≤ N·δρ/(ρ(1 − δ))`. Private helper; pure
real algebra. -/
private lemma abs_scaled_ratio_sub_le {N ρ ρ' δ : ℝ}
    (hN : 0 < N) (_hρ : 0 < ρ) (hρ' : 0 < ρ') (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hpert : |ρ' - ρ| ≤ δ * ρ) :
    |N * ρ / ρ' - N| ≤ N * (δ / (1 - δ)) := by
  have h1d : 0 < 1 - δ := by linarith
  have hρ'ne : ρ' ≠ 0 := hρ'.ne'
  have hlow : ρ * (1 - δ) ≤ ρ' := by nlinarith [(abs_le.mp hpert).1]
  have hrw : N * ρ / ρ' - N = N * (ρ - ρ') / ρ' := by field_simp
  rw [hrw, abs_div, abs_of_pos hρ', abs_mul, abs_of_pos hN]
  have hnd : |ρ - ρ'| ≤ δ * ρ := by rw [abs_sub_comm]; exact hpert
  have hstep : |ρ - ρ'| / ρ' ≤ δ / (1 - δ) := by
    rw [div_le_div_iff₀ hρ' h1d]
    have h1 : |ρ - ρ'| * (1 - δ) ≤ (δ * ρ) * (1 - δ) :=
      mul_le_mul_of_nonneg_right hnd h1d.le
    have h2 : δ * (ρ * (1 - δ)) ≤ δ * ρ' := mul_le_mul_of_nonneg_left hlow hδ0
    nlinarith [h1, h2]
  calc N * |ρ - ρ'| / ρ' = N * (|ρ - ρ'| / ρ') := by rw [mul_div_assoc]
    _ ≤ N * (δ / (1 - δ)) := mul_le_mul_of_nonneg_left hstep hN.le

/-- **Elementary two-factor ratio bound.** For `S, u, v > 0`, `0 ≤ δp < 1`, `0 ≤ δq`,
`|u − 1| ≤ δp`, `|v − 1| ≤ δq`: `|S·v/u − S| ≤ S·((δp + δq)/(1 − δp))`. Since
`S·v/u − S = S·(v − u)/u`, `|v − u| ≤ |v − 1| + |u − 1| ≤ δp + δq`, and `u ≥ 1 − δp > 0`.
Private helper; pure real algebra. -/
private lemma abs_two_ratio_sub_le {S u v δp δq : ℝ}
    (hS : 0 < S) (hu : 0 < u) (_hv : 0 < v)
    (hδp0 : 0 ≤ δp) (hδp1 : δp < 1) (hδq0 : 0 ≤ δq)
    (hu1 : |u - 1| ≤ δp) (hv1 : |v - 1| ≤ δq) :
    |S * v / u - S| ≤ S * ((δp + δq) / (1 - δp)) := by
  have h1d : 0 < 1 - δp := by linarith
  have hlow : 1 - δp ≤ u := by linarith [(abs_le.mp hu1).1]
  have hune : u ≠ 0 := hu.ne'
  have hrw : S * v / u - S = S * (v - u) / u := by field_simp
  rw [hrw, abs_div, abs_of_pos hu, abs_mul, abs_of_pos hS]
  have hnumdev : |v - u| ≤ δp + δq := by
    have h : v - u = (v - 1) + (-(u - 1)) := by ring
    rw [h]
    calc |(v - 1) + (-(u - 1))| ≤ |v - 1| + |-(u - 1)| := abs_add_le _ _
      _ = |v - 1| + |u - 1| := by rw [abs_neg]
      _ ≤ δq + δp := add_le_add hv1 hu1
      _ = δp + δq := by ring
  have hstep : |v - u| / u ≤ (δp + δq) / (1 - δp) := by
    rw [div_le_div_iff₀ hu h1d]
    have h1 : |v - u| * (1 - δp) ≤ (δp + δq) * (1 - δp) :=
      mul_le_mul_of_nonneg_right hnumdev h1d.le
    have h2 : (δp + δq) * (1 - δp) ≤ (δp + δq) * u :=
      mul_le_mul_of_nonneg_left hlow (by linarith)
    linarith
  calc S * |v - u| / u = S * (|v - u| / u) := by rw [mul_div_assoc]
    _ ≤ S * ((δp + δq) / (1 - δp)) := mul_le_mul_of_nonneg_left hstep hS.le

/-- **EXACT aliasing identity.** The spectrum is emitted with the TRUE atomic data `(g, E, A)`
at density `N` and shared calibration `Fcal`; the analyst inverts the same line with the WRONG
data `(g', E', A')`. The recovered density is exactly the true density scaled by the ratio of
response factors:
  `N̂ = N · responseFactor(g,E,A) / responseFactor(g',E',A')`
    `= N · (g_u·A_u·bf(E_u)/U) / (g'_u·A'_u·bf(E'_u)/U')`.
Pure cancellation on `classicDensity ∘ lineIntensity`: the calibration `Fcal` and every
partition-function / Boltzmann factor cancel, leaving the multiplicative atomic-data bias. This
is the algebraic substrate of the CF-LIBS atomic-data accuracy floor (Tognoni et al. 2010): with
correct data (`g'=g, E'=E, A'=A`) the ratio is `1` and `N̂ = N` (`Classic.classicDensity_recovers`);
any mismatch biases `N̂` multiplicatively, with no self-diagnosing signature. -/
theorem classicDensity_aliasing [Nonempty ι]
    {kB T N Fcal : ℝ} {g E A g' E' A' : ι → ℝ}
    (hg : ∀ k, 0 < g k) (hg' : ∀ k, 0 < g' k)
    (hFcal : 0 < Fcal) (u : ι) (hA' : 0 < A' u) :
    Classic.classicDensity kB T Fcal g' E' A' u (lineIntensity kB T N Fcal g E A u)
      = N * responseFactor kB T g E A u / responseFactor kB T g' E' A' u := by
  have hU : partitionFunction kB T g E ≠ 0 := (partitionFunction_pos hg).ne'
  have hU' : partitionFunction kB T g' E' ≠ 0 := (partitionFunction_pos hg').ne'
  have hFne : Fcal ≠ 0 := hFcal.ne'
  have hA'ne : A' u ≠ 0 := hA'.ne'
  have hg'ne : g' u ≠ 0 := (hg' u).ne'
  have hbf' : boltzmannFactor kB T (E' u) ≠ 0 := (boltzmannFactor_pos _ _ _).ne'
  unfold Classic.classicDensity lineIntensity population responseFactor
  field_simp

/-- **REDUCED lumped relative-error bound.** Lumping all atomic-data error into a single relative
response error `|ρ' − ρ| ≤ δ·ρ` (`0 ≤ δ < 1`), the recovered density obeys
`|N̂ − N| ≤ N · δ/(1 − δ)`. Immediate from the `EXACT` aliasing identity plus the elementary
scaled-ratio bound. This single channel absorbs an `E`-channel automatically, because the
response factor `ρ` carries the Boltzmann factor `exp(−E_u/(k_B T))` — an `E' ≠ E` perturbation
simply enters `|ρ' − ρ|`. Reduction: the per-symbol errors in `g`, `A`, `E`, `U` are collapsed
into the one scalar `δ`; the algebra itself is exact (Tognoni et al. 2010, accuracy budget). -/
theorem classicDensity_aliasing_error [Nonempty ι]
    {kB T N Fcal δ : ℝ} {g E A g' E' A' : ι → ℝ}
    (hg : ∀ k, 0 < g k) (hg' : ∀ k, 0 < g' k)
    (hFcal : 0 < Fcal) (u : ι) (hA : 0 < A u) (hA' : 0 < A' u)
    (hN : 0 < N) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hpert : |responseFactor kB T g' E' A' u - responseFactor kB T g E A u|
              ≤ δ * responseFactor kB T g E A u) :
    |Classic.classicDensity kB T Fcal g' E' A' u (lineIntensity kB T N Fcal g E A u) - N|
      ≤ N * (δ / (1 - δ)) := by
  rw [classicDensity_aliasing hg hg' hFcal u hA']
  exact abs_scaled_ratio_sub_le hN (responseFactor_pos hg hA)
    (responseFactor_pos hg' hA') hδ0 hδ1 hpert

/-- **REDUCED two-channel relative-error bound (`E' = E`).** With the same level energies but
perturbed `gA` and partition function, split the atomic-data error into a line-strength channel
`|g'_u·A'_u − g_u·A_u| ≤ δ_gA·(g_u·A_u)` (`0 ≤ δ_gA < 1`) and a partition-function channel
`|U' − U| ≤ δ_U·U` (`0 ≤ δ_U`). Then
  `|N̂ − N| ≤ N · (δ_gA + δ_U)/(1 − δ_gA)`.
Derivation: with `E' = E` the aliasing identity collapses to `N̂ = N · (U'/U)/(g'A'/gA)`, and the
two relative bounds give `|U'/U − 1| ≤ δ_U`, `|g'A'/gA − 1| ≤ δ_gA`; the two-factor ratio bound
finishes. Reduction: `E' = E` (the energy channel is carried separately by
`classicDensity_aliasing_error`) and the per-symbol `g`,`A`,`U` errors are lumped into
`δ_gA`, `δ_U`; the algebra is exact (Tognoni et al. 2010). -/
theorem classicDensity_aliasing_error_channels [Nonempty ι]
    {kB T N Fcal δgA δU : ℝ} {g E A g' A' : ι → ℝ}
    (hg : ∀ k, 0 < g k) (hg' : ∀ k, 0 < g' k)
    (hFcal : 0 < Fcal) (u : ι) (hA : 0 < A u) (hA' : 0 < A' u)
    (hN : 0 < N) (hδgA0 : 0 ≤ δgA) (hδgA1 : δgA < 1) (hδU0 : 0 ≤ δU)
    (hpertGA : |g' u * A' u - g u * A u| ≤ δgA * (g u * A u))
    (hpertU : |partitionFunction kB T g' E - partitionFunction kB T g E|
                ≤ δU * partitionFunction kB T g E) :
    |Classic.classicDensity kB T Fcal g' E A' u (lineIntensity kB T N Fcal g E A u) - N|
      ≤ N * ((δgA + δU) / (1 - δgA)) := by
  have hbf : boltzmannFactor kB T (E u) ≠ 0 := (boltzmannFactor_pos _ _ _).ne'
  have hUpos : 0 < partitionFunction kB T g E := partitionFunction_pos hg
  have hU'pos : 0 < partitionFunction kB T g' E := partitionFunction_pos hg'
  have hgApos : 0 < g u * A u := mul_pos (hg u) hA
  have hg'A'pos : 0 < g' u * A' u := mul_pos (hg' u) hA'
  have hU : partitionFunction kB T g E ≠ 0 := hUpos.ne'
  have hU' : partitionFunction kB T g' E ≠ 0 := hU'pos.ne'
  have hgu : g u ≠ 0 := (hg u).ne'
  have hAu : A u ≠ 0 := hA.ne'
  have hg'u : g' u ≠ 0 := (hg' u).ne'
  have hA'u : A' u ≠ 0 := hA'.ne'
  have hNhat : Classic.classicDensity kB T Fcal g' E A' u (lineIntensity kB T N Fcal g E A u)
      = N * (partitionFunction kB T g' E / partitionFunction kB T g E)
          / (g' u * A' u / (g u * A u)) := by
    rw [classicDensity_aliasing hg hg' hFcal u hA']
    unfold responseFactor
    field_simp
  rw [hNhat]
  have hu1 : |g' u * A' u / (g u * A u) - 1| ≤ δgA := by
    have heq : g' u * A' u / (g u * A u) - 1 = (g' u * A' u - g u * A u) / (g u * A u) := by
      field_simp
    rw [heq, abs_div, abs_of_pos hgApos, div_le_iff₀ hgApos]
    exact hpertGA
  have hv1 : |partitionFunction kB T g' E / partitionFunction kB T g E - 1| ≤ δU := by
    have heq : partitionFunction kB T g' E / partitionFunction kB T g E - 1
        = (partitionFunction kB T g' E - partitionFunction kB T g E)
            / partitionFunction kB T g E := by field_simp
    rw [heq, abs_div, abs_of_pos hUpos, div_le_iff₀ hUpos]
    exact hpertU
  exact abs_two_ratio_sub_le hN (div_pos hg'A'pos hgApos) (div_pos hU'pos hUpos)
    hδgA0 hδgA1 hδU0 hu1 hv1

/-- **Recovered per-species density under wrong atomic data.** For each species `s` the analyst
inverts that species' chosen line — emitted with the TRUE data `(g s, E s, A s)` at density
`N s` — using the WRONG data `(g' s, E' s, A' s)`. Pure packaging (a `κ → ℝ` density vector) so
the composition corollary reads cleanly; not an estimator. -/
noncomputable def recoveredDensity (kB T Fcal : ℝ) (g E A g' E' A' : κ → ι → ℝ)
    (u : κ → ι) (N : κ → ℝ) (s : κ) : ℝ :=
  Classic.classicDensity kB T Fcal (g' s) (E' s) (A' s) (u s)
    (lineIntensity kB T (N s) Fcal (g s) (E s) (A s) (u s))

/-- **REDUCED composition corollary.** Feeding the per-species density bound into the reused
whole-composition bound `composition_abs_sub_le_bound` (from `CompositionRobustness.lean`), the
recovered composition error is controlled by the atomic-data error:
  `|Ĉ_s − C_s| ≤ compositionErrorBound N Ŝ (Nmax·δ/(1 − δ)) s`,
where `Ŝ = totalDensity` of the recovered densities. Hypotheses: a *uniform* lumped relative
response error `δ` (`0 ≤ δ < 1`) across species and a density cap `N s ≤ Nmax`. Reduction:
uniform `δ` and `Nmax` collapse the per-species, per-symbol atomic-data errors into two scalars;
everything downstream is the verbatim `CompositionRobustness` bound (Tognoni et al. 2010). -/
theorem classicComposition_atomicData_error [Nonempty ι] [Nonempty κ]
    {kB T Fcal δ Nmax : ℝ} {N : κ → ℝ} {g E A g' E' A' : κ → ι → ℝ} {u : κ → ι}
    (hg : ∀ s k, 0 < g s k) (hg' : ∀ s k, 0 < g' s k) (hFcal : 0 < Fcal)
    (hA : ∀ s, 0 < A s (u s)) (hA' : ∀ s, 0 < A' s (u s))
    (hN : ∀ s, 0 < N s) (hNmax : ∀ s, N s ≤ Nmax)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hpert : ∀ s, |responseFactor kB T (g' s) (E' s) (A' s) (u s)
                    - responseFactor kB T (g s) (E s) (A s) (u s)|
                  ≤ δ * responseFactor kB T (g s) (E s) (A s) (u s))
    (s : κ) :
    |composition (recoveredDensity kB T Fcal g E A g' E' A' u N) s - composition N s|
      ≤ compositionErrorBound N
          (totalDensity (recoveredDensity kB T Fcal g E A g' E' A' u N))
          (Nmax * (δ / (1 - δ))) s := by
  have hNhat_pos : ∀ t, 0 < recoveredDensity kB T Fcal g E A g' E' A' u N t := by
    intro t
    unfold recoveredDensity
    rw [classicDensity_aliasing (hg t) (hg' t) hFcal (u t) (hA' t)]
    exact div_pos (mul_pos (hN t) (responseFactor_pos (hg t) (hA t)))
      (responseFactor_pos (hg' t) (hA' t))
  have hStot : 0 < totalDensity N := totalDensity_pos hN
  have hShat : 0 < totalDensity (recoveredDensity kB T Fcal g E A g' E' A' u N) :=
    totalDensity_pos hNhat_pos
  have hN0 : ∀ t, 0 ≤ N t := fun t => (hN t).le
  have hΔ0 : 0 ≤ δ / (1 - δ) := div_nonneg hδ0 (by linarith)
  have hdelta : ∀ t, |recoveredDensity kB T Fcal g E A g' E' A' u N t - N t|
      ≤ Nmax * (δ / (1 - δ)) := by
    intro t
    have hbound : |recoveredDensity kB T Fcal g E A g' E' A' u N t - N t|
        ≤ N t * (δ / (1 - δ)) := by
      unfold recoveredDensity
      exact classicDensity_aliasing_error (hg t) (hg' t) hFcal (u t) (hA t) (hA' t)
        (hN t) hδ0 hδ1 (hpert t)
    exact hbound.trans (mul_le_mul_of_nonneg_right (hNmax t) hΔ0)
  exact composition_abs_sub_le_bound hN0 hStot hShat hdelta s

/-! ### Non-vacuity witnesses

The `nvAdp*` data instantiate the aliasing family on `ι = Fin 1` with `kB = T = Fcal = 1`,
`E = E' = 0`, `g = g' = 1`, true `A = 1`, so the true response factor is `ρ = 1`. Changing only
the analyst's transition probability `A'` moves the recovered density off the truth. -/

private def nvAdpg : Fin 1 → ℝ := fun _ => 1
private def nvAdpE : Fin 1 → ℝ := fun _ => 0
private def nvAdpA : Fin 1 → ℝ := fun _ => 1
private def nvAdpA2 : Fin 1 → ℝ := fun _ => 2
private noncomputable def nvAdpA32 : Fin 1 → ℝ := fun _ => 3 / 2

/-- **Aliasing is genuine bias, not `N̂ = N`.** The analyst uses `A' = 2` while the true `A = 1`
(all else correct). The spectrum from `N = 4` is inverted to `N̂ = 2` — exactly half the truth —
so `classicDensity_aliasing` has real content: the ratio of response factors is `1/2 ≠ 1`. -/
example :
    Classic.classicDensity 1 1 1 nvAdpg nvAdpE nvAdpA2 0
        (lineIntensity 1 1 4 1 nvAdpg nvAdpE nvAdpA 0) = 2 := by
  norm_num [Classic.classicDensity, lineIntensity, population, partitionFunction,
    boltzmannFactor, nvAdpg, nvAdpE, nvAdpA, nvAdpA2, Real.exp_zero, Fin.sum_univ_one]

/-- **The relative-error bound is non-vacuous.** With a 50% response perturbation (`A' = 3/2`,
so `δ = 1/2`) the recovered density `N̂ = 2` genuinely differs from the true `N = 3`, yet the
bound `|N̂ − N| ≤ N·(δ/(1 − δ)) = 3` holds (here `1 ≤ 3`). All hypotheses of
`classicDensity_aliasing_error` are jointly satisfiable. -/
example :
    |Classic.classicDensity 1 1 1 nvAdpg nvAdpE nvAdpA32 0
        (lineIntensity 1 1 3 1 nvAdpg nvAdpE nvAdpA 0) - 3|
      ≤ 3 * ((1 / 2 : ℝ) / (1 - 1 / 2)) := by
  apply classicDensity_aliasing_error (fun _ => one_pos) (fun _ => one_pos) one_pos 0
    (by norm_num [nvAdpA]) (by norm_num [nvAdpA32]) (by norm_num) (by norm_num) (by norm_num)
  norm_num [responseFactor, nvAdpg, nvAdpE, nvAdpA, nvAdpA32, partitionFunction,
    boltzmannFactor, Real.exp_zero, Fin.sum_univ_one]

/-! ### T-split aliasing and the energy channel

The identities/bounds below realise the T-split bridge described in the Honest-scope note: the
same-data / wrong-`T` aliasing identity, its box error bound, the isolated energy channel, and the
composition corollary the end-to-end module consumes. -/

/-- **Single-term partition-function floor (PURE-MATH).** For `Eₖ ≥ 0`, `gₖ > 0`, `Tmin ≤ T`, any
level `k0` gives `g_{k0}·exp(−E_{k0}/(k_B·Tmin)) ≤ U(T)`: with `Eₖ ≥ 0` the `k0` Boltzmann factor
is minimised at `Tmin`, and a single term is ≤ the whole (nonnegative) sum. This is the `U`-floor
the temperature-error bound divides by. Private helper. -/
private lemma partitionFunction_floor {kB Tmin T : ℝ} {g E : ι → ℝ}
    (hkB : 0 < kB) (hTmin : 0 < Tmin) (hT : Tmin ≤ T)
    (hg : ∀ k, 0 < g k) (hE : ∀ k, 0 ≤ E k) (k0 : ι) :
    g k0 * Real.exp (-E k0 / (kB * Tmin)) ≤ partitionFunction kB T g E := by
  have hterm : g k0 * Real.exp (-E k0 / (kB * Tmin)) ≤ g k0 * boltzmannFactor kB T (E k0) := by
    refine mul_le_mul_of_nonneg_left ?_ (hg k0).le
    unfold boltzmannFactor
    refine Real.exp_le_exp.mpr ?_
    rw [neg_div, neg_div, neg_le_neg_iff]
    exact div_le_div_of_nonneg_left (hE k0) (mul_pos hkB hTmin)
      (mul_le_mul_of_nonneg_left hT hkB.le)
  refine hterm.trans ?_
  unfold partitionFunction
  exact Finset.single_le_sum
    (fun k _ => mul_nonneg (hg k).le (boltzmannFactor_pos _ _ _).le) (Finset.mem_univ k0)

/-- **EXACT temperature-aliasing identity.** The spectrum is emitted with atomic data `(g, E, A)`
at the TRUE temperature `T` and shared calibration `Fcal`; the analyst inverts the SAME line with
the SAME atomic data but at a WRONG temperature `T̂`. The recovered density is exactly the true
density scaled by the ratio of response factors *at the two temperatures*:
  `N̂ = N · responseFactor(T) / responseFactor(T̂)`
    `= N · (bf(E_u; T)/U(T)) / (bf(E_u; T̂)/U(T̂))`.
Pure cancellation on `classicDensity ∘ lineIntensity`: `Fcal`, `g_u`, `A_u` cancel, leaving the
temperature bias carried by the Boltzmann factor and the partition function. With `T̂ = T` the ratio
is `1` and `N̂ = N` (`Classic.classicDensity_recovers`); any temperature mis-estimate biases `N̂`
multiplicatively (Tognoni et al. 2010, the `U_s(T)`/Boltzmann temperature channel of the accuracy
budget). -/
theorem classicDensity_temperature_aliasing [Nonempty ι]
    {kB T That N Fcal : ℝ} {g E A : ι → ℝ}
    (hg : ∀ k, 0 < g k) (hFcal : 0 < Fcal) (u : ι) (hA : 0 < A u) :
    Classic.classicDensity kB That Fcal g E A u (lineIntensity kB T N Fcal g E A u)
      = N * responseFactor kB T g E A u / responseFactor kB That g E A u := by
  have hU : partitionFunction kB T g E ≠ 0 := (partitionFunction_pos hg).ne'
  have hUhat : partitionFunction kB That g E ≠ 0 := (partitionFunction_pos hg).ne'
  have hFne : Fcal ≠ 0 := hFcal.ne'
  have hAne : A u ≠ 0 := hA.ne'
  have hgne : g u ≠ 0 := (hg u).ne'
  have hbf : boltzmannFactor kB T (E u) ≠ 0 := (boltzmannFactor_pos _ _ _).ne'
  have hbfhat : boltzmannFactor kB That (E u) ≠ 0 := (boltzmannFactor_pos _ _ _).ne'
  unfold Classic.classicDensity lineIntensity population responseFactor
  field_simp

/-- **REDUCED energy-channel isolation (gap #2 residual).** In the wrong-DATA aliasing at the SAME
temperature `T`, isolate the pure energy channel: with matched line strength `g'_u·A'_u = g_u·A_u`
and matched partition function `U(T; g', E') = U(T; g, E)` but a shifted upper-level energy
`E'_u ≠ E_u`, the aliasing identity collapses to `N̂ = N · bf(E_u; T)/bf(E'_u; T)
= N · exp((E'_u − E_u)/(k_B T))`, and on a floor `Tmin ≤ T`:
  `|N̂ − N| ≤ N · (exp(|E'_u − E_u|/(k_B·Tmin)) − 1)`.
Derivation: `|exp w − 1| ≤ exp|w| − 1` (the two-point `|exp − 1|` bound) with
`|w| = |E'_u − E_u|/(k_B T) ≤ |E'_u − E_u|/(k_B·Tmin)` (from `Tmin ≤ T`). Reduction: `Tmin` floors
the temperature; the matched-`gA`/matched-`U` hypotheses isolate the single line's Boltzmann factor
(Tognoni et al. 2010, the energy-parameter channel). Explicit constant, not sharp. -/
theorem classicDensity_aliasing_error_energy [Nonempty ι]
    {kB Tmin T N Fcal : ℝ} {g E A g' E' A' : ι → ℝ}
    (hkB : 0 < kB) (hTmin : 0 < Tmin) (hT : Tmin ≤ T)
    (hg : ∀ k, 0 < g k) (hg' : ∀ k, 0 < g' k)
    (hFcal : 0 < Fcal) (u : ι) (hA : 0 < A u) (hA' : 0 < A' u) (hN : 0 < N)
    (hgA : g' u * A' u = g u * A u)
    (hUeq : partitionFunction kB T g' E' = partitionFunction kB T g E) :
    |Classic.classicDensity kB T Fcal g' E' A' u (lineIntensity kB T N Fcal g E A u) - N|
      ≤ N * (Real.exp (|E' u - E u| / (kB * Tmin)) - 1) := by
  have hkT : 0 < kB * T := mul_pos hkB (lt_of_lt_of_le hTmin hT)
  rw [classicDensity_aliasing hg hg' hFcal u hA']
  have hkey : N * responseFactor kB T g E A u / responseFactor kB T g' E' A' u
      = N * (boltzmannFactor kB T (E u) / boltzmannFactor kB T (E' u)) := by
    have hU : partitionFunction kB T g E ≠ 0 := (partitionFunction_pos hg).ne'
    have hbf' : boltzmannFactor kB T (E' u) ≠ 0 := (boltzmannFactor_pos _ _ _).ne'
    have hgu : g u ≠ 0 := (hg u).ne'
    have hAu : A u ≠ 0 := hA.ne'
    unfold responseFactor
    rw [hUeq, hgA]
    field_simp
  rw [hkey]
  have hbfdiv : boltzmannFactor kB T (E u) / boltzmannFactor kB T (E' u)
      = Real.exp ((E' u - E u) / (kB * T)) := by
    unfold boltzmannFactor
    rw [← Real.exp_sub]
    congr 1
    ring
  rw [hbfdiv,
    show N * Real.exp ((E' u - E u) / (kB * T)) - N
      = N * (Real.exp ((E' u - E u) / (kB * T)) - 1) from by ring,
    abs_mul, abs_of_pos hN]
  refine mul_le_mul_of_nonneg_left ?_ hN.le
  have hwle : |(E' u - E u) / (kB * T)| ≤ |E' u - E u| / (kB * Tmin) := by
    rw [abs_div, abs_of_pos hkT]
    exact div_le_div_of_nonneg_left (abs_nonneg _) (mul_pos hkB hTmin)
      (mul_le_mul_of_nonneg_left hT hkB.le)
  have hmono : Real.exp |(E' u - E u) / (kB * T)| ≤ Real.exp (|E' u - E u| / (kB * Tmin)) :=
    Real.exp_le_exp.mpr hwle
  calc |Real.exp ((E' u - E u) / (kB * T)) - 1|
      ≤ Real.exp |(E' u - E u) / (kB * T)| - 1 := abs_exp_sub_one_le le_rfl
    _ ≤ Real.exp (|E' u - E u| / (kB * Tmin)) - 1 := by linarith

/-- **Named temperature-response error bound.** The explicit `delta/(1 − delta)`-shaped envelope of
the temperature-aliasing error: `delta_exp = exp(E_u·|T̂ − T|/(k_B·Tmin²)) − 1` (exp channel) and
`delta_U = (∑ₖ gₖEₖ)·|T̂ − T|/(k_B·Tmin²) / (g_{k0}·exp(−E_{k0}/(k_B·Tmin)))` (`U` channel, floored
by level `k0`), combined as `(delta_exp + delta_U)/(1 − delta_exp)`. Pure algebraic packaging of the
bound's right-hand side; not an estimator. -/
noncomputable def tempResponseErrorBound (kB Tmin T That : ℝ) (g E : ι → ℝ) (u k0 : ι) : ℝ :=
  ((Real.exp (E u * |That - T| / (kB * Tmin ^ 2)) - 1)
      + (∑ k, g k * E k) * |That - T| / (kB * Tmin ^ 2)
          / (g k0 * Real.exp (-E k0 / (kB * Tmin))))
    / (1 - (Real.exp (E u * |That - T| / (kB * Tmin ^ 2)) - 1))

/-- **REDUCED temperature-error bound.** On a box `Tmin ≤ T, T̂` (`0 < Tmin`), with `gₖ > 0`,
`Eₖ ≥ 0`, and the exp-channel smallness `delta_exp < 1`, the temperature-aliased recovered density
obeys
  `|N̂ − N| ≤ N · tempResponseErrorBound k_B Tmin T T̂ g E u k0`.
Proof: rewrite `N̂ = N · v/u` with `v = U(T̂)/U(T)` (`U` channel) and `u = bf(E_u; T̂)/bf(E_u; T)`
(exp channel), then bound `|u − 1| ≤ delta_exp` via the two-point `|exp − 1|` bound and the
inverse-temperature gap, and `|v − 1| ≤ delta_U` via
`PartitionLipschitz.partitionFunction_two_point_bound` + the single-term `U`-floor
`partitionFunction_floor` (level `k0`); the two-factor ratio helper `abs_two_ratio_sub_le` closes.
Reduction: the constants are honest over-estimates (`exp ≤ 1`, `T₁T₂ ≥ Tmin²`, single-term floor),
not sharp; the algebra is exact (Tognoni et al. 2010, temperature→density channel). -/
theorem classicDensity_temperature_aliasing_error [Nonempty ι]
    {kB Tmin T That N Fcal : ℝ} {g E A : ι → ℝ}
    (hkB : 0 < kB) (hTmin : 0 < Tmin) (hT : Tmin ≤ T) (hThat : Tmin ≤ That)
    (hg : ∀ k, 0 < g k) (hE : ∀ k, 0 ≤ E k)
    (hFcal : 0 < Fcal) (u k0 : ι) (hA : 0 < A u) (hN : 0 < N)
    (hδp1 : Real.exp (E u * |That - T| / (kB * Tmin ^ 2)) - 1 < 1) :
    |Classic.classicDensity kB That Fcal g E A u (lineIntensity kB T N Fcal g E A u) - N|
      ≤ N * tempResponseErrorBound kB Tmin T That g E u k0 := by
  have hTpos : 0 < T := lt_of_lt_of_le hTmin hT
  have hThatpos : 0 < That := lt_of_lt_of_le hTmin hThat
  have hUT : 0 < partitionFunction kB T g E := partitionFunction_pos hg
  have hUThat : 0 < partitionFunction kB That g E := partitionFunction_pos hg
  have hbfT : 0 < boltzmannFactor kB T (E u) := boltzmannFactor_pos _ _ _
  have hbfThat : 0 < boltzmannFactor kB That (E u) := boltzmannFactor_pos _ _ _
  rw [classicDensity_temperature_aliasing hg hFcal u hA]
  have hform : N * responseFactor kB T g E A u / responseFactor kB That g E A u
      = N * (partitionFunction kB That g E / partitionFunction kB T g E)
          / (boltzmannFactor kB That (E u) / boltzmannFactor kB T (E u)) := by
    have hgu : g u ≠ 0 := (hg u).ne'
    have hAu : A u ≠ 0 := hA.ne'
    have h1 : partitionFunction kB T g E ≠ 0 := hUT.ne'
    have h2 : partitionFunction kB That g E ≠ 0 := hUThat.ne'
    have h3 : boltzmannFactor kB T (E u) ≠ 0 := hbfT.ne'
    have h4 : boltzmannFactor kB That (E u) ≠ 0 := hbfThat.ne'
    unfold responseFactor
    field_simp
  rw [hform]
  have hsumnn : 0 ≤ ∑ k, g k * E k :=
    Finset.sum_nonneg (fun k _ => mul_nonneg (hg k).le (hE k))
  have hUfloorpos : 0 < g k0 * Real.exp (-E k0 / (kB * Tmin)) := mul_pos (hg k0) (Real.exp_pos _)
  have hMnn : 0 ≤ (∑ k, g k * E k) * |That - T| / (kB * Tmin ^ 2) :=
    div_nonneg (mul_nonneg hsumnn (abs_nonneg _)) (mul_pos hkB (pow_pos hTmin 2)).le
  have hbfeq : boltzmannFactor kB That (E u) / boltzmannFactor kB T (E u)
      = Real.exp (-E u / (kB * That) - -E u / (kB * T)) := by
    unfold boltzmannFactor
    rw [← Real.exp_sub]
  have hzabs : |(-E u / (kB * That) - -E u / (kB * T))|
      ≤ E u * |That - T| / (kB * Tmin ^ 2) := by
    rw [show -E u / (kB * That) - -E u / (kB * T)
          = E u * (1 / (kB * T) - 1 / (kB * That)) from by ring,
      abs_mul, abs_of_nonneg (hE u)]
    calc E u * |1 / (kB * T) - 1 / (kB * That)|
        ≤ E u * (|T - That| / (kB * Tmin ^ 2)) :=
          mul_le_mul_of_nonneg_left (inv_kT_sub_le hkB hTmin hT hThat) (hE u)
      _ = E u * |That - T| / (kB * Tmin ^ 2) := by rw [abs_sub_comm T That]; ring
  have hu1 : |boltzmannFactor kB That (E u) / boltzmannFactor kB T (E u) - 1|
      ≤ Real.exp (E u * |That - T| / (kB * Tmin ^ 2)) - 1 := by
    rw [hbfeq]
    have hmono : Real.exp |(-E u / (kB * That) - -E u / (kB * T))|
        ≤ Real.exp (E u * |That - T| / (kB * Tmin ^ 2)) := Real.exp_le_exp.mpr hzabs
    calc |Real.exp (-E u / (kB * That) - -E u / (kB * T)) - 1|
        ≤ Real.exp |(-E u / (kB * That) - -E u / (kB * T))| - 1 := abs_exp_sub_one_le le_rfl
      _ ≤ Real.exp (E u * |That - T| / (kB * Tmin ^ 2)) - 1 := by linarith
  have hnum : |partitionFunction kB That g E - partitionFunction kB T g E|
      ≤ (∑ k, g k * E k) * |That - T| / (kB * Tmin ^ 2) := by
    calc |partitionFunction kB That g E - partitionFunction kB T g E|
        ≤ (∑ k, g k * E k) * |1 / (kB * That) - 1 / (kB * T)| :=
          partitionFunction_two_point_bound hkB hThatpos hTpos hg hE
      _ ≤ (∑ k, g k * E k) * (|That - T| / (kB * Tmin ^ 2)) :=
          mul_le_mul_of_nonneg_left (inv_kT_sub_le hkB hTmin hThat hT) hsumnn
      _ = (∑ k, g k * E k) * |That - T| / (kB * Tmin ^ 2) := by ring
  have hUfloor : g k0 * Real.exp (-E k0 / (kB * Tmin)) ≤ partitionFunction kB T g E :=
    partitionFunction_floor hkB hTmin hT hg hE k0
  have hv1 : |partitionFunction kB That g E / partitionFunction kB T g E - 1|
      ≤ (∑ k, g k * E k) * |That - T| / (kB * Tmin ^ 2)
          / (g k0 * Real.exp (-E k0 / (kB * Tmin))) := by
    have hveq : partitionFunction kB That g E / partitionFunction kB T g E - 1
        = (partitionFunction kB That g E - partitionFunction kB T g E)
            / partitionFunction kB T g E := by field_simp
    rw [hveq, abs_div, abs_of_pos hUT, div_le_div_iff₀ hUT hUfloorpos]
    have ha := mul_le_mul_of_nonneg_right hnum hUfloorpos.le
    have hb := mul_le_mul_of_nonneg_left hUfloor hMnn
    linarith
  have hδp0 : (0 : ℝ) ≤ Real.exp (E u * |That - T| / (kB * Tmin ^ 2)) - 1 := by
    have harg : (0 : ℝ) ≤ E u * |That - T| / (kB * Tmin ^ 2) :=
      div_nonneg (mul_nonneg (hE u) (abs_nonneg _)) (mul_pos hkB (pow_pos hTmin 2)).le
    linarith [Real.add_one_le_exp (E u * |That - T| / (kB * Tmin ^ 2))]
  have hδq0 : (0 : ℝ) ≤ (∑ k, g k * E k) * |That - T| / (kB * Tmin ^ 2)
      / (g k0 * Real.exp (-E k0 / (kB * Tmin))) := div_nonneg hMnn hUfloorpos.le
  unfold tempResponseErrorBound
  exact abs_two_ratio_sub_le hN (div_pos hbfThat hbfT) (div_pos hUThat hUT)
    hδp0 hδp1 hδq0 hu1 hv1

/-- **Recovered per-species density at a wrong temperature.** Each species' line is emitted with
the TRUE data at the TRUE temperature `T` and density `N s`, but inverted with the SAME data at the
WRONG temperature `T̂`. Pure packaging (a `κ → ℝ` vector) for the composition corollary;
not an estimator. -/
noncomputable def recoveredDensityAtT (kB T That Fcal : ℝ) (g E A : κ → ι → ℝ)
    (u : κ → ι) (N : κ → ℝ) (s : κ) : ℝ :=
  Classic.classicDensity kB That Fcal (g s) (E s) (A s) (u s)
    (lineIntensity kB T (N s) Fcal (g s) (E s) (A s) (u s))

/-- **REDUCED composition corollary (temperature channel).** A recovered-temperature error now
bounds the composition error. Feeding the per-species temperature-density bound
`classicDensity_temperature_aliasing_error` (uniformly enveloped by `Φ` across species via `henv`,
with `N s ≤ Nmax`) into the verbatim `composition_abs_sub_le_bound` gives
  `|Ĉ_s − C_s| ≤ compositionErrorBound N Ŝ (Nmax·Φ) s`,
where `Ŝ = totalDensity` of the temperature-aliased densities. This is the bridge the end-to-end
temperature→composition module consumes (Tognoni et al. 2010). Reduction: the uniform envelope `Φ`
and cap `Nmax` collapse the per-species temperature-error constants into two scalars; everything
downstream is the verbatim `CompositionRobustness` bound. -/
theorem classicComposition_temperature_error [Nonempty ι] [Nonempty κ]
    {kB Tmin T That Fcal Φ Nmax : ℝ} {N : κ → ℝ} {g E A : κ → ι → ℝ} {u k0 : κ → ι}
    (hkB : 0 < kB) (hTmin : 0 < Tmin) (hT : Tmin ≤ T) (hThat : Tmin ≤ That)
    (hg : ∀ s k, 0 < g s k) (hE : ∀ s k, 0 ≤ E s k) (hFcal : 0 < Fcal)
    (hA : ∀ s, 0 < A s (u s)) (hN : ∀ s, 0 < N s) (hNmax : ∀ s, N s ≤ Nmax)
    (hΦ0 : 0 ≤ Φ)
    (hδp1 : ∀ s, Real.exp (E s (u s) * |That - T| / (kB * Tmin ^ 2)) - 1 < 1)
    (henv : ∀ s, tempResponseErrorBound kB Tmin T That (g s) (E s) (u s) (k0 s) ≤ Φ)
    (s : κ) :
    |composition (recoveredDensityAtT kB T That Fcal g E A u N) s - composition N s|
      ≤ compositionErrorBound N
          (totalDensity (recoveredDensityAtT kB T That Fcal g E A u N))
          (Nmax * Φ) s := by
  have hNhat_pos : ∀ t, 0 < recoveredDensityAtT kB T That Fcal g E A u N t := by
    intro t
    unfold recoveredDensityAtT
    rw [classicDensity_temperature_aliasing (hg t) hFcal (u t) (hA t)]
    exact div_pos (mul_pos (hN t) (responseFactor_pos (hg t) (hA t)))
      (responseFactor_pos (hg t) (hA t))
  have hStot : 0 < totalDensity N := totalDensity_pos hN
  have hShat : 0 < totalDensity (recoveredDensityAtT kB T That Fcal g E A u N) :=
    totalDensity_pos hNhat_pos
  have hN0 : ∀ t, 0 ≤ N t := fun t => (hN t).le
  have hdelta : ∀ t, |recoveredDensityAtT kB T That Fcal g E A u N t - N t| ≤ Nmax * Φ := by
    intro t
    have h2 : |recoveredDensityAtT kB T That Fcal g E A u N t - N t|
        ≤ N t * tempResponseErrorBound kB Tmin T That (g t) (E t) (u t) (k0 t) :=
      classicDensity_temperature_aliasing_error hkB hTmin hT hThat (hg t) (hE t)
        hFcal (u t) (k0 t) (hA t) (hN t) (hδp1 t)
    have hc : N t * tempResponseErrorBound kB Tmin T That (g t) (E t) (u t) (k0 t) ≤ N t * Φ :=
      mul_le_mul_of_nonneg_left (henv t) (hN t).le
    have hd : N t * Φ ≤ Nmax * Φ := mul_le_mul_of_nonneg_right (hNmax t) hΦ0
    linarith
  exact composition_abs_sub_le_bound hN0 hStot hShat hdelta s

/-! ### Non-vacuity witnesses (T-split family)

The `nvTa*` data instantiate the temperature-split family on `ι = Fin 1`/`Fin 2` with
`k_B = Tmin = Fcal = 1`. The two-level instances exhibit genuine `T`-dependence and genuine
positive bounding constants (not a vacuous `0 ≤ 0`); the one-level instance only shows the
hypotheses are satisfiable. -/

private def nvTag : Fin 1 → ℝ := fun _ => 1
private def nvTaE1 : Fin 1 → ℝ := fun _ => 1
private def nvTaA : Fin 1 → ℝ := fun _ => 1
private def nvTag2 : Fin 2 → ℝ := fun _ => 1
private def nvTaE2 : Fin 2 → ℝ := ![0, 1]
private def nvTaE2' : Fin 2 → ℝ := ![1, 0]
private def nvTaA2 : Fin 2 → ℝ := fun _ => 1

/-- The temperature-aliasing identity applies (`E = 1`, `T = 1`, `T̂ = 2`): all hypotheses are
jointly satisfiable. With a single level the response factor does not depend on `T`
(`U = g·exp(−E/k_BT)` cancels the Boltzmann factor), so in this instance the right-hand side
equals `4` and the wrong-`T` reader returns the true density; it is a satisfiability witness, not
an example of temperature aliasing. -/
example :
    Classic.classicDensity 1 2 1 nvTag nvTaE1 nvTaA 0
        (lineIntensity 1 1 4 1 nvTag nvTaE1 nvTaA 0)
      = 4 * responseFactor 1 1 nvTag nvTaE1 nvTaA 0 / responseFactor 1 2 nvTag nvTaE1 nvTaA 0 :=
  classicDensity_temperature_aliasing (fun _ => one_pos) one_pos 0 (by norm_num [nvTaA])

/-- The temperature-error bound applies (line `u = 0` has `E = 0`, so `delta_exp = 0 < 1`; a second
level at `E = 1` makes the `U` channel genuinely nonzero). Hypotheses jointly satisfiable. -/
example :
    |Classic.classicDensity 1 2 1 nvTag2 nvTaE2 nvTaA2 0
        (lineIntensity 1 1 5 1 nvTag2 nvTaE2 nvTaA2 0) - 5|
      ≤ 5 * tempResponseErrorBound 1 1 1 2 nvTag2 nvTaE2 0 0 := by
  apply classicDensity_temperature_aliasing_error one_pos one_pos le_rfl one_le_two
    (fun _ => one_pos) (fun k => by fin_cases k <;> norm_num [nvTaE2]) one_pos 0 0
    (by norm_num [nvTaA2]) (by norm_num)
  norm_num [nvTaE2, Real.exp_zero]

/-- The temperature-error bounding constant is a genuine positive value (`= 1`), so the bound is not
the vacuous `0 ≤ 0`: the `U` channel contributes `delta_U = 1`. -/
example : tempResponseErrorBound 1 1 1 2 nvTag2 nvTaE2 0 0 = 1 := by
  unfold tempResponseErrorBound
  norm_num [nvTag2, nvTaE2, Fin.sum_univ_two, Real.exp_zero]

/-- The energy-channel bound applies with a genuine energy mismatch (`E' = (1,0)` vs `E = (0,1)`,
`U' = U` by the level swap): all hypotheses are jointly satisfiable. -/
example :
    |Classic.classicDensity 1 1 1 nvTag2 nvTaE2' nvTaA2 0
        (lineIntensity 1 1 3 1 nvTag2 nvTaE2 nvTaA2 0) - 3|
      ≤ 3 * (Real.exp (|nvTaE2' 0 - nvTaE2 0| / (1 * 1)) - 1) := by
  apply classicDensity_aliasing_error_energy one_pos one_pos le_rfl
    (fun _ => one_pos) (fun _ => one_pos) one_pos 0
    (by norm_num [nvTaA2]) (by norm_num [nvTaA2]) (by norm_num)
    (by norm_num [nvTag2, nvTaA2])
  simp only [partitionFunction, boltzmannFactor, Fin.sum_univ_two, nvTaE2, nvTaE2',
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- The energy-channel bounding constant is a genuine positive value (`3·(exp 1 − 1)`), so the bound
is not the vacuous `0 ≤ 0`. -/
example : (3 : ℝ) * (Real.exp (|nvTaE2' 0 - nvTaE2 0| / (1 * 1)) - 1) = 3 * (Real.exp 1 - 1) := by
  norm_num [nvTaE2, nvTaE2']

/-! ## Relative (abundance-scaled) composition bound (frontier FT-07) -/

/-- Closure under two-sided ratio bounds `(1 - δ)·N̂ ≤ N ≤ (1 + δ)·N̂`. -/
private theorem comp_rel_ratio {N Nhat : κ → ℝ} {δ : ℝ} (hN : ∀ s, 0 < N s) (hδ0 : 0 ≤ δ)
    (hδ1 : δ < 1)
    (hlo : ∀ t, N t ≤ (1 + δ) * Nhat t) (hhi : ∀ t, (1 - δ) * Nhat t ≤ N t) (s : κ) :
    |composition Nhat s - composition N s| ≤ (2 * δ / (1 - δ)) * composition N s := by
  have hNh : ∀ t, 0 < Nhat t := fun t => by
    have := hlo t; have := hN t; nlinarith
  have hS : 0 < ∑ t, N t := Finset.sum_pos (fun t _ => hN t) ⟨s, Finset.mem_univ s⟩
  have hSh : 0 < ∑ t, Nhat t := Finset.sum_pos (fun t _ => hNh t) ⟨s, Finset.mem_univ s⟩
  have hSlo : ∑ t, N t ≤ (1 + δ) * ∑ t, Nhat t := by
    rw [Finset.mul_sum]; exact Finset.sum_le_sum fun t _ => hlo t
  have hShi : (1 - δ) * ∑ t, Nhat t ≤ ∑ t, N t := by
    rw [Finset.mul_sum]; exact Finset.sum_le_sum fun t _ => hhi t
  have h1δ : 0 < 1 - δ := by linarith
  unfold composition totalDensity
  set S := ∑ t, N t
  set Sh := ∑ t, Nhat t
  have key : Nhat s / Sh - N s / S = (Nhat s * S - N s * Sh) / (Sh * S) := by
    field_simp
  rw [key, abs_div, abs_of_pos (mul_pos hSh hS), div_le_iff₀ (mul_pos hSh hS)]
  have hrhs : 2 * δ / (1 - δ) * (N s / S) * (Sh * S) = 2 * δ * N s * Sh / (1 - δ) := by
    field_simp
  rw [hrhs, le_div_iff₀ h1δ]
  have hNs := hN s
  have hNhs := hNh s
  have p1 : (1 - δ) * Nhat s * S ≤ N s * S := mul_le_mul_of_nonneg_right (hhi s) hS.le
  have p2 : N s * S ≤ N s * ((1 + δ) * Sh) := mul_le_mul_of_nonneg_left hSlo hNs.le
  have p3 : N s * S ≤ (1 + δ) * Nhat s * S := mul_le_mul_of_nonneg_right (hlo s) hS.le
  have p4 : N s * ((1 - δ) * Sh) ≤ N s * S := mul_le_mul_of_nonneg_left hShi hNs.le
  have q : (1 - δ) * (N s * ((1 - δ) * Sh)) ≤ (1 - δ) * ((1 + δ) * Nhat s * S) :=
    mul_le_mul_of_nonneg_left (p4.trans p3) h1δ.le
  have hX : 0 ≤ δ ^ 2 * (N s * Sh) := by positivity
  rcases abs_cases (Nhat s * S - N s * Sh) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h]
  · nlinarith
  · nlinarith

/-- **Relative closure bound for the classic reader under atomic-data error.** Each species `s`
is emitted with the TRUE atomic data `(g s, E s, A s)` at density `N s` (common calibration
`Fcal`, temperature `T` known to the reader) and read off its chosen line `u s` with the WRONG
data `(g' s, E' s, A' s)` (`recoveredDensity`). If every species' response factor
`ρ = g_u·A_u·exp(−E_u/(kB T))/U(T)` is off by at most a relative `δ`, `0 ≤ δ < 1` (`hpert`),
then every recovered number fraction obeys
  `|Ĉ_s − C_s| ≤ (2δ/(1 − δ)) · C_s`,
an error that scales with the true fraction `C_s`. The absolute twin
`classicComposition_atomicData_error` bounds the same error by `compositionErrorBound` with a
density cap `Nmax`, a bound whose leading term `Nmax·δ/((1 − δ)·Ŝ)` does not shrink with `C_s`,
so it is uninformative for minor elements. Example: `δ = 0.05` gives `2δ/(1 − δ) = 2/19 ≈ 0.105`,
so a species with `C_s = 0.005` is recovered within `≈ 5.26·10⁻⁴`.

Route: the EXACT aliasing identity `classicDensity_aliasing` gives `N̂_t = N_t·ρ_t/ρ'_t`, and
`hpert` gives `(1 − δ)·ρ_t ≤ ρ'_t ≤ (1 + δ)·ρ_t`, so `(1 − δ)·N̂_t ≤ N_t ≤ (1 + δ)·N̂_t` for every
species; closure then puts `Ĉ_s/C_s` in `[(1 − δ)/(1 + δ), (1 + δ)/(1 − δ)]`, whose larger
deviation from `1` is `2δ/(1 − δ)`. The constant is approached (numerical check, not
Lean-checked) when species `s` is read high by `1/(1 − δ)`, every other species low by
`1/(1 + δ)`, and the others' share tends to `1`. Routing instead through the additive envelope
`|N̂_t − N_t| ≤ N_t·δ/(1 − δ)` (`classicDensity_aliasing_error`) discards the multiplicative
structure and gives only `2δ/(1 − 2δ)` on `δ < 1/2`, which this statement dominates.

Hypotheses: `hg`, `hg'` (positive degeneracies: both partition functions are positive and
cancel); `hFcal` (the calibration cancels); `hA'` (positive analyst's chosen-line Einstein
coefficient; `A'` divides in the reader); `hA` (positive true chosen-line coefficient; implied by
`hg`, `hg'`, `hA'`, `hδ0` and `hpert`, Lean-checked in the statement-audit scratch, and kept as
the physical guard, as in the absolute twin); `hN` (positive true densities: the bound is
relative to them and the totals must be positive); `hδ0`; `hδ1 : δ < 1` (the absolute twin's
domain; necessary, by hand and not Lean-checked: at `δ ≥ 1` the analyst's response factor can
approach `0` and `Ĉ_s/C_s` is unbounded); `hpert` (the lumped per-species relative response
error: the per-symbol errors in `g`, `A`, `E`, `U` are collapsed into one scalar `δ`, an assumed
input).

Scope: relation REDUCED (lumped uniform relative response error `δ`, classic reader at known
`T`; the algebra itself is exact); definitions used: `lineIntensity` (model tag REDUCED, optically
thin LTE forward map, reached through `recoveredDensity`), `Classic.classicDensity` (estimator
packaging), `composition` (no model tag); published REDUCED. Citation: Tognoni 2010, as for the
absolute twin. -/
theorem classicComposition_atomicData_error_rel [Nonempty ι]
    {kB T Fcal δ : ℝ} {N : κ → ℝ} {g E A g' E' A' : κ → ι → ℝ} {u : κ → ι}
    (hg : ∀ s k, 0 < g s k) (hg' : ∀ s k, 0 < g' s k) (hFcal : 0 < Fcal)
    (hA : ∀ s, 0 < A s (u s)) (hA' : ∀ s, 0 < A' s (u s))
    (hN : ∀ s, 0 < N s) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hpert : ∀ s, |responseFactor kB T (g' s) (E' s) (A' s) (u s)
                    - responseFactor kB T (g s) (E s) (A s) (u s)|
                  ≤ δ * responseFactor kB T (g s) (E s) (A s) (u s))
    (s : κ) :
    |composition (recoveredDensity kB T Fcal g E A g' E' A' u N) s - composition N s|
      ≤ (2 * δ / (1 - δ)) * composition N s := by
  have hρ : ∀ t, 0 < responseFactor kB T (g t) (E t) (A t) (u t) := fun t => by
    unfold responseFactor
    exact div_pos (mul_pos (mul_pos (hg t (u t)) (hA t)) (boltzmannFactor_pos _ _ _))
      (partitionFunction_pos (hg t))
  have hρ' : ∀ t, 0 < responseFactor kB T (g' t) (E' t) (A' t) (u t) := fun t => by
    unfold responseFactor
    exact div_pos (mul_pos (mul_pos (hg' t (u t)) (hA' t)) (boltzmannFactor_pos _ _ _))
      (partitionFunction_pos (hg' t))
  have hrec : ∀ t, recoveredDensity kB T Fcal g E A g' E' A' u N t
      = N t * responseFactor kB T (g t) (E t) (A t) (u t)
          / responseFactor kB T (g' t) (E' t) (A' t) (u t) := fun t => by
    unfold recoveredDensity
    exact classicDensity_aliasing (hg t) (hg' t) hFcal (u t) (hA' t)
  refine comp_rel_ratio hN hδ0 hδ1 (fun t => ?_) (fun t => ?_) s
  · rw [hrec t, mul_div_assoc', le_div_iff₀ (hρ' t)]
    have := (abs_le.mp (hpert t)).2
    have := hN t
    nlinarith
  · rw [hrec t, mul_div_assoc', div_le_iff₀ (hρ' t)]
    have := (abs_le.mp (hpert t)).1
    have := hN t
    nlinarith

end CflibsFormal
