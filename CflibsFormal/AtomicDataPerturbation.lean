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

## Literature

Tognoni et al. 2010 (the CF-LIBS review) identifies atomic-parameter uncertainty — chiefly
transition-probability (`A`) error, but also `g`, `E`, and partition-function error — as the
dominant contribution to the CF-LIBS accuracy budget once the plasma is well-characterized.
The `EXACT` aliasing identity is the algebraic substrate of that discussion: it exhibits the
recovered density as the true density multiplied by a *ratio of response factors*, so any
mismatch between the tabulated and the true atomic data biases the result multiplicatively.
The `REDUCED` bounds turn that identity into first-order error budgets.

## Honest scope

`classicDensity_aliasing` is `EXACT`: a faithful identity, no approximation, `Fcal` and every
partition-function/Boltzmann factor cancels as it does physically. The three error results are
`REDUCED`: they replace the full per-symbol atomic-data error by *lumped* relative bounds — a
single `δ` on the response factor (`classicDensity_aliasing_error`), a `δ_gA`/`δ_U` split with
`E' = E` (`classicDensity_aliasing_error_channels`), or a *uniform* `δ` and a density cap
`Nmax` across species (`classicComposition_atomicData_error`). No linearization of the forward
map is used — the reductions are only in the *hypotheses* (stronger, lumped) not in the
algebra, which stays exact.

This grounds the runtime hard-FAIL on missing / NULL atomic data: `classicDensity_aliasing`
shows that inverting with wrong data returns `N · ρ_true/ρ_wrong`, an *arbitrary* multiplicative
bias with no self-diagnosing signature. A solver handed NULL or unvalidated `(g, A, E, U)` can
therefore emit a perfectly finite, perfectly wrong number; the only sound response is to refuse.
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

end CflibsFormal
