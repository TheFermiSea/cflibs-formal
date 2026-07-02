/-
Copyright (c) 2026 Brian Squires. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Squires
-/
import Mathlib
import CflibsFormal.Boltzmann

/-!
# CF-LIBS formalization — the `U_s(T)` partition-function Lipschitz leg (gap #5)

The end-to-end error budget (`ErrorBudget.lean`, `CompositionRobustness.lean`) still keeps the
*temperature* channel and the *density/composition* channel independent: the recovered
temperature `T̂` feeds the density reader only through the species partition function `U_s(T̂)`,
and no bound on `|U_s(T̂) − U_s(T)|` was available. This module supplies exactly that leg — the
sensitivity of the partition function `U(T) = ∑ₖ gₖ·exp(−Eₖ/(k_B T))` to a temperature error —
so a recovered-temperature error can be converted into a *relative* `U`-error `δ_U`, the input
that the atomic-data density channel (`AtomicDataPerturbation.classicDensity_aliasing_error` and
its `δ_U`-slotted `classicDensity_aliasing_error_channels`) consumes.

The results, in order:

* `partitionFunction_two_point_bound` — the **inverse-temperature** two-point bound
  `|U(T₁) − U(T₂)| ≤ (∑ₖ gₖ·Eₖ)·|1/(k_B T₁) − 1/(k_B T₂)|`. Proved termwise: each Boltzmann
  factor obeys the two-point exponential bound `|exp aₖ − exp bₖ| ≤ max(exp aₖ, exp bₖ)·|aₖ − bₖ|`,
  and with `Eₖ ≥ 0` the exponents `aₖ, bₖ = −Eₖ/(k_B T) ≤ 0` force `max(…) ≤ 1`; the energy gap
  `Eₖ` factors cleanly out of `|aₖ − bₖ|`, and `Finset.abs_sum_le_sum_abs` closes the sum.
* `partitionFunction_lipschitz_temp` — the **Lipschitz-in-`T`** form on a floor `Tmin ≤ T₁, T₂`
  (`0 < Tmin`): converting `|1/(k_B T₁) − 1/(k_B T₂)| ≤ |T₁ − T₂|/(k_B·Tmin²)` gives
  `|U(T₁) − U(T₂)| ≤ L·|T₁ − T₂|` with the explicit constant `L = (∑ₖ gₖ·Eₖ)/(k_B·Tmin²)`.
* `partitionFunction_relative_error_temp` — the **relative** form: dividing by `U(T₂) > 0`
  (`partitionFunction_pos`) yields `|U(T₁) − U(T₂)|/U(T₂) ≤ L·|T₁ − T₂|/U(T₂)`, i.e. the relative
  partition-function error `δ_U` induced by a temperature error. This `δ_U` is the scalar the
  density channel's `δ_U` slot consumes (see the handoff note in Honest scope).

## Literature

Tognoni et al. 2010 (the CF-LIBS review) accounts partition-function uncertainty as one channel
of the CF-LIBS accuracy budget once the plasma is characterized. There, `U(T)` error enters the
recovered density multiplicatively (the substrate is
`AtomicDataPerturbation.classicDensity_aliasing`); this module quantifies the piece of that error
that a residual *temperature* mis-estimate produces, closing the `U_s(T)`-sensitivity leg the
error budget referenced but had not bounded.

## Honest scope

All three public results are `REDUCED` (Tognoni 2010): the constant `∑ₖ gₖ·Eₖ` upper-bounds the
exact sensitivity `∑ₖ gₖ·Eₖ·exp(−Eₖ/(k_B T))` by discarding the factor `exp(…) ≤ 1` (valid because
`Eₖ ≥ 0`), and the Lipschitz/relative forms add the further over-estimate `T₁·T₂ ≥ Tmin²`. No
approximation of the forward model is used — the reductions live only in the *constant* (an honest
over-estimate) and the *floor hypothesis* `Tmin`. The underlying two-point exponential bound and the
inverse-temperature gap bound are pure real analysis, kept as private helpers.

Handoff (what closes gap #5, what remains): this module closes the missing `U_s(T)` Lipschitz
leg — a temperature error now maps to a bounded relative `U`-error `δ_U`. A *literal* Lean
composition into `classicDensity_aliasing_error_channels` is **not** delivered: that theorem's
`δ_U` hypothesis is a
same-`T` atomic-data `U`-mismatch `|U(T; g') − U(T; g)|`, whereas the temperature channel is a
same-`g` `U`-shift `|U(T̂; g) − U(T; g)|`. Wiring the two requires a forward/inverse-`T`-split
aliasing identity (`classicDensity` inverting at `T̂ ≠ T` the emitting `T`) that
`AtomicDataPerturbation` does not currently expose; `partitionFunction_relative_error_temp` provides
the `δ_U` such a bridge would consume. The remaining cross-channel `δ → ΔC` coupling is therefore
left as the honest residual recorded in `docs/SOLVER_FORMALIZATION_GAPS.md` item 5.
-/

namespace CflibsFormal

open Finset Real
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- **Elementary exponential slope bound.** For all reals `a, b`,
`exp a − exp b ≤ exp a · (a − b)` (from `Real.add_one_le_exp (b − a)`). Private helper (no
scope-tag row); pure real analysis. Re-derived here because the copy in `Identifiability.lean`
is private to that module. -/
private lemma exp_sub_le_mul (a b : ℝ) :
    Real.exp a - Real.exp b ≤ Real.exp a * (a - b) := by
  have hstep : b - a + 1 ≤ Real.exp (b - a) := Real.add_one_le_exp (b - a)
  have hle : Real.exp a * (1 - Real.exp (b - a)) ≤ Real.exp a * (a - b) :=
    mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos a).le
  have hrw : Real.exp a * (1 - Real.exp (b - a)) = Real.exp a - Real.exp b := by
    have hab : a + (b - a) = b := by ring
    rw [mul_sub, mul_one, ← Real.exp_add, hab]
  rwa [hrw] at hle

/-- **Two-point Lipschitz-type bound for `exp`.** `|exp a − exp b| ≤ max(exp a, exp b)·|a − b|`:
the slope is controlled by the larger endpoint value. Symmetrising `exp_sub_le_mul` over
`le_total b a`. Private helper (no scope-tag row); pure real analysis. -/
private lemma abs_exp_sub_le (a b : ℝ) :
    |Real.exp a - Real.exp b| ≤ max (Real.exp a) (Real.exp b) * |a - b| := by
  rcases le_total b a with h | h
  · rw [max_eq_left (Real.exp_le_exp.mpr h),
      abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr h)),
      abs_of_nonneg (sub_nonneg.mpr h)]
    exact exp_sub_le_mul a b
  · rw [max_eq_right (Real.exp_le_exp.mpr h),
      abs_sub_comm (Real.exp a) (Real.exp b), abs_sub_comm a b,
      abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr h)),
      abs_of_nonneg (sub_nonneg.mpr h)]
    exact exp_sub_le_mul b a

/-- **Inverse-temperature gap bound.** On a floor `Tmin ≤ T₁, T₂` (`0 < Tmin`, `0 < k_B`),
`|1/(k_B T₁) − 1/(k_B T₂)| ≤ |T₁ − T₂|/(k_B·Tmin²)`, since the difference equals
`(T₂ − T₁)/(k_B T₁ T₂)` and `T₁ T₂ ≥ Tmin²`. Private helper (no scope-tag row); pure real
algebra. -/
private lemma inv_kT_sub_le {kB Tmin T1 T2 : ℝ}
    (hkB : 0 < kB) (hTmin : 0 < Tmin) (hT1 : Tmin ≤ T1) (hT2 : Tmin ≤ T2) :
    |1 / (kB * T1) - 1 / (kB * T2)| ≤ |T1 - T2| / (kB * Tmin ^ 2) := by
  have hT1pos : 0 < T1 := lt_of_lt_of_le hTmin hT1
  have hT2pos : 0 < T2 := lt_of_lt_of_le hTmin hT2
  have hkT1 : kB * T1 ≠ 0 := (mul_pos hkB hT1pos).ne'
  have hkT2 : kB * T2 ≠ 0 := (mul_pos hkB hT2pos).ne'
  have hbig : 0 < kB * T1 * T2 := mul_pos (mul_pos hkB hT1pos) hT2pos
  have hsmall : 0 < kB * Tmin ^ 2 := mul_pos hkB (pow_pos hTmin 2)
  have heq : 1 / (kB * T1) - 1 / (kB * T2) = (T2 - T1) / (kB * T1 * T2) := by
    field_simp
  rw [heq, abs_div, abs_of_pos hbig, abs_sub_comm T2 T1, div_le_div_iff₀ hbig hsmall]
  have hTsq : Tmin ^ 2 ≤ T1 * T2 := by
    rw [sq]; exact mul_le_mul hT1 hT2 hTmin.le hT1pos.le
  have hden : kB * Tmin ^ 2 ≤ kB * T1 * T2 := by
    calc kB * Tmin ^ 2 ≤ kB * (T1 * T2) := mul_le_mul_of_nonneg_left hTsq hkB.le
      _ = kB * T1 * T2 := by ring
  exact mul_le_mul_of_nonneg_left hden (abs_nonneg _)

/-- **Two-point partition-function bound — the `U_s(T)` sensitivity leg (`REDUCED`, Tognoni 2010).**

For `k_B > 0`, `0 < T₁, T₂`, positive degeneracies `gₖ > 0`, and non-negative level energies
`Eₖ ≥ 0` (measured from the ground state), the partition function's sensitivity to a change of
inverse temperature is bounded by

`|U(T₁) − U(T₂)| ≤ (∑ₖ gₖ·Eₖ)·|1/(k_B T₁) − 1/(k_B T₂)|`.

Reduction: the exact sensitivity of the `k`-th term is `gₖ·Eₖ·exp(−Eₖ/(k_B T))`; the constant
`∑ₖ gₖ·Eₖ` upper-bounds it by discarding `exp(−Eₖ/(k_B T)) ≤ 1`, which holds precisely because
`Eₖ ≥ 0` makes both exponents `≤ 0` (so `max(exp aₖ, exp bₖ) ≤ 1`). The forward model is exact;
only the constant is an honest over-estimate. -/
theorem partitionFunction_two_point_bound
    {kB T1 T2 : ℝ} {g E : ι → ℝ}
    (hkB : 0 < kB) (hT1 : 0 < T1) (hT2 : 0 < T2)
    (hg : ∀ k, 0 < g k) (hE : ∀ k, 0 ≤ E k) :
    |partitionFunction kB T1 g E - partitionFunction kB T2 g E|
      ≤ (∑ k, g k * E k) * |1 / (kB * T1) - 1 / (kB * T2)| := by
  set D : ℝ := 1 / (kB * T1) - 1 / (kB * T2) with hD
  have hdiff : partitionFunction kB T1 g E - partitionFunction kB T2 g E
      = ∑ k, g k * (Real.exp (-E k / (kB * T1)) - Real.exp (-E k / (kB * T2))) := by
    simp only [partitionFunction, boltzmannFactor]
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  rw [hdiff]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum (fun k _ => ?_)
  have hkT1 : 0 < kB * T1 := mul_pos hkB hT1
  have hkT2 : 0 < kB * T2 := mul_pos hkB hT2
  set a := -E k / (kB * T1) with ha
  set b := -E k / (kB * T2) with hb
  have hale : a ≤ 0 := by
    rw [ha, neg_div]; exact neg_nonpos.mpr (div_nonneg (hE k) hkT1.le)
  have hble : b ≤ 0 := by
    rw [hb, neg_div]; exact neg_nonpos.mpr (div_nonneg (hE k) hkT2.le)
  have hexpa : Real.exp a ≤ 1 := by
    calc Real.exp a ≤ Real.exp 0 := Real.exp_le_exp.mpr hale
      _ = 1 := Real.exp_zero
  have hexpb : Real.exp b ≤ 1 := by
    calc Real.exp b ≤ Real.exp 0 := Real.exp_le_exp.mpr hble
      _ = 1 := Real.exp_zero
  have hmax : max (Real.exp a) (Real.exp b) ≤ 1 := max_le hexpa hexpb
  have h3 : |a - b| = E k * |D| := by
    rw [ha, hb, hD,
      show -E k / (kB * T1) - -E k / (kB * T2)
        = -(E k * (1 / (kB * T1) - 1 / (kB * T2))) from by ring,
      abs_neg, abs_mul, abs_of_nonneg (hE k)]
  have hbound : |Real.exp a - Real.exp b| ≤ E k * |D| := by
    calc |Real.exp a - Real.exp b|
        ≤ max (Real.exp a) (Real.exp b) * |a - b| := abs_exp_sub_le a b
      _ ≤ 1 * |a - b| := mul_le_mul_of_nonneg_right hmax (abs_nonneg _)
      _ = |a - b| := one_mul _
      _ = E k * |D| := h3
  have habs : |g k * (Real.exp a - Real.exp b)| = g k * |Real.exp a - Real.exp b| := by
    rw [abs_mul, abs_of_pos (hg k)]
  rw [habs]
  calc g k * |Real.exp a - Real.exp b|
      ≤ g k * (E k * |D|) := mul_le_mul_of_nonneg_left hbound (hg k).le
    _ = g k * E k * |D| := by ring

/-- **Lipschitz-in-`T` partition-function bound (`REDUCED`, Tognoni 2010).**

On a temperature floor `Tmin ≤ T₁, T₂` (`0 < Tmin`), with `k_B > 0`, `gₖ > 0`, `Eₖ ≥ 0`, the
partition function is Lipschitz in `T` with the explicit constant `L = (∑ₖ gₖ·Eₖ)/(k_B·Tmin²)`:

`|U(T₁) − U(T₂)| ≤ (∑ₖ gₖ·Eₖ)/(k_B·Tmin²) · |T₁ − T₂|`.

Immediate from `partitionFunction_two_point_bound` and the inverse-temperature gap bound
`|1/(k_B T₁) − 1/(k_B T₂)| ≤ |T₁ − T₂|/(k_B·Tmin²)`. Reduction: the floor `Tmin` supplies the
`T₁ T₂ ≥ Tmin²` over-estimate on top of the two-point bound's `exp ≤ 1` over-estimate. This is the
`U_s(T)` sensitivity leg of the CF-LIBS temperature→composition error budget. -/
theorem partitionFunction_lipschitz_temp
    {kB Tmin T1 T2 : ℝ} {g E : ι → ℝ}
    (hkB : 0 < kB) (hTmin : 0 < Tmin) (hT1 : Tmin ≤ T1) (hT2 : Tmin ≤ T2)
    (hg : ∀ k, 0 < g k) (hE : ∀ k, 0 ≤ E k) :
    |partitionFunction kB T1 g E - partitionFunction kB T2 g E|
      ≤ (∑ k, g k * E k) / (kB * Tmin ^ 2) * |T1 - T2| := by
  have hT1pos : 0 < T1 := lt_of_lt_of_le hTmin hT1
  have hT2pos : 0 < T2 := lt_of_lt_of_le hTmin hT2
  have hsum : 0 ≤ ∑ k, g k * E k := Finset.sum_nonneg (fun k _ => mul_nonneg (hg k).le (hE k))
  have hmain := partitionFunction_two_point_bound hkB hT1pos hT2pos hg hE
  have hinv := inv_kT_sub_le hkB hTmin hT1 hT2
  calc |partitionFunction kB T1 g E - partitionFunction kB T2 g E|
      ≤ (∑ k, g k * E k) * |1 / (kB * T1) - 1 / (kB * T2)| := hmain
    _ ≤ (∑ k, g k * E k) * (|T1 - T2| / (kB * Tmin ^ 2)) :=
        mul_le_mul_of_nonneg_left hinv hsum
    _ = (∑ k, g k * E k) / (kB * Tmin ^ 2) * |T1 - T2| := by ring

/-- **Relative partition-function error from a temperature error (`REDUCED`, Tognoni 2010).**

Dividing the Lipschitz bound by `U(T₂) > 0` (`partitionFunction_pos`) yields the *relative*
partition-function error induced by a temperature error:

`|U(T₁) − U(T₂)|/U(T₂) ≤ (∑ₖ gₖ·Eₖ)/(k_B·Tmin²)·|T₁ − T₂| / U(T₂)`.

The right-hand side is the scalar `δ_U` that a `U`-channel density bound consumes (e.g. the `δ_U`
slot of `AtomicDataPerturbation.classicDensity_aliasing_error_channels`): a recovered-temperature
error `|T̂ − T|` becomes a bounded relative `U`-error. Reduction: same over-estimates as
`partitionFunction_lipschitz_temp`. See the module's Honest-scope note for why the composition into
the density channel is stated as a handoff (the density channel models a same-`T` atomic-data
`U`-mismatch, not the same-`g` temperature `U`-shift) rather than a literal Lean corollary. -/
theorem partitionFunction_relative_error_temp [Nonempty ι]
    {kB Tmin T1 T2 : ℝ} {g E : ι → ℝ}
    (hkB : 0 < kB) (hTmin : 0 < Tmin) (hT1 : Tmin ≤ T1) (hT2 : Tmin ≤ T2)
    (hg : ∀ k, 0 < g k) (hE : ∀ k, 0 ≤ E k) :
    |partitionFunction kB T1 g E - partitionFunction kB T2 g E| / partitionFunction kB T2 g E
      ≤ (∑ k, g k * E k) / (kB * Tmin ^ 2) * |T1 - T2| / partitionFunction kB T2 g E := by
  have hU2 : 0 < partitionFunction kB T2 g E := partitionFunction_pos hg
  have hlip := partitionFunction_lipschitz_temp hkB hTmin hT1 hT2 hg hE
  rw [div_le_div_iff₀ hU2 hU2]
  exact mul_le_mul_of_nonneg_right hlip hU2.le

/-! ### Non-vacuity witnesses

The `nvPl*` data instantiate the family on `ι = Fin 1` with `k_B = 1`, `g = 2`, `E = 3`. All
hypotheses (`k_B > 0`, `gₖ > 0`, `Eₖ ≥ 0`, `0 < Tmin ≤ T₁, T₂`) are jointly satisfiable, and the
bounding constants evaluate to genuine positive numbers (not a vacuous `0 ≤ 0`): at `T₁ = 1`,
`T₂ = 2` the two-point constant is `6·|1 − 1/2| = 3` and the Lipschitz constant (with `Tmin = 1`)
is `6/(1·1²)·|1 − 2| = 6`. -/

private def nvPlg : Fin 1 → ℝ := fun _ => 2
private def nvPlE : Fin 1 → ℝ := fun _ => 3

/-- The two-point bound applies (all hypotheses met): the partition-function difference at
`T₁ = 1`, `T₂ = 2` is bounded by the concrete constant `(∑ gₖEₖ)·|1/(1·1) − 1/(1·2)|`. -/
example :
    |partitionFunction (1 : ℝ) 1 nvPlg nvPlE - partitionFunction 1 2 nvPlg nvPlE|
      ≤ (∑ k, nvPlg k * nvPlE k) * |1 / ((1 : ℝ) * 1) - 1 / (1 * 2)| :=
  partitionFunction_two_point_bound one_pos one_pos two_pos
    (fun _ => by norm_num [nvPlg]) (fun _ => by norm_num [nvPlE])

/-- The two-point bounding constant is a genuine positive value (`= 3`), so the bound is not the
vacuous `0 ≤ 0`. -/
example : (∑ k, nvPlg k * nvPlE k) * |1 / ((1 : ℝ) * 1) - 1 / (1 * 2)| = 3 := by
  norm_num [nvPlg, nvPlE, Fin.sum_univ_one]

/-- The Lipschitz-in-`T` bound applies with floor `Tmin = 1 ≤ 1, 2`. -/
example :
    |partitionFunction (1 : ℝ) 1 nvPlg nvPlE - partitionFunction 1 2 nvPlg nvPlE|
      ≤ (∑ k, nvPlg k * nvPlE k) / ((1 : ℝ) * 1 ^ 2) * |(1 : ℝ) - 2| :=
  partitionFunction_lipschitz_temp one_pos one_pos le_rfl one_le_two
    (fun _ => by norm_num [nvPlg]) (fun _ => by norm_num [nvPlE])

/-- The Lipschitz constant `L = (∑ gₖEₖ)/(k_B·Tmin²)·|T₁ − T₂|` evaluates to the concrete
positive value `6`. -/
example : (∑ k, nvPlg k * nvPlE k) / ((1 : ℝ) * 1 ^ 2) * |(1 : ℝ) - 2| = 6 := by
  norm_num [nvPlg, nvPlE, Fin.sum_univ_one]

/-- The relative-error bound applies (the `δ_U` handoff quantity is well-formed and finite). -/
example :
    |partitionFunction (1 : ℝ) 1 nvPlg nvPlE - partitionFunction 1 2 nvPlg nvPlE|
        / partitionFunction 1 2 nvPlg nvPlE
      ≤ (∑ k, nvPlg k * nvPlE k) / ((1 : ℝ) * 1 ^ 2) * |(1 : ℝ) - 2|
          / partitionFunction 1 2 nvPlg nvPlE :=
  partitionFunction_relative_error_temp one_pos one_pos le_rfl one_le_two
    (fun _ => by norm_num [nvPlg]) (fun _ => by norm_num [nvPlE])

end CflibsFormal
