/-
Copyright (c) 2026 Brian Squires. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Squires
-/
import Mathlib
import CflibsFormal.SelfAbsorption
import CflibsFormal.EquivalentWidth
import CflibsFormal.CurveOfGrowth

/-!
# Profile escape factor versus the flat-slab self-absorption factor

`SelfAbsorption.selfAbsorptionFactor` is the flat-profile escape factor
`SA(τ) = (1 − exp(−τ))/τ`: one optical depth for the whole line. A real line has a profile
`ψ`, and its integrated self-absorbed strength is the equivalent width
`W(ψ, τ₀) = ∫ (1 − exp(−τ₀ ψ(x))) dx` (`EquivalentWidth.equivWidth`), whose optically thin
value is `τ₀ ∫ ψ`. This module compares the two.

## Main results

* `escape_ge_slab`: for a profile with `0 ≤ ψ ≤ 1` (so `τ₀` is at least the depth at every
  frequency; `τ₀` is the line-centre depth when `ψ` peaks at `1`), integrable, and `τ₀ > 0`,
  `SA(τ₀) · (τ₀ ∫ ψ) ≤ W(ψ, τ₀)`. The profile-integrated escape factor `W/(τ₀ ∫ ψ)` is at
  least the flat-slab factor at the line-centre depth. Equality holds for a rectangular profile
  (`equivWidth_rectangular`). Proof: the chord inequality of the convex `exp` applied pointwise
  at `t = ψ(x) ∈ [0, 1]`, then `integral_mono`.
* `inv_sub_inv_exp_sub_one_mem`: `0 < 1/τ − 1/(exp τ − 1) < 1/2` for `τ > 0`. Since
  `d/dτ log SA(τ) = 1/(exp τ − 1) − 1/τ` (`hasDerivAt_log_selfAbsorptionFactor`), this is the
  statement that `log SA` has slope in `(−1/2, 0)`. Both bounds are sharp in the limits.
* `log_selfAbsorptionFactor_lipschitz`: `|log SA(τ) − log SA(τ')| ≤ |τ − τ'|/2` for
  `τ, τ' ≥ 0`, the endpoint `τ = 0` included. An error `Δ` in the optical depth moves the log
  of the slab correction by at most `Δ/2`.

All four results are pure mathematics about the defined functions. No statement here says which
profile a real line has, or how well either factor corrects a measured intensity.

## Literature

Gornushkin, Anzano, King, Smith, Omenetto, Winefordner, "Curve of growth methodology applied
to laser-induced plasma emission spectroscopy", *Spectrochimica Acta Part B* **54** (1999) 491
— the curve of growth, its equivalent width and the slab escape factor; Bulajic, Corsi,
Cristoforetti, Legnaioli, Palleschi, Salvetti, Tognoni, "A procedure for correcting
self-absorption in calibration-free LIBS", *Spectrochimica Acta Part B* **57** (2002) 339 — the
self-absorption correction that uses `SA`.
-/

namespace CflibsFormal

open MeasureTheory

/-- Derivative of `exp t · (t − 2) + t + 2`. -/
private theorem hasDerivAt_exp_mul_sub_two_add (t : ℝ) :
    HasDerivAt (fun t => Real.exp t * (t - 2) + t + 2)
      (Real.exp t * (t - 2) + Real.exp t * 1 + 1) t :=
  (((Real.hasDerivAt_exp t).mul ((hasDerivAt_id t).sub_const 2)).add (hasDerivAt_id t)).add_const 2

/-- Positivity of `exp t · (t − 2) + t + 2` on `t > 0`: it vanishes at `0` and its derivative
`exp t · (t − 1) + 1` is positive there by `exp_mul_one_sub_lt_one`. -/
private theorem exp_mul_sub_two_add_pos {τ : ℝ} (hτ : 0 < τ) :
    0 < Real.exp τ * (τ - 2) + τ + 2 := by
  have hmono : StrictMonoOn (fun t => Real.exp t * (t - 2) + t + 2) (Set.Ici (0:ℝ)) := by
    refine strictMonoOn_of_hasDerivWithinAt_pos (convex_Ici (0:ℝ)) ?_
      (fun x _ => (hasDerivAt_exp_mul_sub_two_add x).hasDerivWithinAt) ?_
    · fun_prop
    · intro x hx
      rw [interior_Ici] at hx
      have hx' : 0 < x := hx
      nlinarith [exp_mul_one_sub_lt_one hx', Real.exp_pos x]
  have h0 : (0:ℝ) ∈ Set.Ici (0:ℝ) := Set.mem_Ici.mpr le_rfl
  have hτ' : τ ∈ Set.Ici (0:ℝ) := Set.mem_Ici.mpr hτ.le
  have := hmono h0 hτ' hτ
  simp at this
  linarith

/-- **The log slab self-absorption factor has slope in `(−1/2, 0)`.** For `τ > 0`,
`0 < 1/τ − 1/(exp τ − 1) < 1/2`. The middle expression is minus the derivative of
`log SA(τ) = log ((1 − exp(−τ))/τ)` (`hasDerivAt_log_selfAbsorptionFactor`, below); with it,
`log SA` is `1/2`-Lipschitz (`log_selfAbsorptionFactor_lipschitz`). Both bounds are strict
and sharp in the limits (`→ 1/2` as `τ → 0⁺`, `→ 0` as `τ → ∞`), so the proof goes through the
exact inequality `exp τ · (τ − 2) + τ + 2 > 0`, not a numerical estimate.

Hypothesis `hτ` is needed: at `τ = 0` Lean's `1/0 = 0` makes the middle expression `0`, and at
`τ = −1` it is `≈ 0.58 > 1/2`. Scope: PURE-MATH. -/
theorem inv_sub_inv_exp_sub_one_mem {τ : ℝ} (hτ : 0 < τ) :
    0 < 1 / τ - 1 / (Real.exp τ - 1) ∧ 1 / τ - 1 / (Real.exp τ - 1) < 1 / 2 := by
  constructor
  · have hlt : τ < Real.exp τ - 1 := by linarith [Real.add_one_lt_exp hτ.ne']
    have := one_div_lt_one_div_of_lt hτ hlt
    linarith
  · have hE : 0 < Real.exp τ - 1 := by linarith [Real.add_one_lt_exp hτ.ne']
    have hf := exp_mul_sub_two_add_pos hτ
    rw [div_sub_div _ _ hτ.ne' hE.ne', div_lt_div_iff₀ (mul_pos hτ hE) (by norm_num : (0:ℝ) < 2)]
    nlinarith [hf, Real.exp_pos τ]

/-! ### The log slab factor: derivative and a `1/2`-Lipschitz bound (frontier FT-13)

The proofs below were found by the proof queue for the audited statement
`log_selfAbsorptionFactor_lipschitz` and re-checked by its verifier; they are restated here on
the repository's own lemmas (`inv_sub_inv_exp_sub_one_mem`, `selfAbsorptionFactor_strictAntiOn`,
`selfAbsorptionFactor_le_one`). -/

/-- `1 − exp(−t) > 0` for `t > 0`. -/
private theorem one_sub_exp_neg_pos {t : ℝ} (ht : 0 < t) : 0 < 1 - Real.exp (-t) := by
  have := Real.exp_lt_exp.mpr (show -t < 0 by linarith)
  rw [Real.exp_zero] at this
  linarith

/-- For `t > 0` the slab factor is its non-totalized branch `(1 − exp(−t))/t`. -/
private theorem selfAbsorptionFactor_of_pos {t : ℝ} (ht : 0 < t) :
    selfAbsorptionFactor t = (1 - Real.exp (-t)) / t := by
  rw [selfAbsorptionFactor, if_neg ht.ne']

/-- Derivative of `log (1 − exp(−s)) − log s` at `t > 0`. -/
private theorem hasDerivAt_log_one_sub_exp_neg_sub_log {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => Real.log (1 - Real.exp (-s)) - Real.log s)
      (1 / (Real.exp t - 1) - 1 / t) t := by
  have he : HasDerivAt (fun s : ℝ => Real.exp (-s)) (Real.exp (-t) * -1) t :=
    (Real.hasDerivAt_exp (-t)).comp t ((hasDerivAt_id t).neg)
  have H := ((he.const_sub 1).log (one_sub_exp_neg_pos ht).ne').sub (Real.hasDerivAt_log ht.ne')
  have hpos : 0 < Real.exp t - 1 := by linarith [Real.add_one_lt_exp ht.ne']
  have hx : Real.exp (-t) * Real.exp t = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have h1 : 1 - Real.exp (-t) = Real.exp (-t) * (Real.exp t - 1) := by
    rw [mul_sub, hx, mul_one]
  have hv : -(Real.exp (-t) * -1) / (1 - Real.exp (-t)) - t⁻¹
      = 1 / (Real.exp t - 1) - 1 / t := by
    have hdiv : Real.exp (-t) / (1 - Real.exp (-t)) = 1 / (Real.exp t - 1) := by
      rw [div_eq_div_iff (one_sub_exp_neg_pos ht).ne' hpos.ne']
      rw [h1]; ring
    rw [show -(Real.exp (-t) * -1) = Real.exp (-t) by ring, hdiv]; ring
  exact H.congr_deriv hv

/-- **Derivative of the log slab self-absorption factor.** For `τ > 0`,
`d/dτ log SA(τ) = 1/(exp τ − 1) − 1/τ`. By `inv_sub_inv_exp_sub_one_mem` this slope lies in
`(−1/2, 0)`.

`hτ` is needed: `selfAbsorptionFactor` is the totalized `if τ = 0 then 1 else …`, and the
statement is about the open half-line where it is the smooth branch. Nothing is claimed at
`τ = 0` (the one-sided slope there is `−1/2`) or for `τ < 0`. Scope: PURE-MATH. -/
theorem hasDerivAt_log_selfAbsorptionFactor {τ : ℝ} (hτ : 0 < τ) :
    HasDerivAt (fun s => Real.log (selfAbsorptionFactor s))
      (1 / (Real.exp τ - 1) - 1 / τ) τ := by
  refine (hasDerivAt_log_one_sub_exp_neg_sub_log hτ).congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hτ] with s hs
  rw [selfAbsorptionFactor_of_pos hs, Real.log_div (one_sub_exp_neg_pos hs).ne' (ne_of_gt hs)]

/-- The endpoint estimate `0 ≤ log ((1 − exp(−b))/b) + b/2` for `b > 0`, i.e.
`SA(b) ≥ exp(−b/2)`: from `x ≤ sinh x` at `x = b/2`. -/
private theorem log_slab_add_half_nonneg {b : ℝ} (hb : 0 < b) :
    0 ≤ Real.log ((1 - Real.exp (-b)) / b) + b / 2 := by
  have hs : b ≤ Real.exp (b / 2) - Real.exp (-(b / 2)) := by
    have h := Real.self_le_sinh_iff.mpr (by linarith : (0:ℝ) ≤ b / 2)
    rw [Real.sinh_eq (b / 2)] at h
    linarith
  have hE : 0 < Real.exp (-(b / 2)) := Real.exp_pos (-(b / 2))
  have hmul : Real.exp (b / 2) * Real.exp (-(b / 2)) = 1 := by
    rw [← Real.exp_add, show b / 2 + -(b / 2) = 0 by ring, Real.exp_zero]
  have hE2 : Real.exp (-b) = Real.exp (-(b / 2)) * Real.exp (-(b / 2)) := by
    rw [show -b = -(b / 2) + -(b / 2) by ring, Real.exp_add]
  have h1 : Real.exp (-(b / 2)) * b ≤ 1 - Real.exp (-(b / 2)) * Real.exp (-(b / 2)) := by
    calc
      _ ≤ Real.exp (-(b / 2)) * (Real.exp (b / 2) - Real.exp (-(b / 2))) :=
        mul_le_mul_of_nonneg_left hs hE.le
      _ = Real.exp (-(b / 2)) * Real.exp (b / 2)
            - Real.exp (-(b / 2)) * Real.exp (-(b / 2)) := by ring
      _ = 1 - Real.exp (-(b / 2)) * Real.exp (-(b / 2)) := by rw [mul_comm, hmul]
  have h2 : Real.exp (-(b / 2)) ≤ (1 - Real.exp (-b)) / b := by
    rw [le_div_iff₀ hb, hE2]
    exact h1
  have h3 : -(b / 2) ≤ Real.log ((1 - Real.exp (-b)) / b) := by
    rw [← Real.log_exp (-(b / 2))]
    exact Real.log_le_log hE h2
  linarith

/-- `log SA` is nonincreasing on `[0, ∞)`: for `0 ≤ a ≤ b`, `log SA(b) ≤ log SA(a)`. -/
private theorem log_selfAbsorptionFactor_anti {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    Real.log (selfAbsorptionFactor b) ≤ Real.log (selfAbsorptionFactor a) := by
  have hle : selfAbsorptionFactor b ≤ selfAbsorptionFactor a := by
    rcases ha.eq_or_lt with h0 | hpos
    · subst h0
      have h1 : selfAbsorptionFactor 0 = 1 := by simp [selfAbsorptionFactor]
      rw [h1]
      exact selfAbsorptionFactor_le_one hab
    · exact selfAbsorptionFactor_strictAntiOn.antitoneOn hpos (lt_of_lt_of_le hpos hab) hab
  exact Real.log_le_log (selfAbsorptionFactor_pos (ha.trans hab)) hle

/-- `τ ↦ log SA(τ) + τ/2` is nondecreasing on `(0, ∞)`: its derivative
`1/(exp τ − 1) − 1/τ + 1/2` is positive by `inv_sub_inv_exp_sub_one_mem`. -/
private theorem log_selfAbsorptionFactor_add_half_monotoneOn :
    MonotoneOn (fun s => Real.log (selfAbsorptionFactor s) + s / 2) (Set.Ioi (0:ℝ)) := by
  have hd : ∀ x, 0 < x → HasDerivAt (fun s => Real.log (selfAbsorptionFactor s) + s / 2)
      (1 / (Real.exp x - 1) - 1 / x + 1 / 2) x :=
    fun x hx => (hasDerivAt_log_selfAbsorptionFactor hx).add ((hasDerivAt_id x).div_const 2)
  exact monotoneOn_of_hasDerivWithinAt_nonneg
      (f' := fun x => 1 / (Real.exp x - 1) - 1 / x + 1 / 2) (convex_Ioi 0)
    (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
    (fun x hx => by
      rw [interior_Ioi] at hx ⊢
      exact (hd x hx).hasDerivWithinAt)
    (fun x hx => by rw [interior_Ioi] at hx; linarith [(inv_sub_inv_exp_sub_one_mem hx).2])

/-- The one-sided form of the Lipschitz bound: for `0 ≤ a ≤ b`,
`log SA(a) − log SA(b) ≤ (b − a)/2`. The case `a = 0` uses the endpoint estimate
`log_slab_add_half_nonneg`, so no limit at `0` is taken. -/
private theorem log_selfAbsorptionFactor_sub_le {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    Real.log (selfAbsorptionFactor a) - Real.log (selfAbsorptionFactor b) ≤ (b - a) / 2 := by
  by_cases ha0 : a = 0
  · by_cases hb0 : b = 0
    · subst ha0 hb0
      simp [selfAbsorptionFactor]
    · have hb' : 0 < b := lt_of_le_of_ne (ha0 ▸ hab) (Ne.symm hb0)
      have hSA0 : selfAbsorptionFactor a = 1 := by simp [ha0, selfAbsorptionFactor]
      rw [hSA0, selfAbsorptionFactor_of_pos hb', Real.log_one]
      linarith [log_slab_add_half_nonneg hb']
  · have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    have hb' : 0 < b := by linarith
    have hmono := log_selfAbsorptionFactor_add_half_monotoneOn ha' hb' hab
    simp only at hmono
    linarith

/-- **The log slab self-absorption factor is `1/2`-Lipschitz on `τ ≥ 0`.**
`|log SA(τ) − log SA(τ')| ≤ |τ − τ'|/2` for `τ, τ' ≥ 0`.

Reading: the self-absorption correction divides an intensity by `SA(τ)`, so an error `Δ` in the
optical depth changes the log of the corrected intensity by at most `Δ/2`, at any depth. The
constant `1/2` is the supremum of the slope magnitude (approached as `τ → 0⁺`, never attained),
so it cannot be lowered; for large `τ` the slope is about `1/τ` and the bound is loose.

Proof: `log SA` is nonincreasing, and `log SA(τ) + τ/2` is nondecreasing on `(0, ∞)` because its
derivative `1/(exp τ − 1) − 1/τ + 1/2` is positive (`hasDerivAt_log_selfAbsorptionFactor`,
`inv_sub_inv_exp_sub_one_mem`); the endpoint `τ = 0` is handled by `SA(b) ≥ exp(−b/2)`, not by
a limit.

Hypotheses `hτ`, `hτ'` are needed: for negative arguments the slope magnitude exceeds `1/2`
(about `0.58` at `τ = −1`). Scope: PURE-MATH, a statement about the defined function. It says
nothing about how well the flat-slab `SA` corrects a real line (`selfAbsorptionFactor` carries
the model tag APPROXIMATION), and the error `Δ` in `τ` is an input, not something this bounds. -/
theorem log_selfAbsorptionFactor_lipschitz {τ τ' : ℝ} (hτ : 0 ≤ τ) (hτ' : 0 ≤ τ') :
    |Real.log (selfAbsorptionFactor τ) - Real.log (selfAbsorptionFactor τ')|
      ≤ |τ - τ'| / 2 := by
  cases le_total τ τ' with
  | inl hle =>
    have hant := log_selfAbsorptionFactor_anti hτ hle
    have hsub : 0 ≤ Real.log (selfAbsorptionFactor τ) - Real.log (selfAbsorptionFactor τ') := by
      linarith
    rw [abs_of_nonneg hsub]
    have hup := log_selfAbsorptionFactor_sub_le hτ hle
    have hd : 0 ≤ τ' - τ := by linarith
    rw [abs_sub_comm, abs_of_nonneg hd]
    linarith
  | inr hle =>
    have hant := log_selfAbsorptionFactor_anti hτ' hle
    have hsub' : Real.log (selfAbsorptionFactor τ) - Real.log (selfAbsorptionFactor τ') ≤ 0 := by
      linarith
    have hup := log_selfAbsorptionFactor_sub_le hτ' hle
    have hd : 0 ≤ τ - τ' := by linarith
    rw [abs_of_nonpos hsub', abs_of_nonneg hd]
    linarith

/-- Non-vacuity of `log_selfAbsorptionFactor_lipschitz` at the endpoint: from `τ = 0`
(`SA = 1`) to `τ' = 2` the log changes by at most `1`. -/
example : |Real.log (selfAbsorptionFactor 0) - Real.log (selfAbsorptionFactor 2)| ≤ |0 - 2| / 2 :=
  log_selfAbsorptionFactor_lipschitz le_rfl (by norm_num)

/-- Chord inequality of the convex `exp`: `(1 − exp(−τ)) · t ≤ 1 − exp(−τ t)` for
`t ∈ [0, 1]`. -/
private theorem slab_chord_le {τ t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 - Real.exp (-τ)) * t ≤ 1 - Real.exp (-(τ * t)) := by
  have hc := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (-τ))
    (by linarith : (0 : ℝ) ≤ 1 - t) ht0 (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at hc
  have : t * -τ = -(τ * t) := by ring
  rw [this] at hc
  nlinarith [hc]

/-- **The profile escape factor bounds the flat-slab factor from above.** For a profile `ψ`
with `0 ≤ ψ ≤ 1`, integrable, and a depth `τ₀ > 0`,
`selfAbsorptionFactor τ₀ · (τ₀ · ∫ ψ) ≤ equivWidth ψ τ₀`.

Reading: `τ₀ ∫ ψ` is the optically thin equivalent width and `W/(τ₀ ∫ ψ)` the profile-integrated
escape factor, so (when `∫ ψ > 0`) that escape factor is at least the flat-slab factor `SA(τ₀)`.
With `ψ ≤ 1`, `τ₀` bounds the depth at every frequency; it is the line-centre depth when `ψ`
peaks at `1`. The wings are less absorbed than the centre, which is the whole mechanism: the
chord inequality `(1 − exp(−τ₀)) t ≤ 1 − exp(−τ₀ t)` for `t = ψ(x) ∈ [0, 1]`, integrated.
Equality holds for the rectangular profile (`equivWidth_rectangular`).

Hypotheses: `hψ1` and `hψ0` are load-bearing (the chord inequality reverses outside `[0, 1]`;
numerically, `ψ = 2` on `[0, 1]` with `τ₀ = 1` gives `1.26 > 0.86`, and `ψ = −1` on `[0, 1]`
gives `−0.63 > −1.72`); `hint` supplies the integrability that `integral_mono` needs
(`equivWidth_integrand_integrable`); `hτ` is the physical domain and selects the non-totalized
branch of `selfAbsorptionFactor`; it is not claimed to be logically necessary.

Scope: PURE-MATH (an inequality between the defined functions). It does not say which profile
a real line has, and it models no inhomogeneity. Literature: Gornushkin 1999 (curve of growth,
escape factor). -/
theorem escape_ge_slab {ψ : ℝ → ℝ} {τ0 : ℝ} (hψ0 : 0 ≤ ψ) (hψ1 : ∀ x, ψ x ≤ 1)
    (hint : Integrable ψ) (hτ : 0 < τ0) :
    selfAbsorptionFactor τ0 * (τ0 * ∫ x, ψ x) ≤ equivWidth ψ τ0 := by
  have hL : selfAbsorptionFactor τ0 * (τ0 * ∫ x, ψ x) = ∫ x, (1 - Real.exp (-τ0)) * ψ x := by
    rw [selfAbsorptionFactor, if_neg hτ.ne']
    field_simp [hτ.ne']
    rw [integral_const_mul]
  rw [hL, equivWidth]
  exact integral_mono (hint.const_mul (1 - Real.exp (-τ0)))
    (equivWidth_integrand_integrable hτ.le hψ0 hint)
    (fun x => slab_chord_le (hψ0 x) (hψ1 x))

end CflibsFormal
