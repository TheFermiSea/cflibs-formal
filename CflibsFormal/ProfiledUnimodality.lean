/-
Copyright (c) 2026 Brian Squires. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Squires
-/
import Mathlib
import CflibsFormal.ForwardMap
import CflibsFormal.Identifiability
import CflibsFormal.NonlinearLeastSquares

/-!
# CF-LIBS formalization — strict unimodality of the profiled temperature objective

`NonlinearLeastSquares.lean` profiles the linear density `N` out of the joint `(T, N)` fit
(variable projection, VARPRO): for two lines the density-profiled objective collapses to the
explicit Rayleigh-quotient residual `g(T) = nlObjective … (T, N̂(T))`, which
(`profiledResidual_two_eq_ratio`) equals `profiledRatioResidual obs₀ obs₁ (t(T))` with
`t(T) = c₁(T)/c₀(T)`, `c_k(T) = lineIntensity kB T 1 Fcal g E A k`. Two facts about the pieces are
already proved there: the ratio residual `Φ(t) = (obs₁ − obs₀·t)² / (1 + t²)` is strictly decreasing
below its apex `t* = obs₁/obs₀` and strictly increasing above it
(`profiledResidual_two_strictAntiOn` / `…strictMonoOn`, at the *ratio* coordinate), any two box
minimizers coincide
(`profiledT_two_offManifold_box_unique`, from minimizer hypotheses).

This module upgrades those into an explicit **shape** statement for `g` *in the temperature
coordinate itself*: `g` is **strictly unimodal** on a bounded box around the apex temperature
`Tstar` (the temperature whose intensity ratio equals the observed ratio `obs₁/obs₀`) — strictly
decreasing on `[Tmin, Tstar]` and strictly increasing on `[Tstar, Tmax]`. Hence `Tstar` is the
**unique** minimizer on the box and there is **no spurious local minimum** in this region of
attraction. That is exactly the region-of-attraction shape a strict-mode descent solver needs —
but the solver's convergence itself, and any derivative / `slope`-sign-change argument, are **not**
formalized here; the landed result is the strict `V`-shape and its unique box minimizer (which may
sit at an endpoint, not necessarily the interior). The
transport is: `t(T)` is strictly monotone in `T`
(`lineIntensity_ratio_closed_form` + `Real.exp` monotonicity, distinct energies), and `Φ` is
strictly unimodal in `t`, so `g = Φ ∘ t` is strictly unimodal in `T`.

The apex hypothesis `obs₁·c₀(Tstar) = obs₀·c₁(Tstar)` (i.e. `t(Tstar) = obs₁/obs₀`) is the honest
role of the two premises the target names: distinct energies `E 0 ≠ E 1` (a positive line-energy
spread `ΔE > 0`) make `t` strictly monotone, and "`Tstar` lies in the box `[Tmin, Tmax]`" is exactly
the requirement that the (noise-perturbed) observed ratio `obs₁/obs₀` still corresponds to a
temperature inside the search region — i.e. a bound on how far the ordinate noise may move the
minimizer. On-manifold (`obs = forward(T₀, N₀)`, noise-free) the apex is `Tstar = T₀` exactly, so
`g` is strictly unimodal about the true temperature `T₀`.

## Literature and scope

Scope tag: **REDUCED**. This is the *two-line* case (`ι = Fin 2`), on an explicit temperature box,
with the apex-in-box hypothesis (equivalently: a positive two-line spectrum and a noise level small
enough to keep the minimizer inside the region). The obtained result is genuinely stronger than the
existing two-line box uniqueness — it constructs the strict `V`-shape and *identifies* the unique
minimizer, rather than assuming minimizers and showing they agree. What is NOT claimed: the general
`m ≥ 3` case is genuinely multimodal off-manifold (`profiledResidual_not_injective_m3`), and no
global (unbounded, or `m ≥ 3`) unimodality is asserted. Citation: Ciucci et al. (1999) two-line
Boltzmann ratio; Cowan & Dieke (1948). The VARPRO reduction is Golub & Pereyra (1973) / Tognoni et
al. (2010). Non-vacuity is witnessed on explicit `E = ![0, 1]` two-line data below.
-/

namespace CflibsFormal

open Finset Real
open scoped BigOperators

/-- Below the apex: with both `v`-terms positive, `u₁ > 0` and `u₂ ≥ 0`, the ratio residual strictly
decreases as `t` increases (`t₁ < t₂ ⟹ Φ(t₂) < Φ(t₁)`). From `profiledRatioResidual_diff`:
the numerator `u₁v₂ + u₂v₁ > 0` and `t₂ − t₁ > 0` make the difference negative. -/
private lemma ratioResidual_lt_below (o0 o1 t1 t2 : ℝ)
    (hv1 : 0 < o0 + o1 * t1) (hv2 : 0 < o0 + o1 * t2)
    (hu1 : 0 < o1 - o0 * t1) (hu2 : 0 ≤ o1 - o0 * t2) (hlt : t1 < t2) :
    profiledRatioResidual o0 o1 t2 < profiledRatioResidual o0 o1 t1 := by
  have hden : (0 : ℝ) < (1 + t1 ^ 2) * (1 + t2 ^ 2) := by positivity
  have hnum : 0 < (o1 - o0 * t1) * (o0 + o1 * t2) + (o1 - o0 * t2) * (o0 + o1 * t1) :=
    add_pos_of_pos_of_nonneg (mul_pos hu1 hv2) (mul_nonneg hu2 hv1.le)
  have hdiff : profiledRatioResidual o0 o1 t2 - profiledRatioResidual o0 o1 t1 < 0 := by
    rw [profiledRatioResidual_diff]
    apply div_neg_of_neg_of_pos _ hden
    nlinarith [mul_pos (sub_pos.mpr hlt) hnum]
  linarith

/-- Above the apex: with both `v`-terms positive, `u₁ ≤ 0` and `u₂ < 0`, the ratio residual strictly
increases as `t` increases (`t₁ < t₂ ⟹ Φ(t₁) < Φ(t₂)`). Symmetric to `ratioResidual_lt_below`:
the numerator `u₁v₂ + u₂v₁ < 0`. -/
private lemma ratioResidual_lt_above (o0 o1 t1 t2 : ℝ)
    (hv1 : 0 < o0 + o1 * t1) (hv2 : 0 < o0 + o1 * t2)
    (hu1 : o1 - o0 * t1 ≤ 0) (hu2 : o1 - o0 * t2 < 0) (hlt : t1 < t2) :
    profiledRatioResidual o0 o1 t1 < profiledRatioResidual o0 o1 t2 := by
  have hden : (0 : ℝ) < (1 + t1 ^ 2) * (1 + t2 ^ 2) := by positivity
  have hnum : (o1 - o0 * t1) * (o0 + o1 * t2) + (o1 - o0 * t2) * (o0 + o1 * t1) < 0 := by
    nlinarith [mul_nonneg (neg_nonneg.mpr hu1) hv2.le, mul_pos (neg_pos.mpr hu2) hv1]
  have hdiff : 0 < profiledRatioResidual o0 o1 t2 - profiledRatioResidual o0 o1 t1 := by
    rw [profiledRatioResidual_diff]
    apply div_pos _ hden
    nlinarith [mul_pos (sub_pos.mpr hlt) (neg_pos.mpr hnum)]
  linarith

/-- Strict monotonicity of the two-line intensity ratio `t(T) = c₁(T)/c₀(T)` under `E 0 < E 1`
(i.e. `E 0 − E 1 < 0`): `t` is strictly **increasing** in `T`. Closed form
`t(T) = ((g₁A₁)/(g₀A₀))·exp((E₀−E₁)/(k_B T))` + `Real.exp` strict monotonicity; `E₀ − E₁ < 0` makes
`(E₀−E₁)/(k_B T)` increase with `T`. -/
private lemma lineIntensityRatio_lt_of_lt {kB Fcal Ta Tb : ℝ} {g E A : Fin 2 → ℝ}
    (hkB : 0 < kB) (hg : ∀ k, 0 < g k) (hFcal : 0 < Fcal) (hA : ∀ k, 0 < A k)
    (hEneg : E 0 - E 1 < 0) (hTa : 0 < Ta) (hab : Ta < Tb) :
    lineIntensity kB Ta 1 Fcal g E A 1 / lineIntensity kB Ta 1 Fcal g E A 0
      < lineIntensity kB Tb 1 Fcal g E A 1 / lineIntensity kB Tb 1 Fcal g E A 0 := by
  have hTb : 0 < Tb := hTa.trans hab
  have hK : (0 : ℝ) < (g 1 * A 1) / (g 0 * A 0) :=
    div_pos (mul_pos (hg 1) (hA 1)) (mul_pos (hg 0) (hA 0))
  rw [lineIntensity_ratio_closed_form hg one_pos hFcal hA 0 1,
      lineIntensity_ratio_closed_form hg one_pos hFcal hA 0 1]
  refine mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr ?_) hK
  rw [div_lt_div_iff₀ (mul_pos hkB hTa) (mul_pos hkB hTb)]
  nlinarith [mul_pos (mul_pos hkB (sub_pos.mpr hab)) (neg_pos.mpr hEneg)]

/-- Strict monotonicity of the two-line intensity ratio under `E 1 < E 0` (i.e. `0 < E 0 − E 1`):
`t` is strictly **decreasing** in `T` (`Ta < Tb ⟹ t(Tb) < t(Ta)`). Mirror of
`lineIntensityRatio_lt_of_lt`. -/
private lemma lineIntensityRatio_gt_of_lt {kB Fcal Ta Tb : ℝ} {g E A : Fin 2 → ℝ}
    (hkB : 0 < kB) (hg : ∀ k, 0 < g k) (hFcal : 0 < Fcal) (hA : ∀ k, 0 < A k)
    (hEpos : 0 < E 0 - E 1) (hTa : 0 < Ta) (hab : Ta < Tb) :
    lineIntensity kB Tb 1 Fcal g E A 1 / lineIntensity kB Tb 1 Fcal g E A 0
      < lineIntensity kB Ta 1 Fcal g E A 1 / lineIntensity kB Ta 1 Fcal g E A 0 := by
  have hTb : 0 < Tb := hTa.trans hab
  have hK : (0 : ℝ) < (g 1 * A 1) / (g 0 * A 0) :=
    div_pos (mul_pos (hg 1) (hA 1)) (mul_pos (hg 0) (hA 0))
  rw [lineIntensity_ratio_closed_form hg one_pos hFcal hA 0 1,
      lineIntensity_ratio_closed_form hg one_pos hFcal hA 0 1]
  refine mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr ?_) hK
  rw [div_lt_div_iff₀ (mul_pos hkB hTb) (mul_pos hkB hTa)]
  nlinarith [mul_pos (mul_pos hkB (sub_pos.mpr hab)) hEpos]

/-- **Two-line strict unimodality of the profiled objective in `T` (REDUCED, Ciucci 1999).** For a
positive two-line spectrum `obs 0, obs 1 > 0`, distinct upper-level energies `E 0 ≠ E 1`, and an
apex temperature `Tstar ∈ [Tmin, Tmax]` (with `Tmin > 0`) at which the intensity ratio matches the
observed ratio — `obs 1 · c₀(Tstar) = obs 0 · c₁(Tstar)`, `c_k(T) = lineIntensity kB T 1 Fcal g E A
k` — the density-profiled objective `g(T) = nlObjective … (T, N̂(T))` is **strictly unimodal**
on the box: strictly decreasing on `[Tmin, Tstar]` and strictly increasing on `[Tstar, Tmax]`.

Mechanism: `g(T) = profiledRatioResidual (obs 0) (obs 1) (t(T))` (`profiledResidual_two_eq_ratio`),
`t(T) = c₁(T)/c₀(T)` is strictly monotone in `T` (`lineIntensityRatio_{lt,gt}_of_lt`, distinct
energies), and `profiledRatioResidual` is strictly decreasing below the apex `t(Tstar) = obs₁/obs₀`
and strictly increasing above it (`ratioResidual_lt_{below,above}`; the antipode `v = obs₀ + obs₁·t
> 0` is automatic since `obs, t > 0`). No Hessian/curvature computation. -/
theorem profiledResidual_two_strictUnimodalOn {kB Fcal Tmin Tmax Tstar : ℝ}
    {g E A obs : Fin 2 → ℝ}
    (hkB : 0 < kB) (hg : ∀ k, 0 < g k) (hFcal : 0 < Fcal) (hA : ∀ k, 0 < A k)
    (ho0 : 0 < obs 0) (ho1 : 0 < obs 1) (hE : E 0 ≠ E 1)
    (hTmin : 0 < Tmin) (hTsL : Tmin ≤ Tstar) (_hTsR : Tstar ≤ Tmax)
    (hstar : obs 1 * lineIntensity kB Tstar 1 Fcal g E A 0
           = obs 0 * lineIntensity kB Tstar 1 Fcal g E A 1) :
    StrictAntiOn
        (fun T => nlObjective kB Fcal g E A obs (T, profiledDensity kB Fcal g E A obs T))
        (Set.Icc Tmin Tstar)
      ∧ StrictMonoOn
        (fun T => nlObjective kB Fcal g E A obs (T, profiledDensity kB Fcal g E A obs T))
        (Set.Icc Tstar Tmax) := by
  have hTs0 : 0 < Tstar := lt_of_lt_of_le hTmin hTsL
  have hc0 : ∀ T, 0 < lineIntensity kB T 1 Fcal g E A 0 :=
    fun T => lineIntensity_pos hg one_pos hFcal hA 0
  have htpos : ∀ T, 0 < lineIntensity kB T 1 Fcal g E A 1 / lineIntensity kB T 1 Fcal g E A 0 :=
    fun T => div_pos (lineIntensity_pos hg one_pos hFcal hA 1) (hc0 T)
  -- bridge to the ratio residual
  have hbr : ∀ T, nlObjective kB Fcal g E A obs (T, profiledDensity kB Fcal g E A obs T)
      = profiledRatioResidual (obs 0) (obs 1)
          (lineIntensity kB T 1 Fcal g E A 1 / lineIntensity kB T 1 Fcal g E A 0) :=
    fun T => profiledResidual_two_eq_ratio (hc0 T)
  -- antipode positivity
  have hv : ∀ T, 0 < obs 0 + obs 1
      * (lineIntensity kB T 1 Fcal g E A 1 / lineIntensity kB T 1 Fcal g E A 0) :=
    fun T => add_pos ho0 (mul_pos ho1 (htpos T))
  -- `obs 1 = obs 0 · t(Tstar)`, hence the `u`-sign identity
  have hc0s : (0 : ℝ) < lineIntensity kB Tstar 1 Fcal g E A 0 := hc0 Tstar
  have hobs1 : obs 1 = obs 0
      * (lineIntensity kB Tstar 1 Fcal g E A 1 / lineIntensity kB Tstar 1 Fcal g E A 0) := by
    rw [← mul_div_assoc, eq_div_iff hc0s.ne']
    linear_combination hstar
  have husign : ∀ T, obs 1 - obs 0
      * (lineIntensity kB T 1 Fcal g E A 1 / lineIntensity kB T 1 Fcal g E A 0)
      = obs 0 * ((lineIntensity kB Tstar 1 Fcal g E A 1 / lineIntensity kB Tstar 1 Fcal g E A 0)
                 - (lineIntensity kB T 1 Fcal g E A 1 / lineIntensity kB T 1 Fcal g E A 0)) :=
    fun T => by rw [hobs1]; ring
  rcases lt_or_gt_of_ne (sub_ne_zero.mpr hE) with hEneg | hEpos
  · -- E 0 < E 1 : t strictly increasing
    have mono : ∀ x y : ℝ, 0 < x → x < y →
        lineIntensity kB x 1 Fcal g E A 1 / lineIntensity kB x 1 Fcal g E A 0
          < lineIntensity kB y 1 Fcal g E A 1 / lineIntensity kB y 1 Fcal g E A 0 :=
      fun x y hx hxy => lineIntensityRatio_lt_of_lt hkB hg hFcal hA hEneg hx hxy
    have mono_le : ∀ x y : ℝ, 0 < x → x ≤ y →
        lineIntensity kB x 1 Fcal g E A 1 / lineIntensity kB x 1 Fcal g E A 0
          ≤ lineIntensity kB y 1 Fcal g E A 1 / lineIntensity kB y 1 Fcal g E A 0 := by
      intro x y hx hxy
      rcases eq_or_lt_of_le hxy with h | h
      · exact le_of_eq (by rw [h])
      · exact le_of_lt (mono x y hx h)
    refine ⟨?_, ?_⟩
    · intro a ha b hb hab
      simp only [Set.mem_Icc] at ha hb
      have h0a : 0 < a := lt_of_lt_of_le hTmin ha.1
      have haS : a < Tstar := lt_of_lt_of_le hab hb.2
      have hua : 0 < obs 1 - obs 0
          * (lineIntensity kB a 1 Fcal g E A 1 / lineIntensity kB a 1 Fcal g E A 0) := by
        rw [husign a]; exact mul_pos ho0 (sub_pos.mpr (mono a Tstar h0a haS))
      have hub : 0 ≤ obs 1 - obs 0
          * (lineIntensity kB b 1 Fcal g E A 1 / lineIntensity kB b 1 Fcal g E A 0) := by
        rw [husign b]
        exact mul_nonneg ho0.le (sub_nonneg.mpr (mono_le b Tstar (lt_of_lt_of_le hTmin hb.1) hb.2))
      simp only [hbr]
      exact ratioResidual_lt_below (obs 0) (obs 1) _ _ (hv a) (hv b) hua hub (mono a b h0a hab)
    · intro a ha b hb hab
      simp only [Set.mem_Icc] at ha hb
      have h0a : 0 < a := lt_of_lt_of_le hTs0 ha.1
      have hSb : Tstar < b := lt_of_le_of_lt ha.1 hab
      have hua : obs 1 - obs 0
          * (lineIntensity kB a 1 Fcal g E A 1 / lineIntensity kB a 1 Fcal g E A 0) ≤ 0 := by
        rw [husign a]
        exact mul_nonpos_of_nonneg_of_nonpos ho0.le
          (sub_nonpos.mpr (mono_le Tstar a hTs0 ha.1))
      have hub : obs 1 - obs 0
          * (lineIntensity kB b 1 Fcal g E A 1 / lineIntensity kB b 1 Fcal g E A 0) < 0 := by
        rw [husign b]
        exact mul_neg_of_pos_of_neg ho0 (sub_neg.mpr (mono Tstar b hTs0 hSb))
      simp only [hbr]
      exact ratioResidual_lt_above (obs 0) (obs 1) _ _ (hv a) (hv b) hua hub (mono a b h0a hab)
  · -- E 1 < E 0 : t strictly decreasing
    have anti : ∀ x y : ℝ, 0 < x → x < y →
        lineIntensity kB y 1 Fcal g E A 1 / lineIntensity kB y 1 Fcal g E A 0
          < lineIntensity kB x 1 Fcal g E A 1 / lineIntensity kB x 1 Fcal g E A 0 :=
      fun x y hx hxy => lineIntensityRatio_gt_of_lt hkB hg hFcal hA hEpos hx hxy
    have anti_le : ∀ x y : ℝ, 0 < x → x ≤ y →
        lineIntensity kB y 1 Fcal g E A 1 / lineIntensity kB y 1 Fcal g E A 0
          ≤ lineIntensity kB x 1 Fcal g E A 1 / lineIntensity kB x 1 Fcal g E A 0 := by
      intro x y hx hxy
      rcases eq_or_lt_of_le hxy with h | h
      · exact le_of_eq (by rw [h])
      · exact le_of_lt (anti x y hx h)
    refine ⟨?_, ?_⟩
    · intro a ha b hb hab
      simp only [Set.mem_Icc] at ha hb
      have h0a : 0 < a := lt_of_lt_of_le hTmin ha.1
      have h0b : 0 < b := lt_of_lt_of_le hTmin hb.1
      have haS : a < Tstar := lt_of_lt_of_le hab hb.2
      -- decreasing: t b < t a, both ≥ t(Tstar); apply the "above apex" lemma at (t b, t a)
      have hub : obs 1 - obs 0
          * (lineIntensity kB b 1 Fcal g E A 1 / lineIntensity kB b 1 Fcal g E A 0) ≤ 0 := by
        rw [husign b]
        exact mul_nonpos_of_nonneg_of_nonpos ho0.le
          (sub_nonpos.mpr (anti_le b Tstar h0b hb.2))
      have hua : obs 1 - obs 0
          * (lineIntensity kB a 1 Fcal g E A 1 / lineIntensity kB a 1 Fcal g E A 0) < 0 := by
        rw [husign a]
        exact mul_neg_of_pos_of_neg ho0 (sub_neg.mpr (anti a Tstar h0a haS))
      simp only [hbr]
      exact ratioResidual_lt_above (obs 0) (obs 1) _ _ (hv b) (hv a) hub hua (anti a b h0a hab)
    · intro a ha b hb hab
      simp only [Set.mem_Icc] at ha hb
      have h0a : 0 < a := lt_of_lt_of_le hTs0 ha.1
      have h0b : 0 < b := lt_of_lt_of_le hTs0 hb.1
      have hSb : Tstar < b := lt_of_le_of_lt ha.1 hab
      -- decreasing: t b < t a, both ≤ t(Tstar); apply the "below apex" lemma at (t b, t a)
      have hub : 0 < obs 1 - obs 0
          * (lineIntensity kB b 1 Fcal g E A 1 / lineIntensity kB b 1 Fcal g E A 0) := by
        rw [husign b]; exact mul_pos ho0 (sub_pos.mpr (anti Tstar b hTs0 hSb))
      have hua : 0 ≤ obs 1 - obs 0
          * (lineIntensity kB a 1 Fcal g E A 1 / lineIntensity kB a 1 Fcal g E A 0) := by
        rw [husign a]
        exact mul_nonneg ho0.le (sub_nonneg.mpr (anti_le Tstar a hTs0 ha.1))
      simp only [hbr]
      exact ratioResidual_lt_below (obs 0) (obs 1) _ _ (hv b) (hv a) hub hua (anti a b h0a hab)

/-- **Unique minimizer / no spurious local minimum (REDUCED, Ciucci 1999).** Under the hypotheses of
`profiledResidual_two_strictUnimodalOn`, the apex temperature `Tstar` is the **strict** global
minimizer of the density-profiled objective on the box `[Tmin, Tmax]`: every other box temperature
gives a strictly larger profiled residual — the objective strictly decreases toward `Tstar` on each
side, so there is no spurious local minimum in the region of attraction. (The reading "a descent
solver cannot stall away from `Tstar`" is the intended consequence, not a formalized solver
theorem.) -/
theorem profiledResidual_two_Tstar_isStrictMin {kB Fcal Tmin Tmax Tstar : ℝ}
    {g E A obs : Fin 2 → ℝ}
    (hkB : 0 < kB) (hg : ∀ k, 0 < g k) (hFcal : 0 < Fcal) (hA : ∀ k, 0 < A k)
    (ho0 : 0 < obs 0) (ho1 : 0 < obs 1) (hE : E 0 ≠ E 1)
    (hTmin : 0 < Tmin) (hTsL : Tmin ≤ Tstar) (hTsR : Tstar ≤ Tmax)
    (hstar : obs 1 * lineIntensity kB Tstar 1 Fcal g E A 0
           = obs 0 * lineIntensity kB Tstar 1 Fcal g E A 1)
    {T : ℝ} (hT : T ∈ Set.Icc Tmin Tmax) (hne : T ≠ Tstar) :
    nlObjective kB Fcal g E A obs (Tstar, profiledDensity kB Fcal g E A obs Tstar)
      < nlObjective kB Fcal g E A obs (T, profiledDensity kB Fcal g E A obs T) := by
  obtain ⟨hanti, hmono⟩ := profiledResidual_two_strictUnimodalOn hkB hg hFcal hA ho0 ho1 hE
    hTmin hTsL hTsR hstar
  simp only [Set.mem_Icc] at hT
  rcases lt_or_gt_of_ne hne with h | h
  · exact hanti ⟨hT.1, le_of_lt h⟩ ⟨hTsL, le_refl _⟩ h
  · exact hmono ⟨le_refl _, hTsR⟩ ⟨le_of_lt h, hT.2⟩ h

/-- **On-manifold strict unimodality about the true temperature `T₀` (REDUCED, Ciucci 1999).**
noise-free case `obs = forward(T₀, N₀)` (with `N₀ > 0`), the apex is `Tstar = T₀`, so the profiled
objective `g` is strictly decreasing on `[Tmin, T₀]`, strictly increasing on `[T₀, Tmax]`, so `T₀`
is the unique box minimizer (a descent solver's convergence to it is the informal consequence, not
formalized). This upgrades the
existence/zero-value anchor `nlObjective_onManifold_min` to a full local *shape* statement. The apex
identity `obs 1 · c₀(T₀) = obs 0 · c₁(T₀)` holds since both sides equal `N₀·c₁(T₀)·c₀(T₀)` (forward
map linear in `N`). -/
theorem profiledResidual_two_strictUnimodal_onManifold {kB Fcal Tmin Tmax T0 N0 : ℝ}
    {g E A obs : Fin 2 → ℝ}
    (hkB : 0 < kB) (hg : ∀ k, 0 < g k) (hFcal : 0 < Fcal) (hA : ∀ k, 0 < A k)
    (hN0 : 0 < N0) (hE : E 0 ≠ E 1)
    (hTmin : 0 < Tmin) (hTL : Tmin ≤ T0) (hTR : T0 ≤ Tmax)
    (hobs : ∀ k, obs k = lineIntensity kB T0 N0 Fcal g E A k) :
    StrictAntiOn
        (fun T => nlObjective kB Fcal g E A obs (T, profiledDensity kB Fcal g E A obs T))
        (Set.Icc Tmin T0)
      ∧ StrictMonoOn
        (fun T => nlObjective kB Fcal g E A obs (T, profiledDensity kB Fcal g E A obs T))
        (Set.Icc T0 Tmax) := by
  have ho0 : 0 < obs 0 := by rw [hobs 0]; exact lineIntensity_pos hg hN0 hFcal hA 0
  have ho1 : 0 < obs 1 := by rw [hobs 1]; exact lineIntensity_pos hg hN0 hFcal hA 1
  have hstar : obs 1 * lineIntensity kB T0 1 Fcal g E A 0
      = obs 0 * lineIntensity kB T0 1 Fcal g E A 1 := by
    rw [hobs 0, hobs 1, lineIntensity_linear_in_N kB T0 N0 Fcal g E A 0,
        lineIntensity_linear_in_N kB T0 N0 Fcal g E A 1]
    ring
  exact profiledResidual_two_strictUnimodalOn hkB hg hFcal hA ho0 ho1 hE hTmin hTL hTR hstar

/-! ### Non-vacuity witnesses -/

/-- Unit degeneracies for the strict-unimodality witness. -/
private def suG : Fin 2 → ℝ := fun _ => 1

/-- **Distinct** upper-level energies (`E 0 = 0 ≠ 1 = E 1`, so `ΔE = 1 > 0`). -/
private def suE : Fin 2 → ℝ := ![0, 1]

/-- Unit Einstein coefficients for the strict-unimodality witness. -/
private def suA : Fin 2 → ℝ := fun _ => 1

/-- On-manifold observation: exact forward spectrum of `(T₀, N₀) = (1, 1)`. -/
private noncomputable def suObs : Fin 2 → ℝ := fun k => lineIntensity 1 1 1 1 suG suE suA k

private lemma suG_pos : ∀ k, 0 < suG k := fun _ => by norm_num [suG]
private lemma suA_pos : ∀ k, 0 < suA k := fun _ => by norm_num [suA]
private lemma suE_ne : suE 0 ≠ suE 1 := by
  simp only [suE, Matrix.cons_val_zero, Matrix.cons_val_one]; norm_num

/-- **Non-vacuity of on-manifold strict unimodality.** With `kB = Fcal = T₀ = N₀ = 1`, distinct
energies `E = ![0, 1]`, and the exact forward spectrum `suObs`, the profiled objective is strictly
decreasing on `[1/2, 1]` and strictly increasing on `[1, 2]` — every hypothesis of
`profiledResidual_two_strictUnimodal_onManifold` is realized at concrete data, so the `V`-shape
about `T₀ = 1` is not vacuous. -/
example :
    StrictAntiOn
        (fun T => nlObjective 1 1 suG suE suA suObs (T, profiledDensity 1 1 suG suE suA suObs T))
        (Set.Icc (1 / 2 : ℝ) 1)
      ∧ StrictMonoOn
        (fun T => nlObjective 1 1 suG suE suA suObs (T, profiledDensity 1 1 suG suE suA suObs T))
        (Set.Icc (1 : ℝ) 2) :=
  profiledResidual_two_strictUnimodal_onManifold one_pos suG_pos one_pos suA_pos one_pos
    suE_ne (by norm_num) (by norm_num) (by norm_num) (fun _ => rfl)

/-- **Non-vacuity of the strict global minimizer.** For the same on-manifold witness, `T₀ = 1`
strictly beats `T = 3/2` on the box `[1/2, 2]`: the profiled residual at the true temperature is
strictly below that at any other box temperature. -/
example :
    nlObjective 1 1 suG suE suA suObs (1, profiledDensity 1 1 suG suE suA suObs 1)
      < nlObjective 1 1 suG suE suA suObs (3 / 2,
          profiledDensity 1 1 suG suE suA suObs (3 / 2)) := by
  have ho0 : 0 < suObs 0 := by rw [suObs]; exact lineIntensity_pos suG_pos one_pos one_pos suA_pos 0
  have ho1 : 0 < suObs 1 := by rw [suObs]; exact lineIntensity_pos suG_pos one_pos one_pos suA_pos 1
  have hstar : suObs 1 * lineIntensity 1 1 1 1 suG suE suA 0
      = suObs 0 * lineIntensity 1 1 1 1 suG suE suA 1 := by
    rw [suObs, suObs, lineIntensity_linear_in_N 1 1 1 1 suG suE suA 0,
        lineIntensity_linear_in_N 1 1 1 1 suG suE suA 1]
    ring
  exact profiledResidual_two_Tstar_isStrictMin (Tmin := 1 / 2) (Tmax := 2) (Tstar := 1)
    (T := 3 / 2) one_pos suG_pos one_pos suA_pos ho0 ho1
    suE_ne (by norm_num) (by norm_num) (by norm_num) hstar (by norm_num) (by norm_num)

end CflibsFormal
