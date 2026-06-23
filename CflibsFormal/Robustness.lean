/-
Copyright (c) 2026 Brian Squires. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Squires
-/
import Mathlib
import CflibsFormal.ForwardMap
import CflibsFormal.Boltzmann

/-!
# Saha–Boltzmann formalization — Robustness / error-propagation bounds

Quantitative perturbation theorems with **explicit constants** (no asymptotics) for
the inverse map that recovers temperature and composition from measured
Boltzmann-plot ordinates. These are the reliability guarantees: a bounded
measurement error on the observed log-ordinates propagates to a bounded error on
the recovered quantity.

The recovered quantities are taken as genuine functions of the *measured*
observations (not of the true answer), matching the inverse expressions that
appear literally in `ForwardMap.temperature_from_two_lines`
(`boltzmann_plot_intensity`):

* `twoLineBeta` — the two-line inverse-temperature (slope) estimate
  `β = (yⱼ - yᵢ) / (Eᵢ - Eⱼ)` from measured ordinates
  `yₖ = log(Iₖ/(gₖ Aₖ))`.
* `logRatioIntercept` — the recovered log number-density ratio of two species,
  `bₛ - bₜ`, a difference of measured Boltzmann-plot intercepts.

We prove:

* `twoLineBeta_stable` — **temperature stability**: the slope estimate is Lipschitz
  in the ordinates with explicit constant `2/|Eᵢ-Eⱼ|`; a per-ordinate log-intensity
  error `≤ ε` propagates to a slope error `≤ 2·ε/|Eᵢ-Eⱼ|`. Wider energy spacing ⇒
  tighter bound, matching LIBS line-selection practice. The bound is sharp.
* `logRatioIntercept_stable` — **composition/ratio stability**: the recovered
  log-ratio is 1-Lipschitz in each intercept, so a per-intercept log-error `≤ ε`
  yields a composition log-error `≤ 2·ε`. The constant `2` is sharp.
* `twoLineBeta_continuous` — **continuous dependence**: the recovered
  inverse-temperature depends continuously on the observed ordinate pair, a
  qualitative well-posedness companion to the Lipschitz bound.

All quantities are real.
-/

namespace CflibsFormal

open Finset Real
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- Two-line inverse-temperature (slope) estimate from measured Boltzmann-plot
ordinates `yi = log(I_i/(g_i A_i))`, `yj = log(I_j/(g_j A_j))` at upper-level
energies `Ei`, `Ej`:
  `β = (yj - yi) / (Ei - Ej)`.
This is exactly the slope `1/(k_B T)` recovered by `temperature_from_two_lines`
when `yi`, `yj` are the unperturbed model ordinates (see `boltzmann_plot_intensity`).
Here it is taken as a function of *measured* ordinates so we can bound its
sensitivity to measurement error. -/
noncomputable def twoLineBeta (yi yj Ei Ej : ℝ) : ℝ :=
  (yj - yi) / (Ei - Ej)

/-- Recovered log number-density ratio of two species `s`, `t` from their measured
Boltzmann-plot *intercepts* `bs = log(Fcal · N_s / U_s)`, `bt = log(Fcal · N_t / U_t)`
(the intercept term of `boltzmann_plot_intensity`). Under a shared calibration `Fcal`
and known partition functions this intercept difference is the recovered
`log(N_s/N_t)` up to the (known, error-free) `log(U_s/U_t)` offset; we model the
recovered log-ratio as the difference of the two measured intercepts:
  `log-ratio = bs - bt`. -/
noncomputable def logRatioIntercept (bs bt : ℝ) : ℝ :=
  bs - bt

/-- **Temperature stability.** The two-line inverse-temperature (slope) estimate is
Lipschitz in the measured ordinates with explicit constant `2/|Eᵢ-Eⱼ|`: perturbing
each ordinate by at most `ε` changes the estimate by at most `2·ε/|Eᵢ-Eⱼ|`. The
bound is sharp (attained with opposite-sign perturbations), and `hEi` is
load-bearing for the nonzero denominator. -/
theorem twoLineBeta_stable {yi yj yiHat yjHat Ei Ej eps : ℝ}
    (hEi : Ei ≠ Ej) (hi : |yiHat - yi| ≤ eps) (hj : |yjHat - yj| ≤ eps) :
    |twoLineBeta yiHat yjHat Ei Ej - twoLineBeta yi yj Ei Ej|
      ≤ 2 * eps / |Ei - Ej| := by
  have hEij : (0 : ℝ) < |Ei - Ej| := abs_pos.mpr (sub_ne_zero.mpr hEi)
  have hcombine : twoLineBeta yiHat yjHat Ei Ej - twoLineBeta yi yj Ei Ej
      = ((yjHat - yj) - (yiHat - yi)) / (Ei - Ej) := by
    unfold twoLineBeta
    rw [div_sub_div_same]
    ring_nf
  rw [hcombine, abs_div]
  have hnum : |(yjHat - yj) - (yiHat - yi)| ≤ 2 * eps := by
    calc |(yjHat - yj) - (yiHat - yi)|
        ≤ |yjHat - yj| + |yiHat - yi| := by
          rw [sub_eq_add_neg]
          refine (abs_add_le _ _).trans ?_
          rw [abs_neg]
      _ ≤ eps + eps := add_le_add hj hi
      _ = 2 * eps := by ring
  gcongr

/-- **Composition/ratio stability.** The recovered log number-density ratio is
1-Lipschitz in each measured intercept, so a per-intercept log-error `≤ ε` yields a
composition log-error `≤ 2·ε`. The constant `2` is sharp (attained with opposite-sign
perturbations). -/
theorem logRatioIntercept_stable {bs bt bsHat btHat eps : ℝ}
    (hs : |bsHat - bs| ≤ eps) (ht : |btHat - bt| ≤ eps) :
    |logRatioIntercept bsHat btHat - logRatioIntercept bs bt| ≤ 2 * eps := by
  have heq : logRatioIntercept bsHat btHat - logRatioIntercept bs bt
      = (bsHat - bs) - (btHat - bt) := by
    unfold logRatioIntercept
    ring
  rw [heq]
  calc |(bsHat - bs) - (btHat - bt)|
      ≤ |bsHat - bs| + |btHat - bt| := by
        rw [sub_eq_add_neg]
        refine (abs_add_le _ _).trans ?_
        rw [abs_neg]
    _ ≤ eps + eps := add_le_add hs ht
    _ = 2 * eps := by ring

/-- **Continuous dependence.** The recovered inverse-temperature depends continuously
on the observed ordinate pair `(yi, yj)` — a qualitative well-posedness companion to
the quantitative Lipschitz bound. The fixed energies enter only through the constant
denominator `Ei - Ej` (division by a constant, including `0`, is continuous in
mathlib), so no nonvanishing hypothesis is required. -/
theorem twoLineBeta_continuous (Ei Ej : ℝ) :
    Continuous (fun p : ℝ × ℝ => twoLineBeta p.1 p.2 Ei Ej) := by
  unfold twoLineBeta
  exact (continuous_snd.sub continuous_fst).div_const _

/-- **Sharpness of the temperature bound.** The Lipschitz constant `2/|Eᵢ−Eⱼ|` of
`twoLineBeta_stable` is attained: with the opposite-sign perturbations `yi ↦ yi − ε`,
`yj ↦ yj + ε` (each of size `ε`), the slope estimate changes by EXACTLY `2·ε/|Eᵢ−Eⱼ|`. So
the bound cannot be improved — the worst case is real, not a loose over-estimate. -/
theorem twoLineBeta_stable_sharp {yi yj Ei Ej eps : ℝ} (_hEi : Ei ≠ Ej) (heps : 0 ≤ eps) :
    |twoLineBeta (yi - eps) (yj + eps) Ei Ej - twoLineBeta yi yj Ei Ej|
      = 2 * eps / |Ei - Ej| := by
  have hcombine : twoLineBeta (yi - eps) (yj + eps) Ei Ej - twoLineBeta yi yj Ei Ej
      = (2 * eps) / (Ei - Ej) := by
    unfold twoLineBeta
    rw [div_sub_div_same]
    congr 1
    ring
  rw [hcombine, abs_div, abs_of_nonneg (mul_nonneg (by norm_num) heps)]

/-- **Sharpness of the composition/ratio bound.** The constant `2` of
`logRatioIntercept_stable` is attained: with opposite-sign intercept perturbations
`bs ↦ bs + ε`, `bt ↦ bt − ε`, the recovered log-ratio changes by EXACTLY `2·ε`. -/
theorem logRatioIntercept_stable_sharp {bs bt eps : ℝ} (heps : 0 ≤ eps) :
    |logRatioIntercept (bs + eps) (bt - eps) - logRatioIntercept bs bt| = 2 * eps := by
  unfold logRatioIntercept
  have hc : (bs + eps) - (bt - eps) - (bs - bt) = 2 * eps := by ring
  rw [hc, abs_of_nonneg (mul_nonneg (by norm_num) heps)]

end CflibsFormal
