/-
Copyright (c) 2026 Brian Squires. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Squires
-/
import Mathlib

/-!
# CF-LIBS formalization — the Voigt FWHM combination (Olivero–Longbothum)

`LineBroadening.lean` builds the Gaussian width budget (Doppler + instrument, combining in
quadrature) and notes the full Voigt FWHM combination is *out of scope* there. This module supplies
exactly that piece: the **Olivero–Longbothum (1977)** empirical fit for the FWHM of a Voigt profile
(Gaussian ⊗ Lorentzian) from its Gaussian (`w_G`: Doppler + instrument, via
`LineBroadening.gaussQuadrature`) and Lorentzian (`w_L`: Stark + natural) component widths:

`w_V = 0.5346·w_L + √(0.2166·w_L² + w_G²)`.

* `voigtFWHM` — the OL combination, positive.
* `voigtFWHM_ge_gauss` / `voigtFWHM_ge_lorentz` — the Voigt FWHM is **at least** each component
  width (`w_G ≤ w_V` and `w_L ≤ w_V`): a Voigt profile is wider than either of its constituents.
* `voigtFWHM_mono_wL` / `voigtFWHM_mono_wG` — monotone increasing in each component width.
* `voigt_gaussian_limit` — **exact**: at `w_L = 0`, `w_V = w_G` (pure Gaussian).
* `voigt_lorentzian_limit` — at `w_G = 0`, `w_V = (0.5346 + √0.2166)·w_L`. Note `0.5346 + √0.2166 =
  1.0000034… ≠ 1` exactly, so this is the **honest algebraic restatement**, *not* `w_V = w_L`: the
  OL coefficients are tuned so the pure-Lorentzian limit is `w_L` only to the fit's accuracy.

## Honest scope

The OL formula is an **empirical fit** (accurate to ~0.01% over all `w_L,w_G`), asserted as the
standard operational Voigt-width rule — the exact Voigt FWHM has no closed form. Consequently the
two limits differ in status: the Gaussian limit `w_V = w_G` is **exact**, while the Lorentzian limit
is `w_V ≈ w_L` only (it equals `(0.5346 + √0.2166)·w_L`, off by `~3·10⁻⁶`). The naive bound
`w_V ≤ w_L + w_G` is likewise **false** at this level (it fails by the same `~3·10⁻⁶·w_L` in the
pure-Lorentzian case), so it is deliberately **not** stated; the faithful bounds are the
lower bounds `w_G ≤ w_V`, `w_L ≤ w_V`.

## Literature

J. J. Olivero, R. L. Longbothum, "Empirical fits to the Voigt line width: A brief review,"
*J. Quant. Spectrosc. Radiat. Transfer* **17** (1977) 233–236 (DOI 10.1016/0022-4073(77)90161-3):
the `w_V = 0.5346·w_L + √(0.2166·w_L² + w_G²)` FWHM approximation. The Gaussian (`LineBroadening`)
and Lorentzian (Stark, `StarkBroadening`) component-width origins are as cited there.
-/

namespace CflibsFormal

/-- **Voigt FWHM (Olivero–Longbothum 1977).** The empirical combination of the Lorentzian width
`wL` (Stark + natural) and the Gaussian width `wG` (Doppler + instrument):
`w_V = 0.5346·w_L + √(0.2166·w_L² + w_G²)`. -/
noncomputable def voigtFWHM (wL wG : ℝ) : ℝ :=
  0.5346 * wL + Real.sqrt (0.2166 * wL ^ 2 + wG ^ 2)

/-- The Voigt FWHM is strictly positive when there is a nonzero Gaussian width (always true in
practice — thermal Doppler — for `wL ≥ 0`). -/
lemma voigtFWHM_pos {wL wG : ℝ} (hwL : 0 ≤ wL) (hwG : 0 < wG) : 0 < voigtFWHM wL wG := by
  unfold voigtFWHM
  have hsqrt : 0 < Real.sqrt (0.2166 * wL ^ 2 + wG ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have h0 : 0 ≤ 0.5346 * wL := by positivity
  linarith

/-- **A Voigt profile is at least as wide as its Gaussian part:** `w_G ≤ w_V`. -/
lemma voigtFWHM_ge_gauss {wL wG : ℝ} (hwL : 0 ≤ wL) (hwG : 0 ≤ wG) :
    wG ≤ voigtFWHM wL wG := by
  unfold voigtFWHM
  have h1 : Real.sqrt (wG ^ 2) ≤ Real.sqrt (0.2166 * wL ^ 2 + wG ^ 2) :=
    Real.sqrt_le_sqrt (by nlinarith [sq_nonneg wL])
  rw [Real.sqrt_sq hwG] at h1
  have h2 : 0 ≤ 0.5346 * wL := by positivity
  linarith

/-- **A Voigt profile is at least as wide as its Lorentzian part:** `w_L ≤ w_V`. Uses that
`0.5346 + √0.2166 ≥ 1` (the OL coefficients satisfy `√0.2166 > 0.4654 = 1 − 0.5346`). -/
lemma voigtFWHM_ge_lorentz {wL wG : ℝ} (hwL : 0 ≤ wL) :
    wL ≤ voigtFWHM wL wG := by
  unfold voigtFWHM
  have h1 : Real.sqrt (0.2166 * wL ^ 2) ≤ Real.sqrt (0.2166 * wL ^ 2 + wG ^ 2) :=
    Real.sqrt_le_sqrt (by nlinarith [sq_nonneg wG])
  rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 0.2166), Real.sqrt_sq hwL] at h1
  have h3 : (0.4654 : ℝ) ≤ Real.sqrt 0.2166 := by
    rw [show (0.4654 : ℝ) = Real.sqrt (0.4654 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hB : 0.4654 * wL ≤ Real.sqrt 0.2166 * wL := mul_le_mul_of_nonneg_right h3 hwL
  linarith

/-- The Voigt FWHM is increasing in the Lorentzian width `wL`. -/
lemma voigtFWHM_mono_wL {wG wL₁ wL₂ : ℝ} (hwL₁ : 0 ≤ wL₁) (h : wL₁ ≤ wL₂) :
    voigtFWHM wL₁ wG ≤ voigtFWHM wL₂ wG := by
  unfold voigtFWHM
  gcongr

/-- The Voigt FWHM is increasing in the Gaussian width `wG`. -/
lemma voigtFWHM_mono_wG {wL wG₁ wG₂ : ℝ} (hwG₁ : 0 ≤ wG₁) (h : wG₁ ≤ wG₂) :
    voigtFWHM wL wG₁ ≤ voigtFWHM wL wG₂ := by
  unfold voigtFWHM
  gcongr

/-- **Pure-Gaussian limit (exact).** With no Lorentzian broadening, the Voigt FWHM is exactly the
Gaussian width: `w_V = w_G` at `w_L = 0`. -/
theorem voigt_gaussian_limit {wG : ℝ} (hwG : 0 ≤ wG) : voigtFWHM 0 wG = wG := by
  unfold voigtFWHM
  rw [show (0.2166 : ℝ) * (0 : ℝ) ^ 2 + wG ^ 2 = wG ^ 2 by ring, Real.sqrt_sq hwG]
  ring

/-- **Pure-Lorentzian limit (honest restatement).** With no Gaussian broadening,
`w_V = (0.5346 + √0.2166)·w_L`. Because `0.5346 + √0.2166 = 1.0000034… ≠ 1`, this is **not** exactly
`w_L`: the OL fit reproduces the Lorentzian limit only to its `~0.01%` accuracy. -/
theorem voigt_lorentzian_limit {wL : ℝ} (hwL : 0 ≤ wL) :
    voigtFWHM wL 0 = (0.5346 + Real.sqrt 0.2166) * wL := by
  unfold voigtFWHM
  rw [show (0.2166 : ℝ) * wL ^ 2 + (0 : ℝ) ^ 2 = 0.2166 * wL ^ 2 by ring,
    Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 0.2166), Real.sqrt_sq hwL]
  ring

end CflibsFormal
