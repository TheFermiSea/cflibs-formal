/-
Copyright (c) 2026 Brian Squires. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Squires
-/
import Mathlib
import CflibsFormal.VoigtWidth

/-!
# CF-LIBS formalization — a non-circular error enclosure for the Voigt FWHM

`VoigtWidth.lean` defines the **Olivero–Longbothum (1977)** algebraic Voigt-FWHM combination
`voigtFWHM wL wG = 0.5346·wL + √(0.2166·wL² + wG²)` and proves the two lower bounds
`wG ≤ voigtFWHM` and `wL ≤ voigtFWHM`. This module turns those into a rigorous, **non-circular**
error enclosure between the OL algebraic value and the *true* (convolution) Voigt FWHM.

The design avoids the vacuity trap. We do **not** define `FWHM_true` as the OL formula (that would
make the error identically `0`). Instead:

1. **Proved outright (no hypothesis).** The OL value sits above the lower sandwich rail and just
   below a sharp upper rail:
   * `voigtFWHM_ge_max` — `max wG wL ≤ voigtFWHM wL wG` (from the two `VoigtWidth` lower bounds);
   * `voigtFWHM_le_olUpper` — `voigtFWHM wL wG ≤ (0.5346 + √0.2166)·wL + wG`, via `√(a²+b²) ≤
     √a·|·| + |·|` (concavity/subadditivity of `√`).
2. **Real finding (proved).** `voigtFWHM_naive_upper_false` — the *naive* upper rail
   `voigtFWHM ≤ wL + wG` is **false**: at `(wL,wG) = (1,0)` the OL value is
   `0.5346 + √0.2166 = 1.0000034… > 1`. So the textbook sandwich `[max(fG,fL), fG+fL]` does **not**
   contain the OL value; the enclosure width picks up a `η·wL` correction with
   `η = 0.5346 + √0.2166 − 1 ∈ (0, 10⁻⁵)`.
3. **Uncited hypothesis (not proved here).** The rigorous bracketing of the *true* convolution FWHM,
   `max(fG,fL) ≤ FWHM_true ≤ fG + fL`, is taken as an explicit hypothesis `hlo`/`hhi` on an abstract
   `Ftrue`. Defining the convolution FWHM in Lean is out of scope; this bracket is a standard
   line-shape fact (see Literature).
4. **Derived enclosure.** `voigtFWHM_true_enclosure` — both `voigtFWHM wL wG` and `Ftrue` lie in the
   common interval `[max(fG,fL), (0.5346+√0.2166)·wL + wG]`, hence
   `|voigtFWHM wL wG − Ftrue| ≤ min(fG,fL) + η·wL`. The clean-constant corollary
   `voigtFWHM_true_enclosure_clean` gives the fully rational bound
   `|voigtFWHM wL wG − Ftrue| ≤ min(fG,fL) + 10⁻⁵·wL`, i.e. `δ ≈ min(fG,fL)` to five decimals.

The bound is honest and non-vacuous: `δ = min(fG,fL) + η·wL` is neither `0` (unless a component
width vanishes) nor the trivial `fG+fL`; it collapses to exactly `0` in the pure-Gaussian case
(`wL = 0`), matching the exact `voigt_gaussian_limit` of `VoigtWidth`.

## Literature and scope

Scope: the headline enclosure is **REDUCED** — the OL-in-sandwich position (steps 1–2) is proved
outright; the *true*-FWHM bracket (step 3) is a clearly-labelled **hypothesis**, so the enclosure
`|voigtFWHM − Ftrue| ≤ δ` is **conditional** on that bracket. Nothing about the convolution FWHM is
asserted as proved. The underlying OL formula is itself an APPROXIMATION (empirical fit, ~0.01%);
this module quantifies the gap between that approximation and the true width *given* the bracket.

Per-theorem tags (the module is deliberately mixed): the two sandwich rails `voigtFWHM_ge_max` /
`voigtFWHM_le_olUpper` are **EXACT** algebra about the OL formula (built from `VoigtWidth`'s EXACT
`voigtFWHM_ge_gauss` / `voigtFWHM_ge_lorentz`); `voigtFWHM_naive_upper_false` is **APPROXIMATION**
(it is proved *through* — and its whole point is to expose the fit error of — `VoigtWidth`'s
APPROXIMATION-tagged `voigt_lorentzian_limit`); the two conditional enclosures are **REDUCED**.

* J. J. Olivero, R. L. Longbothum, "Empirical fits to the Voigt line width: A brief review,"
  *J. Quant. Spectrosc. Radiat. Transfer* **17** (1977) 233–236 (DOI 10.1016/0022-4073(77)90161-3):
  the `w_V = 0.5346·w_L + √(0.2166·w_L² + w_G²)` FWHM fit (as in `VoigtWidth.lean`).
* The bracket `max(fG,fL) ≤ FWHM_V ≤ fG + fL` for the *true* Voigt (Gaussian ⊗ Lorentzian) FWHM
  is an **uncited standard line-shape property** (convolution wider than either constituent — lower
  rail — and no wider than their sum — upper rail). It is *not* proved in this repo and is *not*
  attributed to the Olivero–Longbothum fit above; it enters **only as an explicit hypothesis** on
  `Ftrue` (`hlo`, `hhi`), so every enclosure theorem is conditional on it.
-/

namespace CflibsFormal

/-- **Lower sandwich rail (proved outright).** The OL Voigt FWHM is at least the larger of the two
component widths: `max(w_G, w_L) ≤ voigtFWHM w_L w_G`. Assembled from the two `VoigtWidth` lower
bounds `voigtFWHM_ge_gauss` and `voigtFWHM_ge_lorentz`. -/
lemma voigtFWHM_ge_max {wL wG : ℝ} (hwL : 0 ≤ wL) (hwG : 0 ≤ wG) :
    max wG wL ≤ voigtFWHM wL wG :=
  max_le (voigtFWHM_ge_gauss hwL hwG) (voigtFWHM_ge_lorentz hwL)

/-- **Sharp upper rail (proved outright).** By subadditivity of `√` on the two squared terms,
`voigtFWHM w_L w_G ≤ (0.5346 + √0.2166)·w_L + w_G`. The coefficient `0.5346 + √0.2166 = 1.0000034…`
is just above `1`, which is exactly why the naive rail `w_L + w_G` fails (see
`voigtFWHM_naive_upper_false`). -/
lemma voigtFWHM_le_olUpper {wL wG : ℝ} (hwL : 0 ≤ wL) (hwG : 0 ≤ wG) :
    voigtFWHM wL wG ≤ (0.5346 + Real.sqrt 0.2166) * wL + wG := by
  have hcross : 0 ≤ Real.sqrt 0.2166 * wL * wG :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hwL) hwG
  have hexp : (Real.sqrt 0.2166 * wL + wG) ^ 2
      = Real.sqrt 0.2166 ^ 2 * wL ^ 2 + 2 * (Real.sqrt 0.2166 * wL * wG) + wG ^ 2 := by ring
  rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 0.2166)] at hexp
  have harg : 0.2166 * wL ^ 2 + wG ^ 2 ≤ (Real.sqrt 0.2166 * wL + wG) ^ 2 := by
    rw [hexp]; linarith
  have hY : 0 ≤ Real.sqrt 0.2166 * wL + wG := by positivity
  have key : Real.sqrt (0.2166 * wL ^ 2 + wG ^ 2) ≤ Real.sqrt 0.2166 * wL + wG := by
    calc Real.sqrt (0.2166 * wL ^ 2 + wG ^ 2)
        ≤ Real.sqrt ((Real.sqrt 0.2166 * wL + wG) ^ 2) := Real.sqrt_le_sqrt harg
      _ = Real.sqrt 0.2166 * wL + wG := Real.sqrt_sq hY
  unfold voigtFWHM
  linarith

/-- **Real finding (proved).** The *naive* upper rail `voigtFWHM ≤ w_L + w_G` is FALSE. Witness:
`(w_L, w_G) = (1, 0)` gives `voigtFWHM 1 0 = 0.5346 + √0.2166 > 1 = w_L + w_G`, because
`√0.2166 > 0.4654` (as `0.4654² = 0.21659716 < 0.2166`). This is why the honest enclosure width
carries the `η·w_L` correction rather than the textbook `min(fG,fL)`. -/
theorem voigtFWHM_naive_upper_false :
    ¬ ∀ wL wG : ℝ, 0 ≤ wL → 0 ≤ wG → voigtFWHM wL wG ≤ wL + wG := by
  intro h
  have hbad := h 1 0 (by norm_num) (le_refl 0)
  rw [voigt_lorentzian_limit (by norm_num : (0:ℝ) ≤ 1)] at hbad
  have hs : (0.4654 : ℝ) < Real.sqrt 0.2166 := by
    have h2 : Real.sqrt (0.4654 ^ 2) < Real.sqrt 0.2166 :=
      Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    rwa [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 0.4654)] at h2
  simp only [mul_one] at hbad
  linarith

/-- **Conditional error enclosure (main result).** Let `Ftrue` be the true convolution Voigt FWHM,
bracketed by the standard *uncited* bounds `hlo : max(w_G, w_L) ≤ Ftrue`, `hhi : Ftrue ≤ w_L + w_G`
(taken as hypotheses, not proved here).
Since the OL value also satisfies `max(w_G,w_L) ≤ voigtFWHM w_L w_G ≤ (0.5346+√0.2166)·w_L + w_G`,
both `voigtFWHM w_L w_G` and `Ftrue` live in that common interval, so
`|voigtFWHM w_L w_G − Ftrue| ≤ min(w_G, w_L) + η·w_L` with `η = 0.5346 + √0.2166 − 1 > 0`.
Non-circular: `Ftrue` is abstract and independent of the OL formula; the bound is `0` only when
`w_L = 0` (pure Gaussian, where OL is exact). -/
theorem voigtFWHM_true_enclosure {wL wG Ftrue : ℝ} (hwL : 0 ≤ wL) (hwG : 0 ≤ wG)
    (hlo : max wG wL ≤ Ftrue) (hhi : Ftrue ≤ wL + wG) :
    |voigtFWHM wL wG - Ftrue| ≤ min wG wL + (0.5346 + Real.sqrt 0.2166 - 1) * wL := by
  have hmaxA : max wG wL ≤ voigtFWHM wL wG := voigtFWHM_ge_max hwL hwG
  have hAU : voigtFWHM wL wG ≤ (0.5346 + Real.sqrt 0.2166) * wL + wG :=
    voigtFWHM_le_olUpper hwL hwG
  have hs : (0.4654 : ℝ) ≤ Real.sqrt 0.2166 := by
    have h2 : Real.sqrt (0.4654 ^ 2) ≤ Real.sqrt 0.2166 :=
      Real.sqrt_le_sqrt (by norm_num)
    rwa [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 0.4654)] at h2
  have hFtrueU : Ftrue ≤ (0.5346 + Real.sqrt 0.2166) * wL + wG := by
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ Real.sqrt 0.2166 - 0.4654) hwL]
  have hmin : min wG wL = wG + wL - max wG wL := by
    have := min_add_max wG wL; linarith
  have hδ : (0.5346 + Real.sqrt 0.2166) * wL + wG - max wG wL
      = min wG wL + (0.5346 + Real.sqrt 0.2166 - 1) * wL := by rw [hmin]; ring
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · rw [← hδ]; linarith
  · rw [← hδ]; linarith

/-- **Clean-constant enclosure.** The same bound with a fully rational width: since
`√0.2166 < 0.46541`, the correction `η = 0.5346 + √0.2166 − 1 < 10⁻⁵`, giving
`|voigtFWHM w_L w_G − Ftrue| ≤ min(w_G, w_L) + 10⁻⁵·w_L`. Operationally: the algebraic OL FWHM
tracks the true Voigt FWHM to within `min(fG,fL)` plus at most `0.001% · fL`. -/
theorem voigtFWHM_true_enclosure_clean {wL wG Ftrue : ℝ} (hwL : 0 ≤ wL) (hwG : 0 ≤ wG)
    (hlo : max wG wL ≤ Ftrue) (hhi : Ftrue ≤ wL + wG) :
    |voigtFWHM wL wG - Ftrue| ≤ min wG wL + 0.00001 * wL := by
  have h := voigtFWHM_true_enclosure hwL hwG hlo hhi
  have hs : Real.sqrt 0.2166 < 0.46541 := by
    have h2 : Real.sqrt 0.2166 < Real.sqrt (0.46541 ^ 2) :=
      Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    rwa [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 0.46541)] at h2
  have hcorr : (0.5346 + Real.sqrt 0.2166 - 1) * wL ≤ 0.00001 * wL :=
    mul_le_mul_of_nonneg_right (by linarith) hwL
  linarith

/-- **Non-vacuity witness.** Concrete data `w_L = w_G = 1`, and a true FWHM `Ftrue = 1.5` that is
genuinely inside the (uncited, hypothesized) bracket `max(1,1) = 1 ≤ 1.5 ≤ 2 = 1 + 1`. The enclosure
fires and the
width `min(1,1) + η·1 ≈ 1.0000034` is a real, finite, non-trivial number. -/
example : |voigtFWHM 1 1 - 1.5| ≤ min (1:ℝ) 1 + (0.5346 + Real.sqrt 0.2166 - 1) * 1 :=
  voigtFWHM_true_enclosure (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

/-- **Non-vacuity witness, clean constant.** Same data through the rational-width corollary:
`|voigtFWHM 1 1 − 1.5| ≤ min(1,1) + 10⁻⁵`. -/
example : |voigtFWHM 1 1 - 1.5| ≤ min (1:ℝ) 1 + 0.00001 * 1 :=
  voigtFWHM_true_enclosure_clean (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

/-- **Degenerate check (pure Gaussian ⇒ zero enclosure).** With `w_L = 0` the OL formula is exact
(`voigtFWHM 0 wG = wG`, `voigt_gaussian_limit`) and the bracket forces `Ftrue = wG`, so the
enclosure width is exactly `0`: the bound is not slack here. Witness at `w_G = 2`, `Ftrue = 2`. -/
example : |voigtFWHM 0 2 - 2| ≤ min (2:ℝ) 0 + (0.5346 + Real.sqrt 0.2166 - 1) * 0 :=
  voigtFWHM_true_enclosure (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

end CflibsFormal
