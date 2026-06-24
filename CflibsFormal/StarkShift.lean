/-
Copyright (c) 2026 Brian Squires. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Squires
-/
import Mathlib

/-!
# CF-LIBS formalization — the Stark line-shift electron-density diagnostic

A companion to `StarkBroadening.lean`'s Stark **width** diagnostic: the Stark line-**shift**. By
Griem's impact approximation, both the electron-impact width and the line-center shift are *linear*
in the electron density at not-too-high densities; this module formalizes the shift forward law,
its inverse, and — crucially — the **honest sign handling** that distinguishes a shift from a width.

The distinctive faithfulness point: a Stark **shift** is **signed** (red `> 0`, blue `< 0`), so
`d_ref ∈ ℝ` may be negative, whereas a width parameter `w_ref > 0` is always positive. Consequently
the width module's *unconditional* `StrictMono` does **not** carry over: monotonicity is conditional
(`StrictMono` for red, `StrictAnti` for blue), the sign-robust monotone fact is on the shift
*magnitude* `|d|`, and identifiability needs only `d_ref ≠ 0` (the weakest correct hypothesis).
Stating these with `≠ 0` rather than `> 0` — rather than over-claiming unconditional monotonicity —
is the point.

* `starkShift` — forward map `d = d_ref·(n_e/n_ref)` (signed `d_ref`; **no** factor of 2, since a
  shift is a line-center displacement, not a FWHM — contrast `StarkBroadening.starkFWHM`'s `2·w`).
* `starkDensityFromShift` — inverse diagnostic `n_e = n_ref·d/d_ref` (needs `d_ref ≠ 0`).
* `starkDensityFromShift_recovers` — soundness (the diagnostic inverts the forward map).
* `starkShift_isLinear` — the Griem linearity, bundled as `IsLinearMap` (holds for signed `d_ref`).
* `starkShift_strictMono_of_pos` / `starkShift_strictAnti_of_neg` — the sign-conditional
  monotonicity; `starkShift_abs_strictMono` — the sign-robust magnitude monotonicity;
  `starkShift_injective` — identifiability for any `d_ref ≠ 0`.
* `shiftWidthRatio_indep_ne` / `shift_width_density_agree` — the shift-to-width ratio `d/w`.
  **Honest scope:** because `d` and `w` are extracted from the *same* line and obey the *same*
  `n_e/n_ref` scaling, `n_e` **cancels** in `d/w`, so `d/w = d_ref/w_ref` carries *no* information
  about `n_e`. It is therefore **not** an independent density cross-check (unlike
  `StarkBroadening.stark_saha_lte_consistent`, where the width and a Saha stage-ratio probe
  genuinely different physics); it is a line-identification / impact-approximation consistency
  check (the observed centre-shift-to-width ratio must equal the tabulated atomic constant).

## Literature

The linear electron-impact **width and shift** impact-approximation laws are those of H. R. Griem,
*Spectral Line Broadening by Plasmas*, Academic Press (1974) — "for not too high densities, widths
and shifts are linearly proportional to the perturber density." The canonical tabulation of signed
Stark **shifts** (red/blue) at a reference electron density is N. Konjević and J. R. Roberts, "A
critical review of the Stark widths and shifts of spectral lines from non-hydrogenic atoms,"
*J. Phys. Chem. Ref. Data* **5** (1976) 209–257 (continued 1984/1990/2002); see also the STARK-B
database (Sahal-Bréchot, Dimitrijević et al.). Tables commonly anchor at `n_ref ≈ 10¹⁶ cm⁻³`; here
`n_ref` is a free symbolic reference (`d_ref` is re-anchored to whatever `n_ref` the spec uses).
Honest scope: the linear law is the operational impact-approximation rule (exact given the tabulated
`d_ref`); quasi-static / ion-dynamic nonlinear corrections at very high density are out of scope.
-/

namespace CflibsFormal

/-- **Stark line-shift forward map (Griem linear).** `d = d_ref·(n_e/n_ref)`, with `d_ref` the
**signed** shift parameter (red `> 0`, blue `< 0`) tabulated at reference density `n_ref`. There is
**no** factor of 2 (a shift is a line-center displacement, not a FWHM — contrast
`StarkBroadening.starkFWHM`'s `2·w`). -/
noncomputable def starkShift (dRef nRef ne : ℝ) : ℝ :=
  dRef * (ne / nRef)

/-- **Stark-shift electron-density diagnostic (inverse map).** Solving `d = d_ref·(n_e/n_ref)` for
`n_e` gives `n_e = n_ref·d/d_ref`. Reads `n_e` off a *measured* signed shift `d` — a function of the
observation, never of the true `n_e`. Needs `d_ref ≠ 0`; the measured `d` and `d_ref` must share
sign for a physical (positive) `n_e`. -/
noncomputable def starkDensityFromShift (dRef nRef d : ℝ) : ℝ :=
  nRef * d / dRef

/-- The tabulated, `n_e`-independent shift-to-width ratio `d_ref/w_ref`. See
`shiftWidthRatio_indep_ne` for why its `n_e`-independence makes it a line-identification check, not
an independent density estimate. -/
noncomputable def shiftWidthRatio (dRef wRef : ℝ) : ℝ :=
  dRef / wRef

/-- **Sign-aware positivity (red shift).** For a red-shift parameter `d_ref > 0` and a positive
density, the shift is positive. (The blue-shift companion is `starkShift_strictAnti_of_neg` /
`starkShift_abs_strictMono`.) -/
lemma starkShift_pos_of_dRef_pos {dRef nRef ne : ℝ}
    (hd : 0 < dRef) (hnRef : 0 < nRef) (hne : 0 < ne) : 0 < starkShift dRef nRef ne := by
  unfold starkShift
  exact mul_pos hd (div_pos hne hnRef)

/-- **Soundness of the Stark-shift diagnostic.** The diagnostic exactly inverts the forward map.
The hypothesis is `d_ref ≠ 0` (signed), *not* `0 < d_ref` — the key sign-handling design point;
both `hd` and `hnRef` are load-bearing. -/
theorem starkDensityFromShift_recovers {dRef nRef ne : ℝ} (hd : dRef ≠ 0) (hnRef : nRef ≠ 0) :
    starkDensityFromShift dRef nRef (starkShift dRef nRef ne) = ne := by
  simp only [starkDensityFromShift, starkShift]
  field_simp

/-- **Griem linearity, bundled (`IsLinearMap`).** For fixed `d_ref`, `n_ref`, the Stark shift is an
`ℝ`-linear map in the electron density — for **signed** `d_ref` (and even at the unphysical
`n_ref = 0`, where it degenerates to the zero map). Mirrors `StarkBroadening.starkFWHM_isLinear`. -/
theorem starkShift_isLinear (dRef nRef : ℝ) : IsLinearMap ℝ (starkShift dRef nRef) where
  map_add a b := by simp only [starkShift]; ring
  map_smul c ne := by simp only [starkShift, smul_eq_mul]; ring

/-- **Conditional monotonicity — red shift.** For `d_ref > 0`, the shift strictly increases with
`n_e`. The `0 < d_ref` hypothesis is essential: unlike the width, this does **not** hold
unconditionally (see `starkShift_strictAnti_of_neg` for blue). -/
theorem starkShift_strictMono_of_pos {dRef nRef : ℝ} (hd : 0 < dRef) (hnRef : 0 < nRef) :
    StrictMono (starkShift dRef nRef) := by
  intro a b hab
  simp only [starkShift]
  gcongr

/-- **Conditional anti-monotonicity — blue shift.** For `d_ref < 0`, the shift strictly *decreases*
with `n_e` (it moves further blue). The sign flip is explicit: the proof uses
`mul_lt_mul_of_neg_left`, not `gcongr` (which assumes a nonnegative multiplier). -/
theorem starkShift_strictAnti_of_neg {dRef nRef : ℝ} (hd : dRef < 0) (hnRef : 0 < nRef) :
    StrictAnti (starkShift dRef nRef) := by
  intro a b hab
  simp only [starkShift]
  have hab' : a / nRef < b / nRef := by gcongr
  exact mul_lt_mul_of_neg_left hab' hd

/-- **Identifiability of `n_e` from the shift.** Distinct densities give distinct shifts for any
`d_ref ≠ 0` — the weakest correct hypothesis, covering red **and** blue shifts (reduces to the
sign-conditional monotone maps). -/
theorem starkShift_injective {dRef nRef : ℝ} (hd : dRef ≠ 0) (hnRef : 0 < nRef) :
    Function.Injective (starkShift dRef nRef) := by
  rcases lt_or_gt_of_ne hd with hneg | hpos
  · exact (starkShift_strictAnti_of_neg hneg hnRef).injective
  · exact (starkShift_strictMono_of_pos hpos hnRef).injective

/-- **Sign-robust magnitude monotonicity.** Regardless of red or blue, a denser plasma shifts the
line *further* from line center: the shift *magnitude* `|d|` strictly increases with `n_e` (for
`d_ref ≠ 0`, `0 ≤ a < b`). This is the sign-independent counterpart of the width's monotonicity. -/
theorem starkShift_abs_strictMono {dRef nRef : ℝ} (hd : dRef ≠ 0) (hnRef : 0 < nRef)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    |starkShift dRef nRef a| < |starkShift dRef nRef b| := by
  simp only [starkShift, abs_mul]
  have hda : 0 < |dRef| := abs_pos.mpr hd
  have hb : 0 ≤ b := ha.trans hab.le
  rw [abs_of_nonneg (div_nonneg ha hnRef.le), abs_of_nonneg (div_nonneg hb hnRef.le)]
  have hlt : a / nRef < b / nRef := by gcongr
  exact mul_lt_mul_of_pos_left hlt hda

/-- **The shift-to-width ratio is `n_e`-independent — and that is exactly why it is *not* a density
diagnostic.** With the (factor-free) linear width law `w(n_e) = w_ref·(n_e/n_ref)` written as
`starkShift wRef nRef ne`, the density cancels: `d(n_e)/w(n_e) = d_ref/w_ref` for every `n_e ≠ 0`.
So the ratio determines an *atomic* constant, carrying **no** information about `n_e` — it is a
line-identification / impact-approximation consistency check, not an independent density estimate.
(`StarkBroadening.starkFWHM` carries an extra FWHM factor `2`; with that convention the ratio would
be `d_ref/(2·w_ref)` — the `2` likewise cancels in `n_e`.) -/
theorem shiftWidthRatio_indep_ne {dRef wRef nRef ne : ℝ}
    (hwRef : wRef ≠ 0) (hnRef : nRef ≠ 0) (hne : ne ≠ 0) :
    starkShift dRef nRef ne / starkShift wRef nRef ne = shiftWidthRatio dRef wRef := by
  simp only [starkShift, shiftWidthRatio]
  field_simp

/-- **Shift- and width-route densities coincide — conditioned on the line-ID check.** IF the
observed shift-to-width ratio matches the tabulated `d_ref/w_ref` (`hratio`, the consistency
check of `shiftWidthRatio_indep_ne`), THEN the shift-route density `n_ref·d/d_ref` equals the
(factor-free) width-route density `n_ref·width/w_ref`. **Honest scope:** this is *weaker* than
`StarkBroadening.stark_saha_lte_consistent`. There the two observations probe different physics, so
agreement is real evidence; here `d` and `width` come from the *same* line under the *same* scaling,
so `n_e` already cancels in `hratio` — the agreement is an algebraic consequence of the line-ID
check, not an independent confirmation of `n_e`. -/
theorem shift_width_density_agree {dRef wRef nRef d width : ℝ}
    (hd : dRef ≠ 0) (hw : wRef ≠ 0) (hwidth : width ≠ 0)
    (hratio : d / width = shiftWidthRatio dRef wRef) :
    starkDensityFromShift dRef nRef d = nRef * width / wRef := by
  simp only [shiftWidthRatio] at hratio
  simp only [starkDensityFromShift]
  rw [div_eq_div_iff hwidth hw] at hratio
  rw [div_eq_div_iff hd hw]
  linear_combination nRef * hratio

end CflibsFormal
