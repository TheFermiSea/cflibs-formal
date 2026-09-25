/-
Copyright (c) 2026 Brian Squires. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Squires
-/
import Mathlib

/-!
# CF-LIBS formalization — the continuum background

Real LIBS spectra sit on a **continuum** (free-free bremsstrahlung + free-bound recombination)
that the line-based forward map ignores. This module formalizes the continuum's standard scaling,
baseline subtraction when the continuum level is known exactly, and the temperature dependence of
a **reduced** line-to-continuum ratio. That reduced ratio is *not* a thermometer for neutral lines
(see Honest scope).

* `contEmissivity` — a Kramers/Biberman-type continuum emissivity in dimensionless reduced form
  `ε ∝ n_e·n_ion·exp(-u)/√T`, with `u = hc/(λ·k_B·T) ≥ 0` the reduced continuum photon energy and
  `n_ion` the density of the ion stage that produces the continuum; `contEmissivitySingly` is the
  singly-ionized case `n_ion ≈ n_e` (so `ε ∝ n_e²`). Both positive, and strictly increasing in
  `n_e`.
* `baseline_subtraction_exact` — measured intensity is additive (`I_meas = I_line + ε_cont`), so
  subtracting the continuum level `ε_cont` itself recovers the line **exactly**. Algebraically
  trivial: the additive model and an exactly known continuum are assumptions of the statement. A
  *fitted* baseline differs from `ε_cont`, and that error passes one-for-one into the recovered
  line; no bound on it is proved here.
* `lineToContRatio` / `lineToContRatio_strictMono_T` — the reduced ratio `R_LC(T) = B·√T·exp(-a/T)`
  with `B > 0` and `a` held fixed. Proved: `R_LC` is strictly increasing on `T > 0` **if** `a ≥ 0`
  (both `√T` and `exp(-a/T)` increase). The converse is not proved here; by calculus,
  `d/dT log R_LC = (T + 2a)/(2T²)`, so for `a < 0` the ratio falls on `(0, -2a)` and rises after.
  Whether `R_LC` is a physical line-to-continuum ratio at all depends on the line's ionization
  stage (next section).

## Honest scope

`contEmissivity` is asserted as the operational definition, with the positive constants `K·Z²·ξ`
folded into `C`. Freezing the Biberman/Gaunt correction factor `ξ` into `C` drops its real `λ,T`
dependence (strong for `λ < 450 nm`). The form itself (`exp(-u)` as a common prefactor of the
free-free and free-bound parts, with a factor `ξ` of order one left over) has **not** been checked
against a primary source; treat it as approximate.

Dividing a Boltzmann line of stage `z` (upper level `E_k`, same wavelength `λ`) by
`contEmissivity` gives
`ε_line/ε_cont ∝ [n_z/(n_e·n_ion)]·(gA/U_z)·√T·exp(-(E_k - hc/λ)/(k_B·T))/ξ`,
so `a = (E_k - hc/λ)/k_B`, and `B` absorbs the bracketed density ratio. `B` is therefore **not**
`T`-independent in general. What it carries depends on the stage (derivation from the repo's
definitions; not formalized):

* **Neutral line**, continuum from the next stage (`n_ion = n_{z+1}`). By the repo's own Saha law
  (`sahaFactor`), `n_z/(n_e·n_{z+1}) = 1/S(T)`, which scales as `T^(-3/2)·exp(χ/(k_B·T))` at
  frozen partition functions. This is the dominant temperature dependence, not a correction to
  it. Substituting it gives
  `ε_line/ε_cont ∝ exp((χ - E_k + hc/λ)/(k_B·T))/(T·U_{z+1}(T))`, which strictly **decreases**
  in `T` whenever `E_k ≤ χ + hc/λ` (every bound level), at frozen `U_{z+1}` and `ξ`; a partition
  function that rises with `T` only strengthens the decrease. So `lineToContRatio_strictMono_T`
  does **not** describe a neutral line, and `a ≥ 0` has no physical meaning there.
* **Line of the continuum-producing ion stage** (`n_z = n_ion`, e.g. an ionic line in a singly
  ionized plasma). Then `B ∝ gA/(n_e·U_z(T)·ξ)` and no Saha factor enters, so the reduced form
  holds at **fixed `n_e`** with `U_z` and `ξ` frozen. Only in this reading is
  `lineToContRatio_strictMono_T` a statement about a measurable ratio.

The theorem itself is a calculus fact about `B·√T·exp(-a/T)`. A neutral-line statement would
have to substitute `sahaFactor` explicitly; ionization-potential depression is not modeled in the
repo. Out of scope: spectral integration over the bandpass, the explicit `ξ(λ,T)` fit, absolute
radiometric calibration, and the two-unknown `(T,n_e)` joint inversion.

## Literature

The bremsstrahlung (free-free) + recombination (free-bound) continuum emissivity
`ε ∝ Z²·n_e·n_ion·T^(-1/2)·exp(-hc/λk_BT)·ξ` is standard: H. R. Griem, *Principles of Plasma
Spectroscopy* (Cambridge, 1997), chapters on continuous spectra (Biberman/Gaunt correction
factor). C. Aragón, J. A. Aguilera, "Characterization of laser induced plasmas by optical
emission spectroscopy," *Spectrochim. Acta B* **63** (2008) 893–916 (the line-to-continuum-ratio
temperature method); this module does not formalize that method's formula, only the reduced
`R_LC` above. The additive line+continuum measured-intensity model and baseline subtraction are
universal LIBS practice (Cremers & Radziemski, *Handbook of Laser-Induced Breakdown Spectroscopy*,
2nd ed., Wiley, 2013).
-/

namespace CflibsFormal

/-- **Continuum emissivity (Kramers/Biberman-type, dimensionless reduced form).**
`ε ∝ n_e·n_ion·exp(-u)/√T`, where `u = hc/(λ·k_B·T) ≥ 0` is the reduced continuum photon energy,
`n_ion` is the density of the continuum-producing ion stage, and `C` folds the positive constant
`K·Z²·ξ`. Approximate: freezing the Biberman/Gaunt factor `ξ` into `C` drops its `λ,T`
dependence, and the common `exp(-u)` prefactor on the free-bound part is not checked against a
primary source (module Honest scope). -/
noncomputable def contEmissivity (C ne nion T u : ℝ) : ℝ :=
  C * ne * nion * Real.exp (-u) / Real.sqrt T

/-- **Continuum emissivity in a singly-ionized plasma** (`n_ion ≈ n_e`), so `ε ∝ n_e²·exp(-u)/√T`.
The `n_ion := n_e` specialization of `contEmissivity` (see `contEmissivitySingly_eq`). -/
noncomputable def contEmissivitySingly (C ne T u : ℝ) : ℝ :=
  C * ne ^ 2 * Real.exp (-u) / Real.sqrt T

/-- **Additive measured intensity** at a line pixel: `I_meas = I_line + ε_cont`. -/
noncomputable def totalIntensity (Iline eCont : ℝ) : ℝ :=
  Iline + eCont

/-- **Baseline (continuum) subtraction**: remove a fitted continuum level `eCont` from the measured
intensity. The inverse of `totalIntensity` in its first argument (see
`baseline_subtraction_exact`). -/
noncomputable def subtractBaseline (Imeas eCont : ℝ) : ℝ :=
  Imeas - eCont

/-- **Reduced line-to-continuum ratio** `R_LC(T) = B·√T·exp(-a/T)`, with `B > 0` and `a` held
fixed. With `a = (E_k - hc/λ)/k_B`, it is the ratio of a Boltzmann line to `contEmissivity` only
when `B` does not vary with `T`: for a line of the continuum-producing ion stage at fixed `n_e`,
with partition function and `ξ` frozen, `B ∝ gA/(n_e·U·ξ)`. For a neutral line `B` carries the
Saha factor `1/S(T)`, and this form is not the physical ratio, which decreases with `T` (module
Honest scope). Strictly increasing in `T` if `a ≥ 0`: `lineToContRatio_strictMono_T`. -/
noncomputable def lineToContRatio (B a T : ℝ) : ℝ :=
  B * Real.sqrt T * Real.exp (-a / T)

/-- The continuum emissivity is strictly positive for positive constant, densities, and
temperature (the `exp` factor is positive for any reduced photon energy `u`). -/
lemma contEmissivity_pos {C ne nion T u : ℝ}
    (hC : 0 < C) (hne : 0 < ne) (hnion : 0 < nion) (hT : 0 < T) :
    0 < contEmissivity C ne nion T u := by
  have hsqrt : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  unfold contEmissivity
  positivity

/-- The singly-ionized continuum emissivity is the `n_ion := n_e` case of `contEmissivity`. -/
lemma contEmissivitySingly_eq (C ne T u : ℝ) :
    contEmissivitySingly C ne T u = contEmissivity C ne ne T u := by
  unfold contEmissivitySingly contEmissivity
  ring

/-- **The continuum brightens with electron density.** At fixed temperature and reduced photon
energy, the continuum emissivity is strictly increasing in `n_e` (it is a positive constant times
`n_e`). -/
lemma contEmissivity_strictMono_ne {C nion T u : ℝ} (hC : 0 < C) (hnion : 0 < nion) (hT : 0 < T) :
    StrictMonoOn (fun ne => contEmissivity C ne nion T u) (Set.Ioi 0) := by
  intro a _ha b _hb hab
  have hsqrt : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  simp only [contEmissivity]
  gcongr

/-- The line-to-continuum ratio is strictly positive for positive `B` and temperature. -/
lemma lineToContRatio_pos {B a T : ℝ} (hB : 0 < B) (hT : 0 < T) :
    0 < lineToContRatio B a T := by
  have hsqrt : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  unfold lineToContRatio
  positivity

/-- **Baseline subtraction is exact when the subtracted level is the true continuum.**
`(I_line + ε_cont) - ε_cont = I_line`: algebraically trivial. The content lies in the assumptions,
an additive measured intensity and a subtracted level equal to `ε_cont`. Any error in a fitted
baseline passes one-for-one into the recovered line, and no bound on it is proved here. -/
theorem baseline_subtraction_exact (Iline eCont : ℝ) :
    subtractBaseline (totalIntensity Iline eCont) eCont = Iline := by
  unfold subtractBaseline totalIntensity
  ring

/-- **The reduced ratio `B·√T·exp(-a/T)` is strictly increasing in `T` if `a ≥ 0`.** On
`(0, ∞)`, with `B > 0` and `a` fixed, both `√T` and `exp(-a/T)` increase. This is a calculus fact
about the reduced form. It reads as a temperature diagnostic only for a line of the
continuum-producing ion stage at fixed `n_e` (partition function and `ξ` frozen); for a neutral
line the physical line-to-continuum ratio *decreases* with `T` (module Honest scope). Only the
"if" direction is proved. The hypothesis cannot simply be dropped: for `a < 0` the ratio
decreases on `(0, -2a)`, a calculus fact not formalized here. -/
theorem lineToContRatio_strictMono_T {B a : ℝ} (hB : 0 < B) (ha : 0 ≤ a) :
    StrictMonoOn (lineToContRatio B a) (Set.Ioi 0) := by
  intro x hx y _hy hxy
  have hx0 : 0 < x := hx
  unfold lineToContRatio
  have h1 : Real.sqrt x < Real.sqrt y := Real.sqrt_lt_sqrt hx0.le hxy
  have hdiv : a / y ≤ a / x := by gcongr
  have h2 : Real.exp (-a / x) ≤ Real.exp (-a / y) := by
    apply Real.exp_le_exp.mpr
    rw [neg_div, neg_div]
    exact neg_le_neg hdiv
  have hBx : B * Real.sqrt x < B * Real.sqrt y := by gcongr
  exact mul_lt_mul hBx h2 (Real.exp_pos _) (by positivity)

end CflibsFormal
