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
the (exact) soundness of baseline subtraction, and the line-to-continuum **thermometer**.

* `contEmissivity` — the Kramers/Biberman continuum emissivity in dimensionless reduced form
  `ε ∝ n_e·n_ion·exp(-u)/√T`, with `u = hc/(λ·k_B·T) ≥ 0` the reduced continuum photon energy;
  `contEmissivitySingly` is the singly-ionized case `n_ion ≈ n_e` (so `ε ∝ n_e²`). Both positive,
  and strictly increasing in `n_e`.
* `baseline_subtraction_exact` — measured intensity is additive (`I_meas = I_line + ε_cont`), so
  subtracting a fitted continuum baseline recovers the line **exactly**. Algebraically trivial, but
  the faithful spec statement of why baseline subtraction is sound (cf. `LineBroadening`'s
  deconvolution exactness).
* `lineToContRatio` / `lineToContRatio_strictMono_T` — the line-to-continuum ratio
  `R_LC(T) = B·√T·exp(-a/T)`, a temperature diagnostic. **Honest, conditional** claim: it is a
  valid (strictly increasing) thermometer iff `a ≥ 0`, i.e. the line upper-level energy is at or
  above the continuum photon energy (`E_k ≥ hc/λ`); then both `√T` and `exp(-a/T)` increase. The
  *unconditional* monotonicity claim is **false** (for `a < 0` the ratio is non-monotone on
  `(0, -2a)`), so the `0 ≤ a` hypothesis is load-bearing.

## Honest scope

`contEmissivity` is the standard textbook Kramers/Biberman form asserted as the operational
definition (the positive constants `K·Z²·ξ` folded into `C`); the **Biberman/Gaunt free-bound +
free-free correction factor `ξ` is the genuinely approximate ingredient** (`O(1)` but carrying a
real `λ,T` dependence, strong for `λ < 450 nm`). The line-to-continuum coefficient `B` folds the
Saha density ratio `n_z/(n_e·n_ion)` and `gA/U`, so it is `T`-independent only to **leading order**
under stable LTE — the clean `√T·exp(-a/T)` form is the leading-order LTE reduction, not exact. Out
of scope: spectral integration over the bandpass, the explicit `ξ(λ,T)` fit, absolute radiometric
calibration, and the two-unknown `(T,n_e)` joint inversion (only the forward monotonicity is here).

## Literature

The bremsstrahlung (free-free) + recombination (free-bound) continuum emissivity
`ε ∝ Z²·n_e·n_ion·T^(-1/2)·exp(-hc/λk_BT)·ξ` and the line-to-continuum thermometry are standard:
H. R. Griem, *Principles of Plasma Spectroscopy* (Cambridge, 1997), chapters on continuous spectra
(Biberman/Gaunt correction factor); C. Aragón, J. A. Aguilera, "Characterization of laser induced
plasmas by optical emission spectroscopy," *Spectrochim. Acta B* **63** (2008) 893–916 (the
line-to-continuum-ratio temperature method). The additive line+continuum measured-intensity model
and baseline subtraction are universal LIBS practice (Cremers & Radziemski, *Handbook of
Laser-Induced Breakdown Spectroscopy*, 2nd ed., Wiley, 2013).
-/

namespace CflibsFormal

/-- **Continuum emissivity (Kramers/Biberman, dimensionless reduced form).**
`ε ∝ n_e·n_ion·exp(-u)/√T`, where `u = hc/(λ·k_B·T) ≥ 0` is the reduced continuum photon energy and
`C` folds the positive constant `K·Z²·ξ` — the Biberman/Gaunt factor `ξ` (`O(1)`) being the only
non-exact ingredient. -/
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

/-- **Line-to-continuum intensity ratio**, reduced form `R_LC(T) = B·√T·exp(-a/T)`. `B > 0` folds
the `T`-independent atomic/density constants (to leading order); `a = (E_k - hc/λ)/k_B` is the fixed
exponent coefficient whose sign is set by whether the line upper-level energy `E_k` exceeds the
continuum photon energy `hc/λ`. A temperature diagnostic — but monotone only for `a ≥ 0` (regime
`E_k ≥ hc/λ`), see `lineToContRatio_strictMono_T`. -/
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

/-- **Baseline subtraction is exact.** Subtracting the continuum from the additive measured
intensity recovers the line intensity with no approximation: `(I_line + ε_cont) - ε_cont = I_line`.
Algebraically trivial, but the faithful justification that continuum baseline subtraction is
sound. -/
theorem baseline_subtraction_exact (Iline eCont : ℝ) :
    subtractBaseline (totalIntensity Iline eCont) eCont = Iline := by
  unfold subtractBaseline totalIntensity
  ring

/-- **The line-to-continuum ratio is a thermometer — in the regime `E_k ≥ hc/λ`.** For `a ≥ 0`
(line upper-level energy at or above the continuum photon energy), `R_LC(T) = B·√T·exp(-a/T)` is
strictly increasing in `T` on `(0, ∞)`: both `√T` and `exp(-a/T)` increase. The `0 ≤ a` hypothesis
is **load-bearing** — for `a < 0` the ratio is non-monotone (it decreases on `(0, -2a)`), so the
*unconditional* thermometer claim would be false. -/
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
