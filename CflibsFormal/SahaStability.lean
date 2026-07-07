/-
Copyright (c) 2026 Brian Squires. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Squires
-/
import Mathlib
import CflibsFormal.Saha
import CflibsFormal.PartitionLipschitz
import CflibsFormal.Analysis

/-!
# Saha–Boltzmann formalization — Part 2b: stability of the `n_e` diagnostic

`Saha.lean` establishes only *qualitative* well-posedness of the electron-density
diagnostic `n_e = electronDensityFromRatio … R = S(T)/R`: strict antitonicity
(`electronDensity_antitone`) and hence injectivity in the stage ratio `R`.  It does
**not** quantify how a measurement error in the stage ratio `R = n_{z+1}/n_z`
propagates into the inferred `n_e` — the property the CF-LIBS runtime needs to
carry a stage-ratio error bar through to an `n_e` error budget.  This module adds
that quantitative layer, holding the temperature `T` (hence the Saha factor `S`)
fixed:

* `saha_ratio_cancel` — PURE-MATH core: `(S/R₁)/(S/R₂) = R₂/R₁` for nonzero data.
* `electronDensity_relativeError` — **EXACT relative-error transfer**:
  `n_e(R₁)/n_e(R₂) = R₂/R₁`.  The log-derivative of the diagnostic is exactly `−1`
  (`ln n_e(R₁) − ln n_e(R₂) = −(ln R₁ − ln R₂)`), so a relative stage-ratio error
  maps one-to-one (with unit gain, inverted sign) onto a relative `n_e` error.
* `saha_inv_lipschitz` — PURE-MATH core: on `R ≥ R₀ > 0` the map `R ↦ S/R` is
  Lipschitz with explicit constant `S/R₀²`.
* `electronDensity_lipschitz` — **EXACT sensitivity bound** for the runtime error
  budget: `|n_e(R₁) − n_e(R₂)| ≤ (S/R₀²)·|R₁ − R₂|` on `R₁, R₂ ≥ R₀ > 0`.  The
  constant `S/R₀²` is exactly `|d n_e/dR|` at the worst-case (smallest) ratio `R₀`.

## Literature

Physics-facing statements are labelled EXACT against the Saha–Eggert ionization
equilibrium in the form given by Griem (packaged here as `sahaFactor`, proven
strictly positive by `Saha.sahaFactor_pos`); the relative-error identity and the
Lipschitz constant are elementary consequences of the closed form `n_e = S/R` and
carry no additional physical modelling.  The two `saha_*` cores are pure real
analysis and carry no citation.

## Scope and what remains open

This module began as the *single-ratio, fixed-`T`* sensitivity analysis of `n_e`.
The **T-channel** is now also addressed — but as a *two-sided sensitivity bound*, not
as monotonicity.  Two distinct statements must be kept apart:

* **T-channel monotonicity — STILL OPEN.**  A *signed* bound on `∂n_e/∂T` needs the
  closed form of `dS/dT`, whose sign is *not* definite: `S(T)` mixes the increasing
  thermal-de-Broglie factor `(2π m_e k_B T/h²)^{3/2}` and `exp(−χ/(k_B T))` with the
  partition-function ratio `U_{z+1}(T)/U_z(T)`, which can run either way.  No honest
  one-sided monotonicity of the *whole* `sahaFactor` in `T` is available without extra
  assumptions, so monotonicity remains SKIPPED rather than proven under a hidden
  reduction.
* **T-channel two-sided sensitivity — NOW CLOSED (this module).**  The runtime error
  budget does not need a *sign*; it needs a two-point Lipschitz bound
  `|n_e(T₁,R) − n_e(T₂,R)| ≤ L·|T₁ − T₂|` on a temperature box `[Tmin, Tmax]`.  That is
  sign-free and is provided here via channelwise two-point bounds on each factor of
  `sahaFactor` (thermal bracket, partition ratio, exponential), assembled by a
  three-factor product estimate: `sahaFactor_lipschitz_temp` and its `n_e` corollary
  `electronDensityFromRatio_lipschitz_temp` (constant `sahaFactorLipConst`).  Combined
  with `electronDensity_lipschitz` (the `R`-channel), the full `(δT, δR)` sensitivity
  budget for `n_e` is now available.
* **Multi-element design-matrix conditioning.**  The rank / condition-number
  analysis of the joint multi-element inversion is a separate linear-algebra
  problem, not addressed here.

All quantities are real; nothing in this module redefines `sahaFactor` or
`electronDensityFromRatio` — both are reused verbatim from `Saha.lean`.
-/

namespace CflibsFormal

variable {ι : Type*} [Fintype ι]
variable {κ : Type*} [Fintype κ]

/-- **Ratio-cancellation core (PURE-MATH).** For a nonzero shared factor `S` and
nonzero denominators `R₁, R₂`, the quotient of the two diagnostic readings cancels
`S` completely: `(S/R₁)/(S/R₂) = R₂/R₁`.  This is the algebraic heart of the
relative-error transfer; it is independent of any physics in `S`. -/
theorem saha_ratio_cancel {S R₁ R₂ : ℝ} (hS : S ≠ 0) (hR₁ : R₁ ≠ 0) (hR₂ : R₂ ≠ 0) :
    (S / R₁) / (S / R₂) = R₂ / R₁ := by
  field_simp

/-- **EXACT relative-error transfer for `n_e`.** At fixed temperature (hence fixed
Saha factor `S = sahaFactor … > 0`), the ratio of two inferred electron densities
is the inverse ratio of the stage ratios that produced them:
`n_e(R₁)/n_e(R₂) = R₂/R₁`.  Equivalently, in logarithms,
`ln n_e(R₁) − ln n_e(R₂) = −(ln R₁ − ln R₂)`: the diagnostic's log-derivative is
exactly `−1`, so a relative stage-ratio measurement error maps one-to-one (unit
gain, inverted sign) onto the relative error of `n_e`.  Positivity of the physical
constants/weights is load-bearing only through `S ≠ 0` (via `sahaFactor_pos`); the
identity is otherwise pure algebra. -/
theorem electronDensity_relativeError [Nonempty ι] [Nonempty κ]
    {kB T me h chi : ℝ} {gZ EZ : ι → ℝ} {gZ1 EZ1 : κ → ℝ} {R₁ R₂ : ℝ}
    (hkB : 0 < kB) (hT : 0 < T) (hme : 0 < me) (hh : 0 < h)
    (hgZ : ∀ k, 0 < gZ k) (hgZ1 : ∀ k, 0 < gZ1 k)
    (hR₁ : 0 < R₁) (hR₂ : 0 < R₂) :
    electronDensityFromRatio kB T me h chi gZ EZ gZ1 EZ1 R₁
        / electronDensityFromRatio kB T me h chi gZ EZ gZ1 EZ1 R₂
      = R₂ / R₁ := by
  have hS : 0 < sahaFactor kB T me h chi gZ EZ gZ1 EZ1 :=
    sahaFactor_pos hkB hT hme hh hgZ hgZ1
  unfold electronDensityFromRatio
  exact saha_ratio_cancel hS.ne' hR₁.ne' hR₂.ne'

/-- **Lipschitz core (PURE-MATH).** On the ray `R ≥ R₀ > 0`, the map `R ↦ S/R`
(with `S > 0`) is Lipschitz with the explicit constant `S/R₀²`:
`|S/R₁ − S/R₂| ≤ (S/R₀²)·|R₁ − R₂|`.  Proof: the exact difference is
`S·(R₂ − R₁)/(R₁ R₂)`; taking absolute values and using `R₀² ≤ R₁ R₂` (both ratios
are at least `R₀`) replaces the denominator `R₁ R₂` by the worst case `R₀²`.  This
is the standard `|f(x) − f(y)| ≤ (sup|f′|)·|x − y|` estimate made elementary and
asymptotics-free for `f(R) = S/R`, whose derivative magnitude `S/R²` is maximized
at the smallest admissible `R = R₀`. -/
theorem saha_inv_lipschitz {S R₀ R₁ R₂ : ℝ}
    (hS : 0 < S) (hR₀ : 0 < R₀) (hR₁ : R₀ ≤ R₁) (hR₂ : R₀ ≤ R₂) :
    |S / R₁ - S / R₂| ≤ (S / R₀ ^ 2) * |R₁ - R₂| := by
  have hR₁pos : 0 < R₁ := hR₀.trans_le hR₁
  have hR₂pos : 0 < R₂ := hR₀.trans_le hR₂
  have hprod : 0 < R₁ * R₂ := mul_pos hR₁pos hR₂pos
  have hR0sq : 0 < R₀ ^ 2 := pow_pos hR₀ 2
  have hR₁ne : R₁ ≠ 0 := hR₁pos.ne'
  have hR₂ne : R₂ ≠ 0 := hR₂pos.ne'
  have hnum : 0 ≤ S * |R₁ - R₂| := mul_nonneg hS.le (abs_nonneg _)
  have hR0sqle : R₀ ^ 2 ≤ R₁ * R₂ := by
    rw [pow_two]
    exact mul_le_mul hR₁ hR₂ hR₀.le hR₁pos.le
  have key : S / R₁ - S / R₂ = S * (R₂ - R₁) / (R₁ * R₂) := by
    field_simp
  rw [key, abs_div, abs_of_pos hprod, abs_mul, abs_of_pos hS, abs_sub_comm R₂ R₁,
    div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_left hnum hR0sq hR0sqle

/-- **EXACT sensitivity bound for the `n_e` diagnostic.** For stage ratios
`R₁, R₂ ≥ R₀ > 0` and fixed temperature, the inferred electron densities obey the
explicit Lipschitz estimate `|n_e(R₁) − n_e(R₂)| ≤ (S/R₀²)·|R₁ − R₂|`, with
`S = sahaFactor …`.  The constant `S/R₀²` is exactly `|d n_e/dR|` at the worst-case
(smallest) ratio `R₀`; it is the sensitivity coefficient the runtime multiplies a
stage-ratio error bar by to obtain an `n_e` error budget.  Rests on `S > 0`
(`sahaFactor_pos`) and the pure-analysis core `saha_inv_lipschitz`. -/
theorem electronDensity_lipschitz [Nonempty ι] [Nonempty κ]
    {kB T me h chi : ℝ} {gZ EZ : ι → ℝ} {gZ1 EZ1 : κ → ℝ} {R₀ R₁ R₂ : ℝ}
    (hkB : 0 < kB) (hT : 0 < T) (hme : 0 < me) (hh : 0 < h)
    (hgZ : ∀ k, 0 < gZ k) (hgZ1 : ∀ k, 0 < gZ1 k)
    (hR₀ : 0 < R₀) (hR₁ : R₀ ≤ R₁) (hR₂ : R₀ ≤ R₂) :
    |electronDensityFromRatio kB T me h chi gZ EZ gZ1 EZ1 R₁
        - electronDensityFromRatio kB T me h chi gZ EZ gZ1 EZ1 R₂|
      ≤ (sahaFactor kB T me h chi gZ EZ gZ1 EZ1 / R₀ ^ 2) * |R₁ - R₂| := by
  have hS : 0 < sahaFactor kB T me h chi gZ EZ gZ1 EZ1 :=
    sahaFactor_pos hkB hT hme hh hgZ hgZ1
  unfold electronDensityFromRatio
  exact saha_inv_lipschitz hS hR₀ hR₁ hR₂

/-! ### Non-vacuity witnesses

The two physics theorems are non-vacuous: their hypotheses are simultaneously
satisfiable, and the identified quantities are *specific, non-trivial* values on a
genuinely varying diagnostic (not a constant map, not the degenerate `R₁ = R₂`). -/

private def nvSstG : Fin 1 → ℝ := fun _ => 1
private def nvSstE : Fin 1 → ℝ := fun _ => 0

/-- Non-vacuity for `electronDensity_relativeError`: with unit atomic data and
`R₁ = 1`, `R₂ = 2`, the density ratio is the specific non-trivial value
`R₂/R₁ = 2` (halving the stage ratio doubles the inferred `n_e`).  A ratio of `2`,
not `1`, certifies that the transfer is real content on a non-constant diagnostic:
had the Saha factor been `0` the map would be constantly `0` and the quotient would
degenerate. -/
example :
    electronDensityFromRatio 1 1 1 1 0 nvSstG nvSstE nvSstG nvSstE 1
        / electronDensityFromRatio 1 1 1 1 0 nvSstG nvSstE nvSstG nvSstE 2
      = 2 := by
  have h := electronDensity_relativeError (ι := Fin 1) (κ := Fin 1)
    (kB := 1) (T := 1) (me := 1) (h := 1) (chi := 0)
    (gZ := nvSstG) (EZ := nvSstE) (gZ1 := nvSstG) (EZ1 := nvSstE) (R₁ := 1) (R₂ := 2)
    one_pos one_pos one_pos one_pos (fun _ => one_pos) (fun _ => one_pos) one_pos two_pos
  rw [h]; norm_num

/-- Non-vacuity for `saha_inv_lipschitz` (hence `electronDensity_lipschitz`): with
`S = 2`, `R₀ = 1`, `R₁ = 1`, `R₂ = 2` the bound reads `1 ≤ 2` — a genuine, finite,
non-vacuous constraint (both sides positive), applied to a diagnostic that really
varies (`S/R₁ = 2 ≠ 1 = S/R₂`). -/
example : |(2 : ℝ) / 1 - 2 / 2| ≤ (2 / (1 : ℝ) ^ 2) * |(1 : ℝ) - 2| :=
  saha_inv_lipschitz (by norm_num) (by norm_num) (le_refl 1) (by norm_num)

/-- The Lipschitz witness constrains a genuinely non-constant quantity with a
strictly positive left-hand side: the diagnostic value moves (`2/1 ≠ 2/2`) and the
bounded deviation is nonzero, so the inequality is not the trivial `0 ≤ 0`. -/
example : (0 : ℝ) < |(2 : ℝ) / 1 - 2 / 2| ∧ (2 : ℝ) / 1 ≠ 2 / 2 := by
  norm_num

/-! ### T-channel two-sided sensitivity of the Saha factor (gap #3, T-channel reframed)

Monotonicity of `sahaFactor` in `T` is genuinely unavailable (the partition ratio
`U_{z+1}/U_z` can run either way, see the scope note above).  But the runtime error
budget only needs a *sign-free* two-point Lipschitz bound.  We build it channelwise on a
box `[Tmin, Tmax]` (`0 < Tmin ≤ T₁, T₂ ≤ Tmax`): a two-point bound for each factor of
`sahaFactor` — the thermal bracket `(2π m_e k_B T/h²)^{3/2}`, the partition ratio
`U_{z+1}(T)/U_z(T)`, and `exp(−χ/(k_B T))` — then assemble via a three-factor product
estimate.  All constants are explicit but deliberately **not** sharp (the box floor/ceil
over-estimate each sup, exactly as in `PartitionLipschitz`). -/

/-- **Two-point bound for `Real.sqrt` on a positive floor (PURE-MATH).** For
`0 < xmin ≤ x, y`, `|√x − √y| ≤ |x − y|/(2·√xmin)`, since `(√x − √y)(√x + √y) = x − y`
and `√x + √y ≥ 2·√xmin > 0`. Private helper. -/
private lemma abs_sqrt_sub_le {xmin x y : ℝ}
    (hxmin : 0 < xmin) (hx : xmin ≤ x) (hy : xmin ≤ y) :
    |Real.sqrt x - Real.sqrt y| ≤ |x - y| / (2 * Real.sqrt xmin) := by
  have hx0 : 0 ≤ x := hxmin.le.trans hx
  have hy0 : 0 ≤ y := hxmin.le.trans hy
  have hsxmin : 0 < Real.sqrt xmin := Real.sqrt_pos.mpr hxmin
  have hsx : Real.sqrt xmin ≤ Real.sqrt x := Real.sqrt_le_sqrt hx
  have hsy : Real.sqrt xmin ≤ Real.sqrt y := Real.sqrt_le_sqrt hy
  have hsum : 2 * Real.sqrt xmin ≤ Real.sqrt x + Real.sqrt y := by linarith
  have hsumpos : 0 < Real.sqrt x + Real.sqrt y := by linarith
  have hid : Real.sqrt x - Real.sqrt y = (x - y) / (Real.sqrt x + Real.sqrt y) := by
    rw [eq_div_iff hsumpos.ne']
    have h1 : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0
    have h2 : Real.sqrt y * Real.sqrt y = y := Real.mul_self_sqrt hy0
    linear_combination h1 - h2
  rw [hid, abs_div, abs_of_pos hsumpos]
  exact div_le_div_of_nonneg_left (abs_nonneg _) (by linarith) hsum

/-- **`x^{3/2} = x·√x` for `x > 0` (PURE-MATH).** Private helper unfolding the `rpow`
exponent used by the thermal bracket. -/
private lemma rpow_three_halves {x : ℝ} (hx : 0 < x) :
    x ^ (3 / 2 : ℝ) = x * Real.sqrt x := by
  have h : x * Real.sqrt x = x ^ (1 : ℝ) * x ^ (1 / 2 : ℝ) := by
    rw [Real.rpow_one, Real.sqrt_eq_rpow]
  rw [h, ← Real.rpow_add hx]
  norm_num

/-- **Two-point bound for `x^{3/2}` on a box (PURE-MATH).** For `0 < xmin ≤ x, y ≤ xmax`,
`|x^{3/2} − y^{3/2}| ≤ (√xmax + xmax/(2·√xmin))·|x − y|`, via the split
`x·√x − y·√y = √x·(x − y) + y·(√x − √y)` and `abs_sqrt_sub_le`. Constant not sharp.
Private helper. -/
private lemma rpow_three_halves_two_point {xmin xmax x y : ℝ}
    (hxmin : 0 < xmin) (hx : xmin ≤ x) (hy : xmin ≤ y) (hxM : x ≤ xmax) (hyM : y ≤ xmax) :
    |x ^ (3 / 2 : ℝ) - y ^ (3 / 2 : ℝ)|
      ≤ (Real.sqrt xmax + xmax / (2 * Real.sqrt xmin)) * |x - y| := by
  have hx0 : 0 < x := hxmin.trans_le hx
  have hy0 : 0 < y := hxmin.trans_le hy
  rw [rpow_three_halves hx0, rpow_three_halves hy0]
  have hdecomp : x * Real.sqrt x - y * Real.sqrt y
      = Real.sqrt x * (x - y) + y * (Real.sqrt x - Real.sqrt y) := by ring
  rw [hdecomp]
  refine (abs_add_le _ _).trans ?_
  have h1 : |Real.sqrt x * (x - y)| ≤ Real.sqrt xmax * |x - y| := by
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg x)]
    exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hxM) (abs_nonneg _)
  have h2 : |y * (Real.sqrt x - Real.sqrt y)| ≤ xmax / (2 * Real.sqrt xmin) * |x - y| := by
    rw [abs_mul, abs_of_nonneg hy0.le]
    calc y * |Real.sqrt x - Real.sqrt y|
        ≤ xmax * (|x - y| / (2 * Real.sqrt xmin)) :=
          mul_le_mul hyM (abs_sqrt_sub_le hxmin hx hy) (abs_nonneg _) (hy0.le.trans hyM)
      _ = xmax / (2 * Real.sqrt xmin) * |x - y| := by ring
  calc |Real.sqrt x * (x - y)| + |y * (Real.sqrt x - Real.sqrt y)|
      ≤ Real.sqrt xmax * |x - y| + xmax / (2 * Real.sqrt xmin) * |x - y| := add_le_add h1 h2
    _ = (Real.sqrt xmax + xmax / (2 * Real.sqrt xmin)) * |x - y| := by ring

/-- **Exponential channel two-point bound (PURE-MATH).** For `χ ≥ 0` and a temperature
floor `Tmin ≤ T₁, T₂` (`0 < Tmin`, `0 < k_B`),
`|exp(−χ/(k_B T₁)) − exp(−χ/(k_B T₂))| ≤ χ/(k_B·Tmin²)·|T₁ − T₂|`.  Both exponents are
`≤ 0`, so the two-point exponential constant `max(…) ≤ 1`; the remaining factor `χ`
pulls out and the inverse-temperature gap bound closes it. Private helper. -/
private lemma exp_channel_bound {kB Tmin T1 T2 chi : ℝ}
    (hkB : 0 < kB) (hTmin : 0 < Tmin) (hT1 : Tmin ≤ T1) (hT2 : Tmin ≤ T2) (hchi : 0 ≤ chi) :
    |Real.exp (-chi / (kB * T1)) - Real.exp (-chi / (kB * T2))|
      ≤ chi / (kB * Tmin ^ 2) * |T1 - T2| := by
  have hT1pos : 0 < T1 := hTmin.trans_le hT1
  have hT2pos : 0 < T2 := hTmin.trans_le hT2
  set a := -chi / (kB * T1) with ha
  set b := -chi / (kB * T2) with hb
  have hale : a ≤ 0 := by
    rw [ha, neg_div]; exact neg_nonpos.mpr (div_nonneg hchi (mul_pos hkB hT1pos).le)
  have hble : b ≤ 0 := by
    rw [hb, neg_div]; exact neg_nonpos.mpr (div_nonneg hchi (mul_pos hkB hT2pos).le)
  have hexpa : Real.exp a ≤ 1 := by rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr hale
  have hexpb : Real.exp b ≤ 1 := by rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr hble
  have hmax : max (Real.exp a) (Real.exp b) ≤ 1 := max_le hexpa hexpb
  have habeq : a - b = -(chi * (1 / (kB * T1) - 1 / (kB * T2))) := by rw [ha, hb]; ring
  have habs : |a - b| = chi * |1 / (kB * T1) - 1 / (kB * T2)| := by
    rw [habeq, abs_neg, abs_mul, abs_of_nonneg hchi]
  have hinv := inv_kT_sub_le hkB hTmin hT1 hT2
  calc |Real.exp a - Real.exp b|
      ≤ max (Real.exp a) (Real.exp b) * |a - b| := abs_exp_sub_le a b
    _ ≤ 1 * |a - b| := mul_le_mul_of_nonneg_right hmax (abs_nonneg _)
    _ = |a - b| := one_mul _
    _ = chi * |1 / (kB * T1) - 1 / (kB * T2)| := habs
    _ ≤ chi * (|T1 - T2| / (kB * Tmin ^ 2)) := mul_le_mul_of_nonneg_left hinv hchi
    _ = chi / (kB * Tmin ^ 2) * |T1 - T2| := by ring

/-- **Monotonicity of the thermal bracket (PURE-MATH).** `thermalBracket kB · me h` is
increasing (it is `(2π m_e k_B/h²)·T`). Private helper. -/
private lemma thermalBracket_mono {kB me h Ta Tb : ℝ}
    (hkB : 0 < kB) (hme : 0 < me) (hh : 0 < h) (hab : Ta ≤ Tb) :
    thermalBracket kB Ta me h ≤ thermalBracket kB Tb me h := by
  have hcoef : 0 < 2 * Real.pi * me * kB / h ^ 2 := div_pos (by positivity) (pow_pos hh 2)
  have hdiff : thermalBracket kB Tb me h - thermalBracket kB Ta me h
      = (2 * Real.pi * me * kB / h ^ 2) * (Tb - Ta) := by unfold thermalBracket; ring
  nlinarith [mul_nonneg hcoef.le (sub_nonneg.mpr hab)]

/-- **Thermal-bracket channel two-point bound (PURE-MATH).** On the box `[Tmin, Tmax]`
(`0 < Tmin ≤ T₁, T₂ ≤ Tmax`), the `T^{3/2}`-shaped thermal factor obeys
`|B(T₁)^{3/2} − B(T₂)^{3/2}| ≤ C_B·|T₁ − T₂|` with the explicit (non-sharp) constant
`C_B = (√B(Tmax) + B(Tmax)/(2√B(Tmin)))·(2π m_e k_B/h²)`, `B = thermalBracket`.  Combines
`rpow_three_halves_two_point` with the linearity `B(T₁) − B(T₂) = (2π m_e k_B/h²)(T₁−T₂)`.
Private helper. -/
private lemma thermal_channel_bound {kB Tmin Tmax T1 T2 me h : ℝ}
    (hkB : 0 < kB) (hme : 0 < me) (hh : 0 < h)
    (hTmin : 0 < Tmin) (hT1 : Tmin ≤ T1) (hT2 : Tmin ≤ T2)
    (hT1M : T1 ≤ Tmax) (hT2M : T2 ≤ Tmax) :
    |(thermalBracket kB T1 me h) ^ (3 / 2 : ℝ) - (thermalBracket kB T2 me h) ^ (3 / 2 : ℝ)|
      ≤ (Real.sqrt (thermalBracket kB Tmax me h)
          + thermalBracket kB Tmax me h / (2 * Real.sqrt (thermalBracket kB Tmin me h)))
          * (2 * Real.pi * me * kB / h ^ 2) * |T1 - T2| := by
  have hcoef : 0 < 2 * Real.pi * me * kB / h ^ 2 := div_pos (by positivity) (pow_pos hh 2)
  have hxmin : 0 < thermalBracket kB Tmin me h := thermalBracket_pos hkB hTmin hme hh
  have hx1 : thermalBracket kB Tmin me h ≤ thermalBracket kB T1 me h :=
    thermalBracket_mono hkB hme hh hT1
  have hx2 : thermalBracket kB Tmin me h ≤ thermalBracket kB T2 me h :=
    thermalBracket_mono hkB hme hh hT2
  have hx1M : thermalBracket kB T1 me h ≤ thermalBracket kB Tmax me h :=
    thermalBracket_mono hkB hme hh hT1M
  have hx2M : thermalBracket kB T2 me h ≤ thermalBracket kB Tmax me h :=
    thermalBracket_mono hkB hme hh hT2M
  have hrpow := rpow_three_halves_two_point hxmin hx1 hx2 hx1M hx2M
  have hbdiff : |thermalBracket kB T1 me h - thermalBracket kB T2 me h|
      = (2 * Real.pi * me * kB / h ^ 2) * |T1 - T2| := by
    have hlin : thermalBracket kB T1 me h - thermalBracket kB T2 me h
        = (2 * Real.pi * me * kB / h ^ 2) * (T1 - T2) := by unfold thermalBracket; ring
    rw [hlin, abs_mul, abs_of_pos hcoef]
  calc |(thermalBracket kB T1 me h) ^ (3 / 2 : ℝ) - (thermalBracket kB T2 me h) ^ (3 / 2 : ℝ)|
      ≤ (Real.sqrt (thermalBracket kB Tmax me h)
          + thermalBracket kB Tmax me h / (2 * Real.sqrt (thermalBracket kB Tmin me h)))
          * |thermalBracket kB T1 me h - thermalBracket kB T2 me h| := hrpow
    _ = (Real.sqrt (thermalBracket kB Tmax me h)
          + thermalBracket kB Tmax me h / (2 * Real.sqrt (thermalBracket kB Tmin me h)))
          * (2 * Real.pi * me * kB / h ^ 2) * |T1 - T2| := by rw [hbdiff]; ring

/-- **Partition-function box floor (PURE-MATH).** For `Eₖ ≥ 0`, each Boltzmann factor
`exp(−Eₖ/(k_B T))` is increasing in `T`, so `U(Tmin) ≤ U(T)` for `Tmin ≤ T`.  This gives
a positive lower bound on the denominator partition function valid on the whole box.
Private helper. -/
private lemma partitionFunction_ge_floor {kB Tmin T : ℝ} {g E : ι → ℝ}
    (hkB : 0 < kB) (hTmin : 0 < Tmin) (hT : Tmin ≤ T)
    (hg : ∀ k, 0 < g k) (hE : ∀ k, 0 ≤ E k) :
    partitionFunction kB Tmin g E ≤ partitionFunction kB T g E := by
  unfold partitionFunction
  apply Finset.sum_le_sum
  intro k _
  apply mul_le_mul_of_nonneg_left _ (hg k).le
  unfold boltzmannFactor
  apply Real.exp_le_exp.mpr
  rw [neg_div, neg_div, neg_le_neg_iff]
  exact div_le_div_of_nonneg_left (hE k) (mul_pos hkB hTmin)
    (mul_le_mul_of_nonneg_left hT hkB.le)

/-- **Partition-function ceiling (PURE-MATH).** For `Eₖ ≥ 0`, every Boltzmann factor is
`≤ 1`, so `U(T) ≤ ∑ₖ gₖ`.  Private helper. -/
private lemma partitionFunction_le_sum {kB T : ℝ} {g E : ι → ℝ}
    (hkB : 0 < kB) (hT : 0 < T) (hg : ∀ k, 0 < g k) (hE : ∀ k, 0 ≤ E k) :
    partitionFunction kB T g E ≤ ∑ k, g k := by
  unfold partitionFunction
  apply Finset.sum_le_sum
  intro k _
  unfold boltzmannFactor
  calc g k * Real.exp (-E k / (kB * T))
      ≤ g k * 1 := by
        apply mul_le_mul_of_nonneg_left _ (hg k).le
        rw [Real.exp_le_one_iff, neg_div]
        exact neg_nonpos.mpr (div_nonneg (hE k) (mul_pos hkB hT).le)
    _ = g k := mul_one _

/-- **Quotient two-point bound (PURE-MATH).** With denominators on a positive floor
`0 < bfloor ≤ b₁, b₂` and a numerator ceiling `|a₂| ≤ A`,
`|a₁/b₁ − a₂/b₂| ≤ |a₁ − a₂|/bfloor + A·|b₁ − b₂|/bfloor²`, via the split
`a₁/b₁ − a₂/b₂ = (a₁ − a₂)/b₁ + a₂·(b₂ − b₁)/(b₁ b₂)`. Private helper. -/
private lemma div_two_point_bound {a1 a2 b1 b2 A bfloor : ℝ}
    (hbfloor : 0 < bfloor) (hb1 : bfloor ≤ b1) (hb2 : bfloor ≤ b2) (ha2 : |a2| ≤ A) :
    |a1 / b1 - a2 / b2| ≤ |a1 - a2| / bfloor + A * |b1 - b2| / bfloor ^ 2 := by
  have hb1pos : 0 < b1 := hbfloor.trans_le hb1
  have hb2pos : 0 < b2 := hbfloor.trans_le hb2
  have hA : 0 ≤ A := (abs_nonneg _).trans ha2
  have key : a1 / b1 - a2 / b2 = (a1 - a2) / b1 + a2 * (b2 - b1) / (b1 * b2) := by
    field_simp; ring
  rw [key]
  refine (abs_add_le _ _).trans ?_
  have h1 : |(a1 - a2) / b1| ≤ |a1 - a2| / bfloor := by
    rw [abs_div, abs_of_pos hb1pos]
    exact div_le_div_of_nonneg_left (abs_nonneg _) hbfloor hb1
  have h2 : |a2 * (b2 - b1) / (b1 * b2)| ≤ A * |b1 - b2| / bfloor ^ 2 := by
    rw [abs_div, abs_mul, abs_of_pos (mul_pos hb1pos hb2pos), abs_sub_comm b2 b1]
    have hbsq : bfloor ^ 2 ≤ b1 * b2 := by
      rw [sq]; exact mul_le_mul hb1 hb2 hbfloor.le hb1pos.le
    exact div_le_div₀ (mul_nonneg hA (abs_nonneg _))
      (mul_le_mul_of_nonneg_right ha2 (abs_nonneg _)) (pow_pos hbfloor 2) hbsq
  exact add_le_add h1 h2

/-- **Partition-ratio channel two-point bound (PURE-MATH).** On the box `[Tmin, Tmax]`,
the stage ratio `U_{z+1}(T)/U_z(T)` obeys `|ratio(T₁) − ratio(T₂)| ≤ C_R·|T₁ − T₂|` with
the explicit (non-sharp) constant
`C_R = L_num/U_z(Tmin) + (∑ g_{z+1})·L_den/U_z(Tmin)²`, where
`L_num = (∑ g_{z+1}E_{z+1})/(k_B Tmin²)`, `L_den = (∑ g_z E_z)/(k_B Tmin²)`.  Reuses
`partitionFunction_lipschitz_temp` (numerator + denominator), the floor
`partitionFunction_ge_floor`, and the ceiling `partitionFunction_le_sum`. Private
helper. -/
private lemma partition_ratio_channel_bound [Nonempty ι] [Nonempty κ]
    {kB Tmin T1 T2 : ℝ} {gZ EZ : ι → ℝ} {gZ1 EZ1 : κ → ℝ}
    (hkB : 0 < kB) (hTmin : 0 < Tmin) (hT1 : Tmin ≤ T1) (hT2 : Tmin ≤ T2)
    (hgZ : ∀ k, 0 < gZ k) (hEZ : ∀ k, 0 ≤ EZ k)
    (hgZ1 : ∀ k, 0 < gZ1 k) (hEZ1 : ∀ k, 0 ≤ EZ1 k) :
    |partitionFunction kB T1 gZ1 EZ1 / partitionFunction kB T1 gZ EZ
        - partitionFunction kB T2 gZ1 EZ1 / partitionFunction kB T2 gZ EZ|
      ≤ ((∑ k, gZ1 k * EZ1 k) / (kB * Tmin ^ 2) / partitionFunction kB Tmin gZ EZ
          + (∑ k, gZ1 k) * ((∑ k, gZ k * EZ k) / (kB * Tmin ^ 2))
              / partitionFunction kB Tmin gZ EZ ^ 2) * |T1 - T2| := by
  have hT1pos : 0 < T1 := hTmin.trans_le hT1
  have hT2pos : 0 < T2 := hTmin.trans_le hT2
  have hbfpos : 0 < partitionFunction kB Tmin gZ EZ := partitionFunction_pos hgZ
  have hsum1 : 0 ≤ ∑ k, gZ1 k := Finset.sum_nonneg fun k _ => (hgZ1 k).le
  have hceil : |partitionFunction kB T2 gZ1 EZ1| ≤ ∑ k, gZ1 k := by
    rw [abs_of_pos (partitionFunction_pos hgZ1)]
    exact partitionFunction_le_sum hkB hT2pos hgZ1 hEZ1
  have hdiv := div_two_point_bound (a1 := partitionFunction kB T1 gZ1 EZ1) hbfpos
    (partitionFunction_ge_floor hkB hTmin hT1 hgZ hEZ)
    (partitionFunction_ge_floor hkB hTmin hT2 hgZ hEZ) hceil
  have hnum : |partitionFunction kB T1 gZ1 EZ1 - partitionFunction kB T2 gZ1 EZ1|
      ≤ (∑ k, gZ1 k * EZ1 k) / (kB * Tmin ^ 2) * |T1 - T2| :=
    partitionFunction_lipschitz_temp hkB hTmin hT1 hT2 hgZ1 hEZ1
  have hden : |partitionFunction kB T1 gZ EZ - partitionFunction kB T2 gZ EZ|
      ≤ (∑ k, gZ k * EZ k) / (kB * Tmin ^ 2) * |T1 - T2| :=
    partitionFunction_lipschitz_temp hkB hTmin hT1 hT2 hgZ hEZ
  calc |partitionFunction kB T1 gZ1 EZ1 / partitionFunction kB T1 gZ EZ
          - partitionFunction kB T2 gZ1 EZ1 / partitionFunction kB T2 gZ EZ|
      ≤ |partitionFunction kB T1 gZ1 EZ1 - partitionFunction kB T2 gZ1 EZ1|
            / partitionFunction kB Tmin gZ EZ
          + (∑ k, gZ1 k)
              * |partitionFunction kB T1 gZ EZ - partitionFunction kB T2 gZ EZ|
              / partitionFunction kB Tmin gZ EZ ^ 2 := hdiv
    _ ≤ (∑ k, gZ1 k * EZ1 k) / (kB * Tmin ^ 2) * |T1 - T2|
            / partitionFunction kB Tmin gZ EZ
          + (∑ k, gZ1 k) * ((∑ k, gZ k * EZ k) / (kB * Tmin ^ 2) * |T1 - T2|)
              / partitionFunction kB Tmin gZ EZ ^ 2 := by
        apply add_le_add
        · exact div_le_div_of_nonneg_right hnum hbfpos.le
        · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hden hsum1)
            (pow_pos hbfpos 2).le
    _ = ((∑ k, gZ1 k * EZ1 k) / (kB * Tmin ^ 2) / partitionFunction kB Tmin gZ EZ
          + (∑ k, gZ1 k) * ((∑ k, gZ k * EZ k) / (kB * Tmin ^ 2))
              / partitionFunction kB Tmin gZ EZ ^ 2) * |T1 - T2| := by ring

/-- **Two-factor two-point bound (PURE-MATH).** `|a₁b₁ − a₂b₂| ≤ Kₐ·|b₁ − b₂| + K_b·|a₁ − a₂|`
from the split `a₁b₁ − a₂b₂ = a₁(b₁ − b₂) + b₂(a₁ − a₂)` and sup bounds `|a₁| ≤ Kₐ`,
`|b₂| ≤ K_b`. Private helper. -/
private lemma mul_two_point_bound {a1 a2 b1 b2 Ka Kb : ℝ}
    (ha1 : |a1| ≤ Ka) (hb2 : |b2| ≤ Kb) :
    |a1 * b1 - a2 * b2| ≤ Ka * |b1 - b2| + Kb * |a1 - a2| := by
  have hdecomp : a1 * b1 - a2 * b2 = a1 * (b1 - b2) + b2 * (a1 - a2) := by ring
  rw [hdecomp]
  refine (abs_add_le _ _).trans ?_
  have h1 : |a1 * (b1 - b2)| ≤ Ka * |b1 - b2| := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_right ha1 (abs_nonneg _)
  have h2 : |b2 * (a1 - a2)| ≤ Kb * |a1 - a2| := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_right hb2 (abs_nonneg _)
  exact add_le_add h1 h2

/-- **Three-factor two-point bound (PURE-MATH).** Grouping `(a·b)·c`,
`|a₁b₁c₁ − a₂b₂c₂| ≤ Kₐ·K_b·|c₁ − c₂| + K_c·(Kₐ·|b₁ − b₂| + K_b·|a₁ − a₂|)` from the
sup bounds `|a₁| ≤ Kₐ`, `|b₁|,|b₂| ≤ K_b`, `|c₂| ≤ K_c` (with `Kₐ, K_c ≥ 0`). Private
helper. -/
private lemma mul3_two_point_bound {a1 a2 b1 b2 c1 c2 Ka Kb Kc : ℝ}
    (ha1 : |a1| ≤ Ka) (hb1 : |b1| ≤ Kb) (hb2 : |b2| ≤ Kb) (hc2 : |c2| ≤ Kc)
    (hKa : 0 ≤ Ka) (hKc : 0 ≤ Kc) :
    |a1 * b1 * c1 - a2 * b2 * c2|
      ≤ Ka * Kb * |c1 - c2| + Kc * (Ka * |b1 - b2| + Kb * |a1 - a2|) := by
  have hab1 : |a1 * b1| ≤ Ka * Kb := by
    rw [abs_mul]; exact mul_le_mul ha1 hb1 (abs_nonneg _) hKa
  have step := mul_two_point_bound (a1 := a1 * b1) (a2 := a2 * b2) (b1 := c1) (b2 := c2)
    hab1 hc2
  have hinner := mul_two_point_bound (a1 := a1) (a2 := a2) (b1 := b1) (b2 := b2) ha1 hb2
  calc |a1 * b1 * c1 - a2 * b2 * c2|
      ≤ Ka * Kb * |c1 - c2| + Kc * |a1 * b1 - a2 * b2| := step
    _ ≤ Ka * Kb * |c1 - c2| + Kc * (Ka * |b1 - b2| + Kb * |a1 - a2|) := by
        linarith [mul_le_mul_of_nonneg_left hinner hKc]

/-- **Explicit `T`-Lipschitz constant for `sahaFactor` on a box `[Tmin, Tmax]`**
(`REDUCED`, Saha–Eggert (Griem)).  Assembled from the three channelwise two-point
constants and box sups: the partition-ratio sup `Kₐ = (∑ g_{z+1})/U_z(Tmin)`, the thermal
sup `K_b = B(Tmax)^{3/2}` (`B = thermalBracket`), the exponential-channel slope
`L_c = χ/(k_B Tmin²)`, the thermal-channel slope
`L_b = (√B(Tmax) + B(Tmax)/(2√B(Tmin)))·(2π m_e k_B/h²)`, and the ratio-channel slope
`L_a = L_num/U_z(Tmin) + (∑ g_{z+1})·L_den/U_z(Tmin)²`.  The three-factor product estimate
gives `L_S = 2·(Kₐ·K_b·L_c + (Kₐ·L_b + K_b·L_a))`.  Every factor is an explicit,
deliberately non-sharp box bound (floor/ceiling over-estimates, not tight suprema). -/
noncomputable def sahaFactorLipConst (kB Tmin Tmax me h chi : ℝ)
    (gZ EZ : ι → ℝ) (gZ1 EZ1 : κ → ℝ) : ℝ :=
  2 * ((∑ k, gZ1 k) / partitionFunction kB Tmin gZ EZ
        * thermalBracket kB Tmax me h ^ (3 / 2 : ℝ)
        * (chi / (kB * Tmin ^ 2))
      + ((∑ k, gZ1 k) / partitionFunction kB Tmin gZ EZ
            * ((Real.sqrt (thermalBracket kB Tmax me h)
                + thermalBracket kB Tmax me h / (2 * Real.sqrt (thermalBracket kB Tmin me h)))
              * (2 * Real.pi * me * kB / h ^ 2))
          + thermalBracket kB Tmax me h ^ (3 / 2 : ℝ)
            * ((∑ k, gZ1 k * EZ1 k) / (kB * Tmin ^ 2) / partitionFunction kB Tmin gZ EZ
                + (∑ k, gZ1 k) * ((∑ k, gZ k * EZ k) / (kB * Tmin ^ 2))
                    / partitionFunction kB Tmin gZ EZ ^ 2)))

/-- **Saha-factor `T`-Lipschitz (two-sided sensitivity) bound** (`REDUCED`,
Saha–Eggert (Griem)).  On a temperature box `[Tmin, Tmax]` (`0 < Tmin ≤ T₁, T₂ ≤ Tmax`),
with positive constants/degeneracies, non-negative level energies and `χ ≥ 0`, the Saha
factor is Lipschitz in `T`:

`|S(T₁) − S(T₂)| ≤ sahaFactorLipConst … · |T₁ − T₂|`.

This is the *sign-free* form of the T-channel: no monotonicity of `S` is claimed (the
partition ratio `U_{z+1}/U_z` can run either way — see the scope note), only the two-point
sensitivity the runtime error budget needs.  Proved channelwise — a two-point bound for
each factor of `sahaFactor` (thermal bracket, partition ratio, exponential) — assembled by
`mul3_two_point_bound`.  `REDUCED` (not `EXACT`): the constant lumps three channel
over-estimates (box floor/ceiling for each sup, plus each channel's own reduction as in
`PartitionLipschitz` / the thermal `√` split); the forward model `sahaFactor` is exact. -/
theorem sahaFactor_lipschitz_temp [Nonempty ι] [Nonempty κ]
    {kB Tmin Tmax me h chi : ℝ} {gZ EZ : ι → ℝ} {gZ1 EZ1 : κ → ℝ} {T1 T2 : ℝ}
    (hkB : 0 < kB) (hme : 0 < me) (hh : 0 < h) (hchi : 0 ≤ chi)
    (hTmin : 0 < Tmin) (hT1 : Tmin ≤ T1) (hT2 : Tmin ≤ T2) (hT1M : T1 ≤ Tmax) (hT2M : T2 ≤ Tmax)
    (hgZ : ∀ k, 0 < gZ k) (hEZ : ∀ k, 0 ≤ EZ k)
    (hgZ1 : ∀ k, 0 < gZ1 k) (hEZ1 : ∀ k, 0 ≤ EZ1 k) :
    |sahaFactor kB T1 me h chi gZ EZ gZ1 EZ1 - sahaFactor kB T2 me h chi gZ EZ gZ1 EZ1|
      ≤ sahaFactorLipConst kB Tmin Tmax me h chi gZ EZ gZ1 EZ1 * |T1 - T2| := by
  have hT1pos : 0 < T1 := hTmin.trans_le hT1
  have hT2pos : 0 < T2 := hTmin.trans_le hT2
  have hTmaxpos : 0 < Tmax := hT1pos.trans_le hT1M
  have hbfpos : 0 < partitionFunction kB Tmin gZ EZ := partitionFunction_pos hgZ
  have hsum1 : 0 ≤ ∑ k, gZ1 k := Finset.sum_nonneg fun k _ => (hgZ1 k).le
  have hKa0 : 0 ≤ (∑ k, gZ1 k) / partitionFunction kB Tmin gZ EZ := div_nonneg hsum1 hbfpos.le
  have hKb0 : 0 ≤ thermalBracket kB Tmax me h ^ (3 / 2 : ℝ) :=
    Real.rpow_nonneg (thermalBracket_pos hkB hTmaxpos hme hh).le _
  have h_ra1 : |partitionFunction kB T1 gZ1 EZ1 / partitionFunction kB T1 gZ EZ|
      ≤ (∑ k, gZ1 k) / partitionFunction kB Tmin gZ EZ := by
    rw [abs_of_pos (div_pos (partitionFunction_pos hgZ1) (partitionFunction_pos hgZ))]
    exact div_le_div₀ hsum1 (partitionFunction_le_sum hkB hT1pos hgZ1 hEZ1) hbfpos
      (partitionFunction_ge_floor hkB hTmin hT1 hgZ hEZ)
  have h_tb1 : |thermalBracket kB T1 me h ^ (3 / 2 : ℝ)|
      ≤ thermalBracket kB Tmax me h ^ (3 / 2 : ℝ) := by
    rw [abs_of_nonneg (Real.rpow_nonneg (thermalBracket_pos hkB hT1pos hme hh).le _)]
    exact Real.rpow_le_rpow (thermalBracket_pos hkB hT1pos hme hh).le
      (thermalBracket_mono hkB hme hh hT1M) (by norm_num)
  have h_tb2 : |thermalBracket kB T2 me h ^ (3 / 2 : ℝ)|
      ≤ thermalBracket kB Tmax me h ^ (3 / 2 : ℝ) := by
    rw [abs_of_nonneg (Real.rpow_nonneg (thermalBracket_pos hkB hT2pos hme hh).le _)]
    exact Real.rpow_le_rpow (thermalBracket_pos hkB hT2pos hme hh).le
      (thermalBracket_mono hkB hme hh hT2M) (by norm_num)
  have h_ec2 : |Real.exp (-chi / (kB * T2))| ≤ 1 := by
    rw [abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff, neg_div]
    exact neg_nonpos.mpr (div_nonneg hchi (mul_pos hkB hT2pos).le)
  have ha_bound := partition_ratio_channel_bound hkB hTmin hT1 hT2 hgZ hEZ hgZ1 hEZ1
  have hb_bound := thermal_channel_bound hkB hme hh hTmin hT1 hT2 hT1M hT2M
  have hc_bound := exp_channel_bound hkB hTmin hT1 hT2 hchi
  have hmul3 := mul3_two_point_bound
    (a1 := partitionFunction kB T1 gZ1 EZ1 / partitionFunction kB T1 gZ EZ)
    (a2 := partitionFunction kB T2 gZ1 EZ1 / partitionFunction kB T2 gZ EZ)
    (b1 := thermalBracket kB T1 me h ^ (3 / 2 : ℝ))
    (b2 := thermalBracket kB T2 me h ^ (3 / 2 : ℝ))
    (c1 := Real.exp (-chi / (kB * T1))) (c2 := Real.exp (-chi / (kB * T2)))
    h_ra1 h_tb1 h_tb2 h_ec2 hKa0 (by norm_num)
  have hsplit : |sahaFactor kB T1 me h chi gZ EZ gZ1 EZ1
        - sahaFactor kB T2 me h chi gZ EZ gZ1 EZ1|
      = 2 * |partitionFunction kB T1 gZ1 EZ1 / partitionFunction kB T1 gZ EZ
              * thermalBracket kB T1 me h ^ (3 / 2 : ℝ) * Real.exp (-chi / (kB * T1))
            - partitionFunction kB T2 gZ1 EZ1 / partitionFunction kB T2 gZ EZ
              * thermalBracket kB T2 me h ^ (3 / 2 : ℝ) * Real.exp (-chi / (kB * T2))| := by
    rw [show sahaFactor kB T1 me h chi gZ EZ gZ1 EZ1 - sahaFactor kB T2 me h chi gZ EZ gZ1 EZ1
          = 2 * (partitionFunction kB T1 gZ1 EZ1 / partitionFunction kB T1 gZ EZ
                  * thermalBracket kB T1 me h ^ (3 / 2 : ℝ) * Real.exp (-chi / (kB * T1))
                - partitionFunction kB T2 gZ1 EZ1 / partitionFunction kB T2 gZ EZ
                  * thermalBracket kB T2 me h ^ (3 / 2 : ℝ) * Real.exp (-chi / (kB * T2)))
        from by unfold sahaFactor; ring,
      abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  rw [hsplit]
  have h1 := mul_le_mul_of_nonneg_left hc_bound (mul_nonneg hKa0 hKb0)
  have h2 := mul_le_mul_of_nonneg_left hb_bound hKa0
  have h3 := mul_le_mul_of_nonneg_left ha_bound hKb0
  rw [show sahaFactorLipConst kB Tmin Tmax me h chi gZ EZ gZ1 EZ1 * |T1 - T2|
        = 2 * ((∑ k, gZ1 k) / partitionFunction kB Tmin gZ EZ
                * thermalBracket kB Tmax me h ^ (3 / 2 : ℝ)
                * (chi / (kB * Tmin ^ 2) * |T1 - T2|)
              + ((∑ k, gZ1 k) / partitionFunction kB Tmin gZ EZ
                    * ((Real.sqrt (thermalBracket kB Tmax me h)
                        + thermalBracket kB Tmax me h
                          / (2 * Real.sqrt (thermalBracket kB Tmin me h)))
                      * (2 * Real.pi * me * kB / h ^ 2) * |T1 - T2|)
                  + thermalBracket kB Tmax me h ^ (3 / 2 : ℝ)
                    * (((∑ k, gZ1 k * EZ1 k) / (kB * Tmin ^ 2)
                          / partitionFunction kB Tmin gZ EZ
                        + (∑ k, gZ1 k) * ((∑ k, gZ k * EZ k) / (kB * Tmin ^ 2))
                            / partitionFunction kB Tmin gZ EZ ^ 2) * |T1 - T2|)))
      from by unfold sahaFactorLipConst; ring]
  linarith [hmul3, h1, h2, h3]

/-- **Electron-density `T`-sensitivity bound** (`REDUCED`, Saha–Eggert (Griem)).  For a
fixed measured stage ratio `R ≥ R₀ > 0` and temperatures in the box `[Tmin, Tmax]`, the
inferred electron density `n_e = S(T)/R` obeys the two-point Lipschitz estimate

`|n_e(T₁,R) − n_e(T₂,R)| ≤ (sahaFactorLipConst …/R₀)·|T₁ − T₂|`.

Together with `electronDensity_lipschitz` (the `R`-channel constant `S/R₀²`), this closes
the `(δT, δR)` sensitivity budget for `n_e`: a recovered-temperature error and a
stage-ratio error each map to a bounded `n_e` deviation.  Immediate from
`sahaFactor_lipschitz_temp` and `n_e(T,R) = S(T)/R`; the constant is the worst-case
`R = R₀` reciprocal of the Saha-factor Lipschitz constant.  `REDUCED` for the same reason
as the headline (the constant lumps the channel over-estimates). -/
theorem electronDensityFromRatio_lipschitz_temp [Nonempty ι] [Nonempty κ]
    {kB Tmin Tmax me h chi : ℝ} {gZ EZ : ι → ℝ} {gZ1 EZ1 : κ → ℝ} {R0 R T1 T2 : ℝ}
    (hkB : 0 < kB) (hme : 0 < me) (hh : 0 < h) (hchi : 0 ≤ chi)
    (hTmin : 0 < Tmin) (hT1 : Tmin ≤ T1) (hT2 : Tmin ≤ T2) (hT1M : T1 ≤ Tmax) (hT2M : T2 ≤ Tmax)
    (hgZ : ∀ k, 0 < gZ k) (hEZ : ∀ k, 0 ≤ EZ k)
    (hgZ1 : ∀ k, 0 < gZ1 k) (hEZ1 : ∀ k, 0 ≤ EZ1 k)
    (hR0 : 0 < R0) (hR : R0 ≤ R) :
    |electronDensityFromRatio kB T1 me h chi gZ EZ gZ1 EZ1 R
        - electronDensityFromRatio kB T2 me h chi gZ EZ gZ1 EZ1 R|
      ≤ sahaFactorLipConst kB Tmin Tmax me h chi gZ EZ gZ1 EZ1 / R0 * |T1 - T2| := by
  have hRpos : 0 < R := hR0.trans_le hR
  have hS := sahaFactor_lipschitz_temp hkB hme hh hchi hTmin hT1 hT2 hT1M hT2M hgZ hEZ hgZ1 hEZ1
  have hcdt : 0 ≤ sahaFactorLipConst kB Tmin Tmax me h chi gZ EZ gZ1 EZ1 * |T1 - T2| :=
    le_trans (abs_nonneg _) hS
  unfold electronDensityFromRatio
  rw [div_sub_div_same, abs_div, abs_of_pos hRpos]
  calc |sahaFactor kB T1 me h chi gZ EZ gZ1 EZ1 - sahaFactor kB T2 me h chi gZ EZ gZ1 EZ1| / R
      ≤ sahaFactorLipConst kB Tmin Tmax me h chi gZ EZ gZ1 EZ1 * |T1 - T2| / R :=
        div_le_div_of_nonneg_right hS hRpos.le
    _ ≤ sahaFactorLipConst kB Tmin Tmax me h chi gZ EZ gZ1 EZ1 * |T1 - T2| / R0 :=
        div_le_div_of_nonneg_left hcdt hR0 hR
    _ = sahaFactorLipConst kB Tmin Tmax me h chi gZ EZ gZ1 EZ1 / R0 * |T1 - T2| := by ring

/-! ### Non-vacuity witnesses (T-channel)

The `nvStc*` data instantiate the family on `ι = κ = Fin 1` with `k_B = m_e = h = χ = 1`,
`g = 1`, `E = 0`, box `[Tmin, Tmax] = [1, 2]`, and `T₁ = 1`, `T₂ = 2`.  All hypotheses
(`0 < k_B, m_e, h`, `0 ≤ χ`, `0 < Tmin ≤ T₁, T₂ ≤ Tmax`, `0 < gₖ`, `0 ≤ Eₖ`, `0 < R₀ ≤ R`)
are jointly satisfiable, and the Lipschitz constant `sahaFactorLipConst` evaluates to a
genuine strictly positive value — so the headline and corollary bounds are real
constraints, not the vacuous `0 ≤ 0`. -/

private def nvStcG : Fin 1 → ℝ := fun _ => 1
private def nvStcE : Fin 1 → ℝ := fun _ => 0

/-- The Saha-factor `T`-Lipschitz bound applies to concrete box data (all hypotheses met). -/
example :
    |sahaFactor 1 1 1 1 1 nvStcG nvStcE nvStcG nvStcE
        - sahaFactor 1 2 1 1 1 nvStcG nvStcE nvStcG nvStcE|
      ≤ sahaFactorLipConst 1 1 2 1 1 1 nvStcG nvStcE nvStcG nvStcE * |(1 : ℝ) - 2| :=
  sahaFactor_lipschitz_temp (ι := Fin 1) (κ := Fin 1)
    one_pos one_pos one_pos zero_le_one one_pos le_rfl one_le_two one_le_two le_rfl
    (fun _ => by norm_num [nvStcG]) (fun _ => by norm_num [nvStcE])
    (fun _ => by norm_num [nvStcG]) (fun _ => by norm_num [nvStcE])

/-- The electron-density `T`-sensitivity corollary applies with `R₀ = R = 1`. -/
example :
    |electronDensityFromRatio 1 1 1 1 1 nvStcG nvStcE nvStcG nvStcE 1
        - electronDensityFromRatio 1 2 1 1 1 nvStcG nvStcE nvStcG nvStcE 1|
      ≤ sahaFactorLipConst 1 1 2 1 1 1 nvStcG nvStcE nvStcG nvStcE / 1 * |(1 : ℝ) - 2| :=
  electronDensityFromRatio_lipschitz_temp (ι := Fin 1) (κ := Fin 1)
    one_pos one_pos one_pos zero_le_one one_pos le_rfl one_le_two one_le_two le_rfl
    (fun _ => by norm_num [nvStcG]) (fun _ => by norm_num [nvStcE])
    (fun _ => by norm_num [nvStcG]) (fun _ => by norm_num [nvStcE])
    one_pos le_rfl

/-- The assembled Lipschitz constant is a genuine *strictly positive* value on the witness
data, so the two-sided sensitivity bound is a non-trivial constraint (not `0 ≤ 0`). -/
example : 0 < sahaFactorLipConst 1 1 2 1 1 1 nvStcG nvStcE nvStcG nvStcE := by
  have htb1 : 0 < thermalBracket (1 : ℝ) 1 1 1 := by unfold thermalBracket; positivity
  have htb2 : 0 < thermalBracket (1 : ℝ) 2 1 1 := by unfold thermalBracket; positivity
  have hpf : 0 < partitionFunction (1 : ℝ) 1 nvStcG nvStcE :=
    partitionFunction_pos (fun _ => by norm_num [nvStcG])
  have hs1 : (0 : ℝ) < ∑ k, nvStcG k := by rw [Fin.sum_univ_one]; norm_num [nvStcG]
  have hs2 : (0 : ℝ) ≤ ∑ k, nvStcG k * nvStcE k := by
    rw [Fin.sum_univ_one]; norm_num [nvStcE]
  unfold sahaFactorLipConst
  positivity

/-! ### Partition-function growth & monotonicity groundwork (Frontier 02, Phase 1) -/
/-- **Strict monotonicity of the thermal-de-Broglie bracket in `T` (PURE-MATH).**
`thermalBracket kB · me h = (2π m_e k_B/h²)·T` is *strictly* increasing in the
temperature: for positive constants `k_B, m_e, h` and `Ta < Tb`,
`thermalBracket kB Ta me h < thermalBracket kB Tb me h`.  Strict sibling of the
existing `thermalBracket_mono`; the difference is the positive linear coefficient
`(2π m_e k_B/h²)` times the positive gap `Tb − Ta`. -/
lemma thermalBracket_strictMono {kB me h Ta Tb : ℝ}
    (hkB : 0 < kB) (hme : 0 < me) (hh : 0 < h) (hab : Ta < Tb) :
    thermalBracket kB Ta me h < thermalBracket kB Tb me h := by
  have hcoef : 0 < 2 * Real.pi * me * kB / h ^ 2 := div_pos (by positivity) (pow_pos hh 2)
  have hdiff : thermalBracket kB Tb me h - thermalBracket kB Ta me h
      = (2 * Real.pi * me * kB / h ^ 2) * (Tb - Ta) := by
    unfold thermalBracket; ring
  nlinarith [mul_pos hcoef (sub_pos.mpr hab)]

/-- **Partition-function upper growth against the ionization exponential (PURE-MATH).**
The crux termwise bound.  If every level energy is capped by `chi` (`∀ k, E k ≤ chi`)
and the degeneracies are positive, then raising the temperature from `T₁` to `T₂ ≥ T₁`
inflates the partition function by at most the factor `exp(chi·(1/(k_B T₁) − 1/(k_B T₂)))`:

`U(T₂) ≤ exp(chi·(1/(k_B T₁) − 1/(k_B T₂)))·U(T₁)`.

Proved termwise: dividing by `gₖ > 0` and using `exp` monotonicity, the claim reduces to
the scalar inequality `(E k − chi)·(1/(k_B T₁) − 1/(k_B T₂)) ≤ 0`, which holds because
`1/(k_B T₁) ≥ 1/(k_B T₂) > 0` (temperature raises the inverse-temperature floor) and
`E k − chi ≤ 0`.  This pairs `U`'s growth against the `exp(−chi/(k_B T))` Saha factor —
it does **not** require `E k ≥ 0`. -/
lemma partitionFunction_upper_growth {kB T1 T2 chi : ℝ} {g E : ι → ℝ}
    (hkB : 0 < kB) (hT1 : 0 < T1) (hT12 : T1 ≤ T2)
    (hg : ∀ k, 0 < g k) (hEχ : ∀ k, E k ≤ chi) :
    partitionFunction kB T2 g E
      ≤ Real.exp (chi * (1 / (kB * T1) - 1 / (kB * T2))) * partitionFunction kB T1 g E := by
  have hkT1 : 0 < kB * T1 := mul_pos hkB hT1
  have hinv : 1 / (kB * T2) ≤ 1 / (kB * T1) :=
    one_div_le_one_div_of_le hkT1 (mul_le_mul_of_nonneg_left hT12 hkB.le)
  unfold partitionFunction
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _
  unfold boltzmannFactor
  have hexp : -E k / (kB * T2)
      ≤ chi * (1 / (kB * T1) - 1 / (kB * T2)) + -E k / (kB * T1) := by
    have e1 : -E k / (kB * T2) = -(E k) * (1 / (kB * T2)) := by ring
    have e2 : -E k / (kB * T1) = -(E k) * (1 / (kB * T1)) := by ring
    rw [e1, e2]
    nlinarith [mul_nonneg (sub_nonneg.mpr (hEχ k)) (sub_nonneg.mpr hinv)]
  calc g k * Real.exp (-E k / (kB * T2))
      ≤ g k * Real.exp (chi * (1 / (kB * T1) - 1 / (kB * T2)) + -E k / (kB * T1)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (hg k).le
    _ = Real.exp (chi * (1 / (kB * T1) - 1 / (kB * T2))) * (g k * Real.exp (-E k / (kB * T1))) := by
        rw [Real.exp_add]; ring

/-- **Monotonicity of the partition function in `T` (PURE-MATH).**  For non-negative
level energies (`∀ k, 0 ≤ E k`) and positive degeneracies, the partition function is
nondecreasing in temperature: `T₁ ≤ T₂ ⇒ U(T₁) ≤ U(T₂)`.  Each Boltzmann factor
`exp(−Eₖ/(k_B T))` is nondecreasing in `T` when `Eₖ ≥ 0` and `k_B > 0` (the exponent
`−Eₖ/(k_B T)` rises toward `0` as `T` grows), and a sum of nondecreasing terms is
nondecreasing.  Public restatement of the private `partitionFunction_ge_floor`, with the
floor taken as the lower temperature `T₁`. -/
lemma partitionFunction_mono_temp {kB T1 T2 : ℝ} {g E : ι → ℝ}
    (hkB : 0 < kB) (hT1 : 0 < T1) (hT12 : T1 ≤ T2)
    (hg : ∀ k, 0 < g k) (hE : ∀ k, 0 ≤ E k) :
    partitionFunction kB T1 g E ≤ partitionFunction kB T2 g E := by
  unfold partitionFunction
  apply Finset.sum_le_sum
  intro k _
  apply mul_le_mul_of_nonneg_left _ (hg k).le
  unfold boltzmannFactor
  apply Real.exp_le_exp.mpr
  rw [neg_div, neg_div, neg_le_neg_iff]
  exact div_le_div_of_nonneg_left (hE k) (mul_pos hkB hT1)
    (mul_le_mul_of_nonneg_left hT12 hkB.le)

/-! ### Non-vacuity witnesses

Concrete `Fin 1` data (`k_B = m_e = h = 1`, `g = 1`) certifying that each lemma's
hypotheses are jointly satisfiable and the conclusion is a genuine, non-degenerate
constraint on a varying quantity. -/

private def nvG : Fin 1 → ℝ := fun _ => 1
private def nvE0 : Fin 1 → ℝ := fun _ => 0
private def nvE1 : Fin 1 → ℝ := fun _ => 1

/-- Non-vacuity for `thermalBracket_strictMono`: the bracket strictly increases from
`T = 1` to `T = 2` (a genuine `<`, not `0 < 0`). -/
example : thermalBracket 1 1 1 1 < thermalBracket 1 2 1 1 :=
  thermalBracket_strictMono one_pos one_pos one_pos one_lt_two

/-- Non-vacuity for `partitionFunction_upper_growth`: with `E = 0 < chi = 1`, the growth
factor `exp(1·(1 − 1/2)) = exp(1/2) > 1` is a non-trivial bound (`U(2) = 1 ≤ exp(1/2)`). -/
example :
    partitionFunction (1 : ℝ) 2 nvG nvE0
      ≤ Real.exp (1 * (1 / (1 * 1) - 1 / (1 * 2))) * partitionFunction (1 : ℝ) 1 nvG nvE0 :=
  partitionFunction_upper_growth (ι := Fin 1) one_pos one_pos one_le_two
    (fun _ => one_pos) (fun _ => by norm_num [nvE0])

/-- Non-vacuity for `partitionFunction_mono_temp`: with `E = 1 > 0`, the two temperatures
give strictly different partition values (`exp(−1) < exp(−1/2)`), so the `≤` is a real
constraint on a genuinely varying quantity. -/
example : partitionFunction (1 : ℝ) 1 nvG nvE1 ≤ partitionFunction (1 : ℝ) 2 nvG nvE1 :=
  partitionFunction_mono_temp (ι := Fin 1) one_pos one_pos one_le_two
    (fun _ => one_pos) (fun _ => by norm_num [nvE1])

end CflibsFormal
