/-
Copyright (c) 2026 Brian Squires. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Squires
-/
import Mathlib
import CflibsFormal.Saha

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

This module is the *single-ratio, fixed-`T`* sensitivity analysis of `n_e`.  Two
pieces of gap #3 are deliberately **out of scope** and remain open:

* **T-channel.**  A bound on `∂n_e/∂T` needs the closed form of `dS/dT`, whose
  sign is *not* definite: `S(T)` mixes the increasing thermal-de-Broglie factor
  `(2π m_e k_B T/h²)^{3/2}` and `exp(−χ/(k_B T))` with the partition-function ratio
  `U_{z+1}(T)/U_z(T)`, which can run either way.  No honest one-sided monotonicity
  of the *whole* `sahaFactor` in `T` is available without extra assumptions, so the
  T-channel is SKIPPED here rather than proven under a hidden reduction.
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

end CflibsFormal
