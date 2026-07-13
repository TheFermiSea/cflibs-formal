/-
Copyright (c) 2026 Brian Squires. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Squires
-/
import Mathlib
import CflibsFormal.EquivalentWidth

/-!
# Saha–Boltzmann formalization — the sharp Ladenburg–Reiche asymptotic equivalent

`EquivalentWidth.lean` builds the curve of growth for the normalized Lorentzian profile
`L(x) = (1/π)·1/(1+x²)` (HWHM `= 1`, unit area) up to and including the *sharp constant*
`equivWidth_lorentzian_sqrt_sharp : W(τ)/√τ → 2` (via the scaling identity + dominated
convergence + `∫(1 − e^{−1/u²}) = 2√π`). This module packages that limit in the exact form
the Ladenburg–Reiche curve-of-growth law is usually quoted — an
`Asymptotics.IsEquivalent` statement — and **strengthens it to arbitrary Lorentzian
half-width `γ_L`**, exposing the `√(γ_L · τ)` scaling that governs the damping-wing regime.

* `equivWidth_lorentzian_isEquivalent` — **the sharp asymptotic (unit half-width).**
  `equivWidth lorentzian ~[atTop] fun τ => 2·√τ`, i.e. the equivalent width is asymptotically
  equal (ratio `→ 1`, not merely bracketed) to `2√τ`. Direct repackaging of
  `equivWidth_lorentzian_sqrt_sharp` through `Asymptotics.isEquivalent_of_tendsto_one`.
* `lorentzianG γ` — the **general Lorentzian** `L_γ(x) = (γ/π)·1/(x²+γ²)` of half-width
  `γ` (HWHM `= γ`, unit area, `lorentzianG 1 = lorentzian`).
* `equivWidth_lorentzianG_scaled` — the **exact half-width rescaling**
  `equivWidth (lorentzianG γ) τ = γ · equivWidth lorentzian (τ/γ)` for `γ > 0`
  (substitution `x = γ·u`, `MeasureTheory.Measure.integral_comp_mul_left`).
* `equivWidth_lorentzianG_sqrt_sharp` — `equivWidth (lorentzianG γ) τ / √τ → 2√γ`.
* `equivWidth_lorentzianG_isEquivalent` — **the sharp asymptotic at half-width `γ`:**
  `equivWidth (lorentzianG γ) ~[atTop] fun τ => 2·√(γ·τ)`. So `W(τ) ∼ 2√(γ_L·τ)`: the
  strong-line equivalent width is `2√(γ_L·S)` with `γ_L` the Lorentz half-width and
  `S = τ` the integrated line strength (`∫τL = τ`) — the classical square-root damping wing.

## Literature and scope

* **Scope tag: EXACT (within the model).** The results are exact asymptotic-equivalence
  (`IsEquivalent`) and limit statements for the honest integral definition
  `equivWidth φ τ = ∫ (1 − exp(−(τ·φ)))`; no linearization or approximation is inserted. They
  build on the already-audited `equivWidth_lorentzian_sqrt_sharp` of `EquivalentWidth.lean` (whose
  own axioms are the standard `propext`/`Classical.choice`/`Quot.sound`).
* **Non-circular / independent reference.** The comparison functions `2√τ` and `2√(γ·τ)` are
  explicit elementary functions, *independent* of `equivWidth`; the equivalence is the non-trivial
  fact that the ratio tends to `1` (equivalently the sharp constant is `2`). This is a genuine
  sharpening of the two-sided envelope `equivWidth_lorentzian_sqrt_two_sided` (constants
  `≈ 0.126` and `≈ 2.257`), whose bracket the exact constant `2·√γ` (here `√1 = 1 ⇒ 2`) lies
  strictly inside.
* **Constant/normalization note (honesty about the target form).** In this module's
  normalization — unit-area Lorentzian, HWHM `γ_L`, and `τ` the *integrated* line strength
  `S = ∫ τ·L` — the sharp curve-of-growth constant is `W(τ) ∼ 2√(γ_L·S)` (independent of `π`; see
  the `x = √(Sγ_L/π)·u` reduction). A literal reading of the loosely-quoted target normalizer
  `√(2 γ_L τ / π)` differs from the correct `2√(γ_L τ)` by the constant factor `√(2π)` and
  corresponds to a *different* convention for `τ` / the profile; we therefore prove and assert only
  the correct `2√(γ_L·τ)` form, not the literal `√(2γ_Lτ/π)`.
* **Citation.** Ladenburg, R.; Reiche, F. "Über selektive Absorption," *Annalen der Physik* **42**
  (1913) 181 — the Lorentz-line curve of growth `L(x) = x e^{−x}(I₀(x)+I₁(x))` and its strong-line
  square-root asymptotic. The LIBS curve-of-growth setting is Gornushkin et al.,
  *Spectrochimica Acta Part B* **54** (1999) 491. The full modified-Bessel curve stays out of
  scope (absent from mathlib); only the sharp `τ → ∞` constant is captured, via the bessel-free
  route already resident in `EquivalentWidth.lean`.
-/

namespace CflibsFormal

open MeasureTheory Real Asymptotics Filter
open scoped Topology

/-- **The sharp Ladenburg–Reiche asymptotic (unit half-width), `IsEquivalent` form.**
`equivWidth lorentzian ~[atTop] (fun τ => 2·√τ)`: the Lorentzian equivalent width is
*asymptotically equal* to `2√τ` (the ratio tends to `1`), the exact slope-½ damping-wing law.
This upgrades the two-sided `√τ` envelope `equivWidth_lorentzian_sqrt_two_sided` to a sharp
asymptotic equivalence; it is the `Asymptotics.IsEquivalent` repackaging of the limit
`equivWidth_lorentzian_sqrt_sharp` (`W(τ)/√τ → 2`). -/
theorem equivWidth_lorentzian_isEquivalent :
    (equivWidth lorentzian) ~[atTop] (fun τ => 2 * Real.sqrt τ) := by
  have h2 : Tendsto (fun τ => equivWidth lorentzian τ / (2 * Real.sqrt τ)) atTop (nhds 1) := by
    have hd := equivWidth_lorentzian_sqrt_sharp.div_const 2
    rw [show (2:ℝ) / 2 = 1 by norm_num] at hd
    exact Filter.Tendsto.congr (fun τ => by rw [div_div]; congr 1; ring) hd
  exact Asymptotics.isEquivalent_of_tendsto_one h2

/-- **The general Lorentzian profile of half-width `γ`.** `L_γ(x) = (γ/π)·1/(x²+γ²)`, a unit-area
line shape with HWHM `γ`; `lorentzianG 1 = lorentzian` recovers the unit-width kernel. -/
noncomputable def lorentzianG (γ x : ℝ) : ℝ := (γ / Real.pi) * (1 / (x ^ 2 + γ ^ 2))

/-- The general Lorentzian is strictly positive for `γ > 0`. -/
theorem lorentzianG_pos {γ : ℝ} (hγ : 0 < γ) (x : ℝ) : 0 < lorentzianG γ x := by
  unfold lorentzianG
  have : (0:ℝ) < x ^ 2 + γ ^ 2 := by positivity
  exact mul_pos (div_pos hγ Real.pi_pos) (div_pos one_pos this)

/-- `lorentzianG 1` is the unit-width Lorentzian `lorentzian` of `EquivalentWidth.lean`. -/
theorem lorentzianG_one : lorentzianG 1 = lorentzian := by
  funext x
  unfold lorentzianG lorentzian
  rw [one_pow, add_comm (x ^ 2) (1:ℝ)]

/-- **Exact half-width rescaling of the equivalent width.** For `γ > 0`,
`equivWidth (lorentzianG γ) τ = γ · equivWidth lorentzian (τ / γ)`. Substitution `x = γ·u`
(Jacobian `γ`) trades the profile half-width for a rescaled optical depth on the unit-width
kernel, via the full-line change of variables
`MeasureTheory.Measure.integral_comp_mul_left`. This is the algebraic bridge that carries the
unit-width sharp constant to arbitrary `γ`. -/
theorem equivWidth_lorentzianG_scaled {γ : ℝ} (hγ : 0 < γ) (τ : ℝ) :
    equivWidth (lorentzianG γ) τ = γ * equivWidth lorentzian (τ / γ) := by
  have hπ := Real.pi_pos
  set g : ℝ → ℝ := fun x => 1 - Real.exp (-(τ * lorentzianG γ x)) with hg
  have hpt : ∀ x : ℝ, g (γ * x) = 1 - Real.exp (-((τ / γ) * lorentzian x)) := by
    intro x
    have hkey : τ * lorentzianG γ (γ * x) = (τ / γ) * lorentzian x := by
      unfold lorentzianG lorentzian
      have h1 : (γ * x) ^ 2 + γ ^ 2 = γ ^ 2 * (x ^ 2 + 1) := by ring
      rw [h1]
      have hγ0 : γ ≠ 0 := hγ.ne'
      have hπ0 : Real.pi ≠ 0 := hπ.ne'
      have hx1 : (x ^ 2 + 1 : ℝ) ≠ 0 := by positivity
      have hx1' : (1 + x ^ 2 : ℝ) ≠ 0 := by positivity
      have hγ2 : (γ ^ 2 : ℝ) ≠ 0 := by positivity
      field_simp
      ring
    change (1 : ℝ) - Real.exp (-(τ * lorentzianG γ (γ * x)))
        = 1 - Real.exp (-((τ / γ) * lorentzian x))
    rw [hkey]
  have hlem := MeasureTheory.Measure.integral_comp_mul_left g γ
  have habs : |γ⁻¹| = γ⁻¹ := abs_of_pos (inv_pos.mpr hγ)
  rw [habs, smul_eq_mul] at hlem
  have hval : (∫ y, g y) = γ * ∫ x, g (γ * x) := by
    have hh : γ * ∫ x, g (γ * x) = γ * (γ⁻¹ * ∫ y, g y) :=
      congrArg (fun z => γ * z) hlem
    rw [← mul_assoc, mul_inv_cancel₀ hγ.ne', one_mul] at hh
    exact hh.symm
  have hcongr : (∫ x, g (γ * x))
      = ∫ x, (1 - Real.exp (-((τ / γ) * lorentzian x))) := by
    congr 1; funext x; exact hpt x
  change (∫ y, g y) = γ * ∫ x, (1 - Real.exp (-((τ / γ) * lorentzian x)))
  rw [hval, hcongr]

/-- **The sharp constant at half-width `γ`:** `equivWidth (lorentzianG γ) τ / √τ → 2√γ` as
`τ → ∞`. Reparametrize the unit-width sharp limit `equivWidth_lorentzian_sqrt_sharp` through
`τ ↦ τ/γ` and rescale by `√γ` using `equivWidth_lorentzianG_scaled` and `√(τ/γ) = √τ/√γ`. -/
theorem equivWidth_lorentzianG_sqrt_sharp {γ : ℝ} (hγ : 0 < γ) :
    Tendsto (fun τ => equivWidth (lorentzianG γ) τ / Real.sqrt τ) atTop
      (nhds (2 * Real.sqrt γ)) := by
  have hsqγ : (0:ℝ) < Real.sqrt γ := Real.sqrt_pos.mpr hγ
  have hdiv : Tendsto (fun τ : ℝ => τ / γ) atTop atTop :=
    Filter.tendsto_id.atTop_div_const hγ
  have hcomp : Tendsto
      (fun τ => equivWidth lorentzian (τ / γ) / Real.sqrt (τ / γ)) atTop (nhds 2) :=
    equivWidth_lorentzian_sqrt_sharp.comp hdiv
  have hmul : Tendsto
      (fun τ => Real.sqrt γ * (equivWidth lorentzian (τ / γ) / Real.sqrt (τ / γ)))
      atTop (nhds (Real.sqrt γ * 2)) := hcomp.const_mul (Real.sqrt γ)
  rw [show Real.sqrt γ * 2 = 2 * Real.sqrt γ by ring] at hmul
  refine Filter.Tendsto.congr' ?_ hmul
  filter_upwards [Filter.eventually_gt_atTop (0:ℝ)] with τ hτ
  set E := equivWidth lorentzian (τ / γ) with hE
  rw [equivWidth_lorentzianG_scaled hγ τ, ← hE, Real.sqrt_div hτ.le γ,
    div_div_eq_mul_div, ← mul_div_assoc]
  congr 1
  linear_combination E * Real.mul_self_sqrt hγ.le

/-- **The sharp Ladenburg–Reiche asymptotic at half-width `γ`, `IsEquivalent` form.**
`equivWidth (lorentzianG γ) ~[atTop] (fun τ => 2·√(γ·τ))` for `γ > 0`: the strong-line
equivalent width of a Lorentz line of half-width `γ_L = γ` and integrated line strength
`S = τ` is asymptotically `2√(γ_L·S)`, the classical square-root damping wing. This exposes the
`√(γ_L·τ)` scaling that governs the optically-thick transition; the unit-width case `γ = 1`
recovers `equivWidth_lorentzian_isEquivalent` (`2√τ`). -/
theorem equivWidth_lorentzianG_isEquivalent {γ : ℝ} (hγ : 0 < γ) :
    (equivWidth (lorentzianG γ)) ~[atTop] (fun τ => 2 * Real.sqrt (γ * τ)) := by
  have hne : (2 * Real.sqrt γ) ≠ 0 := by
    have : (0:ℝ) < Real.sqrt γ := Real.sqrt_pos.mpr hγ
    positivity
  have h2 : Tendsto (fun τ => equivWidth (lorentzianG γ) τ / (2 * Real.sqrt (γ * τ)))
      atTop (nhds 1) := by
    have hd := (equivWidth_lorentzianG_sqrt_sharp hγ).div_const (2 * Real.sqrt γ)
    rw [div_self hne] at hd
    exact Filter.Tendsto.congr
      (fun τ => by rw [Real.sqrt_mul hγ.le τ, div_div]; congr 1; ring) hd
  exact Asymptotics.isEquivalent_of_tendsto_one h2

/-! ### Non-vacuity witnesses -/

/-- Non-vacuity (explicit data): at the concrete optical depth `τ = 8π` the Lorentzian equivalent
width is bounded below by the explicit positive number `(1−e⁻¹)/(2√(2π))·√(8π)`
(`equivWidth_lorentzian_sqrt_lower`), so `equivWidth lorentzian` is a genuinely nonzero, growing
quantity — the sharp asymptotic `~ 2√τ` is not an equivalence of a trivially-zero function. -/
example : (1 - Real.exp (-1)) / (2 * Real.sqrt (2 * Real.pi)) * Real.sqrt (8 * Real.pi)
    ≤ equivWidth lorentzian (8 * Real.pi) :=
  equivWidth_lorentzian_sqrt_lower le_rfl

/-- Non-vacuity: the sharp equivalence forces the equivalent width to diverge,
`equivWidth lorentzian → ∞` (since its equivalent `2√τ → ∞`) — witnessing that the Lorentzian
curve of growth keeps growing, never saturating (contrast the slab `W = 1 − e^{−τ} ≤ 1`). -/
example : Tendsto (equivWidth lorentzian) atTop atTop :=
  equivWidth_lorentzian_isEquivalent.symm.tendsto_atTop
    (Real.tendsto_sqrt_atTop.const_mul_atTop (by norm_num : (0:ℝ) < 2))

/-- Non-vacuity (explicit data): the general half-width equivalence instantiates at `γ = 1`,
where `lorentzianG 1 = lorentzian` and the reference `2√(1·τ) = 2√τ` recovers the unit-width
sharp asymptotic — the two `IsEquivalent` statements agree on the concrete profile `lorentzian`. -/
example : (equivWidth (lorentzianG 1)) ~[atTop] (fun τ => 2 * Real.sqrt (1 * τ)) :=
  equivWidth_lorentzianG_isEquivalent one_pos

end CflibsFormal
