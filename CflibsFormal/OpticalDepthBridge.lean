/-
Copyright (c) 2026 Brian Squires. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Squires
-/
import Mathlib
import CflibsFormal.OpticalDepth
import CflibsFormal.SelfAbsorption
import CflibsFormal.CurveOfGrowth

/-!
# Wiring the state-bound optical depth into the free-`τ` corpus

`OpticalDepth.lean` binds the optical depth to the plasma state,
`τ = σ₀ · ℓ · n_l(T, N)`, and proves its laws — but nothing in the development imported it,
so `SelfAbsorption` (`selfAbsorptionFactor (tau : ℝ)`, `slabIntensity (S tau : ℝ)`) and
`CurveOfGrowth` (`cogIntensity (S w n : ℝ)`, `cogRatio (w₁ w₂ n : ℝ)`) still spoke about `τ`
and its proxy `w` as **free reals**. This module is the wiring: it identifies the bound-`τ`
forward map with the audited free-`τ` kernels, and then restates the free-parameter
monotonicity/injectivity results **at the bound `τ`**, where they become statements about the
physical density `N` rather than about an unmoored parameter.

## What is wired

* `thickLineIntensity_eq_cogIntensity` — the bound-`τ` thick line IS the curve-of-growth
  kernel `cogIntensity S w N` with the per-line opacity coefficient instantiated to the
  physically derived `w = σ_ℓ(T) · ℓ` (`effectiveCrossSection · ell`) and the column variable
  to the density `N`. Together with `OpticalDepth.thickLineIntensity_eq_slab` (the
  `slabIntensity` leg, already proven there) this says the three models — multiplicative
  escape factor, radiative-transfer slab, curve of growth — coincide once `τ` is bound.
  They coincide because they are one flat-profile kernel written three ways, so their
  agreement is not independent evidence for that kernel. Every free-`τ` theorem about those
  kernels therefore specializes.
* `boundSelfAbsorptionFactor_strictAntiOn_density` — `SelfAbsorption`'s escape-factor
  antitonicity `SA(τ₂) < SA(τ₁)` becomes: the escape factor is strictly decreasing in the
  DENSITY.
* `thickLineIntensity_lt_lineIntensity_of_pos_density` — the bias-direction theorem becomes:
  at any positive density the measured line falls strictly below its optically-thin value
  (no free `τ > 0` hypothesis is needed any more — positivity of `τ` is derived from the
  state).
* `thickLineIntensity_ratio_eq_source_mul_cogRatio` and
  `thickLineIntensity_ratio_strictAntiOn_density` / `..._injOn_density` — the two-line
  payoff: for two lines of the same species sharing `(T, N)` and one common `σ₀ · ℓ` but with
  distinct lower-level OPACITIES `w₂ < w₁`, the ratio of MEASURED thick intensities is a
  positive `N`-free multiple of `CurveOfGrowth.cogRatio`, hence (for this flat kernel)
  strictly antitone and injective in `N`. The multiplier is the source-strength ratio `S₁/S₂`,
  in which the calibration constant `Fcal` and the (common) lumped `σ₀ · ℓ` cancel exactly
  (`lteSourceStrength_ratio_calibration_free`) — it depends only on `T` and atomic data.
* `effectiveCrossSection_lt_of_energy_lt` — the side condition `w₂ < w₁` of the two-line
  results need not be assumed of free parameters: AT A COMMON `σ₀` it follows from the atomic
  data whenever the more strongly absorbing line has the lower-lying lower level (at equal or
  larger degeneracy). At a common `σ₀` only — see the limitation below.

## Honest limitations

* **Binding `τ` does NOT by itself break the `(N, τ)` alias.**
  `OpticalDepth.no_density_alias_of_boundOpticalDepth` rules the alias out only when `σ₀ · ℓ`
  is KNOWN (it is a hypothesis there, not a conclusion). `boundOpticalDepth_lumped_alias`
  below proves the converse in the same shape as
  `SelfAbsorptionInverse.selfAbsorption_breaks_identifiability`: with `σ₀` unknown there
  EXIST two distinct positive densities and two positive cross-sections giving the SAME
  measured thick intensity. The witness is exact, not asymptotic — `N₁ = SA(2)`, `N₂ = SA(1)`
  with the cross-sections chosen so that `τ₁ = 1`, `τ₂ = 2`, using
  `I ∝ N · SA(τ)` and the symmetry `SA(2)·SA(1) = SA(1)·SA(2)`. So the honest reading is:
  binding `τ` converts one unknown (`τ`) into one unknown (`σ₀ · ℓ`) plus a rigid `N`- and
  `T`-dependence; it buys identifiability only against a SECOND input — either an
  independently known `σ₀ · ℓ` (then `thickLineIntensity_injOn`) or a second observable (then
  the `cogRatio` route restated here). The alias is relocated, not abolished.
* The two-line ratio results still need `w₁, w₂` — hence `σ₀ · ℓ` — known to invert for `N`;
  what they do NOT need is the absolute calibration `Fcal`, and what they do not need to
  ASSUME is `w₂ < w₁`, which `effectiveCrossSection_lt_of_energy_lt` supplies from the atomic
  data at a common `σ₀`.
* **ONE `σ₀` IS SHARED BY BOTH LINES.** Every two-line statement here
  (`lteSourceStrength_ratio_calibration_free`, `..._ratio_eq_source_mul_cogRatio`,
  `..._ratio_strictAntiOn_density`, `..._ratio_injOn_density`,
  `effectiveCrossSection_lt_of_energy_lt`) takes a SINGLE `sigma0` argument and applies it to
  both transitions, so the two lines differ ONLY through the lower-level Boltzmann weight
  `g_l · exp(−E_l/(k_B T))`. Physically `σ₀` is per-transition — it carries `f_lu` and `λ²`
  (`σ₀ ∝ f_lu λ²`), which differ between two real lines, often by orders of magnitude. Two
  consequences, both material: (i) `effectiveCrossSection_lt_of_energy_lt` is NOT the general
  atomic-data fact "a lower-lying lower level absorbs more strongly" — a line with a higher
  lower level but a much larger `f λ²` can easily be the more opaque one; (ii) it is precisely
  the shared `σ₀ · ℓ` that makes it cancel in `S₁/S₂`, so the calibration-free ratio lemma is a
  statement about equal-`σ₀` lines, and for genuinely distinct `σ₀₁ ≠ σ₀₂` the ratio `σ₀₂/σ₀₁`
  survives in the prefactor. Extending these to per-line `σ₀ᵢ` is open work; nothing here
  covers it. `Fcal` cancels unconditionally and is unaffected by this restriction.
* Nothing here is new physics: every physical fact is imported. This module contains
  rewriting bridges and specializations, plus one counterexample.

## Literature and scope

REDUCED — inherited verbatim from the imported modules: a homogeneous, single-temperature
LTE slab with a flat (line-center) absorption cross-section. The frequency-dependent `τ(ν)`,
the Voigt core/wing structure, the profile-integrated slope-½ curve of growth, spatial
gradients, and self-reversal are OUT OF SCOPE. **Stimulated emission is not modelled** (see
the `OpticalDepth` scope block: the `τ` used here overstates the LTE optical depth by
`1 − exp(−(E_u − E_l)/(k_B T))`, ≈ 0.92 for visible LIBS lines, and `S` is correspondingly
the Wien limit of the line source function). The `cogRatio` leg additionally assumes the two
lines share one homogeneous emitting volume and one column density.

**Flat kernel; published tags.** Every statement over `thickLineIntensity` or
`selfAbsorptionFactor` uses the flat-profile escape factor on the frequency-integrated
intensity, whose model tag is APPROXIMATION (1.4–3.5× over-correction at line-centre depths
`3–10` for peaked profiles, in the audit probes; see the `SelfAbsorption` scope block). Those
results publish APPROXIMATION whatever their own (relation) tag (`docs/conventions.md` §8).
The two-line injectivity in `N` is a property of the flat kernel: for Stark-affected Voigt
lines (`γ/σ ≳ 0.1`) the profile-resolved pair ratio is non-monotone inside line-centre depths
`≤ 30` (audit probes; see `CurveOfGrowth`'s scope block).

* Gornushkin, Anzano, King, Smith, Omenetto, Winefordner, "Curve of growth methodology applied
  to laser-induced plasma emission spectroscopy", *Spectrochim. Acta Part B* **54** (1999)
  491–503 — the homogeneous-slab relation `I = S·(1 − exp(−τ))` shared by all three kernels
  reconciled here.
* Cristoforetti and Tognoni, "Calculation of elemental columnar density from self-absorbed
  lines", *Spectrochim. Acta Part B* **79–80** (2013) 63 — the multi-line column-density
  inversion whose ratio observable is restated here at a state-bound `τ`.
-/

namespace CflibsFormal

open Finset Real
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-! ## Leg 1 — the bound-`τ` forward map IS the curve-of-growth kernel -/

/-- **Bridge identity: bound `τ` ⇒ curve of growth.** The state-coupled thick line intensity
equals `CurveOfGrowth.cogIntensity S w N` with the source `S = lteSourceStrength`, the
per-line opacity coefficient `w = σ_ℓ(T) · ℓ` (`effectiveCrossSection · ell`) and the column
variable instantiated by the total density `N`. `CurveOfGrowth`'s `w` and `n` were free reals;
here both are the physical state. Pure rewriting: routes through
`OpticalDepth.thickLineIntensity_eq_slab`, `CurveOfGrowth.cogIntensity_slab_eq` and the
linearity `opticalDepth = σ_ℓ · ℓ · N`; no new physical content.

REDUCED, not PURE-MATH: the proof consumes `thickLineIntensity_eq_slab`, so this identity
inherits that result's homogeneous single-temperature flat-cross-section slab scope. It is
also conditional — `0 < N` (with `σ₀, ℓ > 0`) is needed to get `τ > 0`. Publishes
APPROXIMATION via `selfAbsorbedIntensity` (module scope block). -/
theorem thickLineIntensity_eq_cogIntensity [Nonempty ι] {kB T N Fcal sigma0 ell : ℝ}
    {g E A : ι → ℝ} (hg : ∀ k, 0 < g k) (hN : 0 < N) (hsig : 0 < sigma0) (hell : 0 < ell)
    (u l : ι) :
    thickLineIntensity kB T N Fcal sigma0 ell g E A u l
      = cogIntensity (lteSourceStrength kB T Fcal sigma0 ell g E A u l)
          (effectiveCrossSection kB T sigma0 g E l * ell) N := by
  rw [thickLineIntensity_eq_slab hg hN hsig hell u l, cogIntensity_slab_eq,
    opticalDepth_eq_linear]

/-! ## Leg 2 — free-`τ` laws restated as laws about the density -/

/-- **The escape factor is strictly decreasing in the DENSITY.**
`SelfAbsorption.selfAbsorptionFactor_strictAntiOn` is a statement about a free real `τ`; once
`τ` is the `opticalDepth` of the state, it becomes a statement about `N`: a denser plasma
lets a strictly smaller fraction of its line photons escape. The `τ > 0` side conditions of
the free-`τ` theorem are discharged from the state by `OpticalDepth.opticalDepth_pos`. The
escaping fraction here is the flat-profile `SA`, not a profile-resolved escape factor.

Relation REDUCED (homogeneous single-temperature slab, flat line-center cross-section);
publishes APPROXIMATION via `selfAbsorptionFactor`. -/
theorem boundSelfAbsorptionFactor_strictAntiOn_density [Nonempty ι] {kB T sigma0 ell : ℝ}
    {g E : ι → ℝ} (hg : ∀ k, 0 < g k) (hsig : 0 < sigma0) (hell : 0 < ell) (l : ι) :
    StrictAntiOn (fun N => selfAbsorptionFactor (opticalDepth kB T N sigma0 ell g E l))
      (Set.Ioi 0) := by
  intro Na hNa Nb hNb hab
  have hNa0 : (0 : ℝ) < Na := Set.mem_Ioi.mp hNa
  have hNb0 : (0 : ℝ) < Nb := Set.mem_Ioi.mp hNb
  exact selfAbsorptionFactor_strictAntiOn
    (Set.mem_Ioi.mpr (opticalDepth_pos hg hNa0 hsig hell l))
    (Set.mem_Ioi.mpr (opticalDepth_pos hg hNb0 hsig hell l))
    (opticalDepth_strictMono_density hg hsig hell l hab)

/-- **The bias-direction theorem, at the bound `τ`.** `SelfAbsorption`'s strict dimming law
needs a free hypothesis `0 < τ`; with `τ` bound to the state that hypothesis is DERIVED from
`0 < N`. So: at any positive density the measured (self-absorbed) line lies strictly below
its optically-thin value, and neglecting self-absorption biases the inferred upper-level
population downward.

Scope: homogeneous single-temperature slab, flat line-center cross-section; publishes
APPROXIMATION via `selfAbsorbedIntensity`, like `selfAbsorbedIntensity_lt_lineIntensity`. -/
theorem thickLineIntensity_lt_lineIntensity_of_pos_density [Nonempty ι]
    {kB T N Fcal sigma0 ell : ℝ} {g E A : ι → ℝ} (hg : ∀ k, 0 < g k) (hN : 0 < N)
    (hFcal : 0 < Fcal) (hA : ∀ k, 0 < A k) (hsig : 0 < sigma0) (hell : 0 < ell) (u l : ι) :
    thickLineIntensity kB T N Fcal sigma0 ell g E A u l
      < lineIntensity kB T N Fcal g E A u := by
  unfold thickLineIntensity
  exact selfAbsorbedIntensity_lt_lineIntensity hg hN hFcal hA u
    (opticalDepth_pos hg hN hsig hell l)

/-! ## Leg 3 — the two-line ratio, with the opacity ordering derived from atomic data -/

/-- **A lower-lying lower level absorbs more strongly.** The Boltzmann-weighted line
cross-section is strictly larger for the transition whose LOWER level lies lower in energy
(at equal or larger degeneracy), because a larger LTE fraction of the species sits there.
This discharges the `w₂ < w₁` side condition of the curve-of-growth ratio results from the
atomic data instead of assuming it of free parameters.

SCOPE — READ THIS BEFORE QUOTING THE HEADLINE. A SINGLE `sigma0` is applied to BOTH
transitions, so the two lines here differ only through `g_l · exp(−E_l/(k_B T))`. Physically
`σ₀ ∝ f_lu λ²` is per-transition; for two real lines with different oscillator strengths or
wavelengths the ordering can invert, and this theorem then says nothing about them. So the
honest reading is "at a common line-center cross-section, the lower-lying lower level absorbs
more strongly", NOT the unconditional atomic-data claim.

REDUCED: LTE level populations at a single temperature; `kB * T > 0` is required. -/
theorem effectiveCrossSection_lt_of_energy_lt [Nonempty ι] {kB T sigma0 : ℝ} {g E : ι → ℝ}
    (hg : ∀ k, 0 < g k) (hsig : 0 < sigma0) (hkT : 0 < kB * T) {l₁ l₂ : ι}
    (hgle : g l₂ ≤ g l₁) (hE : E l₁ < E l₂) :
    effectiveCrossSection kB T sigma0 g E l₂ < effectiveCrossSection kB T sigma0 g E l₁ := by
  have hU : 0 < partitionFunction kB T g E := partitionFunction_pos hg
  have hbf : boltzmannFactor kB T (E l₂) < boltzmannFactor kB T (E l₁) := by
    unfold boltzmannFactor
    refine Real.exp_lt_exp.mpr ?_
    rw [div_lt_div_iff₀ hkT hkT]
    nlinarith [mul_pos (sub_pos.mpr hE) hkT]
  have step1 : sigma0 * g l₂ * boltzmannFactor kB T (E l₂)
      < sigma0 * g l₂ * boltzmannFactor kB T (E l₁) :=
    mul_lt_mul_of_pos_left hbf (mul_pos hsig (hg l₂))
  have step2 : sigma0 * g l₂ * boltzmannFactor kB T (E l₁)
      ≤ sigma0 * g l₁ * boltzmannFactor kB T (E l₁) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hgle hsig.le)
      (boltzmannFactor_pos _ _ _).le
  have hnum : sigma0 * g l₂ * boltzmannFactor kB T (E l₂)
      < sigma0 * g l₁ * boltzmannFactor kB T (E l₁) := by linarith
  unfold effectiveCrossSection
  exact (div_lt_div_iff₀ hU hU).mpr (mul_lt_mul_of_pos_right hnum hU)

omit [Fintype ι] in
/-- **The source-strength ratio is calibration- and opacity-free.** Both `lteSourceStrength`
factors carry the same `Fcal` and the same `σ₀ · ℓ`, so in their ratio these cancel EXACTLY:
what survives depends only on `T` and the atomic data `(A, g, E)` of the four levels. This is
the algebraic fact that makes the two-line ratio route below independent of the absolute
calibration; it is proved here rather than asserted in prose. Pure algebra.

The `σ₀ · ℓ` cancellation is CONDITIONAL on the two lines sharing one `σ₀` — a single
`sigma0` argument serves both. `Fcal` cancels unconditionally; `σ₀` cancels only because it
was assumed common (see the module's `## Honest limitations`). -/
theorem lteSourceStrength_ratio_calibration_free {kB T Fcal sigma0 ell : ℝ} {g E A : ι → ℝ}
    (hg : ∀ k, 0 < g k) (hFcal : 0 < Fcal) (hA : ∀ k, 0 < A k) (hsig : 0 < sigma0)
    (hell : 0 < ell) (u₁ l₁ u₂ l₂ : ι) :
    lteSourceStrength kB T Fcal sigma0 ell g E A u₁ l₁
        / lteSourceStrength kB T Fcal sigma0 ell g E A u₂ l₂
      = A u₁ * g u₁ * boltzmannFactor kB T (E u₁) * (g l₂ * boltzmannFactor kB T (E l₂))
        / (A u₂ * g u₂ * boltzmannFactor kB T (E u₂)
            * (g l₁ * boltzmannFactor kB T (E l₁))) := by
  have hF : Fcal ≠ 0 := hFcal.ne'
  have hs : sigma0 ≠ 0 := hsig.ne'
  have he : ell ≠ 0 := hell.ne'
  have hA2 : A u₂ ≠ 0 := (hA u₂).ne'
  have hgu2 : g u₂ ≠ 0 := (hg u₂).ne'
  have hgl1 : g l₁ ≠ 0 := (hg l₁).ne'
  have hgl2 : g l₂ ≠ 0 := (hg l₂).ne'
  have hbu2 : boltzmannFactor kB T (E u₂) ≠ 0 := (boltzmannFactor_pos _ _ _).ne'
  have hbl1 : boltzmannFactor kB T (E l₁) ≠ 0 := (boltzmannFactor_pos _ _ _).ne'
  have hbl2 : boltzmannFactor kB T (E l₂) ≠ 0 := (boltzmannFactor_pos _ _ _).ne'
  unfold lteSourceStrength
  field_simp

/-- **The measured two-line ratio is a known multiple of the source-free `cogRatio`.** For two
lines of the same species observed at the same `(T, N)`, the ratio of measured thick
intensities factors as
  `I₁ / I₂ = (S₁ / S₂) · cogRatio w₁ w₂ N`,
with `wᵢ = σ_ℓᵢ(T) · ℓ`. The `cogRatio` factor is exactly `CurveOfGrowth`'s source-free
observable, now evaluated at the physical density. Note what the prefactor `S₁/S₂` is: both
source strengths carry the same `Fcal` and the same `σ₀ · ℓ`, so these cancel — proved, not
asserted, in `lteSourceStrength_ratio_calibration_free` — leaving a quantity fixed by `T` and
the atomic data of the four levels. Pure rewriting from `thickLineIntensity_eq_cogIntensity`
and `div_mul_div_comm`.

REDUCED, not PURE-MATH: it consumes `thickLineIntensity_eq_cogIntensity` and hence
`thickLineIntensity_eq_slab`, inheriting that slab scope; and one `σ₀` is shared by both
lines (see the module's `## Honest limitations`). Publishes APPROXIMATION via
`selfAbsorbedIntensity`. -/
theorem thickLineIntensity_ratio_eq_source_mul_cogRatio [Nonempty ι]
    {kB T N Fcal sigma0 ell : ℝ} {g E A : ι → ℝ} (hg : ∀ k, 0 < g k) (hN : 0 < N)
    (hsig : 0 < sigma0) (hell : 0 < ell) (u₁ l₁ u₂ l₂ : ι) :
    thickLineIntensity kB T N Fcal sigma0 ell g E A u₁ l₁
        / thickLineIntensity kB T N Fcal sigma0 ell g E A u₂ l₂
      = lteSourceStrength kB T Fcal sigma0 ell g E A u₁ l₁
          / lteSourceStrength kB T Fcal sigma0 ell g E A u₂ l₂
        * cogRatio (effectiveCrossSection kB T sigma0 g E l₁ * ell)
            (effectiveCrossSection kB T sigma0 g E l₂ * ell) N := by
  rw [thickLineIntensity_eq_cogIntensity hg hN hsig hell u₁ l₁,
    thickLineIntensity_eq_cogIntensity hg hN hsig hell u₂ l₂]
  unfold cogIntensity cogRatio
  rw [div_mul_div_comm]

/-- **THE TWO-LINE PAYOFF, at the bound `τ`.** `CurveOfGrowth.cogRatio_strictAntiOn` is a
statement about a free column variable `n` and free opacities `w₁ > w₂`. Restated here at the
bound `τ`: for two lines of the same species sharing `(T, N)`, whose lower levels give
`σ_ℓ₂(T) < σ_ℓ₁(T)`, the ratio of MEASURED thick intensities is strictly ANTITONE in the
physical density `N` on `(0, ∞)` — the thicker line saturates first, so the ratio droops. The
`N`-free prefactor `S₁/S₂` is positive, so it cannot destroy the strictness. Flat kernel
only: the profile-resolved Voigt pair ratio need not be monotone (module scope block).

Relation REDUCED: homogeneous single-temperature slab, flat line-center cross-section, one
shared column density AND one shared `σ₀` for both lines (per-line `f_lu λ²` differences are
not modelled — see the module's `## Honest limitations`). Publishes APPROXIMATION via
`selfAbsorbedIntensity`. -/
theorem thickLineIntensity_ratio_strictAntiOn_density [Nonempty ι]
    {kB T Fcal sigma0 ell : ℝ} {g E A : ι → ℝ} (hg : ∀ k, 0 < g k) (hFcal : 0 < Fcal)
    (hA : ∀ k, 0 < A k) (hsig : 0 < sigma0) (hell : 0 < ell) (u₁ l₁ u₂ l₂ : ι)
    (hw : effectiveCrossSection kB T sigma0 g E l₂
      < effectiveCrossSection kB T sigma0 g E l₁) :
    StrictAntiOn
      (fun N => thickLineIntensity kB T N Fcal sigma0 ell g E A u₁ l₁
        / thickLineIntensity kB T N Fcal sigma0 ell g E A u₂ l₂) (Set.Ioi 0) := by
  have hw₂ : 0 < effectiveCrossSection kB T sigma0 g E l₂ * ell :=
    mul_pos (effectiveCrossSection_pos hg hsig l₂) hell
  have hwlt : effectiveCrossSection kB T sigma0 g E l₂ * ell
      < effectiveCrossSection kB T sigma0 g E l₁ * ell :=
    mul_lt_mul_of_pos_right hw hell
  have hS : 0 < lteSourceStrength kB T Fcal sigma0 ell g E A u₁ l₁
      / lteSourceStrength kB T Fcal sigma0 ell g E A u₂ l₂ :=
    div_pos (lteSourceStrength_pos hg hFcal hA hsig hell u₁ l₁)
      (lteSourceStrength_pos hg hFcal hA hsig hell u₂ l₂)
  intro Na hNa Nb hNb hab
  have hNa0 : (0 : ℝ) < Na := Set.mem_Ioi.mp hNa
  have hNb0 : (0 : ℝ) < Nb := Set.mem_Ioi.mp hNb
  simp only [thickLineIntensity_ratio_eq_source_mul_cogRatio hg hNa0 hsig hell u₁ l₁ u₂ l₂,
    thickLineIntensity_ratio_eq_source_mul_cogRatio hg hNb0 hsig hell u₁ l₁ u₂ l₂]
  exact mul_lt_mul_of_pos_left (cogRatio_strictAntiOn hwlt hw₂ hNa hNb hab) hS

/-- **Injectivity of the measured two-line ratio in the density — flat kernel only.**
Immediate from the strict antitonicity above. Within the flat-profile kernel this is the
identifiability route once `σ₀ · ℓ` is NOT taken as known-and-single-line: two lines of
distinct opacity, at one `(T, N)`, determine `N`. It is the bound-`τ` restatement of
`CurveOfGrowth.cogRatio_injOn`, and like it does not transfer to Stark-affected Voigt lines
(`γ/σ ≳ 0.1`), whose profile-resolved pair ratio is non-monotone inside line-centre depths
`≤ 30` (audit probes; module scope block).

SCOPE — the `wᵢ` (hence `σ₀ · ℓ` and `T`) must be known to invert the ratio for `N`; what is
NOT needed is the absolute calibration `Fcal`, which cancels in `S₁/S₂`.

Relation REDUCED: homogeneous single-temperature slab, flat line-center cross-section, one
shared column density AND one shared `σ₀` for both lines (per-line `f_lu λ²` differences are
not modelled — see the module's `## Honest limitations`). Publishes APPROXIMATION via
`selfAbsorbedIntensity`. -/
theorem thickLineIntensity_ratio_injOn_density [Nonempty ι] {kB T Fcal sigma0 ell : ℝ}
    {g E A : ι → ℝ} (hg : ∀ k, 0 < g k) (hFcal : 0 < Fcal) (hA : ∀ k, 0 < A k)
    (hsig : 0 < sigma0) (hell : 0 < ell) (u₁ l₁ u₂ l₂ : ι)
    (hw : effectiveCrossSection kB T sigma0 g E l₂
      < effectiveCrossSection kB T sigma0 g E l₁) :
    Set.InjOn
      (fun N => thickLineIntensity kB T N Fcal sigma0 ell g E A u₁ l₁
        / thickLineIntensity kB T N Fcal sigma0 ell g E A u₂ l₂) (Set.Ioi 0) :=
  (thickLineIntensity_ratio_strictAntiOn_density hg hFcal hA hsig hell u₁ l₁ u₂ l₂ hw).injOn

/-! ## Leg 4 — what the binding does NOT buy -/

/-- **Binding `τ` to `(T, N)` does NOT by itself break the density alias.**
`OpticalDepth.no_density_alias_of_boundOpticalDepth` excludes the single-line `(N, τ)` alias
only under the HYPOTHESIS that `σ₀` (with `ℓ`) is known. Drop that hypothesis and the alias
returns — inside the lumped parameter — exactly as
`SelfAbsorptionInverse.selfAbsorption_breaks_identifiability` returns it for a free `τ`: there
exist two DISTINCT positive densities and two positive line-center cross-sections whose
measured thick intensities are EQUAL.

The witness is explicit and exact, not asymptotic. Writing `I(N, σ₀) = P · N · SA(τ)` with
`P` independent of `N` and `τ = σ₀ · ℓ · σ_ℓ(T)|_{σ₀=1} · N`, take
`N₁ = SA(2)`, `N₂ = SA(1)` and choose the two cross-sections so that `τ₁ = 1` and `τ₂ = 2`;
then both intensities equal `P · SA(1) · SA(2)`, and `N₁ ≠ N₂` because `SA` is strictly
antitone (`SelfAbsorption.selfAbsorptionFactor_strictAntiOn`). So the binding relocates the
degree of freedom from `τ` into `σ₀ · ℓ`; it is removed only by a second input — a known
`σ₀ · ℓ` (`thickLineIntensity_injOn`) or a second line
(`thickLineIntensity_ratio_injOn_density`, a flat-kernel result). Unlike the `τ = 0` witness of
`SelfAbsorptionInverse.selfAbsorption_breaks_identifiability`, this witness is reachable by a
state-bound `τ`, so it is the physical form of the single-line alias.

Relation REDUCED (homogeneous single-temperature slab, flat line-center cross-section);
publishes APPROXIMATION via `selfAbsorbedIntensity`. -/
theorem boundOpticalDepth_lumped_alias [Nonempty ι] {kB T Fcal ell : ℝ} {g E A : ι → ℝ}
    (hg : ∀ k, 0 < g k) (hell : 0 < ell) (u l : ι) :
    ∃ N₁ N₂ sigma₁ sigma₂ : ℝ, 0 < N₁ ∧ 0 < N₂ ∧ 0 < sigma₁ ∧ 0 < sigma₂ ∧ N₁ ≠ N₂ ∧
      thickLineIntensity kB T N₁ Fcal sigma₁ ell g E A u l
        = thickLineIntensity kB T N₂ Fcal sigma₂ ell g E A u l := by
  have ha : 0 < effectiveCrossSection kB T 1 g E l * ell :=
    mul_pos (effectiveCrossSection_pos hg one_pos l) hell
  have ha' : effectiveCrossSection kB T 1 g E l * ell ≠ 0 := ha.ne'
  have hq' : effectiveCrossSection kB T 1 g E l ≠ 0 :=
    (effectiveCrossSection_pos hg one_pos l).ne'
  have hell' : ell ≠ 0 := hell.ne'
  have hs1 : (0 : ℝ) < selfAbsorptionFactor 2 := selfAbsorptionFactor_pos (by norm_num)
  have hs2 : (0 : ℝ) < selfAbsorptionFactor 1 := selfAbsorptionFactor_pos zero_le_one
  have hs1' : selfAbsorptionFactor 2 ≠ 0 := hs1.ne'
  have hs2' : selfAbsorptionFactor 1 ≠ 0 := hs2.ne'
  have hlt : selfAbsorptionFactor 2 < selfAbsorptionFactor 1 :=
    selfAbsorptionFactor_strictAntiOn (Set.mem_Ioi.mpr one_pos)
      (Set.mem_Ioi.mpr (by norm_num)) (by norm_num)
  have hlin : ∀ s N : ℝ, opticalDepth kB T N s ell g E l
      = s * (effectiveCrossSection kB T 1 g E l * ell) * N := by
    intro s N
    rw [opticalDepth_eq_linear]
    unfold effectiveCrossSection
    ring
  refine ⟨selfAbsorptionFactor 2, selfAbsorptionFactor 1,
    1 / (effectiveCrossSection kB T 1 g E l * ell * selfAbsorptionFactor 2),
    2 / (effectiveCrossSection kB T 1 g E l * ell * selfAbsorptionFactor 1),
    hs1, hs2, div_pos one_pos (mul_pos ha hs1), div_pos two_pos (mul_pos ha hs2),
    ne_of_lt hlt, ?_⟩
  have hτ1 : opticalDepth kB T (selfAbsorptionFactor 2)
      (1 / (effectiveCrossSection kB T 1 g E l * ell * selfAbsorptionFactor 2))
      ell g E l = 1 := by
    rw [hlin]
    field_simp
  have hτ2 : opticalDepth kB T (selfAbsorptionFactor 1)
      (2 / (effectiveCrossSection kB T 1 g E l * ell * selfAbsorptionFactor 1))
      ell g E l = 2 := by
    rw [hlin]
    field_simp
  unfold thickLineIntensity selfAbsorbedIntensity
  rw [hτ1, hτ2]
  unfold lineIntensity population
  ring

/-! ## Non-vacuity witnesses

Explicit three-level data: `ι = Fin 3`, `g = ![1, 1, 1]`, `E = ![0, 1, 2]`, `A = ![1, 1, 1]`,
`kB = T = Fcal = σ₀ = ℓ = 1`. The two lines share the upper level `2` (a genuine branching
pair) and have DISTINCT lower levels `0` and `1` with `E 0 = 0 < 1 = E 1`, so the opacity
ordering `σ_ℓ(1) < σ_ℓ(0)` is real and the two-line results are not vacuous. -/

/-- Non-vacuity of the opacity ordering: on the explicit data the line with the lower-lying
lower level genuinely has the strictly larger Boltzmann-weighted cross-section, so the side
condition `w₂ < w₁` of the two-line results is satisfiable, not vacuous. -/
example : effectiveCrossSection 1 1 1 ![1, 1, 1] ![0, 1, 2] 1
    < effectiveCrossSection 1 1 1 ![1, 1, 1] ![0, 1, 2] 0 := by
  have hg : ∀ k : Fin 3, (0 : ℝ) < ![1, 1, 1] k := by intro k; fin_cases k <;> norm_num
  exact effectiveCrossSection_lt_of_energy_lt hg one_pos (by norm_num)
    (by norm_num) (by norm_num)

/-- Non-vacuity of the escape-factor law at the bound `τ`: doubling the density on explicit
data STRICTLY decreases the escape factor. Both sides are `(1 − exp(−τ))/τ` at two distinct
positive `τ`, so this is a strict inequality between distinct transcendental values — it
cannot collapse to a tie. -/
example : selfAbsorptionFactor (opticalDepth 1 1 2 1 1 ![1, 1, 1] ![0, 1, 2] 0)
    < selfAbsorptionFactor (opticalDepth 1 1 1 1 1 ![1, 1, 1] ![0, 1, 2] 0) := by
  have hg : ∀ k : Fin 3, (0 : ℝ) < ![1, 1, 1] k := by intro k; fin_cases k <;> norm_num
  exact boundSelfAbsorptionFactor_strictAntiOn_density hg one_pos one_pos 0
    (Set.mem_Ioi.mpr one_pos) (Set.mem_Ioi.mpr (by norm_num)) (by norm_num)

/-- Non-vacuity of the TWO-LINE payoff: on the explicit data the measured ratio of the two
branching lines at density `2` is STRICTLY below its value at density `1`. This exercises the
whole chain — bound `τ`, curve-of-growth kernel, source-ratio prefactor — and the two values
are distinct ratios of transcendentals, not a degenerate tie. -/
example :
    thickLineIntensity 1 1 2 1 1 1 ![1, 1, 1] ![0, 1, 2] ![1, 1, 1] 2 0
        / thickLineIntensity 1 1 2 1 1 1 ![1, 1, 1] ![0, 1, 2] ![1, 1, 1] 2 1
      < thickLineIntensity 1 1 1 1 1 1 ![1, 1, 1] ![0, 1, 2] ![1, 1, 1] 2 0
        / thickLineIntensity 1 1 1 1 1 1 ![1, 1, 1] ![0, 1, 2] ![1, 1, 1] 2 1 := by
  have hg : ∀ k : Fin 3, (0 : ℝ) < ![1, 1, 1] k := by intro k; fin_cases k <;> norm_num
  have hw : effectiveCrossSection 1 1 1 ![1, 1, 1] ![0, 1, 2] 1
      < effectiveCrossSection 1 1 1 ![1, 1, 1] ![0, 1, 2] 0 :=
    effectiveCrossSection_lt_of_energy_lt hg one_pos (by norm_num) (by norm_num) (by norm_num)
  exact thickLineIntensity_ratio_strictAntiOn_density hg one_pos hg one_pos one_pos 2 0 2 1 hw
    (Set.mem_Ioi.mpr one_pos) (Set.mem_Ioi.mpr (by norm_num)) (by norm_num)

/-- Non-vacuity of the NEGATIVE result: on the explicit data the lumped-parameter alias is
inhabited — two distinct positive densities with two positive cross-sections and equal
measured thick intensities really exist. The hypotheses of `boundOpticalDepth_lumped_alias`
are therefore satisfiable, so the honest limitation it records is not vacuous. -/
example : ∃ N₁ N₂ sigma₁ sigma₂ : ℝ, 0 < N₁ ∧ 0 < N₂ ∧ 0 < sigma₁ ∧ 0 < sigma₂ ∧ N₁ ≠ N₂ ∧
    thickLineIntensity 1 1 N₁ 1 sigma₁ 1 ![1, 1, 1] ![0, 1, 2] ![1, 1, 1] 2 0
      = thickLineIntensity 1 1 N₂ 1 sigma₂ 1 ![1, 1, 1] ![0, 1, 2] ![1, 1, 1] 2 0 := by
  have hg : ∀ k : Fin 3, (0 : ℝ) < ![1, 1, 1] k := by intro k; fin_cases k <;> norm_num
  exact boundOpticalDepth_lumped_alias hg one_pos 2 0

end CflibsFormal
