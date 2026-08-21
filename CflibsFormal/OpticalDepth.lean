/-
Copyright (c) 2026 Brian Squires. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Squires
-/
import Mathlib
import CflibsFormal.Alt.CSigmaCurveOfGrowth
import CflibsFormal.Certificates

/-!
# Optical depth bound to the plasma state — closing the free-`τ` gap

Everywhere else in this development the optical depth `τ` is a **free real parameter**:
`SelfAbsorption.selfAbsorptionFactor (tau : ℝ)`, `SelfAbsorption.slabIntensity (S tau : ℝ)`,
`EquivalentWidth.equivWidth φ (τ : ℝ)`, and — tellingly — the runtime certificate
`Certificates.knownTauCert (tau : ℝ) : Prop := 0 ≤ tau`, which merely *asserts* `τ ≥ 0`
because nothing in the corpus derives it. A free `τ` carries no temperature dependence, no
atomic data, and no link to the density it measures.

This module supplies the missing definition. `opticalDepth` binds `τ` to the **lower** level
of the transition, at the **same** `(T, N)` that drives the **upper**-level emission
`ForwardMap.lineIntensity`:

  `τ = σ₀ · ℓ · n_l`,   `n_l = Boltzmann.population kB T N g E l`
    ` = σ₀ · ℓ · N · g_l · exp(−E_l/(k_B T)) / U(T)`.

*Physical reading.* `σ₀` is the line-center absorption cross-section (cm²) of the
bound-bound transition, `ℓ` is the absorbing path length through the homogeneous slab (cm),
and `n_l` is the LTE **lower**-level number density (cm⁻³) — reused verbatim from
`Boltzmann.population`, not re-derived, so `τ` and `lineIntensity` are functions of one and
the same plasma state `(T, N)` with one and the same partition function `U(T)`.

## Why this is the one structurally new channel

Emission is **linear** in `N` (`lineIntensity = Fcal · A_u · n_u ∝ N`). Absorption enters
through `1 − exp(−τ)` with `τ ∝ N`. Coupling the two at a shared `(T, N)` gives the
saturation law (`thickLineIntensity_eq_slab`)

  `I_meas(N) = S · (1 − exp(−τ(N)))`,   `S = I_thin/τ = lteSourceStrength`,

whose prefactor `S` is **independent of `N` and of `U(T)`** — the WIEN-LIMIT LTE line source
function (stimulated emission is NOT modelled; see the scope block below, which quantifies the
gap to Planck). `I_meas` is then STRICTLY INCREASING in `N` (`thickLineIntensity_strictMonoOn`)
and hence INJECTIVE (`thickLineIntensity_injOn`), so the single-line `(N, τ)` alias witnessed
by `SelfAbsorptionInverse.selfAbsorption_breaks_identifiability` **cannot be reproduced once
`τ` is bound to `N`** (`no_density_alias_of_boundOpticalDepth`). The alias there is built from
`τ₁ = 0, τ₂ = 1` at two different densities — impossible here, since `τ = 0` forces `N = 0`.

## What this does NOT prove (read before using)

* **Injectivity presumes `σ₀ · ℓ` is KNOWN**, along with `T` and the atomic data. If instead
  `σ₀ · ℓ` is an unknown lumped parameter `a`, then `I_meas = (c/a)·(1 − exp(−a·N))` has two
  unknowns in one equation and the `(N, τ)` alias **reappears inside the lumped parameter** —
  exactly the failure pattern documented in `docs/2dcos/ERRATA.md`. Without a known `σ₀ · ℓ`,
  the alias is broken only by a SECOND observable (a second line of different width:
  `CurveOfGrowth.cogRatio_injOn`, certificate `Certificates.saDistinctCert`). This module does
  NOT repeal `selfAbsorption_breaks_identifiability`; it identifies the extra input under
  which that theorem's witness is unreachable.
* **`opticalDepth` is NOT claimed monotone in `T`.** The partition function `U(T)` redistributes
  population, so no monotone `T`-law holds for `τ` alone at fixed `N`. The clean temperature law
  is the RATIO `τ / I_thin`, which is `N`-free and `U`-free
  (`opticalDepth_div_lineIntensity`) and strictly ANTITONE in `T` whenever `E_l < E_u`
  (`opticalDepth_div_lineIntensity_strictAntiOn_temperature`): a hotter plasma self-absorbs
  less, relative to what it emits.
* **Joint `(T, N)` recovery from ONE line is still dead.** `thickLineIntensity_injOn` is
  injectivity in `N` at FIXED, KNOWN `T`; `T` still has to come from ≥ 2 lines (the Boltzmann
  plot, `ForwardMap.temperature_from_two_lines`).
* **Composition-level non-identifiability is untouched.** With per-species unknown `τ`,
  `SelfAbsorptionInverse.selfAbsorption_breaks_composition_identifiability` still stands.

## Literature and scope

REDUCED — a homogeneous, single-temperature slab with a flat (line-center) absorption
cross-section and LTE level populations. The frequency-dependent profile `τ(ν)`, the Voigt
core/wing structure, the profile-integrated slope-½ curve of growth, spatial gradients, and
self-reversal are all OUT OF SCOPE (see `EquivalentWidth`, `SelfReversal`,
`RadiativeTransferDepth` for those directions).

**Stimulated emission is NOT modelled.** The full LTE line absorption coefficient carries the
negative-absorption correction `1 − exp(−(E_u − E_l)/(k_B T))`; `opticalDepth` omits it. Two
consequences, stated so they cannot be read past: (i) the `τ` defined here OVERSTATES the true
LTE optical depth by exactly that factor; (ii) `S = I_thin/τ` is therefore the WIEN limit
`∝ exp(−(E_u − E_l)/(k_B T))` of the line source function, not the Planck function itself. For
visible LIBS lines (`E_u − E_l ≈ 2.5 eV`, `k_B T ≈ 1 eV`) the omitted factor is ≈ 0.92.
Each result below is an exact statement about the DEFINED `opticalDepth`; this paragraph
records how far that definition sits from the full LTE absorption coefficient.

* Gornushkin, Anzano, King, Smith, Omenetto, Winefordner, "Curve of growth methodology applied
  to laser-induced plasma emission spectroscopy", *Spectrochim. Acta Part B* **54** (1999)
  491–503 — the homogeneous-slab emission `I = S·(1 − exp(−τ))` with `τ = σ ℓ n` built from the
  LTE lower-level density, and the source function `S` as the `N`-free prefactor.
* Aragón & Aguilera, "Direct and inverse models… the Cσ method", *J. Quant. Spectrosc. Radiat.
  Transfer* **149** (2014) 90 — the abscissa `C σ_ℓ ∝ τ = N σ_ℓ ℓ` whose free `σ_ℓ` is
  instantiated here by the Boltzmann-weighted `effectiveCrossSection`.
-/

namespace CflibsFormal

open Finset Real
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-! ## The definition -/

/-- **Line optical depth of a homogeneous LTE slab**, bound to the plasma state:
  `τ = σ₀ · ℓ · n_l`,
with `n_l = Boltzmann.population kB T N g E l` the LTE **lower**-level number density at the
SAME temperature `T` and total density `N` that drive the upper-level emission
`ForwardMap.lineIntensity`. Here `σ₀` is the line-center absorption cross-section and `ℓ` the
absorbing path length. Expanding `population`,
  `τ = σ₀ · ℓ · N · g_l · exp(−E_l/(k_B T)) / U(T)`,
so `τ` carries the temperature dependence, the atomic data `(g_l, E_l)`, and the density `N`
that the free-parameter `tau` of `SelfAbsorption` / `EquivalentWidth` / `knownTauCert` did not.

REDUCED: homogeneous single-temperature slab, flat line-center cross-section; the
frequency-resolved `τ(ν)` is out of scope. -/
noncomputable def opticalDepth (kB T N sigma0 ell : ℝ) (g E : ι → ℝ) (l : ι) : ℝ :=
  sigma0 * ell * population kB T N g E l

/-- **Boltzmann-weighted line cross-section** `σ_ℓ(T) = σ₀ · g_l · exp(−E_l/(k_B T)) / U(T)`:
the line-center cross-section reduced by the LTE *fraction* of the species sitting in the
lower level. This is the quantity that plays the role of the free `σ_ℓ` in the Aragón–Aguilera
Cσ abscissa `τ = N σ_ℓ ℓ` (`Alt.csigmaOpticalDepth`); see `opticalDepth_eq_csigma`. -/
noncomputable def effectiveCrossSection (kB T sigma0 : ℝ) (g E : ι → ℝ) (l : ι) : ℝ :=
  sigma0 * g l * boltzmannFactor kB T (E l) / partitionFunction kB T g E

/-- **LTE line source strength** `S = I_thin / τ`, written out in closed form:
  `S = Fcal · A_u · g_u · exp(−E_u/(k_B T)) / (σ₀ · ℓ · g_l · exp(−E_l/(k_B T)))`.
Both the total density `N` and the partition function `U(T)` cancel — `S` depends only on
`T`, the atomic data of the two levels, and the known constants `Fcal, σ₀, ℓ`. This is the
frequency-integrated, WIEN-LIMIT analogue of the LTE source function (stimulated emission is
not modelled — see the module scope block); it is the `N`-free plateau that the saturated line
approaches. -/
noncomputable def lteSourceStrength (kB T Fcal sigma0 ell : ℝ) (g E A : ι → ℝ)
    (u l : ι) : ℝ :=
  Fcal * A u * g u * boltzmannFactor kB T (E u) /
    (sigma0 * ell * (g l * boltzmannFactor kB T (E l)))

/-- **State-coupled thick line intensity.** The measured (self-absorbed) intensity of the
line with upper level `u` and lower level `l`, with the optical depth NO LONGER FREE: it is
`opticalDepth` at the same `(T, N)`. This is the forward map of the absorption channel. -/
noncomputable def thickLineIntensity (kB T N Fcal sigma0 ell : ℝ) (g E A : ι → ℝ)
    (u l : ι) : ℝ :=
  selfAbsorbedIntensity kB T N Fcal g E A u (opticalDepth kB T N sigma0 ell g E l)

/-! ## Algebraic normal forms -/

/-- `τ` is exactly linear in the total density: `τ = (σ_ℓ(T) · ℓ) · N`. Pure algebra —
`population` is linear in `N`. -/
theorem opticalDepth_eq_linear (kB T N sigma0 ell : ℝ) (g E : ι → ℝ) (l : ι) :
    opticalDepth kB T N sigma0 ell g E l
      = effectiveCrossSection kB T sigma0 g E l * ell * N := by
  unfold opticalDepth effectiveCrossSection population
  ring

/-- **Bridge to the Cσ abscissa.** The state-bound `opticalDepth` IS the Aragón–Aguilera
Cσ optical depth `τ = σ_ℓ · ℓ · C` with the free cross-section instantiated to the
Boltzmann-weighted `effectiveCrossSection` and the column scale `C` to the density `N`. This
is what lets the already-proven curve-of-growth droop theorems be re-read as statements about
a physically bound `τ` (`csigma_density_droop_bound`). Pure algebra. -/
theorem opticalDepth_eq_csigma (kB T N sigma0 ell : ℝ) (g E : ι → ℝ) (l : ι) :
    opticalDepth kB T N sigma0 ell g E l
      = Alt.csigmaOpticalDepth (effectiveCrossSection kB T sigma0 g E l) ell N := by
  unfold opticalDepth effectiveCrossSection population Alt.csigmaOpticalDepth
  ring

/-- The Boltzmann-weighted cross-section is positive: a positive line-center cross-section
times a positive LTE lower-level fraction. -/
theorem effectiveCrossSection_pos [Nonempty ι] {kB T sigma0 : ℝ} {g E : ι → ℝ}
    (hg : ∀ k, 0 < g k) (hsig : 0 < sigma0) (l : ι) :
    0 < effectiveCrossSection kB T sigma0 g E l := by
  unfold effectiveCrossSection
  exact div_pos (mul_pos (mul_pos hsig (hg l)) (boltzmannFactor_pos _ _ _))
    (partitionFunction_pos hg)

omit [Fintype ι] in
/-- The LTE line source strength is positive given positive calibration, atomic data,
cross-section and path length. -/
theorem lteSourceStrength_pos {kB T Fcal sigma0 ell : ℝ} {g E A : ι → ℝ}
    (hg : ∀ k, 0 < g k) (hFcal : 0 < Fcal) (hA : ∀ k, 0 < A k) (hsig : 0 < sigma0)
    (hell : 0 < ell) (u l : ι) :
    0 < lteSourceStrength kB T Fcal sigma0 ell g E A u l := by
  unfold lteSourceStrength
  exact div_pos (mul_pos (mul_pos (mul_pos hFcal (hA u)) (hg u)) (boltzmannFactor_pos _ _ _))
    (mul_pos (mul_pos hsig hell) (mul_pos (hg l) (boltzmannFactor_pos _ _ _)))

/-! ## The basic laws: positivity, monotonicity in `N`, the temperature law -/

/-- **Positivity, DERIVED.** For a physical state (`N > 0`, positive degeneracies, positive
cross-section and path length) the optical depth is strictly positive. Contrast
`Certificates.knownTauCert`, which merely *asserts* `0 ≤ τ`: here `τ ≥ 0` is a consequence of
the state, not an assumption about it.

REDUCED: homogeneous single-temperature slab, flat line-center cross-section. -/
theorem opticalDepth_pos [Nonempty ι] {kB T N sigma0 ell : ℝ} {g E : ι → ℝ}
    (hg : ∀ k, 0 < g k) (hN : 0 < N) (hsig : 0 < sigma0) (hell : 0 < ell) (l : ι) :
    0 < opticalDepth kB T N sigma0 ell g E l := by
  rw [opticalDepth_eq_linear]
  exact mul_pos (mul_pos (effectiveCrossSection_pos hg hsig l) hell) hN

/-- **The C12 certificate is now discharged from physics, not assumed.** A physical state
with `N ≥ 0` produces an optical depth satisfying `Certificates.knownTauCert`. This closes the
gap flagged in the module docstring: the pipeline's `0 ≤ τ` obligation follows from the
Boltzmann state rather than being posited.

REDUCED: homogeneous single-temperature slab, flat line-center cross-section. -/
theorem opticalDepth_knownTauCert [Nonempty ι] {kB T N sigma0 ell : ℝ} {g E : ι → ℝ}
    (hg : ∀ k, 0 < g k) (hN : 0 ≤ N) (hsig : 0 < sigma0) (hell : 0 < ell) (l : ι) :
    knownTauCert (opticalDepth kB T N sigma0 ell g E l) := by
  have h : 0 ≤ opticalDepth kB T N sigma0 ell g E l := by
    rw [opticalDepth_eq_linear]
    exact mul_nonneg (mul_pos (effectiveCrossSection_pos hg hsig l) hell).le hN
  exact h

/-- **Strict monotonicity in density.** More absorbers on the line of sight means strictly
more optical depth: `N ↦ τ(N)` is strictly increasing (on all of `ℝ`; `τ` is linear in `N`
with positive slope `σ_ℓ(T) · ℓ`). This is the mechanism that makes the absorption channel
informative about `N`.

REDUCED: homogeneous single-temperature slab, flat line-center cross-section. -/
theorem opticalDepth_strictMono_density [Nonempty ι] {kB T sigma0 ell : ℝ} {g E : ι → ℝ}
    (hg : ∀ k, 0 < g k) (hsig : 0 < sigma0) (hell : 0 < ell) (l : ι) :
    StrictMono (fun N => opticalDepth kB T N sigma0 ell g E l) := by
  intro a b hab
  simp only [opticalDepth_eq_linear]
  exact mul_lt_mul_of_pos_left hab
    (mul_pos (effectiveCrossSection_pos hg hsig l) hell)

/-- **Emission = source × optical depth.** The optically-thin upper-level emission factors
EXACTLY as `I_thin = S · τ`, where `S = lteSourceStrength` contains no `N` and no `U(T)`.
Holds for every `N` (no positivity needed): both sides are linear in `N`, and the partition
function cancels between the upper-level population and the lower-level column. This single
identity is the algebraic hinge of the module — the two ratio laws below are read off it.

REDUCED: homogeneous single-temperature slab, flat line-center cross-section. -/
theorem lineIntensity_eq_source_mul_opticalDepth [Nonempty ι]
    {kB T N Fcal sigma0 ell : ℝ} {g E A : ι → ℝ} (hg : ∀ k, 0 < g k) (hsig : 0 < sigma0)
    (hell : 0 < ell) (u l : ι) :
    lineIntensity kB T N Fcal g E A u
      = lteSourceStrength kB T Fcal sigma0 ell g E A u l
        * opticalDepth kB T N sigma0 ell g E l := by
  have hU : partitionFunction kB T g E ≠ 0 := (partitionFunction_pos hg).ne'
  have hbl : boltzmannFactor kB T (E l) ≠ 0 := (boltzmannFactor_pos kB T (E l)).ne'
  have hgl : g l ≠ 0 := (hg l).ne'
  have hs : sigma0 ≠ 0 := hsig.ne'
  have he : ell ≠ 0 := hell.ne'
  unfold lineIntensity lteSourceStrength opticalDepth population
  field_simp

/-- **The source strength is the measured ratio `I_thin / τ`.** Dividing the thin emission by
the state-bound optical depth returns a quantity free of `N` and of `U(T)`.

REDUCED: homogeneous single-temperature slab, flat line-center cross-section. -/
theorem lineIntensity_div_opticalDepth [Nonempty ι] {kB T N Fcal sigma0 ell : ℝ}
    {g E A : ι → ℝ} (hg : ∀ k, 0 < g k) (hN : 0 < N) (hsig : 0 < sigma0) (hell : 0 < ell)
    (u l : ι) :
    lineIntensity kB T N Fcal g E A u / opticalDepth kB T N sigma0 ell g E l
      = lteSourceStrength kB T Fcal sigma0 ell g E A u l := by
  have hτ : 0 < opticalDepth kB T N sigma0 ell g E l := opticalDepth_pos hg hN hsig hell l
  rw [lineIntensity_eq_source_mul_opticalDepth hg hsig hell u l,
    mul_div_cancel_right₀ _ hτ.ne']

/-- **The temperature law of the absorption channel.** The ratio of optical depth to thin
emission is
  `τ / I_thin = (σ₀ ℓ g_l)/(Fcal A_u g_u) · exp((E_u − E_l)/(k_B T))`,
in which the total density `N` and the partition function `U(T)` have cancelled COMPLETELY.
So `τ/I` is a function of `T` and known constants alone — a second, structurally different
equation on the same state than the Boltzmann plot supplies.

REDUCED: homogeneous single-temperature slab, flat line-center cross-section. -/
theorem opticalDepth_div_lineIntensity [Nonempty ι] {kB T N Fcal sigma0 ell : ℝ}
    {g E A : ι → ℝ} (hg : ∀ k, 0 < g k) (hN : 0 < N) (hFcal : 0 < Fcal) (hA : ∀ k, 0 < A k)
    (hsig : 0 < sigma0) (hell : 0 < ell) (u l : ι) :
    opticalDepth kB T N sigma0 ell g E l / lineIntensity kB T N Fcal g E A u
      = sigma0 * ell * g l / (Fcal * A u * g u) * Real.exp ((E u - E l) / (kB * T)) := by
  have hI : 0 < lineIntensity kB T N Fcal g E A u := lineIntensity_pos hg hN hFcal hA u
  have hU : partitionFunction kB T g E ≠ 0 := (partitionFunction_pos hg).ne'
  have hgu : g u ≠ 0 := (hg u).ne'
  have hAu : A u ≠ 0 := (hA u).ne'
  have hF : Fcal ≠ 0 := hFcal.ne'
  have hNe : N ≠ 0 := hN.ne'
  have hbf : boltzmannFactor kB T (E l)
      = Real.exp ((E u - E l) / (kB * T)) * boltzmannFactor kB T (E u) := by
    unfold boltzmannFactor
    rw [← Real.exp_add]
    congr 1
    ring
  rw [div_eq_iff hI.ne']
  unfold opticalDepth lineIntensity population
  rw [hbf]
  field_simp

/-- **Hotter plasmas self-absorb less, relative to what they emit.** For a genuine
bound-bound transition (`E_l < E_u`) and `k_B > 0`, the ratio `τ / I_thin` is STRICTLY
ANTITONE in `T` on `(0, ∞)`. Proof: the ratio identity above turns the claim into strict
antitonicity of `T ↦ exp((E_u − E_l)/(k_B T))`, i.e. of `T ↦ (E_u − E_l)/(k_B T)`.

Note the careful statement: `opticalDepth` itself is NOT monotone in `T` (the partition
function `U(T)` redistributes population), so the temperature content of the absorption
channel lives in this ratio, not in `τ` alone.

REDUCED: homogeneous single-temperature slab, flat line-center cross-section. -/
theorem opticalDepth_div_lineIntensity_strictAntiOn_temperature [Nonempty ι]
    {kB N Fcal sigma0 ell : ℝ} {g E A : ι → ℝ} (hg : ∀ k, 0 < g k) (hN : 0 < N)
    (hFcal : 0 < Fcal) (hA : ∀ k, 0 < A k) (hsig : 0 < sigma0) (hell : 0 < ell)
    (hkB : 0 < kB) (u l : ι) (hE : E l < E u) :
    StrictAntiOn
      (fun T => opticalDepth kB T N sigma0 ell g E l / lineIntensity kB T N Fcal g E A u)
      (Set.Ioi 0) := by
  intro Ta hTa Tb _ hab
  have hTa0 : (0 : ℝ) < Ta := Set.mem_Ioi.mp hTa
  simp only [opticalDepth_div_lineIntensity hg hN hFcal hA hsig hell u l]
  have hcoef : 0 < sigma0 * ell * g l / (Fcal * A u * g u) :=
    div_pos (mul_pos (mul_pos hsig hell) (hg l))
      (mul_pos (mul_pos hFcal (hA u)) (hg u))
  refine mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr ?_) hcoef
  exact div_lt_div_of_pos_left (by linarith) (mul_pos hkB hTa0)
    (mul_lt_mul_of_pos_left hab hkB)

/-! ## The payoff: the absorption channel becomes injective in `N` -/

/-- **Saturation law.** With `τ` bound to the same `(T, N)`, the measured thick intensity is
EXACTLY the radiative-transfer slab solution with the `N`-free source strength:
  `I_meas(N) = S · (1 − exp(−τ(N)))`,   `S = lteSourceStrength`.
The linear-in-`N` emission and the `1 − exp(−τ)` absorption combine into a single bounded,
strictly increasing function of `N`. Routes through the EXACT slab identity
`SelfAbsorption.selfAbsorbedIntensity_eq_slab`, so nothing here is definitional sleight of
hand: `slabIntensity` is built from `exp`, independently of `selfAbsorptionFactor`.

REDUCED: homogeneous single-temperature slab, flat line-center cross-section. -/
theorem thickLineIntensity_eq_slab [Nonempty ι] {kB T N Fcal sigma0 ell : ℝ}
    {g E A : ι → ℝ} (hg : ∀ k, 0 < g k) (hN : 0 < N) (hsig : 0 < sigma0) (hell : 0 < ell)
    (u l : ι) :
    thickLineIntensity kB T N Fcal sigma0 ell g E A u l
      = slabIntensity (lteSourceStrength kB T Fcal sigma0 ell g E A u l)
          (opticalDepth kB T N sigma0 ell g E l) := by
  have hτ : 0 < opticalDepth kB T N sigma0 ell g E l := opticalDepth_pos hg hN hsig hell l
  unfold thickLineIntensity
  rw [selfAbsorbedIntensity_eq_slab u hτ, lineIntensity_div_opticalDepth hg hN hsig hell u l]

/-- **The absorption channel is strictly monotone in density.** Once `τ` is bound to `N`,
the MEASURED (self-absorbed) intensity is STRICTLY INCREASING in `N` on `(0, ∞)`. Neither
factor gives this on its own: the thin intensity is linear in `N` but the escape factor
`SA(τ(N))` is strictly *decreasing* in `N`; their product `S·(1 − exp(−τ(N)))` is strictly
increasing because the source strength `S` is `N`-free.

REDUCED: homogeneous single-temperature slab, flat line-center cross-section. -/
theorem thickLineIntensity_strictMonoOn [Nonempty ι] {kB T Fcal sigma0 ell : ℝ}
    {g E A : ι → ℝ} (hg : ∀ k, 0 < g k) (hFcal : 0 < Fcal) (hA : ∀ k, 0 < A k)
    (hsig : 0 < sigma0) (hell : 0 < ell) (u l : ι) :
    StrictMonoOn (fun N => thickLineIntensity kB T N Fcal sigma0 ell g E A u l)
      (Set.Ioi 0) := by
  intro Na hNa Nb hNb hab
  have hNa0 : (0 : ℝ) < Na := Set.mem_Ioi.mp hNa
  have hNb0 : (0 : ℝ) < Nb := Set.mem_Ioi.mp hNb
  have hS : 0 < lteSourceStrength kB T Fcal sigma0 ell g E A u l :=
    lteSourceStrength_pos hg hFcal hA hsig hell u l
  have hτ : opticalDepth kB T Na sigma0 ell g E l < opticalDepth kB T Nb sigma0 ell g E l :=
    opticalDepth_strictMono_density hg hsig hell l hab
  have hexp : Real.exp (-opticalDepth kB T Nb sigma0 ell g E l)
      < Real.exp (-opticalDepth kB T Na sigma0 ell g E l) :=
    Real.exp_lt_exp.mpr (by linarith)
  simp only [thickLineIntensity_eq_slab hg hNa0 hsig hell u l,
    thickLineIntensity_eq_slab hg hNb0 hsig hell u l, slabIntensity]
  exact mul_lt_mul_of_pos_left (by linarith) hS

/-- **THE PAYOFF — the absorption channel identifies the density.** With `τ` bound to the
plasma state, the map `N ↦ I_meas(N)` is INJECTIVE on `(0, ∞)`: two physical densities that
produce the same measured thick intensity are equal. Immediate from
`thickLineIntensity_strictMonoOn` via `StrictMonoOn.injOn`.

SCOPE — the hypotheses are the whole story: `T`, the atomic data `(g, E, A)`, the calibration
`Fcal`, AND the product `σ₀ · ℓ` must all be known. If `σ₀ · ℓ` is an unknown lumped parameter
the `(N, τ)` alias reappears inside it; see the module docstring.

REDUCED: homogeneous single-temperature slab, flat line-center cross-section. -/
theorem thickLineIntensity_injOn [Nonempty ι] {kB T Fcal sigma0 ell : ℝ}
    {g E A : ι → ℝ} (hg : ∀ k, 0 < g k) (hFcal : 0 < Fcal) (hA : ∀ k, 0 < A k)
    (hsig : 0 < sigma0) (hell : 0 < ell) (u l : ι) :
    Set.InjOn (fun N => thickLineIntensity kB T N Fcal sigma0 ell g E A u l) (Set.Ioi 0) :=
  (thickLineIntensity_strictMonoOn hg hFcal hA hsig hell u l).injOn

/-- **The single-line density alias cannot be reproduced.** Stated in exactly the shape of
`SelfAbsorptionInverse.selfAbsorption_breaks_identifiability` — which exhibits `N₁ ≠ N₂` with
equal measured intensities at FREE optical depths `τ₁ = 0`, `τ₂ = 1` — and negated: no such
pair exists once each `τ` is the `opticalDepth` of its own density. The witness there is
unreachable here because `τ = 0` forces `N = 0`, outside the physical domain.

This does NOT contradict that theorem: it identifies the extra input (a known `σ₀ · ℓ` at a
known `T`) that removes its degree of freedom. Without that input the alias returns inside the
lumped parameter, and the honest remedy stays a second observable
(`CurveOfGrowth.cogRatio_injOn`).

REDUCED: homogeneous single-temperature slab, flat line-center cross-section. -/
theorem no_density_alias_of_boundOpticalDepth [Nonempty ι] {kB T Fcal sigma0 ell : ℝ}
    {g E A : ι → ℝ} (hg : ∀ k, 0 < g k) (hFcal : 0 < Fcal) (hA : ∀ k, 0 < A k)
    (hsig : 0 < sigma0) (hell : 0 < ell) (u l : ι) :
    ¬ ∃ N₁ N₂ : ℝ, 0 < N₁ ∧ 0 < N₂ ∧ N₁ ≠ N₂ ∧
      thickLineIntensity kB T N₁ Fcal sigma0 ell g E A u l
        = thickLineIntensity kB T N₂ Fcal sigma0 ell g E A u l := by
  rintro ⟨N₁, N₂, h1, h2, hne, heq⟩
  exact hne (thickLineIntensity_injOn hg hFcal hA hsig hell u l
    (Set.mem_Ioi.mpr h1) (Set.mem_Ioi.mpr h2) heq)

/-! ## The Cσ curve of growth, re-read at a physically bound `τ` -/

/-- **The Cσ density droop at a STATE-BOUND optical depth.** `Alt.csigma_curve_of_growth_
density_droop` proves strict antitonicity in `N` for the free-cross-section abscissa
`τ = σ_ℓ ℓ N` with `σ_ℓ` an arbitrary positive real. Instantiating `σ_ℓ` by the
Boltzmann-weighted `effectiveCrossSection` (legal: it is positive) and transporting along
`opticalDepth_eq_csigma` re-reads that theorem for the `τ` derived here — the droop is now
driven by the actual LTE lower-level population, not by a free parameter.

APPROXIMATION (inherited): the escape factor `SA(τ) = (1 − exp(−τ))/τ` is the flat-profile
reduction of the Aragón–Aguilera curve of growth; the profile-integrated slope-½ Lorentz wing
is out of scope. -/
theorem csigma_density_droop_bound [Nonempty ι] {kB T Fcal sigma0 ell : ℝ} {g E A : ι → ℝ}
    (hg : ∀ k, 0 < g k) (hFcal : 0 < Fcal) (hA : ∀ k, 0 < A k) (hsig : 0 < sigma0)
    (hell : 0 < ell) (u l : ι) :
    StrictAntiOn
      (fun N => Alt.csigmaSelfAbsorbedUniversalOrdinate kB T N Fcal g E A u
        (opticalDepth kB T N sigma0 ell g E l)) (Set.Ioi 0) := by
  have h := Alt.csigma_curve_of_growth_density_droop
    (kB := kB) (T := T) (Fcal := Fcal) (E := E)
    (sigmaL := effectiveCrossSection kB T sigma0 g E l) (ell := ell) hg hFcal hA
    (effectiveCrossSection_pos hg hsig l) hell u
  refine h.congr ?_
  intro N _
  simp only [opticalDepth_eq_csigma]

/-- **Injectivity of the Cσ ordinate in the density**, at a state-bound `τ`. Note the honest
reading: this ordinate is `log(I_meas/(g_u A_u)) − log(N/U)`, i.e. an observable MINUS a
normalization that itself involves `N`, so it is a statement about the Cσ construction rather
than a directly usable single-observable inversion. The directly usable one is
`thickLineIntensity_injOn`.

APPROXIMATION (inherited): flat-profile escape-factor reduction of the Aragón–Aguilera curve
of growth; the profile-integrated slope-½ Lorentz wing is out of scope. -/
theorem csigma_density_injOn [Nonempty ι] {kB T Fcal sigma0 ell : ℝ} {g E A : ι → ℝ}
    (hg : ∀ k, 0 < g k) (hFcal : 0 < Fcal) (hA : ∀ k, 0 < A k) (hsig : 0 < sigma0)
    (hell : 0 < ell) (u l : ι) :
    Set.InjOn
      (fun N => Alt.csigmaSelfAbsorbedUniversalOrdinate kB T N Fcal g E A u
        (opticalDepth kB T N sigma0 ell g E l)) (Set.Ioi 0) :=
  (csigma_density_droop_bound hg hFcal hA hsig hell u l).injOn

/-! ## Non-vacuity witnesses

Explicit two-level data: `ι = Fin 2`, `g = ![1, 1]`, `E = ![0, 1]` (lower level `0`, upper
level `1`, so `E 0 < E 1` genuinely), `A = ![1, 1]`, `kB = T = Fcal = σ₀ = ℓ = 1`. -/

/-- Non-vacuity: on explicit data the derived optical depth is strictly positive — the
`0 ≤ τ` obligation of `knownTauCert` is met by a state, not by fiat. -/
example : (0 : ℝ) < opticalDepth 1 1 2 1 1 ![1, 1] ![0, 1] 0 := by
  have hg : ∀ k : Fin 2, (0 : ℝ) < ![1, 1] k := by intro k; fin_cases k <;> norm_num
  exact opticalDepth_pos hg (by norm_num) one_pos one_pos 0

/-- Non-vacuity: on explicit data doubling the density STRICTLY increases the measured,
self-absorbed intensity. This is a genuine strict inequality between two distinct
transcendental values — not a degenerate `0 ≤ 0`. -/
example :
    thickLineIntensity 1 1 1 1 1 1 ![1, 1] ![0, 1] ![1, 1] 1 0
      < thickLineIntensity 1 1 2 1 1 1 ![1, 1] ![0, 1] ![1, 1] 1 0 := by
  have hg : ∀ k : Fin 2, (0 : ℝ) < ![1, 1] k := by intro k; fin_cases k <;> norm_num
  exact thickLineIntensity_strictMonoOn hg one_pos hg one_pos one_pos 1 0
    (Set.mem_Ioi.mpr one_pos) (Set.mem_Ioi.mpr (by norm_num)) (by norm_num)

/-- Non-vacuity of the TEMPERATURE law: the side conditions `0 < k_B` and `E l < E u` are
jointly satisfiable on the explicit data (`E 0 = 0 < 1 = E 1`), and doubling `T` from `1` to `2`
STRICTLY lowers the ratio `τ / I_thin` — the two values are `exp 1` and `exp (1/2)`, distinct
transcendentals, so this cannot collapse to a tie. -/
example :
    opticalDepth 1 2 1 1 1 ![1, 1] ![0, 1] 0
        / lineIntensity 1 2 1 1 ![1, 1] ![0, 1] ![1, 1] 1
      < opticalDepth 1 1 1 1 1 ![1, 1] ![0, 1] 0
        / lineIntensity 1 1 1 1 ![1, 1] ![0, 1] ![1, 1] 1 := by
  have hg : ∀ k : Fin 2, (0 : ℝ) < ![1, 1] k := by intro k; fin_cases k <;> norm_num
  exact opticalDepth_div_lineIntensity_strictAntiOn_temperature hg one_pos one_pos hg
    one_pos one_pos one_pos 1 0 (by norm_num) (Set.mem_Ioi.mpr one_pos)
    (Set.mem_Ioi.mpr (by norm_num)) (by norm_num)

/-- Non-vacuity of the payoff: on explicit data, equal measured thick intensities force equal
densities — the `(N, τ)` alias is gone. -/
example {N₁ N₂ : ℝ} (h1 : 0 < N₁) (h2 : 0 < N₂)
    (hobs : thickLineIntensity 1 1 N₁ 1 1 1 ![1, 1] ![0, 1] ![1, 1] 1 0
      = thickLineIntensity 1 1 N₂ 1 1 1 ![1, 1] ![0, 1] ![1, 1] 1 0) : N₁ = N₂ := by
  have hg : ∀ k : Fin 2, (0 : ℝ) < ![1, 1] k := by intro k; fin_cases k <;> norm_num
  exact thickLineIntensity_injOn hg one_pos hg one_pos one_pos 1 0
    (Set.mem_Ioi.mpr h1) (Set.mem_Ioi.mpr h2) hobs

end CflibsFormal
