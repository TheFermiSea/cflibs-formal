/-
Copyright (c) 2026 Brian Squires. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Squires
-/
import Mathlib
import CflibsFormal.Alt.CSigma
import CflibsFormal.SelfAbsorption

/-!
# The Cσ curve of growth — self-absorption droop below the universal line

`CSigma.lean` builds the optically-thin **Cσ universal line**: after the
concentration/partition normalization `ln(N_s/U_s(T))`, every line of every element (and,
with the Saha shift, every stage) collapses onto ONE line `Y = ln F − E_k/(k_B T)`
(`csigma_universal_line`). That construction is purely optically thin.

This module adds the **self-absorption droop**. At finite optical depth `τ` the measured
line is dimmed by the curve-of-growth escape factor `SA(τ) = (1 − exp(−τ))/τ ∈ (0, 1]`
(`SelfAbsorption.selfAbsorptionFactor`), so the concentration-normalized **measured**
ordinate sits BELOW the universal line by exactly `ln SA(τ)`. The optical depth carries
the genuine **σ (cross-section) weighting** of the Aragón–Aguilera Cσ graph,
`τ = N · σ_ℓ · ℓ` (`csigmaOpticalDepth`): `σ_ℓ` is the profile-averaged line cross-section
and `N` the species number density. So the droop is strictly monotone (deeper) in `τ`,
hence in `N` — the optically-thick lines bend down off the universal line.

**Note on "σ".** In `csigmaConcentrationLog`/`csigmaUniversalOrdinate` the subtracted
`ln(N_s/U_s)` is the *concentration/partition* normalization, NOT a cross-section; the loose
"σ-normalization" wording elsewhere refers to that collapse. The genuine cross-section `σ_ℓ`
enters only here, through the optical depth `τ = N σ_ℓ ℓ` of `csigmaOpticalDepth`.

**What is and is not proved (honest scope).** The headline droop identity
(`csigma_curve_of_growth_droop`) is a legitimate but mathematically shallow BRIDGE
(`csigma_universal_line` + `Real.log_mul`): it pins the droop magnitude as exactly `ln SA(τ)`
and shows the concentration normalization `ln(N/U)` cancels. The genuinely NEW analytic
content is `selfAbsorptionFactor_strictAntiOn` (a derivative argument absent from the repo),
together with the strict droop `csigma_curve_of_growth_lt` and the shape theorems
`csigma_curve_of_growth_strictAntiOn` / `csigma_curve_of_growth_density_droop`.

**REDUCED model.** `SA(τ) = (1 − exp(−τ))/τ` is the line-center / flat-profile ESCAPE FACTOR
inherited from the radiative-transfer slab kernel `SelfAbsorption.slabIntensity`. It is NOT
the full profile-integrated Aragón–Aguilera curve of growth: the slope-1 → slope-½
Lorentz-wing knee (IntechOpen Eqs. 29–31, the `√x` asymptote) is OUT OF SCOPE, as are the
Voigt `τ(ν)`, inversion of `(C, σ_ℓ)` from a measured curve, and multi-element pooled fits.
Each curve-of-growth-shape theorem below repeats this qualifier.

## Literature

* Aragón & Aguilera, "Direct and inverse models to obtain the spatial distribution of
  electron density and temperature… the Cσ method", *J. Quant. Spectrosc. Radiat. Transfer*
  **149** (2014) 90 — the Cσ graph, the line cross-section `σ_ℓ` and the abscissa
  `Cσ_ℓ ∝ τ = N σ_ℓ ℓ`.
* Aguilera & Aragón, "Multi-element Saha–Boltzmann and Boltzmann plots in laser-induced
  plasmas", *Spectrochim. Acta Part B* **62** (2007) 378 — the optically-thin universal /
  master line, recovered here as the `τ → 0⁺` asymptote.
* Aragón & Aguilera, "Optically Thick Laser-Induced Plasmas in Spectroscopic Analysis",
  IntechOpen — the `(1 − exp(−τ))` self-absorption factor (Eqs. 19/20) and the
  profile-integrated slope-½ wing (Eqs. 29–31) that is explicitly OUT OF SCOPE here.
* Gornushkin, Stevenson, Smith, Omenetto, Winefordner, "Curve of growth methodology applied
  to laser-induced plasma emission", *Spectrochim. Acta Part B* **54** (1999) 491 — the slab
  emission `I = S·(1 − exp(−τ))` underlying `SelfAbsorption.slabIntensity`.
-/

namespace CflibsFormal.Alt

open CflibsFormal
open Finset Real
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- **Cσ optical depth** `τ = σ_ℓ · ℓ · C`: the line cross-section `σ_ℓ`, the absorption path
length `ℓ`, and the absorber column scale `C` (the species number density `N` along the line
of sight). This is the genuine **cross-section weighting** of the Aragón–Aguilera Cσ graph
(JQSRT 149 (2014) 90): the abscissa `Cσ_ℓ` is proportional to `τ`, and it is `σ_ℓ` — not the
`ln(N/U)` normalization — that is the line cross-section. -/
noncomputable def csigmaOpticalDepth (sigmaL ell C : ℝ) : ℝ :=
  sigmaL * ell * C

/-- **Self-absorbed Cσ universal ordinate.** The concentration-normalized ordinate of a
*measured* (optically-thick) line: `ln(I_meas/(g_k A_k)) − ln(N_s/U_s(T))`, where
`I_meas = selfAbsorbedIntensity … = lineIntensity · SA(τ)`. Unlike `csigmaUniversalOrdinate`
(the optically-thin universal ordinate, `τ = 0`), this carries the curve-of-growth droop:
it equals the universal-line value minus `−ln SA(τ) ≥ 0` (`csigma_curve_of_growth_droop`).
The subtracted `ln(N_s/U_s)` is the concentration/partition normalization; the cross-section
`σ_ℓ` lives in `τ`, not here. -/
noncomputable def csigmaSelfAbsorbedUniversalOrdinate (kB T N Fcal : ℝ) (g E A : ι → ℝ)
    (k : ι) (tau : ℝ) : ℝ :=
  Real.log (selfAbsorbedIntensity kB T N Fcal g E A k tau / (g k * A k))
    - csigmaConcentrationLog kB T N g E

/-- **The Cσ curve-of-growth droop identity (the BRIDGE).** The concentration-normalized
measured ordinate equals the universal-line value `ln F − E_k/(k_B T)` PLUS `ln SA(τ)`:
since `SA(τ) ∈ (0, 1]` the `ln SA(τ) ≤ 0` term droops the point below the universal line.
The concentration normalization `ln(N_s/U_s)` cancels exactly (it is `N`-independent in the
droop), so the entire `N`/optical-depth dependence is the single term `ln SA(τ)`.

This is a legitimate but mathematically shallow bridge — `csigma_universal_line` followed by
`Real.log_mul` on `I_meas = I_thin · SA(τ)`. The non-trivial content of the module is the
strict-monotonicity lemma `selfAbsorptionFactor_strictAntiOn` and the strict/shape droop
theorems (`csigma_curve_of_growth_lt`, `…_strictAntiOn`, `…_density_droop`) it powers.

REDUCED: `SA(τ) = (1 − exp(−τ))/τ` is the flat-profile (escape-factor) reduction of the
Aragón–Aguilera Cσ curve of growth; the profile-integrated slope-½ Lorentz wing is out of
scope. -/
theorem csigma_curve_of_growth_droop [Nonempty ι] {kB T N Fcal : ℝ} {g E A : ι → ℝ}
    (hg : ∀ k, 0 < g k) (hN : 0 < N) (hFcal : 0 < Fcal) (hA : ∀ k, 0 < A k) (k : ι)
    {tau : ℝ} (htau : 0 ≤ tau) :
    csigmaSelfAbsorbedUniversalOrdinate kB T N Fcal g E A k tau
      = (Real.log Fcal - E k / (kB * T)) + Real.log (selfAbsorptionFactor tau) := by
  have hI : 0 < lineIntensity kB T N Fcal g E A k := lineIntensity_pos hg hN hFcal hA k
  have hgA : 0 < g k * A k := mul_pos (hg k) (hA k)
  have hSA : 0 < selfAbsorptionFactor tau := selfAbsorptionFactor_pos htau
  have huniv := csigma_universal_line (kB := kB) (T := T) (E := E) hg hN hFcal hA k
  unfold csigmaUniversalOrdinate at huniv
  unfold csigmaSelfAbsorbedUniversalOrdinate selfAbsorbedIntensity
  have hsplit : lineIntensity kB T N Fcal g E A k * selfAbsorptionFactor tau / (g k * A k)
      = (lineIntensity kB T N Fcal g E A k / (g k * A k)) * selfAbsorptionFactor tau := by
    ring
  rw [hsplit, Real.log_mul (div_pos hI hgA).ne' hSA.ne']
  linarith [huniv]

/-- **Optically-thin limit (`τ = 0`).** At zero optical depth the self-absorbed ordinate is
exactly the optically-thin universal-line value `ln F − E_k/(k_B T)`: `SA(0) = 1`, so the
droop term `ln SA(0) = 0` vanishes. The thick model continuously recovers
`csigma_universal_line`.

REDUCED: this is the flat-profile (escape-factor) reduction of the Aragón–Aguilera Cσ curve
of growth; the profile-integrated slope-½ Lorentz wing is out of scope. -/
theorem csigma_curve_of_growth_thin [Nonempty ι] {kB T N Fcal : ℝ} {g E A : ι → ℝ}
    (hg : ∀ k, 0 < g k) (hN : 0 < N) (hFcal : 0 < Fcal) (hA : ∀ k, 0 < A k) (k : ι) :
    csigmaSelfAbsorbedUniversalOrdinate kB T N Fcal g E A k 0
      = Real.log Fcal - E k / (kB * T) := by
  rw [csigma_curve_of_growth_droop hg hN hFcal hA k (le_refl 0)]
  simp [selfAbsorptionFactor]

/-- **The droop is downward (non-strict).** For any `τ ≥ 0` the concentration-normalized
measured ordinate lies AT OR BELOW the universal line `ln F − E_k/(k_B T)`: self-absorption
only dims, so `ln SA(τ) ≤ 0`. Neglecting it biases the inferred composition downward.

REDUCED: this is the flat-profile (escape-factor) reduction of the Aragón–Aguilera Cσ curve
of growth; the profile-integrated slope-½ Lorentz wing is out of scope. -/
theorem csigma_curve_of_growth_le [Nonempty ι] {kB T N Fcal : ℝ} {g E A : ι → ℝ}
    (hg : ∀ k, 0 < g k) (hN : 0 < N) (hFcal : 0 < Fcal) (hA : ∀ k, 0 < A k) (k : ι)
    {tau : ℝ} (htau : 0 ≤ tau) :
    csigmaSelfAbsorbedUniversalOrdinate kB T N Fcal g E A k tau
      ≤ Real.log Fcal - E k / (kB * T) := by
  rw [csigma_curve_of_growth_droop hg hN hFcal hA k htau]
  have hlog : Real.log (selfAbsorptionFactor tau) ≤ 0 :=
    Real.log_nonpos (selfAbsorptionFactor_pos htau).le (selfAbsorptionFactor_le_one htau)
  linarith

/-- **The droop is strict for an actually thick line (`τ > 0`).** Whenever the line carries
nonzero optical depth, the measured ordinate is STRICTLY below the universal line:
`SA(τ) < 1` so `ln SA(τ) < 0`. This is the genuinely new strict content powered by the
sign of the escape factor (the deep monotone version is
`csigma_curve_of_growth_strictAntiOn`).

REDUCED: this is the flat-profile (escape-factor) reduction of the Aragón–Aguilera Cσ curve
of growth; the profile-integrated slope-½ Lorentz wing is out of scope. -/
theorem csigma_curve_of_growth_lt [Nonempty ι] {kB T N Fcal : ℝ} {g E A : ι → ℝ}
    (hg : ∀ k, 0 < g k) (hN : 0 < N) (hFcal : 0 < Fcal) (hA : ∀ k, 0 < A k) (k : ι)
    {tau : ℝ} (htau : 0 < tau) :
    csigmaSelfAbsorbedUniversalOrdinate kB T N Fcal g E A k tau
      < Real.log Fcal - E k / (kB * T) := by
  rw [csigma_curve_of_growth_droop hg hN hFcal hA k htau.le]
  have hSApos : 0 < selfAbsorptionFactor tau := selfAbsorptionFactor_pos htau.le
  have hSAlt : selfAbsorptionFactor tau < 1 := by
    unfold selfAbsorptionFactor
    rw [if_neg htau.ne', div_lt_one htau]
    have := Real.one_sub_lt_exp_neg htau.ne'
    linarith
  have hlog : Real.log (selfAbsorptionFactor tau) < 0 := Real.log_neg hSApos hSAlt
  linarith

/-- **The droop vanishes continuously as `τ → 0⁺`.** The self-absorbed ordinate tends to the
universal-line value `ln F − E_k/(k_B T)` as the optical depth shrinks to zero: the thick Cσ
curve of growth meets the optically-thin universal line in the limit. Routes through
`selfAbsorptionFactor_tendsto_one` and continuity of `Real.log` at `1`.

REDUCED: this is the flat-profile (escape-factor) reduction of the Aragón–Aguilera Cσ curve
of growth; the profile-integrated slope-½ Lorentz wing is out of scope. -/
theorem csigma_curve_of_growth_tendsto_universal [Nonempty ι] {kB T N Fcal : ℝ}
    {g E A : ι → ℝ} (hg : ∀ k, 0 < g k) (hN : 0 < N) (hFcal : 0 < Fcal) (hA : ∀ k, 0 < A k)
    (k : ι) :
    Filter.Tendsto (fun tau => csigmaSelfAbsorbedUniversalOrdinate kB T N Fcal g E A k tau)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (Real.log Fcal - E k / (kB * T))) := by
  have hlog : Filter.Tendsto (fun tau => Real.log (selfAbsorptionFactor tau))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (Real.log 1)) :=
    (Real.continuousAt_log one_ne_zero).tendsto.comp selfAbsorptionFactor_tendsto_one
  rw [Real.log_one] at hlog
  have hconst := hlog.const_add (Real.log Fcal - E k / (kB * T))
  rw [add_zero] at hconst
  refine hconst.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with tau htau
  exact (csigma_curve_of_growth_droop hg hN hFcal hA k (Set.mem_Ioi.mp htau).le).symm

/-- **The escape factor is strictly antitone on `(0, ∞)` — the new analytic core.** The
curve-of-growth self-absorption factor `SA(τ) = (1 − exp(−τ))/τ` is STRICTLY DECREASING in
the optical depth `τ > 0`: a more optically-thick line escapes a strictly smaller fraction
of its photons. This is the genuinely new content of the module (no monotonicity lemma for
`SA` exists in `SelfAbsorption.lean`). Proved exactly as `CurveOfGrowth.cogSlope_strictAntiOn`:
`strictAntiOn_of_deriv_neg` with derivative numerator `exp(−x)·(x + 1) − 1 < 0`, the latter
from `Real.add_one_lt_exp` (`x + 1 < exp x`) scaled by `exp(−x) > 0`. The proof works on the
clean branch `(1 − exp(−x))/x` and transfers across the `if` of `selfAbsorptionFactor` by
`StrictAntiOn.congr`. -/
theorem selfAbsorptionFactor_strictAntiOn :
    StrictAntiOn selfAbsorptionFactor (Set.Ioi 0) := by
  have hclean : StrictAntiOn (fun t : ℝ => (1 - Real.exp (-t)) / t) (Set.Ioi 0) := by
    apply strictAntiOn_of_deriv_neg (convex_Ioi 0)
    · -- continuity on `Ioi 0`: numerator and denominator continuous, denominator ≠ 0
      apply ContinuousOn.div
      · exact continuousOn_const.sub (Real.continuous_exp.comp continuous_neg).continuousOn
      · exact continuousOn_id
      · intro t ht
        exact (Set.mem_Ioi.mp ht).ne'
    · intro x hx
      rw [interior_Ioi] at hx
      have hxpos : 0 < x := hx
      have hxne : x ≠ 0 := hxpos.ne'
      have he : HasDerivAt (fun t : ℝ => Real.exp (-t)) (Real.exp (-x) * -1) x :=
        (Real.hasDerivAt_exp (-x)).comp x ((hasDerivAt_id x).neg)
      have hd : HasDerivAt (fun t : ℝ => (1 - Real.exp (-t)) / t)
          ((Real.exp (-x) * x - (1 - Real.exp (-x)) * 1) / x ^ 2) x := by
        have hnum : HasDerivAt (fun t : ℝ => 1 - Real.exp (-t)) (Real.exp (-x)) x := by
          simpa using he.const_sub 1
        have hden : HasDerivAt (fun t : ℝ => t) (1 : ℝ) x := hasDerivAt_id x
        exact hnum.div hden hxne
      rw [hd.deriv]
      apply div_neg_of_neg_of_pos
      · have hkey : Real.exp (-x) * (x + 1) < 1 := by
          have h1 : x + 1 < Real.exp x := Real.add_one_lt_exp hxne
          have h2 : Real.exp (-x) * (x + 1) < Real.exp (-x) * Real.exp x :=
            mul_lt_mul_of_pos_left h1 (Real.exp_pos _)
          rwa [← Real.exp_add, neg_add_cancel, Real.exp_zero] at h2
        nlinarith [hkey]
      · exact pow_pos hxpos 2
  have heqon : Set.EqOn (fun t : ℝ => (1 - Real.exp (-t)) / t) selfAbsorptionFactor
      (Set.Ioi 0) := by
    intro t ht
    rw [selfAbsorptionFactor, if_neg (Set.mem_Ioi.mp ht).ne']
  exact hclean.congr heqon

/-- **The Cσ curve of growth is strictly antitone in optical depth.** As a function of `τ`,
the concentration-normalized measured ordinate is STRICTLY DECREASING on `(0, ∞)`: deeper
optical depth means a strictly deeper droop below the universal line. Reduces to
`selfAbsorptionFactor_strictAntiOn` through the droop identity and strict monotonicity of
`Real.log`. This is the shape statement of the Cσ curve of growth.

REDUCED: this is the flat-profile (escape-factor) reduction of the Aragón–Aguilera Cσ curve
of growth; the profile-integrated slope-½ Lorentz wing (the slope-1 → slope-½ knee) is out
of scope — only the strict monotone descent of the escape-factor branch is proved. -/
theorem csigma_curve_of_growth_strictAntiOn [Nonempty ι] {kB T N Fcal : ℝ} {g E A : ι → ℝ}
    (hg : ∀ k, 0 < g k) (hN : 0 < N) (hFcal : 0 < Fcal) (hA : ∀ k, 0 < A k) (k : ι) :
    StrictAntiOn (fun tau => csigmaSelfAbsorbedUniversalOrdinate kB T N Fcal g E A k tau)
      (Set.Ioi 0) := by
  intro a ha b hb hab
  change csigmaSelfAbsorbedUniversalOrdinate kB T N Fcal g E A k b
      < csigmaSelfAbsorbedUniversalOrdinate kB T N Fcal g E A k a
  rw [csigma_curve_of_growth_droop hg hN hFcal hA k (Set.mem_Ioi.mp hb).le,
      csigma_curve_of_growth_droop hg hN hFcal hA k (Set.mem_Ioi.mp ha).le]
  have hSAb : 0 < selfAbsorptionFactor b := selfAbsorptionFactor_pos (Set.mem_Ioi.mp hb).le
  have hlt : selfAbsorptionFactor b < selfAbsorptionFactor a :=
    selfAbsorptionFactor_strictAntiOn ha hb hab
  have hlog : Real.log (selfAbsorptionFactor b) < Real.log (selfAbsorptionFactor a) :=
    Real.log_lt_log hSAb hlt
  linarith

/-- **The density droop (the σ cross-section weighting, `N`-coupled).** Couple the optical
depth to the SAME species number density that the universal line normalizes away:
`τ = σ_ℓ · ℓ · N` (`csigmaOpticalDepth`). Then, as a function of `N`, the
concentration-normalized measured ordinate is STRICTLY ANTITONE on `(0, ∞)`. This is faithful
to the physics: the universal-line value `ln F − E_k/(k_B T)` is `N`-independent (the
concentration normalization cancels), so the ONLY `N`-dependence left is the self-absorption
droop, and increasing the density `N` strictly deepens it through `τ = N σ_ℓ ℓ`. Here `σ_ℓ`
is the genuine line cross-section of the Aragón–Aguilera Cσ graph. Reduces to
`csigma_curve_of_growth_strictAntiOn` via strict monotonicity of `N ↦ σ_ℓ ℓ N` on `(0, ∞)`.

REDUCED: this is the flat-profile (escape-factor) reduction of the Aragón–Aguilera Cσ curve
of growth; the profile-integrated slope-½ Lorentz wing is out of scope. -/
theorem csigma_curve_of_growth_density_droop [Nonempty ι] {kB T Fcal sigmaL ell : ℝ}
    {g E A : ι → ℝ} (hg : ∀ k, 0 < g k) (hFcal : 0 < Fcal) (hA : ∀ k, 0 < A k)
    (hsig : 0 < sigmaL) (hell : 0 < ell) (k : ι) :
    StrictAntiOn
      (fun N => csigmaSelfAbsorbedUniversalOrdinate kB T N Fcal g E A k
        (csigmaOpticalDepth sigmaL ell N)) (Set.Ioi 0) := by
  intro Na hNa Nb hNb hab
  have hNa0 : 0 < Na := hNa
  have hNb0 : 0 < Nb := hNb
  have hτa : 0 < csigmaOpticalDepth sigmaL ell Na := by
    unfold csigmaOpticalDepth; positivity
  have hτb : 0 < csigmaOpticalDepth sigmaL ell Nb := by
    unfold csigmaOpticalDepth; positivity
  have hτab : csigmaOpticalDepth sigmaL ell Na < csigmaOpticalDepth sigmaL ell Nb := by
    unfold csigmaOpticalDepth
    exact mul_lt_mul_of_pos_left hab (mul_pos hsig hell)
  change csigmaSelfAbsorbedUniversalOrdinate kB T Nb Fcal g E A k (csigmaOpticalDepth sigmaL ell Nb)
      < csigmaSelfAbsorbedUniversalOrdinate kB T Na Fcal g E A k (csigmaOpticalDepth sigmaL ell Na)
  rw [csigma_curve_of_growth_droop hg hNb0 hFcal hA k hτb.le,
      csigma_curve_of_growth_droop hg hNa0 hFcal hA k hτa.le]
  have hSAb : 0 < selfAbsorptionFactor (csigmaOpticalDepth sigmaL ell Nb) :=
    selfAbsorptionFactor_pos hτb.le
  have hlt : selfAbsorptionFactor (csigmaOpticalDepth sigmaL ell Nb)
      < selfAbsorptionFactor (csigmaOpticalDepth sigmaL ell Na) :=
    selfAbsorptionFactor_strictAntiOn (Set.mem_Ioi.mpr hτa) (Set.mem_Ioi.mpr hτb) hτab
  have hlog : Real.log (selfAbsorptionFactor (csigmaOpticalDepth sigmaL ell Nb))
      < Real.log (selfAbsorptionFactor (csigmaOpticalDepth sigmaL ell Na)) :=
    Real.log_lt_log hSAb hlt
  linarith

end CflibsFormal.Alt
