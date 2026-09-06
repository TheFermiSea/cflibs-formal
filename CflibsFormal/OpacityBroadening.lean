/-
Copyright (c) 2026 Brian Squires. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Squires
-/
import Mathlib
import CflibsFormal.Analysis
import CflibsFormal.SelfAbsorption
import CflibsFormal.EquivalentWidth
import CflibsFormal.StarkOpacityGuard

/-!
# CF-LIBS formalization — opacity broadening: a DERIVED budget for the Stark opacity guard

`StarkOpacityGuard.lean` repairs a real soundness hole in the Stark/McWhirter LTE gate, but
its repair `starkOpacityLteCert` is sound only under the *assumed* opacity budget
`hbudget : widthMeas ≤ kOpac · starkFWHM w nRef neTrue`. That module's REFUSAL note states
plainly that `kOpac` is an epistemic input which nothing in the repo derives, because
self-absorption is modelled only in the INTENSITY domain (`SelfAbsorption`,
`CurveOfGrowth`, `EquivalentWidth`), never in the profile-WIDTH domain.

This module supplies the missing width–optical-depth link and turns `kOpac` into a
*computed function of the optical depth* `τ`.

## The mechanism

For a homogeneous slab of optical depth `τ` whose line has peak-normalized shape `ψ`
(`ψ 0 = 1`, decreasing away from the core), the emergent profile is

  `I(x) = S · (1 − exp(−τ·ψ(x)))`   (`emergentProfile`).

The core saturates faster than the wings, so the profile fattens. Quantitatively
(`emergentProfile_half_iff`), the points at which the emergent profile falls to half its
CENTRAL value are exactly the points where the *intrinsic shape* attains the level

  `h(τ) = (log 2 − log(1 + exp(−τ))) / τ`   (`coreHalfLevel`),

which is `1/2` in the thin limit and STRICTLY BELOW `1/2` for every `τ > 0`
(`coreHalfLevel_lt_half`) and strictly decreasing in `τ`
(`coreHalfLevel_strictAntiOn`). A lower half-max level is reached further out on a
decreasing shape, so the observed half-width STRICTLY exceeds the intrinsic one
(`halfWidth_broadens`) and is nondecreasing in `τ` (`halfWidth_mono_tau`) — for ANY strictly
decreasing shape, no Lorentzian/Gaussian assumption. For the Lorentzian shape the
broadening is STRICT at every `τ > 0` (`one_lt_lorentzWidthRatio`).

## The payoff: an explicit, derived budget

The one elementary inequality `log z ≥ 1 − 1/z` gives the clean lower bound
`h(τ) ≥ SA(τ)/2` (`halfSA_le_coreHalfLevel`), where `SA(τ) = (1 − exp(−τ))/τ` is the
ALREADY-FORMALIZED `SelfAbsorption.selfAbsorptionFactor`. For the Lorentzian shape — the
electron-impact Stark profile itself — inverting the level relation gives the explicit
budget

  `kOpacOf τ = √(2/SA(τ) − 1)`,   `widthObs ≤ kOpacOf τ · widthIntrinsic`

(`lorentzWidthRatio_le_kOpacOf`, `stark_widthObs_le_budget`), with `kOpacOf 0 = 1`,
`1 ≤ kOpacOf τ`, `kOpacOf` strictly increasing in `τ`, and `kOpacOf τ → 1` as `τ → 0⁺`.
`starkOpacity_certificate_sound_of_tau` and `..._of_tau_le` then discharge
`StarkOpacityGuard`'s `hbudget` from a `τ` estimate (or a `τ` UPPER BOUND), so the
guard's opacity BUDGET is no longer assumed — `τ` itself still is. `OpticalDepth.opticalDepth`
binds `τ` to `(T, N, σ₀, ℓ)`, and this module turns that `τ` into `kOpac`.

## The flat-profile boundary case

Opacity broadening is a CORE-SATURATION effect and vanishes without a peaked core. For a
rectangular profile the half-max set of the emergent profile is the box itself for every
`τ > 0`, while the equivalent width `1 − exp(−τ)` (`EquivalentWidth.equivWidth_rectangular`)
grows strictly: `flatProfile_intensity_saturates_width_does_not`. That theorem is exactly
why the repo's intensity-domain self-absorption model could not, by itself, yield a width
budget.

## Literature and scope

REDUCED. The emergent-profile kernel `I = S·(1 − exp(−τ·ψ))` for a homogeneous,
single-temperature slab is the Gornushkin curve-of-growth model already used elsewhere in
this development: Gornushkin, I. B.; Anzano, J. M.; King, L. A.; Smith, B. W.; Omenetto, N.;
Winefordner, J. D., "Curve of growth methodology applied to laser-induced plasma emission
spectroscopy," *Spectrochimica Acta Part B* **54** (1999) 491–503. The Lorentzian shape of
the electron-impact (Stark) profile being inverted is that of H. R. Griem, *Spectral Line
Broadening by Plasmas*, Academic Press (1974) — the same source as
`StarkBroadening.starkFWHM`. The McWhirter LTE bound and the warning that self-absorbed
lines corrupt LTE diagnostics are as recalled by G. Cristoforetti, A. De Giacomo,
M. Dell'Aglio, S. Legnaioli, E. Tognoni, V. Palleschi, N. Omenetto, "Local Thermodynamic
Equilibrium in Laser-Induced Breakdown Spectroscopy: Beyond the McWhirter criterion,"
*Spectrochimica Acta Part B* **65** (2010) 86.

There is a widely used LIBS correlation of the form `w_obs = w_Stark · SA^(−0.54)` (an
EMPIRICAL power-law fit to self-absorbed profile widths, associated with the El Sherbini
group). It is deliberately **not** used here and no bibliographic record for it is asserted
— this module proves a rigorous monotone bound instead of transcribing a fitted exponent.
Nothing below depends on that correlation.

## Honest limitations

* **Homogeneous slab, one shape, one `τ`.** `emergentProfile` presumes a single uniform
  emitting/absorbing layer with a *frequency-dependent* optical depth `τ·ψ(x)` built from
  ONE peak-normalized shape. Spatial gradients (`SpatialForward`,
  `InhomogeneityBias`) and self-reversal from a cooler absorbing halo (`SelfReversal`) are
  out of scope and can *narrow* or *reverse* a core, breaking the monotone picture proved
  here.
* **`ψ` is the intrinsic shape, assumed shape-invariant with `τ`.** The Stark profile is
  taken Lorentzian with a `τ`-independent HWHM `γ`; instrumental and Doppler (Gaussian)
  convolution is NOT folded in. On a real Voigt profile (`VoigtWidth`) the emergent
  half-width lies between the pure-Gaussian and pure-Lorentzian answers; only the
  Lorentzian case is proven.
* **The budget is CONSERVATIVE, not the exact broadening.** `kOpacOf τ = √(2/SA(τ) − 1)`
  over-estimates the exact Lorentzian ratio `lorentzWidthRatio τ = √(1/h(τ) − 1)`, because
  `h(τ) ≥ SA(τ)/2` is a one-sided bound (numerically, at `τ = 2` the exact ratio is
  ≈ 1.59 while the budget is ≈ 1.90; the machine-checked statements are the coarser
  `lorentzWidthRatio_two_bounds` and `lorentzWidthRatio_two_lower`, which together give only
  `1.5 ≤ R(2) ≤ 2`). Conservatism is the correct direction for a soundness guard, but
  `kOpacOf` must not be read as a width-correction formula.
* **`τ` is still an input.** This module converts an *assumed factor* into an *assumed
  optical depth* — a strictly better epistemic position (`OpticalDepth.opticalDepth` binds
  `τ` to `(T, N, σ₀, ℓ)` and `Certificates` can carry it), but it is not a measurement.
  The `..._of_tau_le` form is the honest interface: it consumes an UPPER BOUND on `τ`.
* **Stimulated emission is not modelled** (inherited from `OpticalDepth`), so `τ` here is
  the same Wien-limit optical depth used elsewhere in the corpus.
* **No claim of necessity.** Broadening is proven to follow from core saturation; it is not
  proven that width inflation implies opacity.
-/

namespace CflibsFormal

/-! ## A. The emergent profile and its half-maximum level -/

/-- **Emergent line profile of a homogeneous slab.** For source strength `S`, line optical
depth `τ` and *peak-normalized* profile shape `ψ` (so `ψ 0 = 1` at line centre),
`I(x) = S·(1 − exp(−τ·ψ(x)))`. This is the frequency-resolved refinement of
`SelfAbsorption.slabIntensity` (which is the `ψ ≡ 1` case) and of
`OpticalDepth.thickLineIntensity`: the optical depth seen at offset `x` from line centre is
`τ·ψ(x)`, so the core is absorbed at full `τ` while the wings are nearly thin. -/
noncomputable def emergentProfile (S tau : ℝ) (psi : ℝ → ℝ) (x : ℝ) : ℝ :=
  S * (1 - Real.exp (-(tau * psi x)))

/-- **Half-maximum level of the emergent profile, expressed on the intrinsic shape.**
`h(τ) = (log 2 − log(1 + exp(−τ)))/τ`. `emergentProfile_half_iff` shows that a point `x` is
a half-maximum point of the emergent profile exactly when the *intrinsic* shape there equals
`h(τ)`. In the thin limit `h → 1/2` (the usual half-maximum condition); at finite `τ` it
sits strictly below `1/2`, which is precisely opacity broadening. -/
noncomputable def coreHalfLevel (tau : ℝ) : ℝ :=
  (Real.log 2 - Real.log (1 + Real.exp (-tau))) / tau

/-- **The half-maximum condition, transported to the intrinsic shape.** For `S ≠ 0`,
`τ > 0` and a peak-normalized shape (`ψ 0 = 1`), the emergent profile falls to half its
central value at `x` if and only if the intrinsic shape at `x` equals `coreHalfLevel τ`.
Exact algebra on the definition — this is the lemma that converts a statement about the
OBSERVED profile into a statement about a level set of the INTRINSIC profile. -/
theorem emergentProfile_half_iff {S tau x : ℝ} {psi : ℝ → ℝ} (hS : S ≠ 0) (htau : 0 < tau)
    (hpsi0 : psi 0 = 1) :
    emergentProfile S tau psi x = emergentProfile S tau psi 0 / 2
      ↔ psi x = coreHalfLevel tau := by
  have hexp : (0 : ℝ) < 1 + Real.exp (-tau) := by positivity
  constructor
  · intro heq
    have h : S * (1 - Real.exp (-(tau * psi x)))
        = S * ((1 - Real.exp (-tau)) / 2) := by
      rw [emergentProfile, emergentProfile, hpsi0, mul_one, mul_div_assoc] at heq
      exact heq
    have hcancel : 1 - Real.exp (-(tau * psi x)) = (1 - Real.exp (-tau)) / 2 :=
      mul_left_cancel₀ hS h
    have h1 : Real.exp (-(tau * psi x)) = (1 + Real.exp (-tau)) / 2 := by linarith
    have h2 : -(tau * psi x) = Real.log ((1 + Real.exp (-tau)) / 2) := by
      rw [← h1, Real.log_exp]
    rw [Real.log_div hexp.ne' two_ne_zero] at h2
    rw [coreHalfLevel, eq_div_iff htau.ne']
    linear_combination -h2
  · intro hx
    have h2 : tau * psi x = Real.log 2 - Real.log (1 + Real.exp (-tau)) := by
      rw [hx, coreHalfLevel]
      field_simp
    have h3 : Real.exp (-(tau * psi x)) = (1 + Real.exp (-tau)) / 2 := by
      rw [h2, show -(Real.log 2 - Real.log (1 + Real.exp (-tau)))
          = Real.log ((1 + Real.exp (-tau)) / 2) by
        rw [Real.log_div hexp.ne' two_ne_zero]; ring]
      exact Real.exp_log (by positivity)
    rw [emergentProfile, emergentProfile, hpsi0, mul_one, h3]
    ring

/-! ## B. Where the half-maximum level sits: the two bounds that do all the work -/

/-- **Core saturation strictly lowers the half-maximum level.** `h(τ) < 1/2` for every
`τ > 0`. Proof: with `b = exp(τ/2) > 1`, `log(1 + exp(−τ)) + τ/2 = log(b + b⁻¹)` and
`b + b⁻¹ > 2` (AM–GM, strict for `b ≠ 1`), so `log 2 − log(1 + exp(−τ)) < τ/2`. This is
opacity broadening in one line: a level BELOW half-maximum is reached further out. -/
theorem coreHalfLevel_lt_half {tau : ℝ} (htau : 0 < tau) : coreHalfLevel tau < 1 / 2 := by
  rw [coreHalfLevel, div_lt_iff₀ htau]
  set b := Real.exp (tau / 2) with hbdef
  have hbpos : 0 < b := Real.exp_pos _
  have hb1 : 1 < b := by
    have h := Real.exp_lt_exp.mpr (show (0 : ℝ) < tau / 2 by linarith)
    rwa [Real.exp_zero] at h
  have hbinv : b⁻¹ = Real.exp (-(tau / 2)) := by rw [hbdef, ← Real.exp_neg]
  have hu : Real.exp (-tau) = b⁻¹ * b⁻¹ := by
    rw [hbinv, ← Real.exp_add]
    congr 1
    ring
  have h1 : (1 + Real.exp (-tau)) * b = b + b⁻¹ := by
    rw [hu, hbdef]
    field_simp
  have hlogb : Real.log b = tau / 2 := by rw [hbdef, Real.log_exp]
  have hlog : Real.log (1 + Real.exp (-tau)) + tau / 2 = Real.log (b + b⁻¹) := by
    rw [← hlogb, ← Real.log_mul (by positivity) hbpos.ne', h1]
  have h2lt : (2 : ℝ) < b + b⁻¹ := by
    have hkey : b + b⁻¹ - 2 = (b - 1) ^ 2 / b := by field_simp; ring
    have hnn : 0 < (b - 1) ^ 2 / b := div_pos (by positivity) hbpos
    linarith
  have hfin : Real.log 2 < Real.log (b + b⁻¹) := Real.log_lt_log (by norm_num) h2lt
  linarith

/-- `h(τ) ≤ 1/2`, the non-strict form of `coreHalfLevel_lt_half`. -/
theorem coreHalfLevel_le_half {tau : ℝ} (htau : 0 < tau) : coreHalfLevel tau ≤ 1 / 2 :=
  (coreHalfLevel_lt_half htau).le

/-- **The escape factor bounds the half-maximum level from below:** `SA(τ)/2 ≤ h(τ)`, with
`SA` the already-formalized `SelfAbsorption.selfAbsorptionFactor` `(1 − exp(−τ))/τ`. One
elementary inequality, `log z ≥ 1 − 1/z` at `z = 2/(1 + exp(−τ))`, does the whole job. This
is the bound that converts the exact (transcendental) half-maximum level into the explicit,
already-audited `SA`, and hence produces a COMPUTABLE opacity budget below. -/
theorem halfSA_le_coreHalfLevel {tau : ℝ} (htau : 0 < tau) :
    selfAbsorptionFactor tau / 2 ≤ coreHalfLevel tau := by
  have h1p : (0 : ℝ) < 1 + Real.exp (-tau) := by positivity
  have hnum : (1 - Real.exp (-tau)) / 2 ≤ Real.log 2 - Real.log (1 + Real.exp (-tau)) := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (1 + Real.exp (-tau)) / 2 by positivity)
    rw [Real.log_div h1p.ne' two_ne_zero] at h
    linarith
  have hrw : selfAbsorptionFactor tau / 2 = (1 - Real.exp (-tau)) / 2 / tau := by
    rw [selfAbsorptionFactor, if_neg htau.ne']
    ring
  rw [hrw, coreHalfLevel]
  gcongr

/-- The half-maximum level is strictly positive at every finite optical depth: the emergent
profile really does have half-maximum points on the intrinsic shape's range. -/
theorem coreHalfLevel_pos {tau : ℝ} (htau : 0 < tau) : 0 < coreHalfLevel tau :=
  lt_of_lt_of_le (by have := selfAbsorptionFactor_pos htau.le; linarith)
    (halfSA_le_coreHalfLevel htau)

/-- **The half-maximum level falls strictly with optical depth.** `h` is strictly antitone on
`(0, ∞)`. Via the shared `Analysis.strictAntiOn_div_of_deriv_num_neg` scaffold: the quotient
`h = f/τ` has derivative numerator `f'(τ)·τ − f(τ) < 0`, which reduces (using
`log z ≥ 1 − 1/z` again for `f`, and `x < sinh x` for the remainder) to `2τ < e^τ − e^{−τ}`.
Combined with `halfWidth_mono_tau` this is the monotone broadening law. -/
theorem coreHalfLevel_strictAntiOn : StrictAntiOn coreHalfLevel (Set.Ioi 0) := by
  have hd : StrictAntiOn (fun t : ℝ => (Real.log 2 - Real.log (1 + Real.exp (-t))) / t)
      (Set.Ioi 0) := by
    apply strictAntiOn_div_of_deriv_num_neg
      (f := fun t => Real.log 2 - Real.log (1 + Real.exp (-t))) (g := fun t => t)
      (f' := fun t => Real.exp (-t) / (1 + Real.exp (-t))) (g' := fun _ => 1)
    · intro x hx
      exact Set.mem_Ioi.mp hx
    · intro x _
      have he : HasDerivAt (fun t : ℝ => Real.exp (-t)) (Real.exp (-x) * -1) x :=
        (Real.hasDerivAt_exp (-x)).comp x ((hasDerivAt_id x).neg)
      have h1 : HasDerivAt (fun t : ℝ => 1 + Real.exp (-t)) (Real.exp (-x) * -1) x :=
        he.const_add 1
      have hne : (1 : ℝ) + Real.exp (-x) ≠ 0 := by positivity
      have h3 := (h1.log hne).const_sub (Real.log 2)
      have heq : Real.exp (-x) / (1 + Real.exp (-x))
          = -(Real.exp (-x) * -1 / (1 + Real.exp (-x))) := by ring
      rw [heq]
      exact h3
    · intro x _
      exact hasDerivAt_id x
    · intro x hx
      have hx0 : 0 < x := Set.mem_Ioi.mp hx
      have hu : 0 < Real.exp (-x) := Real.exp_pos _
      have h1p : (0 : ℝ) < 1 + Real.exp (-x) := by positivity
      have hlow : (1 - Real.exp (-x)) / 2 ≤ Real.log 2 - Real.log (1 + Real.exp (-x)) := by
        have h := Real.log_le_sub_one_of_pos
          (show (0 : ℝ) < (1 + Real.exp (-x)) / 2 by positivity)
        rw [Real.log_div h1p.ne' two_ne_zero] at h
        linarith
      have hsinh : 2 * x < Real.exp x - Real.exp (-x) := by
        have h := Real.self_lt_sinh_iff.mpr hx0
        rw [Real.sinh_eq] at h
        linarith
      have hmul : Real.exp (-x) * Real.exp x = 1 := by
        rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
      have hkey : Real.exp (-x) / (1 + Real.exp (-x)) * x < (1 - Real.exp (-x)) / 2 := by
        rw [show Real.exp (-x) / (1 + Real.exp (-x)) * x
            = Real.exp (-x) * x / (1 + Real.exp (-x)) by ring, div_lt_iff₀ h1p]
        nlinarith [mul_lt_mul_of_pos_left hsinh hu]
      simp only [mul_one]
      linarith
  intro a ha b hb hab
  exact hd ha hb hab

/-! ## C. Shape-agnostic broadening laws -/

/-- **Opacity broadens the line — for ANY peaked shape.** If the intrinsic shape `ψ` is
strictly decreasing away from line centre, `x₀` is an intrinsic half-width (`ψ x₀ = 1/2`) and
`x` is an emergent half-width at optical depth `τ > 0` (`ψ x = h(τ)`, the condition supplied
by `emergentProfile_half_iff`), then `x₀ < x`: the observed half-width STRICTLY exceeds the
intrinsic one. No Lorentzian, Gaussian or Voigt assumption is used — only monotonicity of
the shape and `coreHalfLevel_lt_half`. -/
theorem halfWidth_broadens {psi : ℝ → ℝ} (hmono : StrictAntiOn psi (Set.Ici 0))
    {tau x0 x : ℝ} (htau : 0 < tau) (hx0 : 0 ≤ x0) (hx : 0 ≤ x)
    (hint : psi x0 = 1 / 2) (hobs : psi x = coreHalfLevel tau) :
    x0 < x := by
  have hstrict := coreHalfLevel_lt_half htau
  rcases le_or_gt x x0 with hge | hok
  · exfalso
    rcases eq_or_lt_of_le hge with heq | hlt
    · rw [heq, hint] at hobs
      linarith
    · have h := hmono hx hx0 hlt
      rw [hint, hobs] at h
      linarith
  · exact hok

/-- **The observed half-width is monotone nondecreasing in the optical depth** — again for
ANY strictly decreasing shape. Deeper lines are wider lines: `τ₁ ≤ τ₂` forces `x₁ ≤ x₂` for
the corresponding emergent half-widths. Combines `coreHalfLevel_strictAntiOn` with the
monotonicity of the shape. -/
theorem halfWidth_mono_tau {psi : ℝ → ℝ} (hmono : StrictAntiOn psi (Set.Ici 0))
    {tau₁ tau₂ x₁ x₂ : ℝ} (htau₁ : 0 < tau₁) (hle : tau₁ ≤ tau₂)
    (hx₁ : 0 ≤ x₁) (hx₂ : 0 ≤ x₂)
    (hobs₁ : psi x₁ = coreHalfLevel tau₁) (hobs₂ : psi x₂ = coreHalfLevel tau₂) :
    x₁ ≤ x₂ := by
  rcases le_or_gt x₁ x₂ with hok | hlt
  · exact hok
  · exfalso
    have h := hmono hx₂ hx₁ hlt
    rw [hobs₁, hobs₂] at h
    rcases eq_or_lt_of_le hle with heq | hlt2
    · rw [heq] at h
      exact absurd rfl (ne_of_lt h)
    · have := coreHalfLevel_strictAntiOn (Set.mem_Ioi.mpr htau₁)
        (Set.mem_Ioi.mpr (lt_of_lt_of_le htau₁ hle)) hlt2
      linarith

/-! ## D. The Lorentzian (electron-impact Stark) shape: an explicit budget -/

/-- **Peak-normalized Lorentzian shape of half-width-at-half-maximum `γ`:**
`ψ(x) = γ²/(γ² + x²)`, so `ψ(0) = 1` and `ψ(γ) = 1/2`. This is the profile of the
electron-impact (Stark) broadening mechanism whose FWHM `StarkBroadening.starkFWHM`
inverts. -/
noncomputable def lorentzShape (gamma x : ℝ) : ℝ := gamma ^ 2 / (gamma ^ 2 + x ^ 2)

/-- The Lorentzian shape is peak-normalized: `ψ(0) = 1`. -/
theorem lorentzShape_zero {gamma : ℝ} (hg : gamma ≠ 0) : lorentzShape gamma 0 = 1 := by
  rw [lorentzShape, show gamma ^ 2 + (0 : ℝ) ^ 2 = gamma ^ 2 by ring]
  exact div_self (pow_ne_zero 2 hg)

/-- `γ` is the intrinsic half-width at half-maximum of the Lorentzian shape. -/
theorem lorentzShape_hwhm {gamma : ℝ} (hg : gamma ≠ 0) : lorentzShape gamma gamma = 1 / 2 := by
  have h2 : gamma ^ 2 + gamma ^ 2 = 2 * gamma ^ 2 := by ring
  rw [lorentzShape, h2, div_eq_div_iff (by positivity) (by norm_num)]
  ring

/-- The Lorentzian shape is strictly decreasing away from line centre. -/
theorem lorentzShape_strictAntiOn {gamma : ℝ} (hg : 0 < gamma) :
    StrictAntiOn (lorentzShape gamma) (Set.Ici 0) := by
  intro a ha b _ hab
  have ha0 : (0 : ℝ) ≤ a := ha
  have hda : (0 : ℝ) < gamma ^ 2 + a ^ 2 := by positivity
  have hdb : (0 : ℝ) < gamma ^ 2 + b ^ 2 := by positivity
  have hab2 : a ^ 2 < b ^ 2 := by nlinarith
  have hg2 : (0 : ℝ) < gamma ^ 2 := by positivity
  rw [lorentzShape, lorentzShape, div_lt_div_iff₀ hdb hda]
  nlinarith [hab2, hg2]

/-- **Exact Lorentzian broadening ratio.** `R(τ) = √(1/h(τ) − 1)`: the factor by which the
observed half-width of a Lorentzian line exceeds its intrinsic half-width at optical depth
`τ`. Obtained by inverting `lorentzShape gamma x = coreHalfLevel τ`. -/
noncomputable def lorentzWidthRatio (tau : ℝ) : ℝ :=
  Real.sqrt (1 / coreHalfLevel tau - 1)

/-- **The broadening ratio names its own witness.** `γ·R(τ)` IS an emergent half-width of
the Lorentzian line of intrinsic half-width `γ`: it solves the half-maximum condition
`ψ(x) = h(τ)` exactly. Existence is not merely asserted — the point is exhibited. -/
theorem lorentzShape_widthRatio {gamma tau : ℝ} (hg : 0 < gamma) (htau : 0 < tau) :
    lorentzShape gamma (gamma * lorentzWidthRatio tau) = coreHalfLevel tau := by
  have hpos := coreHalfLevel_pos htau
  have hle := coreHalfLevel_le_half htau
  have hnn : 0 ≤ 1 / coreHalfLevel tau - 1 := by
    rw [sub_nonneg, le_div_iff₀ hpos]
    linarith
  have hsq : lorentzWidthRatio tau ^ 2 = 1 / coreHalfLevel tau - 1 := Real.sq_sqrt hnn
  rw [lorentzShape, mul_pow, hsq]
  field_simp
  ring

/-- **Broadening is strict at every positive optical depth:** `1 < R(τ)`. Not merely
"nondecreasing" — an optically thick Lorentzian line is genuinely wider than its intrinsic
profile. -/
theorem one_lt_lorentzWidthRatio {tau : ℝ} (htau : 0 < tau) : 1 < lorentzWidthRatio tau := by
  have hpos := coreHalfLevel_pos htau
  have hlt := coreHalfLevel_lt_half htau
  have h2 : (1 : ℝ) < 1 / coreHalfLevel tau - 1 := by
    rw [lt_sub_iff_add_lt, lt_div_iff₀ hpos]
    linarith
  have hs : Real.sqrt 1 < Real.sqrt (1 / coreHalfLevel tau - 1) :=
    Real.sqrt_lt_sqrt (by norm_num) h2
  rw [Real.sqrt_one] at hs
  rw [lorentzWidthRatio]
  exact hs

/-- **THE DERIVED OPACITY BUDGET.** `kOpacOf τ = √(2/SA(τ) − 1)`, built only from the
already-audited escape factor `SelfAbsorption.selfAbsorptionFactor`. This is the quantity
that `StarkOpacityGuard.starkOpacityLteCert` had to ASSUME: here it is a function of the
optical depth alone. -/
noncomputable def kOpacOf (tau : ℝ) : ℝ :=
  Real.sqrt (2 / selfAbsorptionFactor tau - 1)

/-- In the optically thin limit the budget is exactly `1`: no width correction. -/
theorem kOpacOf_zero : kOpacOf 0 = 1 := by
  rw [kOpacOf, selfAbsorptionFactor, if_pos rfl]
  norm_num

/-- The budget never shrinks a line: `1 ≤ kOpacOf τ` for `τ ≥ 0`. This is exactly the
`1 ≤ kOpac` side condition demanded by `StarkOpacityGuard.starkOpacityLteCert`. -/
theorem one_le_kOpacOf {tau : ℝ} (htau : 0 ≤ tau) : 1 ≤ kOpacOf tau := by
  have hsa := selfAbsorptionFactor_pos htau
  have hle := selfAbsorptionFactor_le_one htau
  have h2 : (2 : ℝ) ≤ 2 / selfAbsorptionFactor tau := by
    rw [le_div_iff₀ hsa]
    linarith
  have hs : Real.sqrt 1 ≤ Real.sqrt (2 / selfAbsorptionFactor tau - 1) :=
    Real.sqrt_le_sqrt (by linarith)
  rw [Real.sqrt_one] at hs
  rw [kOpacOf]
  exact hs

/-- **The budget dominates the exact broadening ratio:** `R(τ) ≤ kOpacOf τ`. This is where
`halfSA_le_coreHalfLevel` is spent: replacing the transcendental half-maximum level by the
escape factor turns the exact ratio into a computable upper bound. Conservative in the
sound direction. -/
theorem lorentzWidthRatio_le_kOpacOf {tau : ℝ} (htau : 0 < tau) :
    lorentzWidthRatio tau ≤ kOpacOf tau := by
  have hpos := coreHalfLevel_pos htau
  have hsa := selfAbsorptionFactor_pos htau.le
  have hhalf : 0 < selfAbsorptionFactor tau / 2 := by linarith
  have hkey : 1 / coreHalfLevel tau ≤ 2 / selfAbsorptionFactor tau := by
    have h := one_div_le_one_div_of_le hhalf (halfSA_le_coreHalfLevel htau)
    rwa [one_div_div] at h
  exact Real.sqrt_le_sqrt (by linarith)

/-- The budget is strictly increasing in the optical depth (inherited from the strict
antitonicity of the escape factor, `SelfAbsorption.selfAbsorptionFactor_strictAntiOn`). -/
theorem kOpacOf_strictMonoOn : StrictMonoOn kOpacOf (Set.Ioi 0) := by
  intro a ha b hb hab
  have ha0 : 0 < a := Set.mem_Ioi.mp ha
  have hb0 : 0 < b := Set.mem_Ioi.mp hb
  have hsa := selfAbsorptionFactor_pos ha0.le
  have hsb := selfAbsorptionFactor_pos hb0.le
  have hlt := selfAbsorptionFactor_strictAntiOn ha hb hab
  have hdiv : 2 / selfAbsorptionFactor a < 2 / selfAbsorptionFactor b :=
    div_lt_div_of_pos_left (by norm_num) hsb hlt
  have hnn : (0 : ℝ) ≤ 2 / selfAbsorptionFactor a - 1 := by
    have hle := selfAbsorptionFactor_le_one ha0.le
    have : (2 : ℝ) ≤ 2 / selfAbsorptionFactor a := by
      rw [le_div_iff₀ hsa]; linarith
    linarith
  exact Real.sqrt_lt_sqrt hnn (by linarith)

/-- Monotone (non-strict) form of `kOpacOf_strictMonoOn`: a larger optical-depth CEILING
gives a larger, still sound, budget. This is what licenses using a `τ` upper bound. -/
theorem kOpacOf_le_of_le {tau tauMax : ℝ} (htau : 0 < tau) (hle : tau ≤ tauMax) :
    kOpacOf tau ≤ kOpacOf tauMax := by
  rcases eq_or_lt_of_le hle with heq | hlt
  · rw [heq]
  · exact (kOpacOf_strictMonoOn (Set.mem_Ioi.mpr htau)
      (Set.mem_Ioi.mpr (lt_trans htau hlt)) hlt).le

/-- **The budget is asymptotically exact in the thin limit:** `kOpacOf τ → 1` as `τ → 0⁺`,
by continuity of `√(2/· − 1)` at `SA → 1` (`SelfAbsorption.selfAbsorptionFactor_tendsto_one`).
So the derived correction switches itself off on an optically thin line. -/
theorem kOpacOf_tendsto_one :
    Filter.Tendsto kOpacOf (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  have h1 : Filter.Tendsto (fun t => 2 / selfAbsorptionFactor t - 1)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (2 / 1 - 1)) :=
    (Filter.Tendsto.div tendsto_const_nhds selfAbsorptionFactor_tendsto_one
      one_ne_zero).sub tendsto_const_nhds
  have h2 := h1.sqrt
  rw [show (2 : ℝ) / 1 - 1 = 1 by norm_num, Real.sqrt_one] at h2
  exact h2

/-- **The exact Lorentzian half-width returns to the intrinsic one as `τ → 0⁺`.** Squeezed
between the constant `1` (`one_lt_lorentzWidthRatio`) and the budget (`kOpacOf_tendsto_one`).
Together with `one_lt_lorentzWidthRatio` and `halfWidth_mono_tau` this is the full
qualitative law: the observed width starts at the intrinsic width, is strictly above it at
every positive `τ`, and never decreases as `τ` grows. -/
theorem lorentzWidthRatio_tendsto_one :
    Filter.Tendsto lorentzWidthRatio (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds kOpacOf_tendsto_one
    ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact (one_lt_lorentzWidthRatio (Set.mem_Ioi.mp ht)).le
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact lorentzWidthRatio_le_kOpacOf (Set.mem_Ioi.mp ht)

/-! ## E. The payoff — discharging `StarkOpacityGuard`'s assumed budget -/

/-- **The width budget in FWHM form.** A Lorentzian line of intrinsic FWHM `2γ` observed at
optical depth `τ` has emergent FWHM `2·γ·R(τ)`, and that is at most `kOpacOf τ` times the
intrinsic FWHM. This is literally the shape of `StarkOpacityGuard`'s `hbudget`. -/
theorem stark_widthObs_le_budget {gamma tau widthObs widthInt : ℝ} (hg : 0 < gamma)
    (htau : 0 < tau) (hint : widthInt = 2 * gamma)
    (hobs : widthObs = 2 * (gamma * lorentzWidthRatio tau)) :
    widthObs ≤ kOpacOf tau * widthInt := by
  have hR := lorentzWidthRatio_le_kOpacOf htau
  rw [hobs, hint]
  nlinarith [hg, hR]

/-- **THE SELF-CONTAINED STARK/LTE CERTIFICATE.** `StarkOpacityGuard.starkOpacityLteCert`'s
soundness needed an ASSUMED opacity budget `kOpac`. Here the budget is the DERIVED
`kOpacOf τ`, and the premise is instead the profile physics: the measured FWHM is the
emergent FWHM of a Lorentzian Stark line of intrinsic FWHM `starkFWHM w nRef neTrue = 2γ`
at optical depth `τ`. Conclusion: the McWhirter condition holds at the TRUE electron
density. The only opacity NUMBER assumed is `τ` itself — and `OpticalDepth.opticalDepth`
binds `τ` to `(T, N, σ₀, ℓ)`; the modelling assumptions (homogeneous slab, a Lorentzian
shape of `τ`-independent HWHM `γ`, and `widthMeas` being exactly that model's emergent
FWHM) are carried by `hstark`/`hmeas` and are listed in the module's limitations. -/
theorem starkOpacity_certificate_sound_of_tau {C T dE w nRef neTrue gamma tau widthMeas : ℝ}
    (hg : 0 < gamma) (htau : 0 < tau)
    (hstark : starkFWHM w nRef neTrue = 2 * gamma)
    (hmeas : widthMeas = 2 * (gamma * lorentzWidthRatio tau))
    (hcert : starkOpacityLteCert C T dE w nRef widthMeas (kOpacOf tau)) :
    mcWhirterCert C T dE neTrue :=
  starkOpacity_certificate_sound
    (by rw [hstark]; exact stark_widthObs_le_budget hg htau rfl hmeas) hcert

/-- **The usable interface: a `τ` UPPER BOUND suffices.** In practice `τ` is estimated, not
known; a ceiling `τ ≤ τmax` is the honest input. Because `kOpacOf` is monotone
(`kOpacOf_le_of_le`), running the repaired certificate at the larger budget `kOpacOf τmax`
is still sound, and still certifies McWhirter at the true electron density. -/
theorem starkOpacity_certificate_sound_of_tau_le
    {C T dE w nRef neTrue gamma tau tauMax widthMeas : ℝ}
    (hg : 0 < gamma) (htau : 0 < tau) (hle : tau ≤ tauMax)
    (hstark : starkFWHM w nRef neTrue = 2 * gamma)
    (hmeas : widthMeas = 2 * (gamma * lorentzWidthRatio tau))
    (hcert : starkOpacityLteCert C T dE w nRef widthMeas (kOpacOf tauMax)) :
    mcWhirterCert C T dE neTrue := by
  refine starkOpacity_certificate_sound (kOpac := kOpacOf tauMax) ?_ hcert
  rw [hstark]
  have h1 : widthMeas ≤ kOpacOf tau * (2 * gamma) :=
    stark_widthObs_le_budget hg htau rfl hmeas
  have h2 : kOpacOf tau ≤ kOpacOf tauMax := kOpacOf_le_of_le htau hle
  nlinarith [hg, h1, h2]

/-! ## F. The flat-profile boundary case: why the intensity domain was not enough -/

/-- **A flat-topped line saturates in intensity but does NOT broaden.** For the rectangular
profile (the indicator of `[0,1]`, `EquivalentWidth.equivWidth_rectangular`'s shape) the set
where the emergent profile exceeds half its central value is the box itself at EVERY
`τ > 0`: opacity broadening is strictly a core-saturation effect and needs a peaked core.
Meanwhile the equivalent width `1 − exp(−τ)` grows strictly with `τ`. This pair of facts is
exactly why `SelfAbsorption` / `CurveOfGrowth` / `EquivalentWidth` — all intensity-domain
models — could not by themselves supply `StarkOpacityGuard`'s width budget. -/
theorem flatProfile_intensity_saturates_width_does_not {S tau₁ tau₂ : ℝ} (hS : 0 < S)
    (htau₁ : 0 < tau₁) (h12 : tau₁ < tau₂) :
    ({x : ℝ | emergentProfile S tau₁ (Set.indicator (Set.Icc (0 : ℝ) 1) (fun _ => (1 : ℝ))) 0
          / 2
        < emergentProfile S tau₁ (Set.indicator (Set.Icc (0 : ℝ) 1) (fun _ => (1 : ℝ))) x}
      = Set.Icc (0 : ℝ) 1)
      ∧ ({x : ℝ | emergentProfile S tau₂
            (Set.indicator (Set.Icc (0 : ℝ) 1) (fun _ => (1 : ℝ))) 0 / 2
          < emergentProfile S tau₂
            (Set.indicator (Set.Icc (0 : ℝ) 1) (fun _ => (1 : ℝ))) x}
        = Set.Icc (0 : ℝ) 1)
      ∧ equivWidth (Set.indicator (Set.Icc (0 : ℝ) 1) (fun _ => (1 : ℝ))) tau₁
        < equivWidth (Set.indicator (Set.Icc (0 : ℝ) 1) (fun _ => (1 : ℝ))) tau₂ := by
  have hbox : ∀ tau : ℝ, 0 < tau →
      {x : ℝ | emergentProfile S tau (Set.indicator (Set.Icc (0 : ℝ) 1) (fun _ => (1 : ℝ))) 0
            / 2
          < emergentProfile S tau (Set.indicator (Set.Icc (0 : ℝ) 1) (fun _ => (1 : ℝ))) x}
        = Set.Icc (0 : ℝ) 1 := by
    intro tau htau
    have h0mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
    have hlt : Real.exp (-tau) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    have hpeak : 0 < S * (1 - Real.exp (-tau)) := mul_pos hS (by linarith)
    ext x
    by_cases hmem : x ∈ Set.Icc (0 : ℝ) 1
    · simp only [Set.mem_ofPred_eq, emergentProfile, Set.indicator_of_mem hmem,
        Set.indicator_of_mem h0mem, mul_one]
      exact iff_of_true (by linarith) hmem
    · simp only [Set.mem_ofPred_eq, emergentProfile, Set.indicator_of_notMem hmem,
        Set.indicator_of_mem h0mem, mul_one, mul_zero, neg_zero, Real.exp_zero, sub_self]
      exact iff_of_false (by linarith) hmem
  refine ⟨hbox tau₁ htau₁, hbox tau₂ (lt_trans htau₁ h12), ?_⟩
  rw [equivWidth_rectangular, equivWidth_rectangular]
  have := Real.exp_lt_exp.mpr (show -tau₂ < -tau₁ by linarith)
  linarith

/-! ### Non-vacuity witnesses

The witnesses below run the derived budget on explicit numbers and show it BITES: at
`τ = 2` the budget is a genuine `≤ 2×` width haircut (not `1`, not vacuous), the exact
broadening ratio is strictly between `1` and that budget, and the repaired
`StarkOpacityGuard` certificate is satisfiable at the DERIVED `kOpacOf 2` on the same data
family used there — with a real margin after the haircut. -/

/-- The derived budget at `τ = 2` is a genuine, finite, non-trivial factor:
`1 ≤ kOpacOf 2 ≤ 2`. Uses only `e² > 5`, from `Real.exp_one_gt_d9`. -/
theorem kOpacOf_two_bounds : 1 ≤ kOpacOf 2 ∧ kOpacOf 2 ≤ 2 := by
  have hexp1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have hsum : Real.exp 1 * Real.exp 1 = Real.exp 2 := by
    rw [← Real.exp_add]
    norm_num
  have hexp2 : (5 : ℝ) < Real.exp 2 := by nlinarith [Real.exp_pos 1]
  have hneg : Real.exp (-2 : ℝ) = (Real.exp 2)⁻¹ := Real.exp_neg 2
  have hlt : Real.exp (-2 : ℝ) < 1 / 5 := by
    rw [hneg, inv_eq_one_div, div_lt_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hsa : selfAbsorptionFactor 2 = (1 - Real.exp (-2)) / 2 := by
    rw [selfAbsorptionFactor, if_neg (by norm_num : (2 : ℝ) ≠ 0)]
  have hsapos : 0 < selfAbsorptionFactor 2 := selfAbsorptionFactor_pos (by norm_num)
  refine ⟨one_le_kOpacOf (by norm_num), ?_⟩
  have hbound : 2 / selfAbsorptionFactor 2 - 1 ≤ 4 := by
    rw [hsa] at hsapos ⊢
    rw [sub_le_iff_le_add, div_le_iff₀ hsapos]
    linarith
  have h4 : Real.sqrt (2 / selfAbsorptionFactor 2 - 1) ≤ Real.sqrt 4 :=
    Real.sqrt_le_sqrt hbound
  have h5 : Real.sqrt (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  rw [kOpacOf]
  linarith

/-- The EXACT Lorentzian broadening at `τ = 2` is strictly inside the derived budget:
`1 < R(2) ≤ kOpacOf 2 ≤ 2`. The observed FWHM of a `τ = 2` Stark line is genuinely wider
than the intrinsic one, and by a factor the budget covers. -/
theorem lorentzWidthRatio_two_bounds :
    1 < lorentzWidthRatio 2 ∧ lorentzWidthRatio 2 ≤ 2 :=
  ⟨one_lt_lorentzWidthRatio (by norm_num),
    le_trans (lorentzWidthRatio_le_kOpacOf (by norm_num)) kOpacOf_two_bounds.2⟩

/-- **Sharpened lower end of the `τ = 2` bracket:** `1.5 ≤ R(2)`. With
`lorentzWidthRatio_two_bounds` this traps the exact Lorentzian broadening at `τ = 2` in
`[1.5, 2]` (the true value is ≈ 1.591), so the conservatism of `kOpacOf 2` over the exact
ratio is bounded. Uses only `e < 2.7182818286` (`Real.exp_one_lt_d9`),
`log 2 < 0.6931471808` (`Real.log_two_lt_d9`) and `log z ≥ 1 − 1/z`. -/
theorem lorentzWidthRatio_two_lower : 1.5 ≤ lorentzWidthRatio 2 := by
  have hpos := coreHalfLevel_pos (show (0 : ℝ) < 2 by norm_num)
  have he1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have hsum : Real.exp 1 * Real.exp 1 = Real.exp 2 := by
    rw [← Real.exp_add]
    norm_num
  have hexp2 : Real.exp 2 < 8 := by nlinarith [Real.exp_pos 1]
  have hneg : Real.exp (-2 : ℝ) = (Real.exp 2)⁻¹ := Real.exp_neg 2
  have hgt : (1 : ℝ) / 8 < Real.exp (-2) := by
    rw [hneg, inv_eq_one_div, div_lt_div_iff₀ (by norm_num) (Real.exp_pos 2)]
    linarith
  have hlog98 : Real.log (9 / 8) ≤ Real.log (1 + Real.exp (-2)) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hlb : (1 : ℝ) / 9 ≤ Real.log (9 / 8) := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 8 / 9 by norm_num)
    have hinv : Real.log (8 / 9) = -Real.log (9 / 8) := by
      rw [show (8 : ℝ) / 9 = (9 / 8)⁻¹ by norm_num, Real.log_inv]
    rw [hinv] at h
    linarith
  have hlog2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hh : coreHalfLevel 2 ≤ 4 / 13 := by
    rw [coreHalfLevel, div_le_iff₀ (show (0 : ℝ) < 2 by norm_num)]
    linarith
  have hstep : (2.25 : ℝ) ≤ 1 / coreHalfLevel 2 - 1 := by
    rw [le_sub_iff_add_le, le_div_iff₀ hpos]
    linarith
  have hsq : Real.sqrt 2.25 ≤ lorentzWidthRatio 2 := by
    rw [lorentzWidthRatio]
    exact Real.sqrt_le_sqrt hstep
  have h15 : Real.sqrt (2.25 : ℝ) = 1.5 := by
    rw [show (2.25 : ℝ) = 1.5 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1.5)]
  linarith

-- Non-vacuity (the derived budget is a satisfiable certificate): the `StarkOpacityGuard`
-- data family `w = 0.02`, `n_ref = 10¹⁶`, measured FWHM `0.016` nm, now at the DERIVED
-- budget `kOpacOf 2 ≤ 2` instead of an assumed `kOpac = 2`. Raw estimate `4·10¹⁵`;
-- after the derived haircut still `≥ 2·10¹⁵ ≥ 1.28·10¹⁵`.
example : starkOpacityLteCert 1.6e12 10000 2 0.02 1e16 0.016 (kOpacOf 2) := by
  have hs : Real.sqrt 10000 = 100 := by
    rw [show (10000 : ℝ) = 100 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 100)]
  obtain ⟨hk1, hk2⟩ := kOpacOf_two_bounds
  have hk0 : (0 : ℝ) < kOpacOf 2 := lt_of_lt_of_le zero_lt_one hk1
  refine ⟨by norm_num, by norm_num, hk1, ?_⟩
  rw [mcWhirterCert, starkDensity, hs, le_div_iff₀ hk0]
  nlinarith [hk2]

-- Non-vacuity (the emergent-profile half-max characterization is exercised): for a
-- Lorentzian Stark line of intrinsic HWHM `γ = 0.004` nm at `τ = 2`, the point
-- `γ·R(2)` really is a half-maximum point of the emergent profile with source strength
-- `S = 1`, and it lies strictly outside the intrinsic HWHM.
example :
    emergentProfile 1 2 (lorentzShape 0.004) (0.004 * lorentzWidthRatio 2)
        = emergentProfile 1 2 (lorentzShape 0.004) 0 / 2
      ∧ (0.004 : ℝ) < 0.004 * lorentzWidthRatio 2 := by
  constructor
  · rw [emergentProfile_half_iff (by norm_num) (by norm_num)
      (lorentzShape_zero (by norm_num))]
    exact lorentzShape_widthRatio (by norm_num) (by norm_num)
  · nlinarith [one_lt_lorentzWidthRatio (show (0 : ℝ) < 2 by norm_num)]

-- Non-vacuity (THE PAYOFF theorem exercised end-to-end): the hypotheses of
-- `starkOpacity_certificate_sound_of_tau` are JOINTLY satisfiable on explicit data, so the
-- theorem is not vacuously true. Intrinsic Stark HWHM `γ = 0.004` nm with `w = 0.02`,
-- `n_ref = 10¹⁶` pins the TRUE density at `nₑ = 2·10¹⁵` through `starkFWHM = 2γ`; at `τ = 2`
-- the measured FWHM is the emergent `2·γ·R(2)` (an inflation of ≥ 1.5×), and the certificate
-- run at the DERIVED budget `kOpacOf 2` still clears McWhirter with margin
-- (`≥ 1.5·10¹⁵` against the `1.28·10¹⁵` bound). All three hypotheses hold simultaneously.
example : mcWhirterCert 1.6e12 10000 2 2e15 := by
  have hs : Real.sqrt 10000 = 100 := by
    rw [show (10000 : ℝ) = 100 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 100)]
  have hk1 := kOpacOf_two_bounds.1
  have hk2 := kOpacOf_two_bounds.2
  have hk0 : (0 : ℝ) < kOpacOf 2 := lt_of_lt_of_le zero_lt_one hk1
  have hR := lorentzWidthRatio_two_lower
  refine starkOpacity_certificate_sound_of_tau (gamma := 0.004) (tau := 2) (w := 0.02)
    (nRef := 1e16) (by norm_num) (by norm_num) (by norm_num [starkFWHM]) rfl
    ⟨by norm_num, by norm_num, hk1, ?_⟩
  rw [mcWhirterCert, starkDensity, hs, le_div_iff₀ hk0,
    show (1e16 : ℝ) * (2 * (0.004 * lorentzWidthRatio 2)) / (2 * 0.02)
      = 2e15 * lorentzWidthRatio 2 by ring]
  nlinarith [hR, hk2]


end CflibsFormal
