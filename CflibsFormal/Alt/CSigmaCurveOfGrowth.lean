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
(`csigma_universal_line`). That construction is purely optically thin, and it assumes ONE
temperature `T` for every species and both stages (a homogeneous plasma; see the scope note
in `CSigma.lean`). Line-of-sight integration over an inhomogeneous plasma generally gives
neutral and ion lines different apparent temperatures; nothing here covers that case.

This module adds the **self-absorption droop**. At finite optical depth `τ` the measured
line is dimmed, in the flat-profile model, by the escape factor
`SA(τ) = (1 − exp(−τ))/τ ∈ (0, 1]` (`SelfAbsorption.selfAbsorptionFactor`), so the
concentration-normalized **measured** ordinate sits BELOW the universal line by exactly
`ln SA(τ)`. The optical depth carries the **σ (cross-section) weighting** of the
Aragón–Aguilera Cσ graph, `τ = N · σ_ℓ · ℓ` (`csigmaOpticalDepth`), with `N` the species
number density. Here `σ_ℓ` is an uninterpreted positive parameter: the module does not
construct a cross-section from atomic data (for instance the companion `csigma.py`'s
lower-level, stimulated-emission-corrected cross-section, which depends on `T`), so the
density droop holds with `σ_ℓ` held fixed (for a cross-section built from atomic data, at
fixed `T`). So the droop is strictly monotone
(deeper) in `τ`, hence in `N` — the optically-thick lines bend down off the universal line.
This module is not a formal twin of `csigma.py`, which fits a Doppler curve of growth.

**Note on "σ".** In `csigmaConcentrationLog`/`csigmaUniversalOrdinate` the subtracted
`ln(N_s/U_s)` is the *concentration/partition* normalization, NOT a cross-section; the loose
"σ-normalization" wording elsewhere refers to that collapse. The genuine cross-section `σ_ℓ`
enters only here, through the optical depth `τ = N σ_ℓ ℓ` of `csigmaOpticalDepth`.

**What is and is not proved (honest scope).** The headline droop identity
(`csigma_curve_of_growth_droop`) is a legitimate but mathematically shallow BRIDGE
(`csigma_universal_line` + `Real.log_mul`): it pins the droop magnitude as exactly `ln SA(τ)`
and shows the concentration normalization `ln(N/U)` cancels. The non-trivial content is the
strict droop `csigma_curve_of_growth_lt` and the shape theorems
`csigma_curve_of_growth_strictAntiOn` / `csigma_curve_of_growth_density_droop`, which rest on the
escape-factor monotonicity `SelfAbsorption.selfAbsorptionFactor_strictAntiOn` (the derivative
argument, proved beside the other `selfAbsorptionFactor_*` lemmas).

**APPROXIMATION model.** `SA(τ) = (1 − exp(−τ))/τ` is the line-center / flat-profile ESCAPE
FACTOR inherited from the radiative-transfer slab kernel `SelfAbsorption.slabIntensity`. It is
exact for a rectangular profile or at one frequency; applied to the integrated intensity of a
peaked line it understates the escaping fraction, so the droop `ln SA(τ)` is overstated (see the
scope block of `SelfAbsorption`). `selfAbsorptionFactor` carries the model tag APPROXIMATION,
so every theorem here publishes APPROXIMATION. It is NOT the full profile-integrated
Aragón–Aguilera curve of growth: the slope-1 → slope-½ Lorentz-wing knee (Rezaei 2016, Eqs. 29–31,
the `√x` asymptote) is OUT OF SCOPE, as are the Voigt `τ(ν)`, inversion of `(C, σ_ℓ)` from a
measured curve, and multi-element pooled fits. Each curve-of-growth-shape theorem below repeats
this qualifier. Each theorem is an exact statement about the flat-profile model; the
approximation is in the model.

## Literature

* Aragón & Aguilera, "CSigma graphs: A new approach for plasma characterization in
  laser-induced breakdown spectroscopy", *J. Quant. Spectrosc. Radiat. Transfer* **149** (2014)
  90–102, DOI 10.1016/j.jqsrt.2014.07.026 — the Cσ graph, the line cross-section `σ_ℓ`
  (Eqs. 16–18) and the line optical depth `τ_ℓ = 10⁻² C · N ℓ · σ_ℓ` (Eq. 19), so the abscissa
  `10⁻² C σ_ℓ` is proportional to `τ`; one Cσ graph per ionization stage. Equation numbers are
  from the authors' accepted manuscript. A corrigendum, *JQSRT* **159** (2015) 94–95, DOI
  10.1016/j.jqsrt.2015.03.001, was not opened, so whether it amends these is unchecked.
* Aguilera & Aragón, "Multi-element Saha–Boltzmann and Boltzmann plots in laser-induced
  plasmas", *Spectrochim. Acta Part B* **62** (2007) 378 — the optically-thin universal /
  master line, recovered here as the `τ → 0⁺` asymptote.
* F. Rezaei, "Optically Thick Laser-Induced Plasmas in Spectroscopic Analysis", ch. 13 of
  *Plasma Science and Technology – Progress in Physical States and Chemical Reactions* (InTech,
  2016), DOI 10.5772/61941 — a review chapter: the line-centre self-absorption coefficient
  `SA = (1 − exp(−τ₀))/τ₀` (Eq. 16), the profile-integrated intensity
  `I = I_P ∫ (1 − exp(−τ(ν))) dν` with the LTE `τ(ν)` (Eqs. 19–20, presented there as the
  Aragón–Aguilera curve of growth), and the slope-1 / slope-½ asymptotes and their intersection
  (Eqs. 29–31), which are explicitly OUT OF SCOPE here.
* Gornushkin, Anzano, King, Smith, Omenetto, Winefordner, "Curve of growth methodology applied
  to laser-induced plasma emission spectroscopy", *Spectrochim. Acta Part B* **54** (1999)
  491–503 — the slab emission `I = S·(1 − exp(−τ))` underlying `SelfAbsorption.slabIntensity`.
-/

namespace CflibsFormal.Alt

open CflibsFormal
open Finset Real
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- **Cσ optical depth** `τ = σ_ℓ · ℓ · C`: the line cross-section `σ_ℓ`, the absorption path
length `ℓ`, and the absorber column scale `C` (the species number density `N` along the line
of sight). This is the **cross-section weighting** of the Aragón–Aguilera Cσ graph
(JQSRT 149 (2014) 90): the abscissa `Cσ_ℓ` is proportional to `τ`, and it is `σ_ℓ` — not the
`ln(N/U)` normalization — that is the line cross-section. Here `σ_ℓ` is a free parameter: no
cross-section is computed from atomic data, and `τ` is a plain product. -/
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
strict/shape droop theorems (`csigma_curve_of_growth_lt`, `…_strictAntiOn`, `…_density_droop`),
powered by the escape-factor monotonicity `SelfAbsorption.selfAbsorptionFactor_strictAntiOn`.

APPROXIMATION: exact for the flat-profile escape factor `SA(τ) = (1 − exp(−τ))/τ`, which only
approximates the Aragón–Aguilera Cσ curve of growth (for a peaked profile it overstates the
droop); the profile-integrated slope-½ Lorentz wing is out of scope. -/
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

APPROXIMATION: exact for the flat-profile (escape-factor) model, which only approximates the
Aragón–Aguilera Cσ curve of growth (for a peaked profile it overstates the droop); the
profile-integrated slope-½ Lorentz wing is out of scope. -/
theorem csigma_curve_of_growth_thin [Nonempty ι] {kB T N Fcal : ℝ} {g E A : ι → ℝ}
    (hg : ∀ k, 0 < g k) (hN : 0 < N) (hFcal : 0 < Fcal) (hA : ∀ k, 0 < A k) (k : ι) :
    csigmaSelfAbsorbedUniversalOrdinate kB T N Fcal g E A k 0
      = Real.log Fcal - E k / (kB * T) := by
  rw [csigma_curve_of_growth_droop hg hN hFcal hA k le_rfl]
  simp [selfAbsorptionFactor]

/-- **The droop is downward (non-strict).** For any `τ ≥ 0` the concentration-normalized
measured ordinate lies AT OR BELOW the universal line `ln F − E_k/(k_B T)`: self-absorption
only dims, so `ln SA(τ) ≤ 0`. Neglecting it biases the inferred composition downward.

APPROXIMATION: exact for the flat-profile (escape-factor) model, which only approximates the
Aragón–Aguilera Cσ curve of growth (for a peaked profile it overstates the droop); the
profile-integrated slope-½ Lorentz wing is out of scope. -/
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

APPROXIMATION: exact for the flat-profile (escape-factor) model, which only approximates the
Aragón–Aguilera Cσ curve of growth (for a peaked profile it overstates the droop); the
profile-integrated slope-½ Lorentz wing is out of scope. -/
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

APPROXIMATION: exact for the flat-profile (escape-factor) model, which only approximates the
Aragón–Aguilera Cσ curve of growth (for a peaked profile it overstates the droop); the
profile-integrated slope-½ Lorentz wing is out of scope. -/
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

/-- **The Cσ curve of growth is strictly antitone in optical depth.** As a function of `τ`,
the concentration-normalized measured ordinate is STRICTLY DECREASING on `(0, ∞)`: deeper
optical depth means a strictly deeper droop below the universal line. Reduces to
`selfAbsorptionFactor_strictAntiOn` through the droop identity and strict monotonicity of
`Real.log`. This is the shape statement of the Cσ curve of growth.

APPROXIMATION: exact for the flat-profile (escape-factor) model, which only approximates the
Aragón–Aguilera Cσ curve of growth (for a peaked profile it overstates the droop); the
profile-integrated slope-½ Lorentz wing (the slope-1 → slope-½ knee) is out of scope — only
the strict monotone descent of the escape-factor branch is proved. -/
theorem csigma_curve_of_growth_strictAntiOn [Nonempty ι] {kB T N Fcal : ℝ} {g E A : ι → ℝ}
    (hg : ∀ k, 0 < g k) (hN : 0 < N) (hFcal : 0 < Fcal) (hA : ∀ k, 0 < A k) (k : ι) :
    StrictAntiOn (fun tau => csigmaSelfAbsorbedUniversalOrdinate kB T N Fcal g E A k tau)
      (Set.Ioi 0) := by
  intro a ha b hb hab
  beta_reduce
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
concentration-normalized measured ordinate is STRICTLY ANTITONE on `(0, ∞)`. Within the model,
the universal-line value `ln F − E_k/(k_B T)` is `N`-independent (the concentration
normalization cancels), so the ONLY `N`-dependence left is the self-absorption droop, and
increasing the density `N` strictly deepens it through `τ = N σ_ℓ ℓ`. Here `σ_ℓ` stands for the
line cross-section of the Aragón–Aguilera Cσ graph but is a free positive parameter held fixed;
a cross-section built from atomic data depends on `T`, so the statement is at fixed `T` (the
module's one-temperature, homogeneous-plasma model). Proved by the same mechanism
as `csigma_curve_of_growth_strictAntiOn` — the droop identity cancels the direct `N`-dependence,
leaving the escape-factor descent — composed with `τ = σ_ℓ ℓ N` strictly increasing in `N`.

APPROXIMATION: exact for the flat-profile (escape-factor) model, which only approximates the
Aragón–Aguilera Cσ curve of growth (for a peaked profile it overstates the droop); the
profile-integrated slope-½ Lorentz wing is out of scope. -/
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
  beta_reduce
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
