/-
Copyright (c) 2026 Brian Squires. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Squires
-/
import Mathlib
import CflibsFormal.ForwardMap

/-!
# Inhomogeneity bias: the sign of the Boltzmann-plot error is a theorem

Every other module of this development assumes the observed spectrum comes from **one**
plasma state (one `T`, one `N`, one `U`). Real LIBS spectra do not: a single shot integrates
over a spatially inhomogeneous plume, over the gate window, and (for accumulated spectra)
over shot-to-shot fluctuations. The standard defence in the CF-LIBS literature is the
folklore claim that *mixing biases the Boltzmann plot in a known direction*. This module
turns that excuse into a **sign-definite theorem**.

## The model

Write the observed ordinate of the Boltzmann plot for the line with upper level `k` as
`y k = log (I k / (g k A k))`. If the observation is a **positive mixture** over plasma
states `z` (zones, time slices, shots) with weights `w z > 0` and inverse temperatures
`b z = 1/(k_B T_z)`, then

  `y k = log (∑ z, w z · exp (−(E k · b z)))  =  logMixture w b (E k)`,

the log of a (discrete) **Laplace transform of a positive measure** in the variable `E k`.
`mixedLineIntensity` builds exactly this from `ForwardMap.lineIntensity`, one summand per
zone, and `mixed_boltzmann_ordinate` proves the identification, with
`w z = Fcal · N z / U(T_z)` (`zoneWeight`) and `b z = 1/(k_B T_z)` (`zoneBeta`).

## The engine

`logMixture_tangent_le` is the whole content: **the observed Boltzmann plot never falls
below the straight line of a homogeneous plasma tangent to it.** Concretely, for any anchor
energy `a`,

  `logMixture w b a − (E − a) · tiltMean w b a  ≤  logMixture w b E`   for all `E`,

where `tiltMean w b a = ∑ z, tiltWeight w b a z · b z` is the **intensity-weighted (i.e.
exponentially tilted) mean inverse temperature at the anchor line `a`** — the mean of `b`
under the probability weights `tiltWeight w b a z = w z e^{−a b z} / ∑ w e^{−a b}`, which are
precisely each zone's fractional contribution to the *observed intensity of that line*.
The proof is Jensen's inequality for `Real.exp` (`convexOn_exp.map_sum_le`); the strict form
`logMixture_tangent_lt` uses `strictConvexOn_exp.map_sum_lt` and needs only two zones with
`b j ≠ b k`. No derivatives, no measure theory, no temperature box.

Three sign-definite consequences follow, each by applying the tangent inequality at one
anchor and reading off the other endpoint:

* `intercept_le_log_total` / `mixed_intercept_le_log_column` — the two-line Boltzmann
  **intercept is a LOWER bound** on the true log column density `log (∑ z, w z)`.
* `pairSlope_le_tiltMean` / `mixed_apparentBeta_le_tiltMean` — the apparent inverse
  temperature `β_app = (y_i − y_j)/(E_j − E_i)` is **at most** `tiltMean` at the lower line;
  `tiltMean_le_pairSlope` brackets it from below by `tiltMean` at the *upper* line. Feeding
  the upper bound to `apparentTemperature_ge` makes the apparent temperature an **UPPER
  bound** on `1/(k_B · tiltMean)`. That step needs `β_app > 0`, which is *not* automatic
  from convexity; `pairSlope_pos` supplies it from `∀ z, 0 < b z` (every zone at a positive
  temperature). The composed observable statement is left to the caller.
* `pairSlope_antitone` / `mixed_apparentBeta_antitone` — the Boltzmann plot is convex:
  `β_app` from a higher-energy line pair never exceeds `β_app` from a lower-energy pair, so
  the apparent temperature rises monotonically with the fitted energy window.

Both bounds are **sharp in the homogeneous limit**: `intercept_eq_log_total_homogeneous`,
`apparentBeta_eq_homogeneous` and `tiltMean_homogeneous` (which puts the *other* side of the
temperature bound at `β` too, so that bound is saturated and not merely satisfied) show they
hold with equality whenever all mixed states share one temperature. Sharpness is *not* an
iff: the converse is proved only under the strict theorems' hypotheses, and
is **not** an iff: `logMixture_secant_lt` needs `E₀ < E₁`, so an intercept read at `E = 0`
from a line pair whose *lower* line sits at `E₁ = 0` is exact even for an inhomogeneous
plasma — the secant then passes through `y(0)` itself. Strictness is claimed only when the
lower fitted line lies strictly above the extrapolation point.

## Literature and scope

**This is not new physics, and the module does not claim to be.** The identical argument —
log of a Laplace transform of a positive measure is convex, its derivatives are cumulants of
the exponentially tilted measure — was transplanted into plasma spectroscopy fifty years ago
for the X-ray differential emission measure by Craig, I. J. D. & Brown, J. C.,
*"Fundamental limitations of X-ray spectra as diagnostics of plasma temperature structure"*,
Astron. Astrophys. **49** (1976) 239. The LIBS-side estimator whose bias is bounded here is
the multi-element Saha–Boltzmann / Boltzmann plot of Aguilera, J. A. & Aragón, C.,
*"Multi-element Saha–Boltzmann and Boltzmann plots in laser-induced plasmas"*,
Spectrochim. Acta B **62** (2007) 378; that paper is cited for the **estimator**, not for the
convexity argument, which is Craig & Brown's. What is new here is only the **machine-checked
statement with explicit hypotheses**.

**Honesty caveats — all four are load-bearing.**

1. *Exact-noiseless limit.* Every inequality below is stated for the exact forward model with
   no measurement noise, no self-absorption, and no atomic-data error. Adding noise to the
   ordinates destroys the sign guarantee pointwise; the bound is a statement about the
   deterministic mixing bias only, not about a finite-sample estimate.
2. *Which mean temperature.* The bounded quantity is **not** the arithmetic mean temperature
   and **not** a volume-weighted mean temperature. It is `1/(k_B · tiltMean w b (E i))` — a
   harmonic-type mean of `T` over the zones, weighted by each zone's *intensity share of the
   lower fitted line*. That weighting depends on `E i`, so different line pairs bound
   different means. Claiming "apparent T overestimates the mean temperature" without naming
   the tilt is an overclaim; this module does not make it.
3. *The curvature is not a practical diagnostic.* `pairSlope_strictAnti` proves the
   curvature is strictly nonzero whenever two zones differ, but strict is not measurable:
   for the referee's realistic two-region case the full convex signature amounted to only
   ~0.08 nats peak-to-peak over a 4 eV energy span — the same order as residual
   self-absorption and atomic-data scatter. The **bound** is supported; a curvature-based
   inhomogeneity *diagnostic* is **not**, and nothing here should be read as endorsing one.
4. *The intercept bound is on `log (∑ z, w z)`, NOT on a column density in cm⁻².* The bounded
   quantity is `∑ z, Fcal · N z / U(T_z)`: the calibration constant `Fcal` is still inside it
   and each `N z` is still divided by its **own** zone partition function. Recovering `∑ z, N z`
   from the intercept requires dividing by `Fcal` and multiplying by `U` evaluated at the
   *fitted* temperature — and that fitted temperature is itself biased (caveat 2). Nothing in
   this module bounds the composite error of that conversion, so **"CF-LIBS underestimates the
   concentration" does not follow** from `intercept_le_log_total`, and must not be inferred.

**Scope tags.** Everything from `mixture_pos` through `apparentBeta_eq_homogeneous` — the
mixture/Jensen core, all three consequences and all three sharpness results — is `PURE-MATH`:
it is a statement about positive finite mixtures of exponentials and contains no physics. Only
the `mixed*` / `zone*` results are `REDUCED` — they read the pure-math core through
`ForwardMap.lineIntensity`, and therefore inherit its optically-thin, LTE-per-zone,
calibration-absorbed assumptions.

**Deliberately NOT proved.** (a) The bounds are for the **two-line (pairwise) fit**, i.e. the
exact secant through two Boltzmann points; the analogous statement for the `n`-line OLS fit
of `OLS.olsSlope` is true but needs the endpoint-residual sign of a least-squares fit to
convex data, which is a separate development. (b) The mixture is **finite**; the general
positive-measure (continuous DEM) case is not formalized here. (c) Sharpness is proved only
as *saturation in the homogeneous limit*; no quantitative bound on the size of the bias for a
given degree of inhomogeneity is proved, and none should be inferred.
-/

namespace CflibsFormal

open Finset Real
open scoped BigOperators

-- `ζ` indexes the mixed-over plasma states: spatial zones, time slices, or shots.
-- `ι` indexes the spectral lines of the fitted species.
variable {ζ : Type*} [Fintype ζ]
variable {ι : Type*} [Fintype ι]

/-! ### The pure-math core: positive finite mixtures of exponentials -/

/-- Discrete Laplace transform of the positive measure with masses `w z` at abscissae `b z`:
`M(E) = ∑ z, w z · exp (−(E · b z))`. In the physics reading `b z = 1/(k_B T_z)` is a zone's
inverse temperature and `w z` its (partition-normalized, calibration-absorbed) column
density, so `M(E k)` is the observed `I k / (g k A k)`. -/
noncomputable def mixture (w b : ζ → ℝ) (E : ℝ) : ℝ :=
  ∑ z, w z * Real.exp (-(E * b z))

/-- The Boltzmann-plot ordinate of a mixed observation: `log` of the discrete Laplace
transform. This is the function whose convexity in `E` is the entire content of the module. -/
noncomputable def logMixture (w b : ζ → ℝ) (E : ℝ) : ℝ := Real.log (mixture w b E)

/-- **Exponentially tilted weight.** `tiltWeight w b a z = w z e^{−a b z} / M(a)` is zone
`z`'s *fractional share of the observed intensity of the line at energy `a`*. These are
nonnegative and sum to one (`tiltWeight_sum_one`), i.e. they form the tilted probability
measure at anchor `a`. -/
noncomputable def tiltWeight (w b : ζ → ℝ) (a : ℝ) (z : ζ) : ℝ :=
  w z * Real.exp (-(a * b z)) / mixture w b a

/-- **Tilted mean inverse temperature at the anchor energy `a`**:
`⟨b⟩_a = ∑ z, tiltWeight w b a z · b z`. This — not the arithmetic mean of `b`, and not the
reciprocal of any volume-averaged temperature — is the quantity the apparent Boltzmann
temperature bounds. -/
noncomputable def tiltMean (w b : ζ → ℝ) (a : ℝ) : ℝ :=
  ∑ z, tiltWeight w b a z * b z

/-- Value at `E` of the straight line drawn through the two Boltzmann points
`(E₁, y₁)` and `(E₂, y₂)`: the exact two-line CF-LIBS fit. Its value at `E = 0` is the
classical Boltzmann-plot intercept. -/
noncomputable def secantAt (E₁ y₁ E₂ y₂ E : ℝ) : ℝ :=
  y₁ + (y₂ - y₁) / (E₂ - E₁) * (E - E₁)

/-- **Apparent inverse temperature** from a line pair: `β_app = (y₁ − y₂)/(E₂ − E₁)`, the
negated Boltzmann-plot slope. The classical apparent temperature is `1/(k_B β_app)`. -/
noncomputable def apparentBeta (E₁ y₁ E₂ y₂ : ℝ) : ℝ := (y₁ - y₂) / (E₂ - E₁)

/-- The mixture is a strictly positive observable, so its `log` is genuine. -/
theorem mixture_pos [Nonempty ζ] {w b : ζ → ℝ} (hw : ∀ z, 0 < w z) (E : ℝ) :
    0 < mixture w b E :=
  Finset.sum_pos (fun z _ => mul_pos (hw z) (Real.exp_pos _)) univ_nonempty

/-- Tilted weights are strictly positive. -/
theorem tiltWeight_pos [Nonempty ζ] {w b : ζ → ℝ} (hw : ∀ z, 0 < w z) (a : ℝ) (z : ζ) :
    0 < tiltWeight w b a z :=
  div_pos (mul_pos (hw z) (Real.exp_pos _)) (mixture_pos hw a)

/-- The tilted weights form a probability vector: they sum to one. This is what licenses
Jensen's inequality against them. -/
theorem tiltWeight_sum_one [Nonempty ζ] {w b : ζ → ℝ} (hw : ∀ z, 0 < w z) (a : ℝ) :
    ∑ z, tiltWeight w b a z = 1 := by
  have hMa : 0 < mixture w b a := mixture_pos hw a
  simp only [tiltWeight, ← Finset.sum_div]
  exact div_self hMa.ne'

/-- The tilted average of the linear exponent `−(E − a)·b` is `−(E − a)·⟨b⟩_a`. Pure
bookkeeping: it is the step that identifies Jensen's left-hand side with the tangent line. -/
theorem tiltWeight_exponent_sum (w b : ζ → ℝ) (a E : ℝ) :
    ∑ z, tiltWeight w b a z * (-((E - a) * b z)) = -((E - a) * tiltMean w b a) := by
  have h : ∀ z : ζ, tiltWeight w b a z * (-((E - a) * b z))
      = (-(E - a)) * (tiltWeight w b a z * b z) := fun z => by ring
  rw [Finset.sum_congr rfl (fun z _ => h z), ← Finset.mul_sum]
  simp only [tiltMean]
  ring

/-- Reindexing the mixture through the tilt: `∑ z, p_a(z) · e^{−(E−a) b z} = M(E)/M(a)`.
This is what identifies Jensen's right-hand side with the observed ordinate ratio. -/
theorem tiltWeight_mixture [Nonempty ζ] {w b : ζ → ℝ} (hw : ∀ z, 0 < w z) (a E : ℝ) :
    ∑ z, tiltWeight w b a z * Real.exp (-((E - a) * b z)) = mixture w b E / mixture w b a := by
  have hMa : 0 < mixture w b a := mixture_pos hw a
  have hterm : ∀ z : ζ, tiltWeight w b a z * Real.exp (-((E - a) * b z))
      = w z * Real.exp (-(E * b z)) / mixture w b a := by
    intro z
    have h1 : Real.exp (-(E * b z))
        = Real.exp (-(a * b z)) * Real.exp (-((E - a) * b z)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    simp only [tiltWeight, h1]
    field_simp
  rw [Finset.sum_congr rfl (fun z _ => hterm z), ← Finset.sum_div]
  simp only [mixture]

/-- At zero energy the mixture collapses to the total mass: `y(0) = log (∑ z, w z)`. In the
physics reading this is the log of the true (partition-normalized, calibration-absorbed)
column density summed over all zones — the quantity CF-LIBS reads off the intercept. -/
theorem logMixture_zero (w b : ζ → ℝ) : logMixture w b 0 = Real.log (∑ z, w z) := by
  simp only [logMixture, mixture, zero_mul, neg_zero, Real.exp_zero, mul_one]

/-- **The engine: the observed Boltzmann plot lies above its tangent homogeneous line.**

For any anchor energy `a`, the straight line with ordinate `logMixture w b a` at `a` and
slope `−tiltMean w b a` — that is, the Boltzmann line of the *fictitious homogeneous plasma
at the tilted temperature* — never lies above the observed mixed plot. Equivalently
`E ↦ logMixture w b E` is convex, in supporting-hyperplane form.

Proof: Jensen's inequality for `Real.exp` against the tilted probability weights. No
derivatives are needed, and no bound on the temperature range is assumed. -/
theorem logMixture_tangent_le [Nonempty ζ] {w b : ζ → ℝ} (hw : ∀ z, 0 < w z) (a E : ℝ) :
    logMixture w b a - (E - a) * tiltMean w b a ≤ logMixture w b E := by
  have hMa : 0 < mixture w b a := mixture_pos hw a
  have hME : 0 < mixture w b E := mixture_pos hw E
  have hJ : Real.exp (∑ z, tiltWeight w b a z * (-((E - a) * b z)))
      ≤ ∑ z, tiltWeight w b a z * Real.exp (-((E - a) * b z)) := by
    have hcvx := convexOn_exp.map_sum_le (t := (Finset.univ : Finset ζ))
      (w := tiltWeight w b a) (p := fun z => -((E - a) * b z))
      (fun z _ => (tiltWeight_pos hw a z).le) (tiltWeight_sum_one hw a)
      (fun z _ => Set.mem_univ _)
    simpa only [smul_eq_mul] using hcvx
  rw [tiltWeight_exponent_sum, tiltWeight_mixture hw] at hJ
  have hlog := Real.log_le_log (Real.exp_pos _) hJ
  rw [Real.log_exp, Real.log_div hME.ne' hMa.ne'] at hlog
  simp only [logMixture]
  linarith

/-- **Strict form of the engine.** As soon as two mixed states have genuinely different
inverse temperatures (`b j ≠ b k`) and the probe energy differs from the anchor (`E ≠ a`),
the tangent inequality is strict: the mixed Boltzmann plot is *strictly* convex there.

This is the non-degeneracy statement behind the two-state case: for `ζ = Fin 2` with
`w 0, w 1 > 0` and `b 0 ≠ b 1` the hypothesis `hb` is discharged by `⟨0, 1, _⟩`.

Strict is *not* the same as measurable — see caveat 3 in the module docstring. -/
theorem logMixture_tangent_lt [Nonempty ζ] {w b : ζ → ℝ} (hw : ∀ z, 0 < w z)
    {a E : ℝ} (hEa : E ≠ a) (hb : ∃ j k, b j ≠ b k) :
    logMixture w b a - (E - a) * tiltMean w b a < logMixture w b E := by
  obtain ⟨j, k, hjk⟩ := hb
  have hEa' : E - a ≠ 0 := sub_ne_zero.mpr hEa
  have hMa : 0 < mixture w b a := mixture_pos hw a
  have hME : 0 < mixture w b E := mixture_pos hw E
  have hJ : Real.exp (∑ z, tiltWeight w b a z * (-((E - a) * b z)))
      < ∑ z, tiltWeight w b a z * Real.exp (-((E - a) * b z)) := by
    have hne : (fun z => -((E - a) * b z)) j ≠ (fun z => -((E - a) * b z)) k := by
      simpa using fun hcontra => hjk (mul_left_cancel₀ hEa' hcontra)
    have hstrict := strictConvexOn_exp.map_sum_lt (t := (Finset.univ : Finset ζ))
      (w := tiltWeight w b a) (p := fun z => -((E - a) * b z))
      (fun z _ => tiltWeight_pos hw a z) (tiltWeight_sum_one hw a)
      (fun z _ => Set.mem_univ _) ⟨j, Finset.mem_univ j, k, Finset.mem_univ k, hne⟩
    simpa only [smul_eq_mul] using hstrict
  rw [tiltWeight_exponent_sum, tiltWeight_mixture hw] at hJ
  have hlog := Real.log_lt_log (Real.exp_pos _) hJ
  rw [Real.log_exp, Real.log_div hME.ne' hMa.ne'] at hlog
  simp only [logMixture]
  linarith

/-! ### Consequence 1 — the apparent temperature is an upper bound -/

/-- **The apparent inverse temperature is at most the tilted mean at the lower line.**

For two lines with `E₁ < E₂`, the classical two-line Boltzmann estimate
`β_app = (y₁ − y₂)/(E₂ − E₁)` satisfies `β_app ≤ ⟨b⟩_{E₁}`. Since `T_app = 1/(k_B β_app)`,
this says the apparent temperature *overestimates* `1/(k_B ⟨b⟩_{E₁})` — see
`apparentTemperature_ge`. The bounded mean is the intensity-share-weighted mean of `1/T`
at the **lower** fitted line, not an arithmetic or volume mean (docstring caveat 2). -/
theorem pairSlope_le_tiltMean [Nonempty ζ] {w b : ζ → ℝ} (hw : ∀ z, 0 < w z)
    {E₁ E₂ : ℝ} (h12 : E₁ < E₂) :
    apparentBeta E₁ (logMixture w b E₁) E₂ (logMixture w b E₂) ≤ tiltMean w b E₁ := by
  have hd : (0 : ℝ) < E₂ - E₁ := by linarith
  have h := logMixture_tangent_le (b := b) hw E₁ E₂
  rw [apparentBeta, div_le_iff₀ hd]
  linarith

/-- Strict version of `pairSlope_le_tiltMean` for a genuinely inhomogeneous mixture. -/
theorem pairSlope_lt_tiltMean [Nonempty ζ] {w b : ζ → ℝ} (hw : ∀ z, 0 < w z)
    (hb : ∃ j k, b j ≠ b k) {E₁ E₂ : ℝ} (h12 : E₁ < E₂) :
    apparentBeta E₁ (logMixture w b E₁) E₂ (logMixture w b E₂) < tiltMean w b E₁ := by
  have hd : (0 : ℝ) < E₂ - E₁ := by linarith
  have h := logMixture_tangent_lt hw (a := E₁) (E := E₂) (by linarith) hb
  rw [apparentBeta, div_lt_iff₀ hd]
  linarith

/-- **The mirror bound: the tilted mean at the UPPER line is a lower bound on `β_app`.**
Anchoring the tangent inequality at `E₂` instead of `E₁` and reading it off at `E₁` brackets
the apparent inverse temperature from below, giving `⟨b⟩_{E₂} ≤ β_app ≤ ⟨b⟩_{E₁}`. -/
theorem tiltMean_le_pairSlope [Nonempty ζ] {w b : ζ → ℝ} (hw : ∀ z, 0 < w z)
    {E₁ E₂ : ℝ} (h12 : E₁ < E₂) :
    tiltMean w b E₂ ≤ apparentBeta E₁ (logMixture w b E₁) E₂ (logMixture w b E₂) := by
  have h := logMixture_tangent_le (b := b) hw E₂ E₁
  rw [apparentBeta, le_div_iff₀ (by linarith : (0 : ℝ) < E₂ - E₁)]
  linarith

/-- **The apparent inverse temperature of a positive-temperature mixture is positive.** This
is what discharges the `0 < betaApp` side condition of `apparentTemperature_ge`, so that the
apparent *temperature* `1/(k_B β_app)` is well-defined and finite rather than merely formal. -/
theorem pairSlope_pos [Nonempty ζ] {w b : ζ → ℝ} (hw : ∀ z, 0 < w z) (hb0 : ∀ z, 0 < b z)
    {E₁ E₂ : ℝ} (h12 : E₁ < E₂) :
    0 < apparentBeta E₁ (logMixture w b E₁) E₂ (logMixture w b E₂) := by
  have hpos : 0 < tiltMean w b E₂ :=
    Finset.sum_pos (fun z _ => mul_pos (tiltWeight_pos hw E₂ z) (hb0 z)) univ_nonempty
  exact lt_of_lt_of_le hpos (tiltMean_le_pairSlope hw h12)

/-- **Reading the slope bound as a temperature bound.** If `β_app ≤ τ` with `β_app > 0` and
`k_B > 0` then `1/(k_B τ) ≤ 1/(k_B β_app)`: the apparent temperature is an *upper* bound on
the tilted mean temperature. Kept separate so the sign convention is explicit. -/
theorem apparentTemperature_ge {kB betaApp tau : ℝ} (hkB : 0 < kB) (hbeta : 0 < betaApp)
    (h : betaApp ≤ tau) : 1 / (kB * tau) ≤ 1 / (kB * betaApp) :=
  one_div_le_one_div_of_le (by positivity) (by nlinarith)

/-! ### Consequence 2 — the intercept is a lower bound -/

/-- **The two-line secant, extrapolated below the fitted window, understates the plot.**

For `E₀ ≤ E₁ < E₂` the straight line through the two Boltzmann points `(E₁, y₁)`, `(E₂, y₂)`
evaluated at `E₀` never exceeds the true ordinate `y(E₀)`. Convexity again, read as: a chord
extended backwards falls below the curve. -/
theorem logMixture_secant_le [Nonempty ζ] {w b : ζ → ℝ} (hw : ∀ z, 0 < w z)
    {E₀ E₁ E₂ : ℝ} (h01 : E₀ ≤ E₁) (h12 : E₁ < E₂) :
    secantAt E₁ (logMixture w b E₁) E₂ (logMixture w b E₂) E₀ ≤ logMixture w b E₀ := by
  have hd : (0 : ℝ) < E₂ - E₁ := by linarith
  have hs : -tiltMean w b E₁ ≤ (logMixture w b E₂ - logMixture w b E₁) / (E₂ - E₁) := by
    rw [le_div_iff₀ hd]
    have h := logMixture_tangent_le (b := b) hw E₁ E₂
    linarith
  have ht := logMixture_tangent_le (b := b) hw E₁ E₀
  have hmul := mul_le_mul_of_nonpos_right hs (by linarith : E₀ - E₁ ≤ 0)
  simp only [secantAt]
  linarith

/-- Strict version of `logMixture_secant_le` when the extrapolation is genuine (`E₀ < E₁`)
and the mixture genuinely inhomogeneous. -/
theorem logMixture_secant_lt [Nonempty ζ] {w b : ζ → ℝ} (hw : ∀ z, 0 < w z)
    (hb : ∃ j k, b j ≠ b k) {E₀ E₁ E₂ : ℝ} (h01 : E₀ < E₁) (h12 : E₁ < E₂) :
    secantAt E₁ (logMixture w b E₁) E₂ (logMixture w b E₂) E₀ < logMixture w b E₀ := by
  have hd : (0 : ℝ) < E₂ - E₁ := by linarith
  have hs : -tiltMean w b E₁ < (logMixture w b E₂ - logMixture w b E₁) / (E₂ - E₁) := by
    rw [lt_div_iff₀ hd]
    have h := logMixture_tangent_lt hw (a := E₁) (E := E₂) (by linarith) hb
    linarith
  have ht := logMixture_tangent_lt hw (a := E₁) (E := E₀) (by linarith) hb
  have hmul := mul_lt_mul_of_neg_right hs (by linarith : E₀ - E₁ < 0)
  simp only [secantAt]
  linarith

/-- **The classical Boltzmann intercept is a guaranteed lower bound on the true log column
density.** For any two fitted lines with `0 ≤ E₁ < E₂`, the two-line fit evaluated at `E = 0`
is at most `log (∑ z, w z)` — the log of the total mass of the mixture, i.e. the true
(partition-normalized) column density summed over all mixed plasma states.

Exact-noiseless (docstring caveat 1): this is a statement about the deterministic mixing
bias, not about a noisy estimate. -/
theorem intercept_le_log_total [Nonempty ζ] {w b : ζ → ℝ} (hw : ∀ z, 0 < w z)
    {E₁ E₂ : ℝ} (h01 : 0 ≤ E₁) (h12 : E₁ < E₂) :
    secantAt E₁ (logMixture w b E₁) E₂ (logMixture w b E₂) 0 ≤ Real.log (∑ z, w z) := by
  rw [← logMixture_zero w b]
  exact logMixture_secant_le hw h01 h12

/-! ### Consequence 3 — the curvature has a sign (but is not a diagnostic) -/

/-- **Convexity read on line pairs.** For three lines `E₁ < E₂ < E₃`, the apparent inverse
temperature of the *upper* pair never exceeds that of the *lower* pair; equivalently the
apparent temperature increases with the energy window of the fit. Both halves come from the
single tangent inequality anchored at the middle line `E₂`. -/
theorem pairSlope_antitone [Nonempty ζ] {w b : ζ → ℝ} (hw : ∀ z, 0 < w z)
    {E₁ E₂ E₃ : ℝ} (h12 : E₁ < E₂) (h23 : E₂ < E₃) :
    apparentBeta E₂ (logMixture w b E₂) E₃ (logMixture w b E₃)
      ≤ apparentBeta E₁ (logMixture w b E₁) E₂ (logMixture w b E₂) := by
  have hlow : tiltMean w b E₂
      ≤ apparentBeta E₁ (logMixture w b E₁) E₂ (logMixture w b E₂) :=
    tiltMean_le_pairSlope hw h12
  have hhigh : apparentBeta E₂ (logMixture w b E₂) E₃ (logMixture w b E₃)
      ≤ tiltMean w b E₂ := pairSlope_le_tiltMean hw h23
  linarith

/-- Strict version of `pairSlope_antitone`: for a genuinely inhomogeneous mixture the
Boltzmann plot is *strictly* convex, so the two window temperatures never agree.

**This strictness is not a diagnostic.** See docstring caveat 3: the realistic two-region
signature measured only ~0.08 nats peak-to-peak over a 4 eV span, comparable to residual
self-absorption, so the gap is not resolvable in practice. -/
theorem pairSlope_strictAnti [Nonempty ζ] {w b : ζ → ℝ} (hw : ∀ z, 0 < w z)
    (hb : ∃ j k, b j ≠ b k) {E₁ E₂ E₃ : ℝ} (h12 : E₁ < E₂) (h23 : E₂ < E₃) :
    apparentBeta E₂ (logMixture w b E₂) E₃ (logMixture w b E₃)
      < apparentBeta E₁ (logMixture w b E₁) E₂ (logMixture w b E₂) := by
  have hlow : tiltMean w b E₂
      < apparentBeta E₁ (logMixture w b E₁) E₂ (logMixture w b E₂) := by
    have h := logMixture_tangent_lt hw (a := E₂) (E := E₁) (by linarith) hb
    rw [apparentBeta, lt_div_iff₀ (by linarith : (0 : ℝ) < E₂ - E₁)]
    linarith
  have hhigh : apparentBeta E₂ (logMixture w b E₂) E₃ (logMixture w b E₃)
      ≤ tiltMean w b E₂ := pairSlope_le_tiltMean hw h23
  linarith

/-! ### Sharpness — the homogeneous limit saturates every bound

Without these the inequalities above could be uninformatively slack. They are not: a
homogeneous plasma makes the Boltzmann plot exactly affine, so the intercept bound and the
temperature bound both hold with **equality**. This is equality *in* the homogeneous case,
not an iff — see the module docstring for the `E₁ = 0` case in which the intercept is exact
despite inhomogeneity. -/

/-- If every mixed state shares one inverse temperature `β`, the observed Boltzmann plot is
exactly affine — the classical single-zone `ForwardMap.boltzmann_plot_intensity` picture. -/
theorem logMixture_homogeneous [Nonempty ζ] {w b : ζ → ℝ} (hw : ∀ z, 0 < w z) {beta : ℝ}
    (hb : ∀ z, b z = beta) (E : ℝ) :
    logMixture w b E = Real.log (∑ z, w z) - E * beta := by
  have hs : 0 < ∑ z, w z := Finset.sum_pos (fun z _ => hw z) univ_nonempty
  have h : mixture w b E = (∑ z, w z) * Real.exp (-(E * beta)) := by
    simp only [mixture, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun z _ => by rw [hb z])
  rw [logMixture, h, Real.log_mul hs.ne' (Real.exp_ne_zero _), Real.log_exp]
  ring

/-- If every mixed state shares one inverse temperature `β`, the tilted mean collapses to `β`
at every anchor energy. Without this the temperature bound `pairSlope_le_tiltMean` could still
be slack in the homogeneous limit: it is what makes `apparentBeta_eq_homogeneous` a *sharpness*
statement about that bound rather than about the left-hand side alone. -/
theorem tiltMean_homogeneous [Nonempty ζ] {w b : ζ → ℝ} (hw : ∀ z, 0 < w z) {beta : ℝ}
    (hb : ∀ z, b z = beta) (a : ℝ) : tiltMean w b a = beta := by
  have h : ∀ z : ζ, tiltWeight w b a z * b z = tiltWeight w b a z * beta :=
    fun z => by rw [hb z]
  rw [tiltMean, Finset.sum_congr rfl (fun z _ => h z), ← Finset.sum_mul,
    tiltWeight_sum_one hw a, one_mul]

/-- **The intercept bound is sharp.** For a homogeneous plasma the two-line Boltzmann
intercept equals the true log column density exactly: `intercept_le_log_total` is tight, and
the strict inequality `logMixture_secant_lt` is what mixing costs. -/
theorem intercept_eq_log_total_homogeneous [Nonempty ζ] {w b : ζ → ℝ} (hw : ∀ z, 0 < w z)
    {beta : ℝ} (hb : ∀ z, b z = beta) {E₁ E₂ : ℝ} (h12 : E₁ < E₂) :
    secantAt E₁ (logMixture w b E₁) E₂ (logMixture w b E₂) 0 = Real.log (∑ z, w z) := by
  have hne : E₂ - E₁ ≠ 0 := (sub_pos.mpr h12).ne'
  simp only [secantAt, logMixture_homogeneous hw hb]
  field_simp
  ring

/-- **The temperature bound is sharp.** For a homogeneous plasma the apparent inverse
temperature equals `β` exactly. Together with `tiltMean_homogeneous` — which puts the *other*
side of `pairSlope_le_tiltMean` at `β` too — this shows the temperature bound is saturated,
not merely satisfied, in the homogeneous limit. -/
theorem apparentBeta_eq_homogeneous [Nonempty ζ] {w b : ζ → ℝ} (hw : ∀ z, 0 < w z)
    {beta : ℝ} (hb : ∀ z, b z = beta) {E₁ E₂ : ℝ} (h12 : E₁ < E₂) :
    apparentBeta E₁ (logMixture w b E₁) E₂ (logMixture w b E₂) = beta := by
  have hne : E₂ - E₁ ≠ 0 := (sub_pos.mpr h12).ne'
  simp only [apparentBeta, logMixture_homogeneous hw hb]
  field_simp
  ring

/-! ### The physics reading: a mixed observation of `ForwardMap.lineIntensity` -/

/-- **Mixed line intensity.** One integrated spectrum from an inhomogeneous plasma: a finite
positive superposition of single-zone optically-thin intensities, zone `z` contributing at
its own temperature `T z` and column density `N z`. The single-zone model of every other
module is the one-element case. The calibration `Fcal` and the level data `g, E, A` are
shared across zones (same instrument, same species). -/
noncomputable def mixedLineIntensity (kB : ℝ) (T N : ζ → ℝ) (Fcal : ℝ)
    (g E A : ι → ℝ) (k : ι) : ℝ :=
  ∑ z, lineIntensity kB (T z) (N z) Fcal g E A k

/-- Zone `z`'s Boltzmann-plot mass `w z = Fcal · N z / U(T_z)`: its partition-normalized,
calibration-absorbed column density. `∑ z, zoneWeight …` is the quantity the intercept
bounds from below. -/
noncomputable def zoneWeight (kB Fcal : ℝ) (T N : ζ → ℝ) (g E : ι → ℝ)
    (z : ζ) : ℝ :=
  Fcal * N z / partitionFunction kB (T z) g E

/-- Zone `z`'s inverse temperature `b z = 1/(k_B T_z)`, the Laplace abscissa. -/
noncomputable def zoneBeta (kB : ℝ) (T : ζ → ℝ) (z : ζ) : ℝ := 1 / (kB * T z)

omit [Fintype ζ] in
/-- Zone masses are positive, so the mixture machinery applies. -/
theorem zoneWeight_pos [Nonempty ι] {kB Fcal : ℝ} {T N : ζ → ℝ} {g E : ι → ℝ}
    (hg : ∀ k, 0 < g k) (hN : ∀ z, 0 < N z) (hFcal : 0 < Fcal) (z : ζ) :
    0 < zoneWeight kB Fcal T N g E z :=
  div_pos (mul_pos hFcal (hN z)) (partitionFunction_pos hg)

/-- **The bridge.** The Boltzmann ordinate of a mixed observation *is* the log of a discrete
Laplace transform: `log (I_k /(g_k A_k)) = logMixture (zoneWeight …) (zoneBeta …) (E k)`.
Everything in the pure-math core therefore applies verbatim to observed CF-LIBS spectra of an
inhomogeneous plasma. -/
theorem mixed_boltzmann_ordinate [Nonempty ι] {kB Fcal : ℝ} {T N : ζ → ℝ}
    {g E A : ι → ℝ} (hkB : 0 < kB) (hT : ∀ z, 0 < T z) (hg : ∀ k, 0 < g k)
    (hA : ∀ k, 0 < A k) (k : ι) :
    Real.log (mixedLineIntensity kB T N Fcal g E A k / (g k * A k))
      = logMixture (zoneWeight kB Fcal T N g E) (zoneBeta kB T) (E k) := by
  have hterm : ∀ z : ζ, lineIntensity kB (T z) (N z) Fcal g E A k / (g k * A k)
      = zoneWeight kB Fcal T N g E z
        * Real.exp (-(E k * zoneBeta kB T z)) := by
    intro z
    have hkT : kB * T z ≠ 0 := (mul_pos hkB (hT z)).ne'
    have hgk : g k ≠ 0 := (hg k).ne'
    have hAk : A k ≠ 0 := (hA k).ne'
    have hU : partitionFunction kB (T z) g E ≠ 0 := (partitionFunction_pos hg).ne'
    have hbf : boltzmannFactor kB (T z) (E k) = Real.exp (-(E k * zoneBeta kB T z)) := by
      simp only [boltzmannFactor, zoneBeta]
      congr 1
      field_simp
    simp only [lineIntensity, population, zoneWeight, hbf]
    field_simp
  simp only [logMixture, mixture, mixedLineIntensity, Finset.sum_div]
  rw [Finset.sum_congr rfl (fun z _ => hterm z)]

/-- **The headline bound, in observables.** The classical two-line Boltzmann intercept
computed from a mixed (spatially / temporally / shot-to-shot integrated) spectrum is a
guaranteed **lower bound** on the log of the true total column density `∑ z, w z`.

Exact-noiseless; two-line fit (not `n`-line OLS); finite mixture. See the module docstring. -/
theorem mixed_intercept_le_log_column [Nonempty ι] [Nonempty ζ] {kB Fcal : ℝ} {T N : ζ → ℝ}
    {g E A : ι → ℝ} (hkB : 0 < kB) (hT : ∀ z, 0 < T z) (hg : ∀ k, 0 < g k)
    (hA : ∀ k, 0 < A k) (hN : ∀ z, 0 < N z) (hFcal : 0 < Fcal) (i j : ι)
    (hE0 : 0 ≤ E i) (hEij : E i < E j) :
    secantAt (E i) (Real.log (mixedLineIntensity kB T N Fcal g E A i / (g i * A i)))
        (E j) (Real.log (mixedLineIntensity kB T N Fcal g E A j / (g j * A j))) 0
      ≤ Real.log (∑ z, zoneWeight kB Fcal T N g E z) := by
  rw [mixed_boltzmann_ordinate hkB hT hg hA i, mixed_boltzmann_ordinate hkB hT hg hA j]
  exact intercept_le_log_total (fun z => zoneWeight_pos hg hN hFcal z) hE0 hEij

/-- **The temperature bound, in observables.** The apparent inverse temperature read off a
mixed spectrum from any two lines `E i < E j` is at most the intensity-share-weighted mean of
`1/(k_B T_z)` at the lower line — so the apparent *temperature* is an upper bound on the
corresponding tilted mean temperature (`apparentTemperature_ge`). -/
theorem mixed_apparentBeta_le_tiltMean [Nonempty ι] [Nonempty ζ] {kB Fcal : ℝ} {T N : ζ → ℝ}
    {g E A : ι → ℝ} (hkB : 0 < kB) (hT : ∀ z, 0 < T z) (hg : ∀ k, 0 < g k)
    (hA : ∀ k, 0 < A k) (hN : ∀ z, 0 < N z) (hFcal : 0 < Fcal) (i j : ι) (hEij : E i < E j) :
    apparentBeta (E i) (Real.log (mixedLineIntensity kB T N Fcal g E A i / (g i * A i)))
        (E j) (Real.log (mixedLineIntensity kB T N Fcal g E A j / (g j * A j)))
      ≤ tiltMean (zoneWeight kB Fcal T N g E) (zoneBeta kB T) (E i) := by
  rw [mixed_boltzmann_ordinate hkB hT hg hA i, mixed_boltzmann_ordinate hkB hT hg hA j]
  exact pairSlope_le_tiltMean (fun z => zoneWeight_pos hg hN hFcal z) hEij

/-- **The curvature sign, in observables.** For three lines `E i < E j < E k` of a mixed
spectrum, the apparent inverse temperature of the upper pair never exceeds that of the lower
pair: the observed Boltzmann plot is convex, so the apparent temperature grows with the
energy window. *Not* a usable diagnostic — docstring caveat 3. -/
theorem mixed_apparentBeta_antitone [Nonempty ι] [Nonempty ζ] {kB Fcal : ℝ} {T N : ζ → ℝ}
    {g E A : ι → ℝ} (hkB : 0 < kB) (hT : ∀ z, 0 < T z) (hg : ∀ k, 0 < g k)
    (hA : ∀ k, 0 < A k) (hN : ∀ z, 0 < N z) (hFcal : 0 < Fcal) (i j k : ι)
    (hij : E i < E j) (hjk : E j < E k) :
    apparentBeta (E j) (Real.log (mixedLineIntensity kB T N Fcal g E A j / (g j * A j)))
        (E k) (Real.log (mixedLineIntensity kB T N Fcal g E A k / (g k * A k)))
      ≤ apparentBeta (E i) (Real.log (mixedLineIntensity kB T N Fcal g E A i / (g i * A i)))
        (E j) (Real.log (mixedLineIntensity kB T N Fcal g E A j / (g j * A j))) := by
  rw [mixed_boltzmann_ordinate hkB hT hg hA i, mixed_boltzmann_ordinate hkB hT hg hA j,
    mixed_boltzmann_ordinate hkB hT hg hA k]
  exact pairSlope_antitone (fun z => zoneWeight_pos hg hN hFcal z) hij hjk

/-! ### Non-vacuity witnesses

Explicit two-zone data: equal masses `w = (1, 1)`, inverse temperatures `b = (1, 2)` in
eV⁻¹ — one zone at `k_B T = 1 eV` (≈ 11 600 K) and one at `k_B T = 0.5 eV` (≈ 5 800 K).
Energies below are in eV. Each witness instantiates a *strict* theorem on literal data, so
none of them collapses to `0 ≤ 0`.

This split is deliberately **strong** (a factor two in `k_B T`) so that the strict gaps are
comfortably nonzero: it produces ~0.24 nats of chord-minus-curve over a 0–4 eV span, about
three times the ~0.08 nats of the realistic two-region case quoted in caveat 3. The witnesses
demonstrate non-vacuity of the theorems, **not** that the curvature is measurable. -/

/-- The mixture data used by the witnesses is genuinely positive and genuinely inhomogeneous. -/
example : (∀ z, 0 < (![1, 1] : Fin 2 → ℝ) z) ∧ ∃ j k, (![1, 2] : Fin 2 → ℝ) j ≠ ![1, 2] k := by
  refine ⟨fun z => ?_, ⟨0, 1, by norm_num⟩⟩
  fin_cases z <;> norm_num

/-- **Witness 1 — strict convexity.** The observed ordinate at `E = 3 eV` strictly exceeds
the homogeneous tangent line drawn at the anchor line `E = 1 eV`. -/
example : logMixture (![1, 1] : Fin 2 → ℝ) ![1, 2] 1
      - (3 - 1) * tiltMean (![1, 1] : Fin 2 → ℝ) ![1, 2] 1
    < logMixture (![1, 1] : Fin 2 → ℝ) ![1, 2] 3 :=
  logMixture_tangent_lt (fun z => by fin_cases z <;> norm_num) (by norm_num) ⟨0, 1, by norm_num⟩

/-- **Witness 2 — the intercept is strictly understated.** The two-line fit through the
lines at `1 eV` and `3 eV`, extrapolated to `E = 0`, falls strictly below the true ordinate
`log (1 + 1) = log 2`, i.e. strictly below the true log column density. -/
example : secantAt 1 (logMixture (![1, 1] : Fin 2 → ℝ) ![1, 2] 1)
      3 (logMixture (![1, 1] : Fin 2 → ℝ) ![1, 2] 3) 0
    < Real.log ((1 : ℝ) + 1) := by
  have hlt := logMixture_secant_lt (w := (![1, 1] : Fin 2 → ℝ)) (b := ![1, 2])
    (fun z => by fin_cases z <;> norm_num) ⟨0, 1, by norm_num⟩
    (E₀ := 0) (E₁ := 1) (E₂ := 3) (by norm_num) (by norm_num)
  rw [logMixture_zero] at hlt
  simpa [Fin.sum_univ_two] using hlt

/-- **Witness 3 — the apparent temperature strictly grows with the fitted window.** The
apparent inverse temperature from the `(2 eV, 3 eV)` pair is strictly below that from the
`(1 eV, 2 eV)` pair, so the fitted temperature from the upper pair is strictly the larger. -/
example : apparentBeta 2 (logMixture (![1, 1] : Fin 2 → ℝ) ![1, 2] 2)
      3 (logMixture (![1, 1] : Fin 2 → ℝ) ![1, 2] 3)
    < apparentBeta 1 (logMixture (![1, 1] : Fin 2 → ℝ) ![1, 2] 1)
      2 (logMixture (![1, 1] : Fin 2 → ℝ) ![1, 2] 2) :=
  pairSlope_strictAnti (fun z => by fin_cases z <;> norm_num) ⟨0, 1, by norm_num⟩
    (by norm_num) (by norm_num)

/-- **Witness 4 — the apparent temperature strictly overstates the tilted mean.** For the
`(1 eV, 2 eV)` pair the apparent inverse temperature is strictly below the tilted mean of
`b` at the lower line, hence the apparent temperature strictly exceeds `1/(k_B ⟨b⟩)`. -/
example : apparentBeta 1 (logMixture (![1, 1] : Fin 2 → ℝ) ![1, 2] 1)
      2 (logMixture (![1, 1] : Fin 2 → ℝ) ![1, 2] 2)
    < tiltMean (![1, 1] : Fin 2 → ℝ) ![1, 2] 1 :=
  pairSlope_lt_tiltMean (fun z => by fin_cases z <;> norm_num) ⟨0, 1, by norm_num⟩ (by norm_num)

/-- **Witness 5 — the lower bracket, and positivity of the apparent inverse temperature.**
The tilted mean at the *upper* line `2 eV` (numerically 1.119 eV⁻¹) sits below the apparent
inverse temperature of the `(1 eV, 2 eV)` pair (1.186 eV⁻¹), which is itself strictly
positive — so `apparentTemperature_ge` is applicable to this data, not merely formal. -/
example : tiltMean (![1, 1] : Fin 2 → ℝ) ![1, 2] 2
      ≤ apparentBeta 1 (logMixture (![1, 1] : Fin 2 → ℝ) ![1, 2] 1)
        2 (logMixture (![1, 1] : Fin 2 → ℝ) ![1, 2] 2)
    ∧ 0 < apparentBeta 1 (logMixture (![1, 1] : Fin 2 → ℝ) ![1, 2] 1)
        2 (logMixture (![1, 1] : Fin 2 → ℝ) ![1, 2] 2) :=
  ⟨tiltMean_le_pairSlope (fun z => by fin_cases z <;> norm_num) (by norm_num),
    pairSlope_pos (fun z => by fin_cases z <;> norm_num)
      (fun z => by fin_cases z <;> norm_num) (by norm_num)⟩

end CflibsFormal
