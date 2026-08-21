/-
Copyright (c) 2026 Brian Squires. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Squires
-/
import Mathlib
import CflibsFormal.SelfAbsorption
import CflibsFormal.CurveOfGrowth

/-!
# The doublet channel — the second observable that breaks the `N`–`τ` alias

A **single** self-absorbed line is a one-equation, two-unknown measurement: the emergent
slab intensity `I = F · (1 - exp(-τ))` constrains only the *product* of the source scale
`F` and the opacity, so density and optical thickness are not separable
(`single_line_tau_alias` here; `SelfAbsorptionInverse.selfAbsorption_breaks_identifiability`
in the intensity-model variables).

This module formalizes the standard fix: measure **two lines of the same multiplet**. They
share the temperature, the lower-level column density and the path length, and differ only
in oscillator strength, so their optical depths are proportional,

  `τ₂ = r · τ₁`,   `r = (gf)₂ / (gf)₁ ≠ 1` known from atomic data,

and the *ratio* of the two measured intensities

  `doubletRatio r τ₁ = (1 - exp(-(r · τ₁))) / (1 - exp(-τ₁))`

is **free of the common source scale `F`** (`doubletRatio_eq_measured_ratio`,
`doubletRatio_scale_invariant`) — the calibration-free content — and is **strictly
monotone**, hence **injective**, in `τ₁` (`doubletRatio_strictAntiOn` for `r > 1`,
`doubletRatio_strictMonoOn` for `r < 1`, `doubletRatio_injOn` for any `r ≠ 1`). With
`τ₁ = κ · N` for a known positive line-strength coefficient `κ` (stated abstractly here —
this module deliberately does not depend on any optical-depth construction), the ratio
determines `τ₁` and hence `N` (`doublet_determines_columnDensity`), even when the two
measurements carry *different, unknown* calibration scales
(`doublet_identifies_columnDensity_calibration_free`).

## The method is NOT new; the theorem is

The doublet diagnostic itself is prior art — D'Angelo, Garcimuño, Díaz Pace & Bertuccelli
(2015) — and this module claims no methodological novelty whatsoever. What is formalized
here is (i) an *identifiability* statement (injectivity on the physical domain, with the
`F`-cancellation proved rather than asserted), and (ii) an explicit statement of the
conditions under which the inversion is trustworthy — and of the one condition it can
never check.

## CRITICAL LIMITATION — the doublet channel CANNOT detect model error

The rung is **exactly determined**: two observables `(I₁, I₂)` against two unknowns
`(F, τ₁)`. Consequently

* it **always returns an answer** for any datum whose intensity ratio is attainable
  (`doublet_exact_fit`, `doublet_residual_vacuous`) — the fitted parameters reproduce
  **both** measurements with residual exactly zero; and
* that answer is **unique** (`doublet_fit_unique`).

A square, uniquely-solvable system has **no redundancy**: there is no left-over degree of
freedom, hence no residual, hence no consistency check. A perfect fit is therefore *not*
evidence that the homogeneous-slab kernel is correct — it is a tautology of the counting.
`inhomogeneous_doublet_admits_exact_homogeneous_fit` makes this concrete and adversarial:
for a spatially-integrated **two-zone** emitter (two homogeneous zones with genuinely
different optical depths `τ_a ≠ τ_b`, summed over the collection solid angle — physically
not a single homogeneous slab), the homogeneous doublet inversion still fits **both**
measured intensities *exactly*, at a fitted optical depth that equals **neither** zone's.
So an inhomogeneous plasma is observationally indistinguishable, through this channel,
from a homogeneous one — while the reported column density corresponds to no region of
the plasma. Inhomogeneity is exactly where this failure bites, and the doublet channel is
blind to it by construction.

**Do not read any theorem in this module as a model-adequacy test.** Detecting
inhomogeneity requires an *over*-determined observable set (a third line, a spatially or
temporally resolved measurement, or a line-shape constraint), which this module does not
supply and does not claim.

Further honest scope caveats:

* `r` is treated as exactly known. Atomic-data error in `(gf)₂/(gf)₁` propagates into `τ₁`
  and is not bounded here. Strictly, `r` is the ratio of the two line-centre opacities,
  which equals `(gf)₂/(gf)₁` only up to the near-unity wavelength / Doppler-width factor
  common to both members of a multiplet; `r` enters every theorem below as an abstract free
  variable, so no proof depends on that identification.
* The two lines are assumed to share one source scale `F` (same upper level / same
  multiplet, so the source functions coincide to within the `ν³` factor that is negligible
  across a multiplet). This is an assumption of the model, not a theorem.
* The attainable range of `doubletRatio r ·` on `(0, ∞)` is *not* characterized here
  (that would need the `τ → 0⁺` and `τ → ∞` limits); `doublet_exact_fit` is therefore
  conditioned on the observed ratio being attained at some `τ₀ > 0`, and the two-zone
  theorem supplies that hypothesis by an intermediate-value argument rather than by a
  range computation.

## Literature and scope

* Gornushkin, Anzano, King, Smith, Omenetto, Winefordner, "Curve of growth methodology
  applied to laser-induced plasma emission spectroscopy", *Spectrochimica Acta Part B*
  **54** (1999) 491–503 — the homogeneous-slab curve of growth `I = S·(1 - exp(-τ))` reused
  verbatim here as `SelfAbsorption.slabIntensity`. No new radiative-transfer kernel is
  introduced by this module.
* D'Angelo, Garcimuño, Díaz Pace, Bertuccelli, "Plasma diagnostics from self-absorbed
  doublet lines in laser-induced breakdown spectroscopy", *Journal of Quantitative
  Spectroscopy and Radiative Transfer* **164** (2015) 89–96,
  DOI `10.1016/j.jqsrt.2015.05.014` (DOI, title, volume and pagination verified against
  the Crossref record) — **prior art for the method formalized here**: plasma diagnostics
  from the ratio of two self-absorbed lines of the same multiplet, computed, in the
  authors' own words, "under the framework of a homogeneous plasma in local thermodynamic
  equilibrium". That homogeneity framework is precisely the assumption the exactly
  determined inversion cannot test — see the limitation section above.
* Aragón, Peñalba & Aguilera, "Curves of growth of neutral atom and ion lines emitted by a
  laser induced plasma", *Spectrochimica Acta Part B* **60** (2005) 879–887, DOI
  `10.1016/j.sab.2005.05.015` (authors, journal, volume, pagination and year verified
  against the Crossref record) — the curve-of-growth systematics (distinct `gf` ⇒ distinct
  saturation) that make two multiplet members carry independent information.
  NOTE: this is **not** the paper the repo-wide citation string "Aragón & Aguilera 2014"
  denotes — that string is the Cσ method, *JQSRT* **149** (2014) 90–102, used in
  `Alt/CSigma.lean`. The scope-tag rows for this module therefore cite Gornushkin 1999 for
  the curve-of-growth kernel rather than reusing that string.

Everything is dimensionless `ℝ`. Results are tagged **REDUCED** where they depend on the
homogeneous-slab kernel and the shared-`F` / proportional-`τ` multiplet idealization, and
**PURE-MATH** where they are pure algebra or analysis.
-/

namespace CflibsFormal

open Real

/-- **The doublet (multiplet-pair) intensity ratio.** For two lines of one multiplet
sharing `(T, N, ℓ)` and differing only in oscillator strength, the optical depths are
proportional, `τ₂ = r · τ₁` with `r = (gf)₂/(gf)₁`. Their measured-intensity ratio is
`(1 - exp(-(r·τ₁))) / (1 - exp(-τ₁))`. This is the *observable*: the common source scale
has already cancelled (`doubletRatio_eq_measured_ratio`). -/
noncomputable def doubletRatio (r tau : ℝ) : ℝ :=
  (1 - Real.exp (-(r * tau))) / (1 - Real.exp (-tau))

/-- The doublet ratio is the curve-of-growth ratio `cogRatio` at opacities `(r, 1)`: the
doublet channel introduces no new function, only a normalization of the weaker line's
opacity to `1`. -/
theorem doubletRatio_eq_cogRatio (r tau : ℝ) : doubletRatio r tau = cogRatio r 1 tau := by
  unfold doubletRatio cogRatio
  rw [one_mul]

/-- Reciprocal form: `doubletRatio r τ = (cogRatio 1 r τ)⁻¹`. Used to transfer the
`r > 1` (antitone) curve-of-growth monotonicity to the `r < 1` (monotone) case. -/
theorem doubletRatio_eq_inv_cogRatio (r tau : ℝ) :
    doubletRatio r tau = (cogRatio 1 r tau)⁻¹ := by
  unfold doubletRatio cogRatio
  rw [one_mul, inv_div]

/-- Positivity of the weaker line's emergent factor: `0 < 1 - exp(-τ)` for `τ > 0`. This
is the denominator of the doublet ratio and the reason the ratio is well defined on the
physical domain. -/
theorem doublet_denom_pos {tau : ℝ} (htau : 0 < tau) : 0 < 1 - Real.exp (-tau) := by
  have h := cog_denom_pos one_pos htau
  rwa [one_mul] at h

/-- Positivity of the curve-of-growth ratio on the physical domain. -/
theorem cogRatio_pos {w₁ w₂ tau : ℝ} (hw₁ : 0 < w₁) (hw₂ : 0 < w₂) (htau : 0 < tau) :
    0 < cogRatio w₁ w₂ tau :=
  div_pos (cog_denom_pos hw₁ htau) (cog_denom_pos hw₂ htau)

/-- The doublet ratio is a positive observable for `r > 0`, `τ > 0` — so its logarithm is
defined and it can be compared to a measured intensity ratio. -/
theorem doubletRatio_pos {r tau : ℝ} (hr : 0 < r) (htau : 0 < tau) :
    0 < doubletRatio r tau := by
  rw [doubletRatio_eq_cogRatio]
  exact cogRatio_pos hr one_pos htau

/-- **The doublet ratio is genuinely informative.** For the stronger line (`r > 1`) the
ratio strictly exceeds `1` at every *positive* optical depth: the second multiplet member is
not a redundant copy of the first. (Non-vacuity: the observable is never the constant `1`
on the physical domain.) -/
theorem one_lt_doubletRatio {r tau : ℝ} (hr : 1 < r) (htau : 0 < tau) :
    1 < doubletRatio r tau := by
  have hd : 0 < 1 - Real.exp (-tau) := doublet_denom_pos htau
  unfold doubletRatio
  rw [lt_div_iff₀ hd, one_mul]
  have h1 : tau < r * tau := by nlinarith
  have h2 : Real.exp (-(r * tau)) < Real.exp (-tau) :=
    Real.exp_lt_exp.mpr (neg_lt_neg h1)
  linarith

/-! ### (1) The source scale cancels — the calibration-free content -/

/-- **`F`-cancellation (the calibration-free content).** Both multiplet members are
emitted by the same plasma and collected through the same optics, so both carry the *same*
unknown source/instrument scale `F` in the slab kernel `I = F·(1 - exp(-τ))`. In the ratio
of the two measured intensities that scale divides out exactly:
`I₂ / I₁ = doubletRatio r τ₁`. No radiometric calibration and no knowledge of plasma
volume, solid angle, or detector response is needed to evaluate the observable. -/
theorem doubletRatio_eq_measured_ratio {F r tau : ℝ} (hF : F ≠ 0) :
    slabIntensity F (r * tau) / slabIntensity F tau = doubletRatio r tau := by
  unfold slabIntensity doubletRatio
  rw [mul_div_mul_left _ _ hF]

/-- **The observable does not depend on the source scale at all.** Two experiments with
*different* unknown scales `F ≠ F'` (different shot energy, different collection geometry,
different detector gain) but the same optical depth produce the *same* doublet ratio. This
is the `F`-freedom stated as an invariance rather than as a cancellation. -/
theorem doubletRatio_scale_invariant {F F' r tau : ℝ} (hF : F ≠ 0) (hF' : F' ≠ 0) :
    slabIntensity F (r * tau) / slabIntensity F tau
      = slabIntensity F' (r * tau) / slabIntensity F' tau := by
  rw [doubletRatio_eq_measured_ratio hF, doubletRatio_eq_measured_ratio hF']

/-- The stronger member's intensity is the weaker member's intensity times the doublet
ratio: `I₂ = I₁ · ρ(τ)`. The multiplicative form of `doubletRatio_eq_measured_ratio`,
valid for every `F` (including `F = 0`). -/
theorem slab_second_eq_mul_ratio {F r tau : ℝ} (htau : 0 < tau) :
    slabIntensity F (r * tau) = slabIntensity F tau * doubletRatio r tau := by
  have hd : (1 - Real.exp (-tau)) ≠ 0 := (doublet_denom_pos htau).ne'
  unfold slabIntensity doubletRatio
  field_simp

/-! ### (2) Strict monotonicity and injectivity in the optical depth -/

/-- **Strict antitonicity for the stronger line (`r > 1`).** The doublet ratio decreases
strictly with optical depth: the stronger member saturates first, so the ratio falls from
the optically-thin value toward `1` (those limiting values, `r` as `τ → 0⁺` and `1` as
`τ → ∞`, are descriptive curve-of-growth context and are **not** proved by this theorem —
only strict decrease is). Inherited verbatim from
`CurveOfGrowth.cogRatio_strictAntiOn` at opacities `(r, 1)`. -/
theorem doubletRatio_strictAntiOn {r : ℝ} (hr : 1 < r) :
    StrictAntiOn (fun tau => doubletRatio r tau) (Set.Ioi 0) := by
  have h := cogRatio_strictAntiOn hr one_pos
  intro a ha b hb hab
  simp only [doubletRatio_eq_cogRatio]
  exact h ha hb hab

/-- **Strict monotonicity for the weaker line (`0 < r < 1`).** With the roles reversed the
ratio increases strictly with optical depth. Proved from the same curve-of-growth fact by
taking reciprocals (`doubletRatio_eq_inv_cogRatio`), so the two orientations are one
theorem, not two derivations. -/
theorem doubletRatio_strictMonoOn {r : ℝ} (hr0 : 0 < r) (hr : r < 1) :
    StrictMonoOn (fun tau => doubletRatio r tau) (Set.Ioi 0) := by
  intro a ha b hb hab
  have hA : 0 < cogRatio 1 r a := cogRatio_pos one_pos hr0 (Set.mem_Ioi.mp ha)
  have hB : 0 < cogRatio 1 r b := cogRatio_pos one_pos hr0 (Set.mem_Ioi.mp hb)
  have hlt : cogRatio 1 r b < cogRatio 1 r a := cogRatio_strictAntiOn hr hr0 ha hb hab
  have key : (cogRatio 1 r a)⁻¹ < (cogRatio 1 r b)⁻¹ := by
    rw [inv_eq_one_div, inv_eq_one_div, div_lt_div_iff₀ hA hB]
    linarith
  simp only [doubletRatio_eq_inv_cogRatio]
  exact key

/-- **Injectivity of the doublet channel on the physical domain.** For any known ratio of
oscillator strengths `r > 0` with `r ≠ 1` — i.e. two *genuinely different* multiplet
members — distinct positive optical depths give distinct doublet ratios. This is the
identifiability statement: the second observable removes the one-line `N`–`τ` alias. -/
theorem doubletRatio_injOn {r : ℝ} (hr0 : 0 < r) (hr1 : r ≠ 1) :
    Set.InjOn (fun tau => doubletRatio r tau) (Set.Ioi 0) := by
  rcases lt_or_gt_of_ne hr1 with h | h
  · exact (doubletRatio_strictMonoOn hr0 h).injOn
  · exact (doubletRatio_strictAntiOn h).injOn

/-! ### (3) The identifiability payoff -/

/-- **The ratio determines the optical depth.** Equal doublet ratios at positive optical
depths force equal optical depths: the calibration-free observable inverts uniquely for
`τ₁`. -/
theorem doubletRatio_determines_tau {r : ℝ} (hr0 : 0 < r) (hr1 : r ≠ 1)
    {tau tau' : ℝ} (htau : 0 < tau) (htau' : 0 < tau')
    (hEq : doubletRatio r tau = doubletRatio r tau') : tau = tau' :=
  doubletRatio_injOn hr0 hr1 (Set.mem_Ioi.mpr htau) (Set.mem_Ioi.mpr htau') hEq

/-- **The ratio determines the column density.** With the optical depth proportional to the
lower-level column density, `τ₁ = κ · N` for a known `κ > 0` collecting the line strength
and path length (stated abstractly — this module depends on no optical-depth
construction), equal doublet ratios force equal column densities. Combined with
`doubletRatio_eq_measured_ratio`, this is the whole point of the doublet channel: `N` is
recovered from two intensities *without* radiometric calibration. -/
theorem doublet_determines_columnDensity {r kappa : ℝ} (hr0 : 0 < r) (hr1 : r ≠ 1)
    (hk : 0 < kappa) {N N' : ℝ} (hN : 0 < N) (hN' : 0 < N')
    (hEq : doubletRatio r (kappa * N) = doubletRatio r (kappa * N')) : N = N' := by
  have h := doubletRatio_determines_tau hr0 hr1 (mul_pos hk hN) (mul_pos hk hN') hEq
  exact mul_left_cancel₀ hk.ne' h

/-- **Calibration-free identifiability of the column density (headline).** Two experiments
whose *unknown and possibly different* source scales are `F` and `F'`, observing the same
multiplet pair, and yielding equal measured intensity ratios, must have the same column
density. The scales never appear in the conclusion: they cancel inside each ratio, so no
radiometric calibration enters the inversion of `N`.

Scope: REDUCED — homogeneous-slab kernel, one shared `F` per experiment, exactly known
`r`, and `τ₁ = κ·N` with known `κ`. Note that `κ` is a **single** bound variable shared by
*both* experiments: only the radiometric scale `F` is permitted to differ, while equal line
strength, equal temperature (which fixes the lower-level population inside `κ`) and equal
path length are load-bearing hypotheses, not consequences. "Calibration-free" here means
free of `F`; it does **not** mean free of `κ`. See the module docstring for what this does
**not** prove. -/
theorem doublet_identifies_columnDensity_calibration_free
    {r kappa F F' : ℝ} (hr0 : 0 < r) (hr1 : r ≠ 1) (hk : 0 < kappa)
    (hF : F ≠ 0) (hF' : F' ≠ 0) {N N' : ℝ} (hN : 0 < N) (hN' : 0 < N')
    (hEq : slabIntensity F (r * (kappa * N)) / slabIntensity F (kappa * N)
      = slabIntensity F' (r * (kappa * N')) / slabIntensity F' (kappa * N')) :
    N = N' := by
  rw [doubletRatio_eq_measured_ratio hF, doubletRatio_eq_measured_ratio hF'] at hEq
  exact doublet_determines_columnDensity hr0 hr1 hk hN hN' hEq

/-- **Why the second line is needed: the one-line alias, in slab variables.** A single
measured intensity is reproduced *exactly* at **any** prescribed optical depth by choosing
the source scale accordingly. One line therefore constrains only the product `F·(1 -
exp(-τ))`, never `τ` (equivalently `N`) alone — the alias recorded at the intensity-model
level by `SelfAbsorptionInverse.selfAbsorption_breaks_identifiability`. -/
theorem single_line_tau_alias {F tau tau' : ℝ} (hF : 0 < F) (htau : 0 < tau)
    (htau' : 0 < tau') :
    ∃ F', 0 < F' ∧ slabIntensity F' tau' = slabIntensity F tau := by
  have hd : 0 < 1 - Real.exp (-tau) := doublet_denom_pos htau
  have hd' : 0 < 1 - Real.exp (-tau') := doublet_denom_pos htau'
  refine ⟨F * (1 - Real.exp (-tau)) / (1 - Real.exp (-tau')), ?_, ?_⟩
  · exact div_pos (mul_pos hF hd) hd'
  · unfold slabIntensity
    field_simp

/-! ### (4) The critical limitation: an exactly determined rung has no residual -/

/-- **The inversion always returns an answer — zero residual, by construction.** Let
`(I₁, I₂)` be *any* pair of measured intensities with `I₁ > 0` whose ratio is attained by
the doublet-ratio curve at some `τ₀ > 0`. Then there is a source scale `F > 0` for which
the homogeneous-slab model reproduces **both** measurements *exactly*.

Note what the hypotheses do **not** include: nothing at all is assumed about how the data
were produced. The datum need not come from a homogeneous slab; it need not come from a
plasma. The fit residual is identically zero regardless, so a zero residual carries **no
information** about the validity of the homogeneous-slab kernel. -/
theorem doublet_exact_fit {r I₁ I₂ tau₀ : ℝ} (hI₁ : 0 < I₁) (htau₀ : 0 < tau₀)
    (hrho : I₂ / I₁ = doubletRatio r tau₀) :
    ∃ F, 0 < F ∧ slabIntensity F tau₀ = I₁ ∧ slabIntensity F (r * tau₀) = I₂ := by
  have hd : 0 < 1 - Real.exp (-tau₀) := doublet_denom_pos htau₀
  refine ⟨I₁ / (1 - Real.exp (-tau₀)), div_pos hI₁ hd, ?_, ?_⟩
  · unfold slabIntensity
    field_simp
  · have h2 : I₂ = doubletRatio r tau₀ * I₁ := (div_eq_iff hI₁.ne').mp hrho
    rw [h2]
    unfold slabIntensity doubletRatio
    field_simp

/-- **No residual exists (existential form).** Restatement of `doublet_exact_fit` as: the
two-observable / two-unknown system is solvable for every attainable datum. There is no
left-over equation, hence nothing to test — the "goodness of fit" of a doublet inversion
is vacuous. -/
theorem doublet_residual_vacuous {r I₁ I₂ tau₀ : ℝ} (hI₁ : 0 < I₁) (htau₀ : 0 < tau₀)
    (hrho : I₂ / I₁ = doubletRatio r tau₀) :
    ∃ F tau, 0 < F ∧ 0 < tau ∧
      slabIntensity F tau = I₁ ∧ slabIntensity F (r * tau) = I₂ := by
  obtain ⟨F, hFpos, h1, h2⟩ := doublet_exact_fit hI₁ htau₀ hrho
  exact ⟨F, tau₀, hFpos, htau₀, h1, h2⟩

/-- **The exact fit is unique.** Two parameter pairs `(F, τ)`, `(F', τ')` in the physical
domain that reproduce the same two measured intensities are equal. Together with
`doublet_exact_fit` this pins the epistemic situation exactly: the map
`(F, τ) ↦ (I₁, I₂)` is a bijection onto its image, so the system has **exactly zero**
degrees of redundancy. Uniqueness is the identifiability payoff *and* the reason no
consistency check exists — the same fact seen from both sides. -/
theorem doublet_fit_unique {r : ℝ} (hr0 : 0 < r) (hr1 : r ≠ 1)
    {F tau F' tau' : ℝ} (hF : 0 < F) (htau : 0 < tau) (hF' : 0 < F') (htau' : 0 < tau')
    (h1 : slabIntensity F tau = slabIntensity F' tau')
    (h2 : slabIntensity F (r * tau) = slabIntensity F' (r * tau')) :
    F = F' ∧ tau = tau' := by
  have hd : 0 < 1 - Real.exp (-tau) := doublet_denom_pos htau
  have hratio : doubletRatio r tau = doubletRatio r tau' := by
    rw [← doubletRatio_eq_measured_ratio (F := F) (r := r) (tau := tau) hF.ne',
      ← doubletRatio_eq_measured_ratio (F := F') (r := r) (tau := tau') hF'.ne', h1, h2]
  have htt : tau = tau' := doubletRatio_determines_tau hr0 hr1 htau htau' hratio
  refine ⟨?_, htt⟩
  subst htt
  unfold slabIntensity at h1
  exact mul_right_cancel₀ hd.ne' h1

/-- Pure-algebra mediant lemma: a strictly positive weighted mean of two *distinct* reals
lies strictly between them — in particular it lies in their unordered interval and equals
neither. No orientation (`x < y` or `y < x`) is assumed. -/
theorem weighted_mean_strict_between {wa wb x y : ℝ} (hwa : 0 < wa) (hwb : 0 < wb)
    (hxy : x ≠ y) :
    (wa * x + wb * y) / (wa + wb) ∈ Set.uIcc x y ∧
      (wa * x + wb * y) / (wa + wb) ≠ x ∧ (wa * x + wb * y) / (wa + wb) ≠ y := by
  have key : ∀ p q u v : ℝ, 0 < p → 0 < q → u < v →
      u < (p * u + q * v) / (p + q) ∧ (p * u + q * v) / (p + q) < v := by
    intro p q u v hp hq huv
    have hpq : 0 < p + q := by linarith
    refine ⟨?_, ?_⟩
    · rw [lt_div_iff₀ hpq]
      nlinarith
    · rw [div_lt_iff₀ hpq]
      nlinarith
  rcases lt_or_gt_of_ne hxy with h | h
  · obtain ⟨h1, h2⟩ := key wa wb x y hwa hwb h
    exact ⟨Set.mem_uIcc.mpr (Or.inl ⟨h1.le, h2.le⟩), h1.ne', h2.ne⟩
  · obtain ⟨h1, h2⟩ := key wb wa y x hwb hwa h
    have hcomm : (wb * y + wa * x) / (wb + wa) = (wa * x + wb * y) / (wa + wb) := by
      rw [add_comm (wb * y), add_comm wb wa]
    rw [hcomm] at h1 h2
    exact ⟨Set.mem_uIcc.mpr (Or.inr ⟨h1.le, h2.le⟩), h2.ne, h1.ne'⟩

/-- Continuity of the doublet-ratio curve on the physical domain — the analytic input to
the intermediate-value step below. -/
theorem doubletRatio_continuousOn (r : ℝ) :
    ContinuousOn (fun tau => doubletRatio r tau) (Set.Ioi 0) := by
  have hnum : Continuous fun tau : ℝ => 1 - Real.exp (-(r * tau)) := by fun_prop
  have hden : Continuous fun tau : ℝ => 1 - Real.exp (-tau) := by fun_prop
  exact hnum.continuousOn.div hden.continuousOn
    fun t ht => (doublet_denom_pos (Set.mem_Ioi.mp ht)).ne'

/-- **THE INVERSION CANNOT DETECT THAT ITS KERNEL IS WRONG.** Consider a spatially
integrated, genuinely **inhomogeneous** emitter: two homogeneous zones with source scales
`Fa, Fb > 0` and *different* optical depths `τa ≠ τb`, whose emissions add over the
collection solid angle. The source is not a single homogeneous slab — it has two distinct
optical depths, and no zone of it has the optical depth the inversion will report.

The theorem says the homogeneous doublet inversion nevertheless returns a fit that
reproduces **both** measured intensities *exactly*, with `F > 0` and `τ > 0`, and with
`τ ≠ τa`, `τ ≠ τb`. Read the conclusion carefully and in the harshest direction: it does
**not** say the composite is detectably non-homogeneous. It says the opposite — through
this two-line channel the inhomogeneous emitter is **observationally indistinguishable**
from a homogeneous slab, and the optical depth (hence column density) the inversion
confidently reports belongs to *neither* physical zone. Proof: the composite ratio is a
positively weighted
mean of the two zone ratios (`weighted_mean_strict_between`), hence strictly between them,
hence attained at some interior `τ` by the intermediate value theorem
(`intermediate_value_uIcc` with `doubletRatio_continuousOn`); `doublet_exact_fit` then
supplies the scale.

This is the formal content of the honesty warning in the module docstring: an exactly
determined rung has no residual, so model error — and inhomogeneity in particular — is
invisible to it. Do **not** cite this module as evidence that a doublet inversion
validates the homogeneous-slab assumption; it proves the opposite. -/
theorem inhomogeneous_doublet_admits_exact_homogeneous_fit
    {r Fa Fb ta tb : ℝ} (hr0 : 0 < r) (hr1 : r ≠ 1) (hFa : 0 < Fa) (hFb : 0 < Fb)
    (hta : 0 < ta) (htb : 0 < tb) (hab : ta ≠ tb) :
    ∃ F tau, 0 < F ∧ 0 < tau ∧ tau ≠ ta ∧ tau ≠ tb ∧
      slabIntensity F tau = slabIntensity Fa ta + slabIntensity Fb tb ∧
      slabIntensity F (r * tau)
        = slabIntensity Fa (r * ta) + slabIntensity Fb (r * tb) := by
  have hIa : 0 < slabIntensity Fa ta := mul_pos hFa (doublet_denom_pos hta)
  have hIb : 0 < slabIntensity Fb tb := mul_pos hFb (doublet_denom_pos htb)
  have hJ1 : 0 < slabIntensity Fa ta + slabIntensity Fb tb := add_pos hIa hIb
  -- the composite second-line intensity is the weighted sum of the zone ratios
  have hJ2 : slabIntensity Fa (r * ta) + slabIntensity Fb (r * tb)
      = slabIntensity Fa ta * doubletRatio r ta
        + slabIntensity Fb tb * doubletRatio r tb := by
    rw [slab_second_eq_mul_ratio hta, slab_second_eq_mul_ratio htb]
  -- the two zones have distinct ratios, because they have distinct optical depths
  have hrho : doubletRatio r ta ≠ doubletRatio r tb := fun h =>
    hab (doubletRatio_determines_tau hr0 hr1 hta htb h)
  obtain ⟨hmem, hnea, hneb⟩ := weighted_mean_strict_between hIa hIb hrho
  -- the physical domain contains the whole interval between the zone optical depths
  have hsub : Set.uIcc ta tb ⊆ Set.Ioi 0 := by
    intro x hx
    rcases Set.mem_uIcc.mp hx with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact Set.mem_Ioi.mpr (lt_of_lt_of_le hta h1)
    · exact Set.mem_Ioi.mpr (lt_of_lt_of_le htb h1)
  have hcont : ContinuousOn (fun t => doubletRatio r t) (Set.uIcc ta tb) :=
    (doubletRatio_continuousOn r).mono hsub
  obtain ⟨tau, htaumem, htaueq⟩ := intermediate_value_uIcc hcont hmem
  have htaupos : 0 < tau := Set.mem_Ioi.mp (hsub htaumem)
  have htaueq' : doubletRatio r tau
      = (slabIntensity Fa ta * doubletRatio r ta
          + slabIntensity Fb tb * doubletRatio r tb)
        / (slabIntensity Fa ta + slabIntensity Fb tb) := htaueq
  have hfit : (slabIntensity Fa (r * ta) + slabIntensity Fb (r * tb))
      / (slabIntensity Fa ta + slabIntensity Fb tb) = doubletRatio r tau := by
    rw [hJ2, htaueq']
  obtain ⟨F, hFpos, h1, h2⟩ := doublet_exact_fit hJ1 htaupos hfit
  refine ⟨F, tau, hFpos, htaupos, ?_, ?_, h1, h2⟩
  · intro hEq
    exact hnea (by rw [← htaueq', hEq])
  · intro hEq
    exact hneb (by rw [← htaueq', hEq])

/-! ### Non-vacuity witnesses (explicit data)

These are `example`s on concrete numerals: they exercise the theorems on data that does
not collapse to a triviality. -/

/-- The doublet observable genuinely varies with optical depth: for `r = 2` the ratio at
`τ = 2` is strictly below the ratio at `τ = 1`. -/
example : doubletRatio 2 2 < doubletRatio 2 1 :=
  doubletRatio_strictAntiOn (by norm_num) (Set.mem_Ioi.mpr (by norm_num))
    (Set.mem_Ioi.mpr (by norm_num)) (by norm_num)

/-- ... and it is bounded away from the trivial value `1` at that explicit datum. -/
example : 1 < doubletRatio 2 1 := one_lt_doubletRatio (by norm_num) (by norm_num)

/-- Explicit identifiability: at `r = 2`, `κ = 3`, equal ratios force equal densities. -/
example {N N' : ℝ} (hN : 0 < N) (hN' : 0 < N')
    (h : doubletRatio 2 (3 * N) = doubletRatio 2 (3 * N')) : N = N' :=
  doublet_determines_columnDensity (by norm_num) (by norm_num) (by norm_num) hN hN' h

/-- Explicit failure witness: a two-zone emitter with `Fa = 1, τa = 1` and `Fb = 3,
τb = 4`, observed through the `r = 2` doublet, is fit *exactly* by a single homogeneous
slab whose optical depth is neither `1` nor `4`. -/
example : ∃ F tau, 0 < F ∧ 0 < tau ∧ tau ≠ 1 ∧ tau ≠ 4 ∧
    slabIntensity F tau = slabIntensity 1 1 + slabIntensity 3 4 ∧
    slabIntensity F (2 * tau) = slabIntensity 1 (2 * 1) + slabIntensity 3 (2 * 4) :=
  inhomogeneous_doublet_admits_exact_homogeneous_fit (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end CflibsFormal
