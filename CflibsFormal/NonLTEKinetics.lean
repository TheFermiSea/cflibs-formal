/-
Copyright (c) 2026 Brian Squires. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Squires
-/
import Mathlib
import CflibsFormal.ErrorBudget
import CflibsFormal.PartialLTE

/-!
# CF-LIBS formalization — non-LTE departure coefficients and the departure error budget

`PartialLTE.lean` formalizes the *algebra* of the McWhirter LTE criterion (the density bound
`n_e ≥ 1.6·10¹²·√T·(ΔE)³` inverted into a thermalization-limit energy), but its scope note
explicitly disclaims **level departure coefficients** — the object that quantifies *how far* a
level's population sits from its LTE value. This module fills exactly that gap, staying
**algebraic and static**: the two-level "steady state" is an algebraic balance equation (not an
ODE), and a departure coefficient enters the Boltzmann plot as a *pure additive log shift*.

## The departure coefficient

For a two-level atom (lower `1`, upper `2`) in steady state, collisional excitation balances
collisional de-excitation plus radiative decay, `n₁ R₁₂ = n₂ (R₂₁ + A₂₁)`. Dividing by the
detailed-balance identity `n₁ R₁₂ = n₂ᴸᵀᴱ R₂₁` (which presumes the *lower* level is itself
thermalized, `b₁ ≈ 1` — the standard two-level assumption) gives the departure coefficient

```
  b₂ := n₂ / n₂ᴸᵀᴱ = R₂₁ / (R₂₁ + A₂₁) = 1 / (1 + A₂₁/(n_e C₂₁))          (★)
```

* `departureCoeff` / `two_level_balance` — the object `(★)` and its balance-quotient derivation.
* `departureCoeffNe` — the density form `b₂(n_e) = n_e C₂₁/(n_e C₂₁ + A₂₁)`, with the sandwich
  `0 ≤ b₂ ≤ 1` (radiative leakage only *underpopulates* the upper level), the explicit density
  bound `|b₂ − 1| ≤ A₂₁/(n_e C₂₁)`, and strict monotonicity in `n_e` (denser ⇒ closer to LTE).
* `departureCoeffNe_tendsto_one` — the LTE limit `b₂(n_e) → 1` as `n_e → ∞`.
* `mcwhirter_forces_departure` / `departure_threshold_iff` — the McWhirter *factor-of-10 rate
  ratio* `n_e C₂₁ ≥ 10 A₂₁` forces `b₂ ≥ 10/11`, and the general threshold equivalence.

## The departure error budget (crown jewel)

Under non-LTE, `nₖᴺᴸᵀᴱ = bₖ · nₖᴸᵀᴱ`, so the Boltzmann-plot ordinate `log(nₖ/gₖ)` picks up a
*per-line additive shift* `δₖ = log bₖ` (`nonlte_ordinate_shift`, an EXACT `log_mul` identity).
That is precisely the abstract per-line ordinate perturbation `εₖ` of the heteroscedastic
`ErrorBudget` chain. A bounded departure `|bₖ − 1| ≤ δ_b` gives `|log bₖ| ≤ δ_b/(1 − δ_b)`
(`abs_log_departure_le`, via the promoted `ErrorBudget.log_lip_floor`), and the *entire existing*
`ErrorBudget` machinery then fires verbatim with `εₖ := |log bₖ|`:

```
  |bₖ − 1| ≤ δ_b   ─ nonlte_ordinate_shift + abs_log_departure_le ─▶   εₖ = |log bₖ| ≤ δ_b/(1−δ_b)
        │ temp_rel_error_hetero                        │ olsIntercept_stable_hetero + relDensity_le
        ▼                                              ▼
  |ΔT|/T ≤ k_B·T̂·(∑ₖ|Eₖ−Ē|·|log bₖ|)/SS_E        non-LTE density error  (needs mean E = 0)
```

* `nonlte_temp_error` / `nonlte_temp_error_uniform` — the temperature leg (per-line and
  uniform-`δ_b`).
* `nonlte_density_error` — the density leg (carries the centered-convention `mean E = 0`).

## Honest scope

* **Two-level reduction.** `two_level_balance` is the two-level reduction of the full
  collisional–radiative system; `(★)` presumes the lower level is itself thermalized (`b₁ ≈ 1`).
  It states a *departure*, never that LTE holds — McWhirter is necessary, not sufficient
  (cf. `PartialLTE.lean`). The full `N`-level rate-matrix kernel and time-dependent kinetics are
  out of scope (no ODE / rate-matrix-kernel infrastructure; the rate coefficients `C_{jk}` are
  atomic-physics *input data*, not derivable).
* **No numeric bridge to `mcWhirterBound`.** `mcwhirter_forces_departure` /
  `departure_threshold_iff` are *standalone algebra on the abstract rate ratio* `n_e C₂₁` vs
  `A₂₁`. They reproduce McWhirter's `10/11` content but are **not** proven equivalent to the
  repo's numeric `StarkBroadening.mcWhirterBound = 1.6·10¹²·√T·(ΔE)³`; that bridge would need the
  non-derivable atomic-physics identity `1.6·10¹²·√T·(ΔE)³ ↔ 10·A₂₁/C₂₁`. The `PartialLTE`
  import is narrative co-location, not a proof dependency.
* **Near-LTE budget.** The error budget is a small-`δ_b` statement: `abs_log_departure_le` needs
  the positive floor `1 − δ_b > 0`; a departure so large it admits `bₖ = 0` has unbounded
  `|log bₖ|` (the corona limit).

## Literature

R. W. P. McWhirter, "Spectral Intensities," in *Plasma Diagnostic Techniques* (Academic Press,
1965), ch. 5 — the collisional-dominance (factor-of-10 rate ratio) criterion. H. R. Griem,
*Principles of Plasma Spectroscopy* (Cambridge, 1997), §6 — the two-level collisional–radiative
balance and departure coefficient. G. Cristoforetti et al., "Local Thermodynamic Equilibrium in
Laser-Induced Breakdown Spectroscopy: Beyond the McWhirter criterion," *Spectrochim. Acta B*
**65** (2010) 86–95 — the departure-coefficient / boundary-regime framing beyond McWhirter. The
Boltzmann-plot ordinate is `Boltzmann.boltzmann_plot`; the heteroscedastic error chain is
`ErrorBudget` (Tognoni et al. 2010 lineage).
-/

namespace CflibsFormal

open Finset Real Filter Topology
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-! ## The two-level departure coefficient (M1) -/

/-- **Two-level departure coefficient** `b₂ = R₂₁/(R₂₁ + A₂₁)`: the fraction of the LTE upper-level
population that survives radiative leakage, in terms of the collisional de-excitation rate `R₂₁`
and the spontaneous-decay coefficient `A₂₁`. Kept parametric in the (atomic-physics-input) rates. -/
noncomputable def departureCoeff (R21 A21 : ℝ) : ℝ := R21 / (R21 + A21)

/-- **Two-level balance fixed point** (`REDUCED`; Griem 1997 §6). In steady state the collisional
excitation `n₁ R₁₂` balances collisional de-excitation plus radiative decay `n₂ (R₂₁ + A₂₁)`
(`hbal`); the LTE detailed-balance identity `n₁ R₁₂ = n₂ᴸᵀᴱ R₂₁` (`hlte`) *presumes the lower
level is itself thermalized*, `b₁ ≈ 1` — the standard two-level assumption. Their quotient is the
departure coefficient: `n₂/n₂ᴸᵀᴱ = R₂₁/(R₂₁ + A₂₁)`. This is a *departure* statement, not a claim
that LTE holds. `REDUCED`: the two-level reduction of the full collisional–radiative system. -/
theorem two_level_balance {n1 n2 n2LTE R12 R21 A21 : ℝ}
    (hbal : n1 * R12 = n2 * (R21 + A21))
    (hlte : n1 * R12 = n2LTE * R21)
    (hn2LTE : n2LTE ≠ 0) (hden : R21 + A21 ≠ 0) :
    n2 / n2LTE = departureCoeff R21 A21 := by
  unfold departureCoeff
  have h : n2 * (R21 + A21) = n2LTE * R21 := by rw [← hbal, hlte]
  rw [div_eq_div_iff hn2LTE hden]
  linear_combination h

/-- The departure coefficient is strictly positive for positive rates. -/
theorem departureCoeff_pos {R21 A21 : ℝ} (hR21 : 0 < R21) (hA21 : 0 < A21) :
    0 < departureCoeff R21 A21 := by
  unfold departureCoeff
  exact div_pos hR21 (by linarith)

/-- The departure coefficient is at most `1` (sub-LTE: radiative leakage can only *underpopulate*
the upper level). -/
theorem departureCoeff_le_one {R21 A21 : ℝ} (hR21 : 0 ≤ R21) (hA21 : 0 < A21) :
    departureCoeff R21 A21 ≤ 1 := by
  unfold departureCoeff
  rw [div_le_one (by linarith)]
  linarith

/-! ## Density form, sandwich, monotonicity (M2) -/

/-- **Density-parametric departure coefficient** `b₂(n_e) = n_e C₂₁/(n_e C₂₁ + A₂₁)`, the
electron-impact form of `departureCoeff` with `R₂₁ = n_e C₂₁` (`C₂₁` the electron-impact rate
coefficient). Pure real algebra in the parameters; the physics enters at the McWhirter and
error-budget theorems. -/
noncomputable def departureCoeffNe (C21 A21 ne : ℝ) : ℝ :=
  ne * C21 / (ne * C21 + A21)

/-- Closed form `b₂(n_e) = 1 − A₂₁/(n_e C₂₁ + A₂₁)` — the `1 − b` workhorse. -/
private theorem departureCoeffNe_eq_one_sub {C21 A21 ne : ℝ} (hden : 0 < ne * C21 + A21) :
    departureCoeffNe C21 A21 ne = 1 - A21 / (ne * C21 + A21) := by
  unfold departureCoeffNe
  rw [eq_sub_iff_add_eq, ← add_div, div_self hden.ne']

/-- The density-form departure coefficient is nonnegative. -/
theorem departureCoeffNe_nonneg {C21 A21 ne : ℝ} (hC : 0 < C21) (hne : 0 ≤ ne) (hA : 0 < A21) :
    0 ≤ departureCoeffNe C21 A21 ne := by
  unfold departureCoeffNe
  have hx : 0 ≤ ne * C21 := mul_nonneg hne hC.le
  exact div_nonneg hx (by linarith)

/-- The density-form departure coefficient is at most `1` (sub-LTE). -/
theorem departureCoeffNe_le_one {C21 A21 ne : ℝ} (hC : 0 < C21) (hne : 0 ≤ ne) (hA : 0 < A21) :
    departureCoeffNe C21 A21 ne ≤ 1 := by
  unfold departureCoeffNe
  have hx : 0 ≤ ne * C21 := mul_nonneg hne hC.le
  rw [div_le_one (by linarith)]
  linarith

/-- **Explicit density bound on the departure** (`PURE-MATH`). The exact gap
`1 − b₂ = A₂₁/(n_e C₂₁ + A₂₁)` is bounded by dropping the `+A₂₁` in the denominator:
`|b₂(n_e) − 1| ≤ A₂₁/(n_e C₂₁)`. The clean, transcendental-free handle on "closeness to LTE." -/
theorem one_sub_departureCoeffNe {C21 A21 ne : ℝ} (hC : 0 < C21) (hA : 0 < A21) (hne : 0 < ne) :
    |departureCoeffNe C21 A21 ne - 1| ≤ A21 / (ne * C21) := by
  have hpos : 0 < ne * C21 := mul_pos hne hC
  have hden : 0 < ne * C21 + A21 := by linarith
  have heq : departureCoeffNe C21 A21 ne - 1 = -(A21 / (ne * C21 + A21)) := by
    rw [departureCoeffNe_eq_one_sub hden]; ring
  rw [heq, abs_neg, abs_of_nonneg (by positivity)]
  rw [div_le_div_iff₀ hden hpos]
  nlinarith [hA]

/-- **Denser plasma is closer to LTE** (`PURE-MATH`). `b₂(n_e)` is strictly increasing in the
electron density on `(0, ∞)`: as `n_e` grows the subtracted term `A₂₁/(n_e C₂₁ + A₂₁)` strictly
decreases. -/
theorem departureCoeffNe_strictMonoOn_ne {C21 A21 : ℝ} (hC : 0 < C21) (hA : 0 < A21) :
    StrictMonoOn (fun ne => departureCoeffNe C21 A21 ne) (Set.Ioi 0) := by
  intro a ha b hb hab
  simp only [Set.mem_Ioi] at ha hb
  have hda : 0 < a * C21 + A21 := by nlinarith [mul_pos ha hC]
  have hdb : 0 < b * C21 + A21 := by nlinarith [mul_pos hb hC]
  have hdab : a * C21 + A21 < b * C21 + A21 := by nlinarith [hab, hC]
  simp only [departureCoeffNe_eq_one_sub hda, departureCoeffNe_eq_one_sub hdb]
  have hfrac : A21 / (b * C21 + A21) < A21 / (a * C21 + A21) := by
    rw [div_lt_div_iff₀ hdb hda]
    nlinarith [hA, hdab]
  linarith

/-! ## The LTE limit (M3) -/

/-- **LTE limit** (`REDUCED`; Cristoforetti 2010 boundary regime). As the electron density grows
without bound the departure coefficient tends to `1`: `b₂(n_e) → 1` as `n_e → ∞`, since
`1 − b₂ = A₂₁/(n_e C₂₁ + A₂₁) → 0` (the denominator `→ +∞`). The high-density LTE recovery. -/
theorem departureCoeffNe_tendsto_one {C21 A21 : ℝ} (hC : 0 < C21) (hA : 0 < A21) :
    Tendsto (fun ne => departureCoeffNe C21 A21 ne) atTop (𝓝 1) := by
  have hg : Tendsto (fun ne : ℝ => ne * C21 + A21) atTop atTop :=
    tendsto_atTop_add_const_right atTop A21 (tendsto_id.atTop_mul_const hC)
  have hfrac : Tendsto (fun ne : ℝ => A21 / (ne * C21 + A21)) atTop (𝓝 0) :=
    Tendsto.div_atTop tendsto_const_nhds hg
  have hmain : Tendsto (fun ne : ℝ => 1 - A21 / (ne * C21 + A21)) atTop (𝓝 (1 - 0)) :=
    Tendsto.sub tendsto_const_nhds hfrac
  rw [sub_zero] at hmain
  refine hmain.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with ne hne
  have hden : 0 < ne * C21 + A21 := by nlinarith [mul_pos hne hC]
  rw [departureCoeffNe_eq_one_sub hden]

/-! ## McWhirter's factor-of-10 ⇒ a departure threshold (M4)

Standalone algebra on the abstract rate ratio `n_e C₂₁` vs `A₂₁`. **Not** a formal bridge to the
repo's numeric `StarkBroadening.mcWhirterBound`; the bridge `1.6·10¹²·√T·(ΔE)³ ↔ 10·A₂₁/C₂₁` is a
non-derivable atomic-physics identity (see the module's honest scope). -/

/-- **McWhirter's factor-of-10 rate ratio forces `b₂ ≥ 10/11`** (`EXACT`; McWhirter 1965). When
collisional de-excitation dominates radiative decay by McWhirter's factor of ten,
`10 A₂₁ ≤ n_e C₂₁`, the departure coefficient satisfies `b₂(n_e) ≥ 10/11 ≈ 0.909`. This is the
exact departure content of the McWhirter *rate ratio* — stated over the abstract rates, **not**
identified with the repo's numeric density bound. -/
theorem mcwhirter_forces_departure {C21 A21 ne : ℝ} (hC : 0 < C21) (hA : 0 < A21) (hne : 0 ≤ ne)
    (h10 : 10 * A21 ≤ ne * C21) : (10 : ℝ) / 11 ≤ departureCoeffNe C21 A21 ne := by
  have hx : 0 ≤ ne * C21 := mul_nonneg hne hC.le
  unfold departureCoeffNe
  rw [div_le_div_iff₀ (by norm_num : (0:ℝ) < 11) (by linarith : (0:ℝ) < ne * C21 + A21)]
  linarith

/-- **Departure threshold equivalence** (`REDUCED`; Cristoforetti 2010). For a target closeness
`δ > 0`, the departure meets `b₂(n_e) ≥ 1 − δ` iff the electron density clears the explicit
threshold `n_e ≥ A₂₁(1 − δ)/(C₂₁ δ)` — the departure analogue of
`PartialLTE.mcwhirter_iff_thermalizationLimit`, in proof style only (over the abstract rate ratio,
not the numeric McWhirter bound). Stated for all `δ > 0`; the informative near-LTE regime is
`0 < δ < 1` (for `δ ≥ 1` both sides hold trivially). -/
theorem departure_threshold_iff {C21 A21 ne : ℝ} (hC : 0 < C21) (hA : 0 < A21) (hne : 0 ≤ ne)
    {δ : ℝ} (hδ0 : 0 < δ) :
    (1 - δ ≤ departureCoeffNe C21 A21 ne) ↔ (A21 * (1 - δ) / (C21 * δ) ≤ ne) := by
  have hx : 0 ≤ ne * C21 := mul_nonneg hne hC.le
  have hden : 0 < ne * C21 + A21 := by linarith
  unfold departureCoeffNe
  rw [le_div_iff₀ hden, div_le_iff₀ (by positivity : (0:ℝ) < C21 * δ)]
  constructor
  · intro h; nlinarith [h]
  · intro h; nlinarith [h]

/-! ## The departure error budget (M5, crown jewel) -/

/-- **A departure coefficient is an additive Boltzmann-plot ordinate shift** (`EXACT`; Boltzmann).
Under non-LTE the population scales as `nᴺᴸᵀᴱ = b · nᴸᵀᴱ`, so the Boltzmann-plot ordinate
`log(n/g)` picks up the pure additive shift `log b`:
`log(b·nᴸᵀᴱ/g) = log(nᴸᵀᴱ/g) + log b`. A definitional `log_mul` identity, faithful to
`Boltzmann.boltzmann_plot`; it identifies a per-line departure coefficient with the abstract
per-line ordinate perturbation `εₖ` of the `ErrorBudget` chain. -/
theorem nonlte_ordinate_shift {g nLTE : ℝ} (b : ℝ) (hnLTE : 0 < nLTE) (hg : 0 < g) (hb : 0 < b) :
    Real.log (b * nLTE / g) = Real.log (nLTE / g) + Real.log b := by
  rw [show b * nLTE / g = b * (nLTE / g) by ring,
    Real.log_mul hb.ne' (div_pos hnLTE hg).ne']
  ring

/-- **A bounded departure gives a bounded log-ordinate perturbation** (`PURE-MATH`). If
`|b − 1| ≤ δ_b` with `0 ≤ δ_b < 1` then `|log b| ≤ δ_b/(1 − δ_b)`, via the positive-floor
Lipschitz bound `ErrorBudget.log_lip_floor` applied with `a = b`, `b = 1`, `c = 1 − δ_b`
(`log 1 = 0`). The near-LTE floor `1 − δ_b > 0` is load-bearing. -/
theorem abs_log_departure_le {b δb : ℝ} (hδ0 : 0 ≤ δb) (hδ1 : δb < 1) (hb : |b - 1| ≤ δb) :
    |Real.log b| ≤ δb / (1 - δb) := by
  have hc : 0 < 1 - δb := by linarith
  have habs := abs_le.mp hb
  have hlb : 1 - δb ≤ b := by linarith [habs.1]
  have hub : 1 - δb ≤ 1 := by linarith
  have hlip := log_lip_floor hc hlb hub
  rw [Real.log_one, sub_zero] at hlip
  refine hlip.trans ?_
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right hb (inv_nonneg.mpr hc.le)

/-- **Non-LTE temperature error budget, temperature leg** (`REDUCED`; Cristoforetti 2010). A
per-line departure `bₖ` shifts the Boltzmann ordinate by `log bₖ` (`hshift`, from
`nonlte_ordinate_shift`), so — instantiating the heteroscedastic chain
`ErrorBudget.temp_rel_error_hetero` with `εₖ := |log bₖ|` — the recovered temperature inherits the
relative error `|T̂ − T|/T ≤ k_B·T̂·(∑ₖ|Eₖ − Ē|·|log bₖ|)/SS_E`. Under the Boltzmann-plot
identification of the fitted slope with `1/(k_B T)`. `REDUCED`: worst-case / deterministic. -/
theorem nonlte_temp_error [Nonempty ι] {E yLTE yNLTE b : ι → ℝ} {kB T THat : ℝ}
    (hkB : 0 < kB) (hT : 0 < T) (hTHat : 0 < THat)
    (hshift : ∀ k, yNLTE k = yLTE k + Real.log (b k))
    (hvar : 0 < ∑ k, (E k - mean E) ^ 2)
    (hβ : olsSlope E yLTE = 1 / (kB * T)) (hβHat : olsSlope E yNLTE = 1 / (kB * THat)) :
    |THat - T| / T ≤ kB * THat * ((∑ k, |E k - mean E| * |Real.log (b k)|)
                                    / (∑ k, (E k - mean E) ^ 2)) := by
  have hδ : ∀ k, |yNLTE k - yLTE k| ≤ |Real.log (b k)| := by
    intro k; rw [hshift k, add_sub_cancel_left]
  exact temp_rel_error_hetero hkB hT hTHat hvar hδ hβ hβHat

/-- **Non-LTE density error budget, density leg** (`REDUCED`; Cristoforetti 2010). The intercept
twin of `nonlte_temp_error`: the per-line ordinate shifts `log bₖ` propagate through
`ErrorBudget.olsIntercept_stable_hetero` and the density reader `ErrorBudget.relDensity_le` to
`|N̂ − N| ≤ N·(exp((∑ₖ|log bₖ|)/card ι) − 1)`. Carries the centered-convention hypothesis
`hcent : mean E = 0` (the standard Boltzmann-plot normalization the intercept engine requires). -/
theorem nonlte_density_error [Nonempty ι] {E yLTE yNLTE b : ι → ℝ} {U Fcal : ℝ}
    (hU : 0 ≤ U) (hFcal : 0 < Fcal) (hcent : mean E = 0)
    (hshift : ∀ k, yNLTE k = yLTE k + Real.log (b k)) :
    |Real.exp (olsIntercept E yNLTE) * U / Fcal - Real.exp (olsIntercept E yLTE) * U / Fcal|
      ≤ (Real.exp (olsIntercept E yLTE) * U / Fcal)
          * (Real.exp ((∑ k, |Real.log (b k)|) / (Fintype.card ι)) - 1) := by
  have hδ : ∀ k, |yNLTE k - yLTE k| ≤ |Real.log (b k)| := by
    intro k; rw [hshift k, add_sub_cancel_left]
  have hint := olsIntercept_stable_hetero (eps := fun k => |Real.log (b k)|) hcent hδ
  exact relDensity_le hU hFcal hint

/-! ## Uniform-`δ_b` temperature budget (M6) -/

/-- **Non-LTE temperature error budget, uniform departure bound** (`REDUCED`; Cristoforetti 2010).
The near-LTE specialization of `nonlte_temp_error`: a *uniform* departure bound `|bₖ − 1| ≤ δ_b`
(with `0 ≤ δ_b < 1`) yields `|log bₖ| ≤ δ_b/(1 − δ_b)` on every line (`abs_log_departure_le`), and
that constant factors out of the sum:
`|T̂ − T|/T ≤ k_B·T̂·(δ_b/(1 − δ_b))·(∑ₖ|Eₖ − Ē|)/SS_E`. The single-number departure-budget form. -/
theorem nonlte_temp_error_uniform [Nonempty ι] {E yLTE yNLTE b : ι → ℝ} {kB T THat δb : ℝ}
    (hkB : 0 < kB) (hT : 0 < T) (hTHat : 0 < THat)
    (hshift : ∀ k, yNLTE k = yLTE k + Real.log (b k))
    (hvar : 0 < ∑ k, (E k - mean E) ^ 2)
    (hδ0 : 0 ≤ δb) (hδ1 : δb < 1) (hb : ∀ k, |b k - 1| ≤ δb)
    (hβ : olsSlope E yLTE = 1 / (kB * T)) (hβHat : olsSlope E yNLTE = 1 / (kB * THat)) :
    |THat - T| / T ≤ kB * THat * (δb / (1 - δb))
        * (∑ k, |E k - mean E|) / (∑ k, (E k - mean E) ^ 2) := by
  have hmain := nonlte_temp_error hkB hT hTHat hshift hvar hβ hβHat
  refine hmain.trans ?_
  have hsum : (∑ k, |E k - mean E| * |Real.log (b k)|)
      ≤ (δb / (1 - δb)) * (∑ k, |E k - mean E|) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun k _ => ?_)
    rw [mul_comm (δb / (1 - δb)) _]
    exact mul_le_mul_of_nonneg_left (abs_log_departure_le hδ0 hδ1 (hb k)) (abs_nonneg _)
  calc kB * THat * ((∑ k, |E k - mean E| * |Real.log (b k)|)
          / (∑ k, (E k - mean E) ^ 2))
      ≤ kB * THat * ((δb / (1 - δb)) * (∑ k, |E k - mean E|)
          / (∑ k, (E k - mean E) ^ 2)) := by
        gcongr
    _ = kB * THat * (δb / (1 - δb)) * (∑ k, |E k - mean E|)
          / (∑ k, (E k - mean E) ^ 2) := by ring

/-! ## Non-vacuity witnesses -/

/-- `R₂₁ = A₂₁ = 1` gives the balance quotient `b₂ = 1/2` on concrete data. -/
example : (1 : ℝ) / 2 = departureCoeff 1 1 :=
  two_level_balance (n1 := 1) (n2 := 1) (n2LTE := 2) (R12 := 2) (R21 := 1) (A21 := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

example : (0:ℝ) < departureCoeff 1 1 := departureCoeff_pos (by norm_num) (by norm_num)

example : departureCoeff 1 1 ≤ 1 := departureCoeff_le_one (by norm_num) (by norm_num)

example : |departureCoeffNe 1 1 1 - 1| ≤ 1 / (1 * 1) :=
  one_sub_departureCoeffNe (by norm_num) (by norm_num) (by norm_num)

example : departureCoeffNe 1 1 1 < departureCoeffNe 1 1 2 :=
  departureCoeffNe_strictMonoOn_ne (by norm_num) (by norm_num)
    (Set.mem_Ioi.mpr (by norm_num)) (Set.mem_Ioi.mpr (by norm_num)) (by norm_num)

example : (10 : ℝ) / 11 ≤ departureCoeffNe 1 1 10 :=
  mcwhirter_forces_departure (by norm_num) (by norm_num) (by norm_num) (by norm_num)

example : (1 - (1:ℝ)/2 ≤ departureCoeffNe 1 1 1) ↔ ((1:ℝ) * (1 - 1/2) / (1 * (1/2)) ≤ 1) :=
  departure_threshold_iff (C21 := 1) (A21 := 1) (ne := 1) (δ := 1/2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

example : Real.log (Real.exp 1 * Real.exp 2 / Real.exp 3)
    = Real.log (Real.exp 2 / Real.exp 3) + Real.log (Real.exp 1) :=
  nonlte_ordinate_shift _ (by positivity) (by positivity) (by positivity)

example : |Real.log 1| ≤ (1 / 2 : ℝ) / (1 - 1 / 2) :=
  abs_log_departure_le (by norm_num) (by norm_num) (by norm_num)

/-- Non-vacuity witness for `nonlte_temp_error`: the slope-identification and shift hypotheses
are jointly satisfiable on concrete data (`E = (0, 1)`, `yLTE = (0, 1)`, `b = (1, e)` so
`yNLTE = (0, 2)`; `k_B = T = 1`, `T̂ = 1/2`). The data saturates the bound (equality case). -/
example :
    |(1/2 : ℝ) - 1| / 1
      ≤ 1 * (1/2) * ((∑ k, |(![0, 1] : Fin 2 → ℝ) k - mean ![0, 1]|
            * |Real.log ((![1, Real.exp 1] : Fin 2 → ℝ) k)|)
          / (∑ k, ((![0, 1] : Fin 2 → ℝ) k - mean ![0, 1]) ^ 2)) :=
  nonlte_temp_error (yLTE := ![0, 1]) (yNLTE := ![0, 2]) (b := ![1, Real.exp 1])
    (kB := 1) (T := 1) (THat := 1/2)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro k; fin_cases k <;> norm_num [Real.log_one, Real.log_exp])
    (by simp only [mean, Fin.sum_univ_two, Fintype.card_fin, Matrix.cons_val_zero,
          Matrix.cons_val_one]; norm_num)
    (by simp only [olsSlope, mean, Fin.sum_univ_two, Fintype.card_fin, Matrix.cons_val_zero,
          Matrix.cons_val_one]; norm_num)
    (by simp only [olsSlope, mean, Fin.sum_univ_two, Fintype.card_fin, Matrix.cons_val_zero,
          Matrix.cons_val_one]; norm_num)

/-- Non-vacuity witness for `nonlte_density_error`: two centered lines `E = (−1, 1)`
(so `mean E = 0`), a genuine departure `b = (1, 2)` on the second line. -/
example :
    |Real.exp (olsIntercept (![-1, 1] : Fin 2 → ℝ) ![0, Real.log 2]) * 1 / 1
        - Real.exp (olsIntercept (![-1, 1] : Fin 2 → ℝ) ![0, 0]) * 1 / 1|
      ≤ (Real.exp (olsIntercept (![-1, 1] : Fin 2 → ℝ) ![0, 0]) * 1 / 1)
          * (Real.exp ((∑ k, |Real.log ((![1, 2] : Fin 2 → ℝ) k)|)
              / (Fintype.card (Fin 2))) - 1) :=
  nonlte_density_error (b := ![1, 2]) (by norm_num) (by norm_num)
    (by simp only [mean, Fin.sum_univ_two, Fintype.card_fin]; norm_num)
    (by intro k; fin_cases k <;> simp [Real.log_one])

end CflibsFormal
