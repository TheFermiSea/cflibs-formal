/-
Copyright (c) 2026 Brian Squires. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Squires
-/
import Mathlib
import CflibsFormal.Robustness
import CflibsFormal.CompositionRobustness
import CflibsFormal.Alt.LeastSquares

/-!
# CF-LIBS formalization — the error-propagation chain and DERIVED reliability thresholds

A numerical CF-LIBS pipeline guards its inversion with empirical "magic-number" thresholds
— a minimum number of lines per element, a minimum upper-level energy spread, a minimum SNR.
This module turns those thresholds into **proven corollaries of a single deterministic
error-propagation chain**, so they follow *from a target accuracy* rather than being tuned.

The chain is the multi-line generalization of `Robustness.twoLineBeta_stable` (which bounds the
TWO-line slope) to the full ordinary-least-squares Boltzmann-plot slope `Alt.olsSlope` over
`N` lines, then forward through temperature and composition:

```
  per-line ordinate error ε                       (measurement / SNR)
        │  olsSlope_stable_l1 (sharp ℓ¹ bound) / _l2 (Cauchy–Schwarz bound)
        ▼
  inverse-temperature (slope) error |Δβ|
        │  temp_rel_error_eq         (EXACT identity)
        ▼
  relative temperature error |ΔT|/T
        │  CompositionRobustness.composition_abs_sub_le
        ▼
  composition error |ΔCₛ|  ≤  target τ
```

The links are *upper bounds* except `temp_rel_error_eq` (and `olsSlope_noise_gain`), which are
exact identities. `olsSlope_stable_l1` is sharp (its worst case is attained); `olsSlope_stable_l2`
is a Cauchy–Schwarz bound (tight only when the ordinate errors are proportional to `Eₖ − Ē`).

Inverting the chain yields the thresholds (`requiredEnergySpread_sufficient`,
`maxPerLineError_sufficient`): the energy spread / SNR that *guarantee* a target slope (hence
temperature, hence composition) accuracy.

## Honest scope of the line-count threshold

The bounds here are **deterministic worst-case** (adversarial, perfectly-correlated ordinate
errors). In that regime the dominant levers are the **energy spread** `SS_E = ∑ (Eₖ − Ē)²` and
the **per-line error** `ε` — and adding more lines at the SAME energies does *not* improve the
worst case (`olsSlope_stable_l2_sq` has `card ι` in the numerator). The familiar "more lines ⇒
better" rule is a **statistical** statement: under independent zero-mean noise of variance
`σ²` the slope variance is `σ²·(∑ wₖ²) = σ²/SS_E` (Gauss–Markov). Its deterministic kernel —
the OLS slope's noise gain `∑ wₖ² = 1/SS_E` — is proven here as `olsSlope_noise_gain`; the
probabilistic `Var` layer is deliberately out of scope (it needs `Mathlib`'s probability
stack), and we do **not** claim a deterministic min-line-count bound the worst case cannot
support. See `oracle/Generate.lean` for the Float mirrors the numerical pipeline consumes.

Modeling assumptions (all explicit, inherited from the forward map): LTE single-temperature
populations, optically-thin emission (`lineIntensity`), a shared calibration `Fcal`, and known
partition functions `U_s(T)`. `mean` / `olsSlope` are reused verbatim from `Alt.LeastSquares`.

Scope of the chain: the temperature channel (Tasks 1–2) and the density/concentration channel
(Task 3) are bounded **independently** — the latter (`relDensity_le`) treats `U` and `Fcal` as
exactly known and confines the perturbation to the intercept `b`. We do **not** prove a single
closed end-to-end `ε ⇒ composition` bound that feeds the recovered temperature error back into
`U(T̂)`; the two channels are reliability budgets to be combined by the caller, not composed here.
-/

namespace CflibsFormal

open Finset Real
open scoped BigOperators
open CflibsFormal.Alt

variable {ι : Type*} [Fintype ι]
variable {κ : Type*} [Fintype κ]

/-! ## Task 1 — N-line least-squares slope sensitivity (generalizes `twoLineBeta_stable`) -/

/-- The centered energies sum to zero: `∑ₖ (Eₖ − Ē) = 0`. The lever that makes the OLS slope a
*centered-linear* functional of the ordinates (the `mean y` term drops out). Needs at least one
line (`[Nonempty ι]`, so `card ι ≠ 0`). -/
theorem centered_sum_zero [Nonempty ι] (E : ι → ℝ) :
    ∑ k, (E k - mean E) = 0 := by
  have hcard : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  unfold mean
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp
  ring

/-- **OLS slope is centered-linear in the ordinates.** `olsSlope E y =
(∑ₖ (Eₖ − Ē)·yₖ) / SS_E`: centering kills the `mean y` term because `∑ (Eₖ − Ē) = 0`. This is
the representation `β̂(y) = ∑ₖ wₖ yₖ` with weights `wₖ = (Eₖ − Ē)/SS_E` on which every
sensitivity bound below rests. -/
theorem olsSlope_eq_centered [Nonempty ι] (E y : ι → ℝ) :
    olsSlope E y = (∑ k, (E k - mean E) * y k) / (∑ k, (E k - mean E) ^ 2) := by
  unfold olsSlope
  congr 1
  have h0 : ∑ k, (E k - mean E) = 0 := centered_sum_zero E
  calc ∑ k, (E k - mean E) * (y k - mean y)
      = ∑ k, ((E k - mean E) * y k - (E k - mean E) * mean y) := by
        refine Finset.sum_congr rfl (fun k _ => ?_); ring
    _ = (∑ k, (E k - mean E) * y k) - (∑ k, (E k - mean E)) * mean y := by
        rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
    _ = ∑ k, (E k - mean E) * y k := by rw [h0]; ring

/-- **Slope perturbation is linear in the ordinate perturbation.**
`olsSlope E ŷ − olsSlope E y = (∑ₖ (Eₖ − Ē)(ŷₖ − yₖ)) / SS_E`. The bridge for the Lipschitz
bounds: the slope error is the centered-energy-weighted sum of the per-line ordinate errors. -/
theorem olsSlope_sub_eq [Nonempty ι] (E y yHat : ι → ℝ) :
    olsSlope E yHat - olsSlope E y
      = (∑ k, (E k - mean E) * (yHat k - y k)) / (∑ k, (E k - mean E) ^ 2) := by
  rw [olsSlope_eq_centered E yHat, olsSlope_eq_centered E y, div_sub_div_same]
  congr 1
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  ring

/-- **N-line slope sensitivity (ℓ¹, sharp worst case).** If every ordinate is perturbed by at
most `ε` then the OLS slope changes by at most `ε·(∑ₖ |Eₖ − Ē|)/SS_E`. This is the multi-line
generalization of `Robustness.twoLineBeta_stable`; the worst case (all ordinate errors aligned
in sign with `Eₖ − Ē`) attains it. `hvar : 0 < SS_E` (at least two distinct energies) is
load-bearing for the nonzero denominator. -/
theorem olsSlope_stable_l1 [Nonempty ι] {E y yHat : ι → ℝ} {eps : ℝ}
    (hvar : 0 < ∑ k, (E k - mean E) ^ 2)
    (hδ : ∀ k, |yHat k - y k| ≤ eps) :
    |olsSlope E yHat - olsSlope E y|
      ≤ eps * (∑ k, |E k - mean E|) / (∑ k, (E k - mean E) ^ 2) := by
  rw [olsSlope_sub_eq, abs_div, abs_of_pos hvar]
  gcongr
  calc |∑ k, (E k - mean E) * (yHat k - y k)|
      ≤ ∑ k, |(E k - mean E) * (yHat k - y k)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k, |E k - mean E| * |yHat k - y k| := by simp_rw [abs_mul]
    _ ≤ ∑ k, |E k - mean E| * eps := by
        refine Finset.sum_le_sum (fun k _ => ?_)
        exact mul_le_mul_of_nonneg_left (hδ k) (abs_nonneg _)
    _ = eps * ∑ k, |E k - mean E| := by rw [← Finset.sum_mul]; ring

/-- **N-line slope sensitivity (ℓ², squared form).** `(Δβ)² ≤ ε²·(card ι)/SS_E`, via the
Cauchy–Schwarz inequality `(∑ wₖ δₖ)² ≤ (∑ wₖ²)(∑ δₖ²)`. The squared form avoids all square
roots and is the cleanest object to invert into thresholds (see Task 4). Note `card ι` sits in
the NUMERATOR — the deterministic worst case does not improve with more lines (see the module
docstring). -/
theorem olsSlope_stable_l2_sq [Nonempty ι] {E y yHat : ι → ℝ} {eps : ℝ}
    (hvar : 0 < ∑ k, (E k - mean E) ^ 2)
    (hδ : ∀ k, |yHat k - y k| ≤ eps) :
    (olsSlope E yHat - olsSlope E y) ^ 2
      ≤ eps ^ 2 * (Fintype.card ι) / (∑ k, (E k - mean E) ^ 2) := by
  rw [olsSlope_sub_eq, div_pow]
  have hSSnn : 0 ≤ ∑ k, (E k - mean E) ^ 2 := Finset.sum_nonneg (fun k _ => sq_nonneg _)
  have hSne : (∑ k, (E k - mean E) ^ 2) ≠ 0 := hvar.ne'
  have hSS2 : (0 : ℝ) < (∑ k, (E k - mean E) ^ 2) ^ 2 := by positivity
  have hCS : (∑ k, (E k - mean E) * (yHat k - y k)) ^ 2
      ≤ (∑ k, (E k - mean E) ^ 2) * (∑ k, (yHat k - y k) ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq univ (fun k => E k - mean E) (fun k => yHat k - y k)
  have hδ2 : (∑ k, (yHat k - y k) ^ 2) ≤ (Fintype.card ι : ℝ) * eps ^ 2 := by
    have hle : (∑ k, (yHat k - y k) ^ 2) ≤ ∑ _k : ι, eps ^ 2 := by
      refine Finset.sum_le_sum (fun k _ => ?_)
      have h := abs_le.mp (hδ k)
      nlinarith [h.1, h.2]
    simpa [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm] using hle
  have hnum : (∑ k, (E k - mean E) * (yHat k - y k)) ^ 2
      ≤ (∑ k, (E k - mean E) ^ 2) * ((Fintype.card ι : ℝ) * eps ^ 2) :=
    hCS.trans (mul_le_mul_of_nonneg_left hδ2 hSSnn)
  rw [div_le_iff₀ hSS2]
  have hrhs : eps ^ 2 * (Fintype.card ι) / (∑ k, (E k - mean E) ^ 2)
        * (∑ k, (E k - mean E) ^ 2) ^ 2
      = eps ^ 2 * (Fintype.card ι) * (∑ k, (E k - mean E) ^ 2) := by
    field_simp
  rw [hrhs]
  nlinarith [hnum]

/-- **N-line slope sensitivity (ℓ², root form).** `|Δβ| ≤ ε·√(card ι)/√SS_E`, the square root
of `olsSlope_stable_l2_sq` — the form quoted in textbook LIBS error budgets. -/
theorem olsSlope_stable_l2 [Nonempty ι] {E y yHat : ι → ℝ} {eps : ℝ}
    (hvar : 0 < ∑ k, (E k - mean E) ^ 2)
    (hδ : ∀ k, |yHat k - y k| ≤ eps) :
    |olsSlope E yHat - olsSlope E y|
      ≤ eps * Real.sqrt (Fintype.card ι) / Real.sqrt (∑ k, (E k - mean E) ^ 2) := by
  have heps0 : 0 ≤ eps := le_trans (abs_nonneg _) (hδ (Classical.arbitrary ι))
  have hsq := olsSlope_stable_l2_sq hvar hδ
  calc |olsSlope E yHat - olsSlope E y|
      = Real.sqrt ((olsSlope E yHat - olsSlope E y) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (eps ^ 2 * (Fintype.card ι) / (∑ k, (E k - mean E) ^ 2)) :=
        Real.sqrt_le_sqrt hsq
    _ = eps * Real.sqrt (Fintype.card ι) / Real.sqrt (∑ k, (E k - mean E) ^ 2) := by
        rw [Real.sqrt_div (by positivity), Real.sqrt_mul (by positivity), Real.sqrt_sq heps0]

/-- **OLS slope noise gain.** `∑ₖ wₖ² = 1/SS_E` for the weights `wₖ = (Eₖ − Ē)/SS_E`. This is
the deterministic kernel of the Gauss–Markov variance law `Var(β̂) = σ²·∑ wₖ² = σ²/SS_E`: under
independent ordinate noise of variance `σ²` the slope variance is `σ²/SS_E`, which (with
`SS_E ≈ N·Var(E)`) is the principled origin of the "more lines ⇒ better" rule. The probabilistic
`Var` layer is out of scope; this identity is the part that is purely algebraic. -/
theorem olsSlope_noise_gain (E : ι → ℝ) (hvar : 0 < ∑ k, (E k - mean E) ^ 2) :
    ∑ k, ((E k - mean E) / (∑ j, (E j - mean E) ^ 2)) ^ 2
      = 1 / (∑ k, (E k - mean E) ^ 2) := by
  have hS : (∑ k, (E k - mean E) ^ 2) ≠ 0 := hvar.ne'
  calc ∑ k, ((E k - mean E) / (∑ j, (E j - mean E) ^ 2)) ^ 2
      = ∑ k, (E k - mean E) ^ 2 / (∑ j, (E j - mean E) ^ 2) ^ 2 := by
        refine Finset.sum_congr rfl (fun k _ => ?_); rw [div_pow]
    _ = (∑ k, (E k - mean E) ^ 2) / (∑ j, (E j - mean E) ^ 2) ^ 2 := by rw [← Finset.sum_div]
    _ = 1 / (∑ k, (E k - mean E) ^ 2) := by rw [sq]; field_simp

/-- **N = 2 reduces to the classic two-line constant.** For exactly two lines the ℓ¹
slope-sensitivity constant `(∑ₖ |Eₖ − Ē|)/SS_E` equals `2/|E₀ − E₁|` — exactly the Lipschitz
constant of `Robustness.twoLineBeta_stable`. So the multi-line bound specializes to the classic
two-line bound, confirming the generalization. -/
theorem olsSlope_l1_const_two {E : Fin 2 → ℝ} (hE : E 0 ≠ E 1) :
    (∑ k, |E k - mean E|) / (∑ k, (E k - mean E) ^ 2) = 2 / |E 0 - E 1| := by
  have hd : E 0 - E 1 ≠ 0 := sub_ne_zero.mpr hE
  have habs : |E 0 - E 1| ≠ 0 := abs_ne_zero.mpr hd
  have hmean : mean E = (E 0 + E 1) / 2 := by
    unfold mean; rw [show (Fintype.card (Fin 2) : ℝ) = 2 by simp, Fin.sum_univ_two]
  have hnum : (∑ k, |E k - mean E|) = |E 0 - E 1| := by
    rw [Fin.sum_univ_two, hmean]
    have e0 : E 0 - (E 0 + E 1) / 2 = (E 0 - E 1) / 2 := by ring
    have e1 : E 1 - (E 0 + E 1) / 2 = -((E 0 - E 1) / 2) := by ring
    rw [e0, e1, abs_neg]
    have hhalf : |(E 0 - E 1) / 2| = |E 0 - E 1| / 2 := by rw [abs_div]; norm_num
    rw [hhalf]; ring
  have hden : (∑ k, (E k - mean E) ^ 2) = (E 0 - E 1) ^ 2 / 2 := by
    rw [Fin.sum_univ_two, hmean]; ring
  rw [hnum, hden, ← sq_abs (E 0 - E 1)]
  field_simp

/-- **N = 2 bound matches `twoLineBeta_stable`.** Specializing `olsSlope_stable_l1` to two lines
gives `|Δβ| ≤ 2·ε/|E₀ − E₁|` — the exact form of `Robustness.twoLineBeta_stable`. -/
theorem olsSlope_stable_two {E y yHat : Fin 2 → ℝ} {eps : ℝ}
    (hE : E 0 ≠ E 1) (hδ : ∀ k, |yHat k - y k| ≤ eps) :
    |olsSlope E yHat - olsSlope E y| ≤ 2 * eps / |E 0 - E 1| := by
  have hne : E 0 - E 1 ≠ 0 := sub_ne_zero.mpr hE
  have hmean : mean E = (E 0 + E 1) / 2 := by
    unfold mean; rw [show (Fintype.card (Fin 2) : ℝ) = 2 by simp, Fin.sum_univ_two]
  have hden : (∑ k, (E k - mean E) ^ 2) = (E 0 - E 1) ^ 2 / 2 := by
    rw [Fin.sum_univ_two, hmean]; ring
  have hvar : 0 < ∑ k, (E k - mean E) ^ 2 := by
    rw [hden]; positivity
  calc |olsSlope E yHat - olsSlope E y|
      ≤ eps * (∑ k, |E k - mean E|) / (∑ k, (E k - mean E) ^ 2) :=
        olsSlope_stable_l1 hvar hδ
    _ = eps * ((∑ k, |E k - mean E|) / (∑ k, (E k - mean E) ^ 2)) := by ring
    _ = eps * (2 / |E 0 - E 1|) := by rw [olsSlope_l1_const_two hE]
    _ = 2 * eps / |E 0 - E 1| := by ring

/-! ## Task 2 — temperature relative-error bound -/

/-- **Exact temperature relative error.** With inverse temperatures `β = 1/(k_B T)` and
`β̂ = 1/(k_B T̂)`, the recovered temperature's relative error is *exactly*
`|T̂ − T|/T = k_B·T̂·|β̂ − β|`. (No linearization: this is an identity, not a first-order
estimate. The leading constant `k_B·T̂` reduces to `1/β̂`; with `T̂ → T` it is the textbook
`σ_T/T = k_B T σ_β`.) -/
theorem temp_rel_error_eq {kB T THat : ℝ} (hkB : 0 < kB) (hT : 0 < T) (hTHat : 0 < THat) :
    |THat - T| / T = kB * THat * |1 / (kB * THat) - 1 / (kB * T)| := by
  have hTne : T ≠ 0 := hT.ne'
  have hkBne : kB ≠ 0 := hkB.ne'
  have hTHatne : THat ≠ 0 := hTHat.ne'
  have hpos : (0 : ℝ) < kB * T * THat := by positivity
  have h1 : 1 / (kB * THat) - 1 / (kB * T) = (T - THat) / (kB * T * THat) := by
    field_simp
  rw [h1, abs_div, abs_of_pos hpos, abs_sub_comm T THat]
  field_simp

/-- **Temperature stability from a slope-error bound.** Any bound `|β̂ − β| ≤ B` on the
inverse-temperature (slope) error propagates to `|T̂ − T|/T ≤ k_B·T̂·B`. Composed with
`olsSlope_stable_l1`/`_l2` (which bound `B` in terms of `ε`, `card ι`, `SS_E`), this is the
`σ_T/T` reliability criterion: temperature accuracy improves with energy spread and per-line
precision. -/
theorem temp_rel_error_le {kB T THat B : ℝ} (hkB : 0 < kB) (hT : 0 < T) (hTHat : 0 < THat)
    (hB : |1 / (kB * THat) - 1 / (kB * T)| ≤ B) :
    |THat - T| / T ≤ kB * THat * B := by
  rw [temp_rel_error_eq hkB hT hTHat]
  exact mul_le_mul_of_nonneg_left hB (by positivity)

/-! ## Task 4 — threshold corollaries (the DERIVE tier) -/

/-- **Minimum energy spread is SUFFICIENT for a target slope accuracy.** If
`SS_E ≥ ε²·(card ι)/τ²` then `|Δβ| ≤ τ`. Solving the master ℓ² bound for `SS_E` turns the
empirical `min_energy_spread` knob into a derived quantity: the spread needed to hit a target
inverse-temperature error `τ` given the per-line error `ε`. -/
theorem requiredEnergySpread_sufficient [Nonempty ι] {E y yHat : ι → ℝ} {eps tauBeta : ℝ}
    (htau : 0 < tauBeta) (hvar : 0 < ∑ k, (E k - mean E) ^ 2)
    (hδ : ∀ k, |yHat k - y k| ≤ eps)
    (hSS : eps ^ 2 * (Fintype.card ι) / tauBeta ^ 2 ≤ ∑ k, (E k - mean E) ^ 2) :
    |olsSlope E yHat - olsSlope E y| ≤ tauBeta := by
  have htau2 : (0 : ℝ) < tauBeta ^ 2 := by positivity
  have hsq := olsSlope_stable_l2_sq hvar hδ
  have key : eps ^ 2 * (Fintype.card ι) ≤ (∑ k, (E k - mean E) ^ 2) * tauBeta ^ 2 :=
    (div_le_iff₀ htau2).mp hSS
  have hbound : (olsSlope E yHat - olsSlope E y) ^ 2 ≤ tauBeta ^ 2 :=
    hsq.trans ((div_le_iff₀ hvar).mpr (by nlinarith [key]))
  exact abs_le_of_sq_le_sq hbound htau.le

/-- **Maximum per-line error (minimum SNR) is SUFFICIENT for a target slope accuracy.** If
`ε²·(card ι) ≤ τ²·SS_E` then `|Δβ| ≤ τ`. Solving the master ℓ² bound for `ε` turns the
empirical `min_snr` knob into a derived quantity: the largest per-line ordinate error tolerable
for a target inverse-temperature error `τ` at the available energy spread. -/
theorem maxPerLineError_sufficient [Nonempty ι] {E y yHat : ι → ℝ} {eps tauBeta : ℝ}
    (htau : 0 < tauBeta) (hvar : 0 < ∑ k, (E k - mean E) ^ 2)
    (hδ : ∀ k, |yHat k - y k| ≤ eps)
    (heps : eps ^ 2 * (Fintype.card ι) ≤ tauBeta ^ 2 * (∑ k, (E k - mean E) ^ 2)) :
    |olsSlope E yHat - olsSlope E y| ≤ tauBeta := by
  have hsq := olsSlope_stable_l2_sq hvar hδ
  have hbound : (olsSlope E yHat - olsSlope E y) ^ 2 ≤ tauBeta ^ 2 :=
    hsq.trans ((div_le_iff₀ hvar).mpr heps)
  exact abs_le_of_sq_le_sq hbound htau.le

/-! ## Task 3 — compose into composition error (the concentration channel + closure) -/

/-- A clean exponential perturbation bound: `|exp x − 1| ≤ exp η − 1` whenever `|x| ≤ η`. The
kernel of "log-domain error ⇒ relative error": a bounded additive error on a log-quantity (an
intercept, a temperature) maps to a bounded relative error. Exact (no linearization); the
leading term is `η`, since `exp η − 1 → η` as `η → 0`. -/
theorem abs_exp_sub_one_le {x eta : ℝ} (hx : |x| ≤ eta) :
    |Real.exp x - 1| ≤ Real.exp eta - 1 := by
  have h := abs_le.mp hx
  have hup : Real.exp x ≤ Real.exp eta := Real.exp_le_exp.mpr h.2
  have hlo : Real.exp (-eta) ≤ Real.exp x := Real.exp_le_exp.mpr h.1
  have hsum : (2 : ℝ) ≤ Real.exp eta + Real.exp (-eta) := by
    have a := Real.add_one_le_exp eta
    have b := Real.add_one_le_exp (-eta)
    linarith
  rw [abs_le]
  exact ⟨by nlinarith [hlo, hsum], by linarith [hup]⟩

/-- **Relative density error from an intercept (log-concentration) error.** The OLS density
reader is `N = exp(b)·U/Fcal` (`Alt.olsDensity`); at fixed temperature (`U`, `Fcal` shared) an
intercept perturbation `|b̂ − b| ≤ η` gives `|N̂ − N| ≤ N·(exp η − 1)`. Exact; the leading term
is `η`. This is the density/concentration channel that complements the slope/temperature
channel of Tasks 1–2 — both feed the composition error below. -/
theorem relDensity_le {b bHat U Fcal eta : ℝ} (hU : 0 ≤ U) (hFcal : 0 < Fcal)
    (heta : |bHat - b| ≤ eta) :
    |Real.exp bHat * U / Fcal - Real.exp b * U / Fcal|
      ≤ (Real.exp b * U / Fcal) * (Real.exp eta - 1) := by
  have hkey : |Real.exp bHat - Real.exp b| ≤ Real.exp b * (Real.exp eta - 1) := by
    have hb : b + (bHat - b) = bHat := by ring
    have hrw : Real.exp bHat - Real.exp b = Real.exp b * (Real.exp (bHat - b) - 1) := by
      rw [mul_sub, mul_one, ← Real.exp_add, hb]
    rw [hrw, abs_mul, abs_of_pos (Real.exp_pos b)]
    exact mul_le_mul_of_nonneg_left (abs_exp_sub_one_le heta) (Real.exp_pos b).le
  rw [show Real.exp bHat * U / Fcal - Real.exp b * U / Fcal
        = (Real.exp bHat - Real.exp b) * (U / Fcal) by ring,
     show (Real.exp b * U / Fcal) * (Real.exp eta - 1)
        = (Real.exp b * (Real.exp eta - 1)) * (U / Fcal) by ring,
     abs_mul, abs_of_nonneg (div_nonneg hU hFcal.le)]
  exact mul_le_mul_of_nonneg_right hkey (div_nonneg hU hFcal.le)

/-- **Intercept (concentration) sensitivity, centered convention.** With energies referenced to
their mean (`mean E = 0`, the standard Boltzmann-plot normalization), the OLS intercept reduces
to `mean y` and inherits its sensitivity: a per-line ordinate error `≤ ε` gives an intercept
error `≤ ε`. This bounds the `η` consumed by `relDensity_le`. -/
theorem olsIntercept_stable_centered [Nonempty ι] {E y yHat : ι → ℝ} {eps : ℝ}
    (hcent : mean E = 0) (hδ : ∀ k, |yHat k - y k| ≤ eps) :
    |olsIntercept E yHat - olsIntercept E y| ≤ eps := by
  have hcard : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hi : ∀ z : ι → ℝ, olsIntercept E z = mean z := by
    intro z; unfold olsIntercept; rw [hcent, mul_zero, sub_zero]
  rw [hi, hi]
  have heq : mean yHat - mean y = (∑ k, (yHat k - y k)) / (Fintype.card ι) := by
    unfold mean; rw [← sub_div, ← Finset.sum_sub_distrib]
  rw [heq, abs_div, abs_of_pos hcard, div_le_iff₀ hcard]
  calc |∑ k, (yHat k - y k)|
      ≤ ∑ k, |yHat k - y k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : ι, eps := Finset.sum_le_sum (fun k _ => hδ k)
    _ = (Fintype.card ι) * eps := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = eps * (Fintype.card ι) := by ring

/-- **Uniform composition error bound.** Since `N s ≤ S = ∑ N`, the per-fraction bound
`CompositionRobustness.composition_abs_sub_le` simplifies to the uniform
`|ΔCₛ| ≤ (card κ + 1)·δ/Ŝ`, with `δ` the per-species absolute density error. -/
theorem composition_abs_sub_le_uniform {N Nhat : κ → ℝ} {delta : ℝ}
    (hN : ∀ s, 0 ≤ N s) (hS : 0 < totalDensity N) (hShat : 0 < totalDensity Nhat)
    (hdelta : ∀ s, |Nhat s - N s| ≤ delta) (s : κ) :
    |composition Nhat s - composition N s|
      ≤ ((Fintype.card κ : ℝ) + 1) * delta / totalDensity Nhat := by
  have hδ0 : 0 ≤ delta := le_trans (abs_nonneg _) (hdelta s)
  have hcard0 : (0 : ℝ) ≤ (Fintype.card κ : ℝ) := Nat.cast_nonneg _
  have hSŜ : 0 < totalDensity N * totalDensity Nhat := mul_pos hS hShat
  have hNsS : N s ≤ totalDensity N := Finset.single_le_sum (fun t _ => hN t) (Finset.mem_univ s)
  refine (composition_abs_sub_le hN hS hShat hdelta s).trans ?_
  have h2 : (N s / (totalDensity N * totalDensity Nhat)) * (Fintype.card κ : ℝ) * delta
      ≤ (Fintype.card κ : ℝ) * delta / totalDensity Nhat := by
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_div_iff₀ hSŜ hShat]
    nlinarith [mul_nonneg (sub_nonneg.mpr hNsS) (mul_nonneg (mul_nonneg hcard0 hδ0) hShat.le)]
  calc delta / totalDensity Nhat
        + (N s / (totalDensity N * totalDensity Nhat)) * (Fintype.card κ : ℝ) * delta
      ≤ delta / totalDensity Nhat + (Fintype.card κ : ℝ) * delta / totalDensity Nhat := by
        linarith [h2]
    _ = ((Fintype.card κ : ℝ) + 1) * delta / totalDensity Nhat := by ring

/-- **Composition accuracy ⇒ per-species density-error budget (the closure-leg inverse).** A
target composition accuracy `τ` is guaranteed once the uniform per-species density error meets
`(card κ + 1)·δ ≤ τ·Ŝ`. Chained with `relDensity_le` (intercept/SNR budget ⇒ `δ`) this closes
the loop from a composition target back to a measurement specification. -/
theorem composition_target_sufficient {N Nhat : κ → ℝ} {delta tauC : ℝ}
    (hN : ∀ s, 0 ≤ N s) (hS : 0 < totalDensity N) (hShat : 0 < totalDensity Nhat)
    (hdelta : ∀ s, |Nhat s - N s| ≤ delta)
    (hbudget : ((Fintype.card κ : ℝ) + 1) * delta ≤ tauC * totalDensity Nhat) (s : κ) :
    |composition Nhat s - composition N s| ≤ tauC := by
  refine (composition_abs_sub_le_uniform hN hS hShat hdelta s).trans ?_
  rw [div_le_iff₀ hShat]
  exact hbudget

end CflibsFormal
