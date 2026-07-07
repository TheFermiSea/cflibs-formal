/-
Copyright (c) 2026 Brian Squires. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Squires
-/
import Mathlib
import CflibsFormal.CompositionRobustness
import CflibsFormal.Analysis
import CflibsFormal.OLS

/-!
# CF-LIBS formalization — the error-propagation chain and DERIVED reliability thresholds

A numerical CF-LIBS pipeline guards its inversion with empirical "magic-number" thresholds
— a minimum number of lines per element, a minimum upper-level energy spread, a minimum SNR.
This module turns those thresholds into **proven corollaries of a single deterministic
error-propagation chain**, so they follow *from a target accuracy* rather than being tuned.

The chain is the multi-line generalization of `Robustness.twoLineBeta_stable` (which bounds the
TWO-line slope) to the full ordinary-least-squares Boltzmann-plot slope `olsSlope` over
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
the OLS slope's noise gain `∑ wₖ² = 1/SS_E` — is proven in `OLS` as `olsSlope_noise_gain`; the
probabilistic `Var` layer is now formalized in `Alt.OLSVariance`
(`olsSlope_variance_eq : Var(β̂) = σ²/SS_E`, on `Mathlib`'s probability stack), and we still do
**not** claim a deterministic min-line-count bound the worst case cannot support.
See `oracle/Generate.lean` for the Float mirrors the numerical pipeline consumes.

Modeling assumptions (all explicit, inherited from the forward map): LTE single-temperature
populations, optically-thin emission (`lineIntensity`), a shared calibration `Fcal`, and known
partition functions `U_s(T)`. `mean` / `olsSlope` are reused verbatim from `OLS`.

Scope of the chain: the temperature channel (Tasks 1–2) and the density/concentration channel
(Task 3) are bounded **independently** — the latter (`relDensity_le`) treats `U` and `Fcal` as
exactly known and confines the perturbation to the intercept `b`. We do **not** prove a single
closed end-to-end `ε ⇒ composition` bound that feeds the recovered temperature error back into
`U(T̂)`; the two channels are reliability budgets to be combined by the caller, not composed here.
-/

namespace CflibsFormal

open Finset Real
open scoped BigOperators

variable {ι : Type*} [Fintype ι]
variable {κ : Type*} [Fintype κ]

/-! ## Task 1 — N-line least-squares slope sensitivity (generalizes `twoLineBeta_stable`) -/

/-- **N-line slope sensitivity (ℓ¹ worst-case bound).** If every ordinate is perturbed by at
most `ε` then the OLS slope changes by at most `ε·(∑ₖ |Eₖ − Ē|)/SS_E`. This is the multi-line
generalization of `Robustness.twoLineBeta_stable`; the bound's worst case — all ordinate errors
aligned in sign with `Eₖ − Ē` — saturates it (the attainment is not separately formalized here,
unlike `Robustness.twoLineBeta_stable_sharp`). `hvar : 0 < SS_E` (at least two distinct energies)
is load-bearing for the nonzero denominator. -/
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
of `olsSlope_stable_l2_sq` — the root form of the deterministic worst-case bound. (The textbook
`σ_β = σ_y/√SS_E` is the *statistical* Gauss–Markov law; this is the deterministic `ε·√N/√SS_E`
worst case — see the module docstring on the deterministic-vs-statistical distinction.) -/
theorem olsSlope_stable_l2 [Nonempty ι] {E y yHat : ι → ℝ} {eps : ℝ}
    (hvar : 0 < ∑ k, (E k - mean E) ^ 2)
    (hδ : ∀ k, |yHat k - y k| ≤ eps) :
    |olsSlope E yHat - olsSlope E y|
      ≤ eps * Real.sqrt (Fintype.card ι) / Real.sqrt (∑ k, (E k - mean E) ^ 2) := by
  have heps0 : 0 ≤ eps := (abs_nonneg _).trans (hδ (Classical.arbitrary ι))
  have hsq := olsSlope_stable_l2_sq hvar hδ
  calc |olsSlope E yHat - olsSlope E y|
      = Real.sqrt ((olsSlope E yHat - olsSlope E y) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (eps ^ 2 * (Fintype.card ι) / (∑ k, (E k - mean E) ^ 2)) :=
        Real.sqrt_le_sqrt hsq
    _ = eps * Real.sqrt (Fintype.card ι) / Real.sqrt (∑ k, (E k - mean E) ^ 2) := by
        rw [Real.sqrt_div (by positivity), Real.sqrt_mul (by positivity), Real.sqrt_sq heps0]

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

/-! ## Task 5 — heteroscedastic (per-line) noise ⇒ slope ⇒ temperature (gap #5)

Tasks 1–4 above carry a SINGLE GLOBAL per-line error `ε` through the chain. Real LIBS spectra are
**heteroscedastic**: strong and weak lines have different SNRs, so each line `k` carries its own
error budget `εₖ`. This section lifts the ℓ¹ slope-sensitivity and its temperature composition to
a per-line budget `ε : ι → ℝ`, and records what of the full `ε ⇒ composition` closure remains
OPEN. -/

/-- **N-line slope sensitivity, HETEROSCEDASTIC (per-line ℓ¹ bound).** The single global per-line
error `ε` of `olsSlope_stable_l1` is replaced by a per-line budget `εₖ` (a function `ε : ι → ℝ`,
one bound per line): if `|ŷₖ − yₖ| ≤ εₖ` for every line then `|Δβ| ≤ (∑ₖ |Eₖ − Ē|·εₖ)/SS_E`. Same
one-line derivation as the homoscedastic bound (`olsSlope_sub_eq` + `Finset.abs_sum_le_sum_abs` +
`abs_mul` + sum monotonicity), but each summand keeps its own `εₖ` rather than a common factor.
This is the natural object when different lines have different SNRs — the realistic regime, where a
single-`ε` bound must pessimistically use the worst line. `hvar : 0 < SS_E` (at least two distinct
energies) is load-bearing for the nonzero denominator. -/
theorem olsSlope_stable_hetero [Nonempty ι] {E y yHat eps : ι → ℝ}
    (hvar : 0 < ∑ k, (E k - mean E) ^ 2)
    (hδ : ∀ k, |yHat k - y k| ≤ eps k) :
    |olsSlope E yHat - olsSlope E y|
      ≤ (∑ k, |E k - mean E| * eps k) / (∑ k, (E k - mean E) ^ 2) := by
  rw [olsSlope_sub_eq, abs_div, abs_of_pos hvar]
  gcongr
  calc |∑ k, (E k - mean E) * (yHat k - y k)|
      ≤ ∑ k, |(E k - mean E) * (yHat k - y k)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k, |E k - mean E| * |yHat k - y k| := by simp_rw [abs_mul]
    _ ≤ ∑ k, |E k - mean E| * eps k := by
        refine Finset.sum_le_sum (fun k _ => ?_)
        exact mul_le_mul_of_nonneg_left (hδ k) (abs_nonneg _)

/-- **The heteroscedastic bound strictly generalizes `olsSlope_stable_l1`.** Feeding the constant
budget `εₖ := ε` into `olsSlope_stable_hetero` recovers the homoscedastic ℓ¹ bound
`|Δβ| ≤ ε·(∑ₖ |Eₖ − Ē|)/SS_E` verbatim: the per-line sum `∑ₖ |Eₖ − Ē|·ε` factors as
`ε·∑ₖ |Eₖ − Ē|`. So the single-`ε` chain of Tasks 1–4 is exactly the special case `εₖ ≡ ε`, and
`olsSlope_stable_hetero` is a genuine generalization (it can, e.g., exploit `εₖ = 0` on a noiseless
line, which no global-`ε` bound can). -/
theorem olsSlope_stable_l1_of_hetero [Nonempty ι] {E y yHat : ι → ℝ} {eps : ℝ}
    (hvar : 0 < ∑ k, (E k - mean E) ^ 2)
    (hδ : ∀ k, |yHat k - y k| ≤ eps) :
    |olsSlope E yHat - olsSlope E y|
      ≤ eps * (∑ k, |E k - mean E|) / (∑ k, (E k - mean E) ^ 2) := by
  refine (olsSlope_stable_hetero (eps := fun _ => eps) hvar hδ).trans (le_of_eq ?_)
  rw [← Finset.sum_mul]; ring

/-- **Composed heteroscedastic noise ⇒ relative temperature error (gap #5, temperature leg).** A
genuine composition of two existing links: the heteroscedastic slope bound `olsSlope_stable_hetero`
feeds the exact temperature identity `temp_rel_error_le`. Under the Boltzmann-plot identification of
the fitted slope with the inverse temperature (`olsSlope E y = 1/(k_B T)`,
`olsSlope E ŷ = 1/(k_B T̂)` — the sign-normalized slope; the physical Boltzmann slope is
`−1/(k_B T)`, immaterial here as only `|·|` enters), per-line ordinate budgets `εₖ` propagate to
`|T̂ − T|/T ≤ k_B·T̂·(∑ₖ |Eₖ − Ē|·εₖ)/SS_E`. REDUCED: this closes the noise ⇒ temperature leg with a
per-line budget; the density/composition leg is separate (see the OPEN note below). -/
theorem temp_rel_error_hetero [Nonempty ι] {E y yHat eps : ι → ℝ} {kB T THat : ℝ}
    (hkB : 0 < kB) (hT : 0 < T) (hTHat : 0 < THat)
    (hvar : 0 < ∑ k, (E k - mean E) ^ 2)
    (hδ : ∀ k, |yHat k - y k| ≤ eps k)
    (hβ : olsSlope E y = 1 / (kB * T))
    (hβHat : olsSlope E yHat = 1 / (kB * THat)) :
    |THat - T| / T
      ≤ kB * THat * ((∑ k, |E k - mean E| * eps k) / (∑ k, (E k - mean E) ^ 2)) := by
  have hslope := olsSlope_stable_hetero hvar hδ
  rw [hβHat, hβ] at hslope
  exact temp_rel_error_le hkB hT hTHat hslope

/-! ### What of gap #5 remains OPEN (honest scope)

`temp_rel_error_hetero` closes the **noise ⇒ temperature** leg with a per-line budget, and the
existing `relDensity_le` → `composition_target_sufficient` chain closes the **intercept ⇒ density ⇒
composition** leg. What is **not** yet a single closed `ε ⇒ ΔC` bound:

* **The `U_s(T)` Lipschitz leg.** A recovered-temperature error `|ΔT|` perturbs the partition
  functions `U_s(T̂)`, hence the intercept-to-density map `N = exp(b)·U/Fcal`. We have no
  `|U_s(T̂) − U_s(T)| ≤ L·|ΔT|` (partition-function Lipschitz) lemma, so the temperature error is
  not yet propagated **into** the density channel; `relDensity_le` treats `U` as exactly known.
* **The final `δ ⇒ ΔC` composition.** `composition_target_sufficient` (and
  `CompositionRobustness.composition_abs_sub_le`) take the per-species density error `δ` as a
  HYPOTHESIS. A fully closed end-to-end bound must feed the recovered-`T` error through `U_s(T̂)`
  and the intercept into `δ`, then into `ΔC`. That cross-channel coupling — temperature error
  re-entering the density channel — is future work; here the two channels remain independent
  reliability budgets to be combined by the caller. -/

/-- **Non-vacuity witness for `olsSlope_stable_hetero`.** Two lines at energies `E = (0, 1)`
(so `SS_E = 1/2 > 0`, satisfying `hvar`), true ordinates `y = (0, 0)`, measured `ŷ = (0, 1)`, with a
genuinely PER-LINE budget `ε = (0, 1)`: line 0 noiseless (`ε₀ = 0`), line 1 at `ε₁ = 1`. The
hypotheses are jointly satisfiable with a heteroscedastic budget a homoscedastic single-`ε` bound
could not use (it would need `ε ≥ 1` on the noiseless line 0). -/
private def nvHetE : Fin 2 → ℝ := ![0, 1]
private def nvHetY : Fin 2 → ℝ := ![0, 0]
private def nvHetYhat : Fin 2 → ℝ := ![0, 1]
private def nvHetEps : Fin 2 → ℝ := ![0, 1]

example :
    |olsSlope nvHetE nvHetYhat - olsSlope nvHetE nvHetY|
      ≤ (∑ k, |nvHetE k - mean nvHetE| * nvHetEps k) / (∑ k, (nvHetE k - mean nvHetE) ^ 2) :=
  olsSlope_stable_hetero
    (by simp only [nvHetE, mean, Fin.sum_univ_two]; norm_num)
    (by intro k; fin_cases k <;> simp [nvHetY, nvHetYhat, nvHetEps])

/-! ### Heteroscedastic intercept sensitivity (Frontier 05, Phase 1) -/
/-- **Intercept sensitivity, HETEROSCEDASTIC (per-line budget, centered convention).** The
per-line-budget mirror of `olsIntercept_stable_centered`: with energies referenced to their mean
(`mean E = 0`) and a per-line ordinate-error budget `εₖ` (rather than one global `ε`), the OLS
intercept error is bounded by the average of the per-line budgets: `|b̂ - b| ≤ (∑ₖ εₖ) / card ι`.
Same proof shape as `olsSlope_stable_hetero` — the per-line `εₖ` survives the final
`Finset.sum_le_sum` unfactored, rather than being pulled out as a common constant. This is the
missing intercept twin of `olsSlope_stable_hetero` referenced in the frontier-05 dossier. -/
theorem olsIntercept_stable_hetero [Nonempty ι] {E y yHat eps : ι → ℝ}
    (hcent : mean E = 0) (hδ : ∀ k, |yHat k - y k| ≤ eps k) :
    |olsIntercept E yHat - olsIntercept E y| ≤ (∑ k, eps k) / (Fintype.card ι) := by
  have hcard : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hi : ∀ z : ι → ℝ, olsIntercept E z = mean z := by
    intro z; unfold olsIntercept; rw [hcent, mul_zero, sub_zero]
  rw [hi, hi]
  have heq : mean yHat - mean y = (∑ k, (yHat k - y k)) / (Fintype.card ι) := by
    unfold mean; rw [← sub_div, ← Finset.sum_sub_distrib]
  rw [heq, abs_div, abs_of_pos hcard, div_le_div_iff_of_pos_right hcard]
  calc |∑ k, (yHat k - y k)|
      ≤ ∑ k, |yHat k - y k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k, eps k := Finset.sum_le_sum (fun k _ => hδ k)

/-- **Non-vacuity witness for `olsIntercept_stable_hetero`.** Two lines at energies `E = (-1, 1)`
(centered: `mean E = 0`), true ordinates `y = (0, 0)`, measured `ŷ = (0, 2)`, with a genuinely
PER-LINE budget `ε = (0, 2)`: line 0 noiseless (`ε₀ = 0`), line 1 at `ε₁ = 2`. The hypotheses are
jointly satisfiable with a heteroscedastic budget a homoscedastic single-`ε` bound could not use
(it would need `ε ≥ 2` on the noiseless line 0). -/
private def nvHetIE : Fin 2 → ℝ := ![-1, 1]
private def nvHetIY : Fin 2 → ℝ := ![0, 0]
private def nvHetIYhat : Fin 2 → ℝ := ![0, 2]
private def nvHetIEps : Fin 2 → ℝ := ![0, 2]

example :
    |olsIntercept nvHetIE nvHetIYhat - olsIntercept nvHetIE nvHetIY|
      ≤ (∑ k, nvHetIEps k) / (Fintype.card (Fin 2)) :=
  olsIntercept_stable_hetero
    (by simp only [nvHetIE, mean, Fin.sum_univ_two]; norm_num)
    (by intro k; fin_cases k <;> simp [nvHetIY, nvHetIYhat, nvHetIEps])

end CflibsFormal
