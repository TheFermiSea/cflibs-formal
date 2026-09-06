/-
Copyright (c) 2026 Brian Squires. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Squires
-/
import Mathlib
import CflibsFormal.OLS
import CflibsFormal.ErrorBudget
import CflibsFormal.LineSelection

/-!
# CF-LIBS formalization — the condition number as an ERROR-AMPLIFICATION factor

`OLS.lean` already builds the conditioning object itself: `centeredDesignNormalMatrix_eq_diagonal`
exhibits the centered two-column Boltzmann design as `diagonal ![SS_E, n]`,
`boltzmannConditionNumber E = max(SS_E, n)/min(SS_E, n)` is its 2-norm condition number,
`boltzmannConditionNumber_ge_one` gives `κ ≥ 1`, and `centeredSolve_perturbation` /
`centeredSolve_relative_condition` give the textbook `‖Δx‖/‖x‖ ≤ κ·‖Δc‖/‖c‖` bound for a
perturbed *right-hand side* of the normal equations. What was **not** there is the join with the
measurement-noise chain of `ErrorBudget.lean`: `κ` never appeared in any bound whose input is a
per-line ordinate error `ε`, so the amplification factor was never composed into the noise budget
that the pipeline actually spends. This module supplies exactly that join.

## The headline: `√κ` bounds the slope-channel amplification

`olsSlope_error_le_sqrt_conditionNumber` — for **any** design with positive energy spread and
per-line ordinate errors bounded by `ε`,

  `|β̂(ŷ) − β̂(y)| ≤ ε · √(boltzmannConditionNumber E)`.

The proof composes `ErrorBudget.olsSlope_stable_l2` (`|Δβ| ≤ ε·√n/√SS_E`) with the elementary
inequality `n/SS_E ≤ κ` (`card_div_spread_le_conditionNumber`). The exponent is `1/2`, not `1` —
that is a bare algebraic fact about the constant `√n/√SS_E` already carried by
`olsSlope_stable_l2`, not a claim about which norm or channel "really" governs the solve; no
mechanism beyond that identification is asserted. On the spread-starved
branch `SS_E ≤ n` the inequality `n/SS_E ≤ κ` is an **equality**
(`boltzmannConditionNumber_eq_of_spread_le`), so there the `√κ` factor is not merely an upper
bound on the amplification — it *is* the `ℓ²` amplification constant of `olsSlope_stable_l2`.

Downstream: `olsFit_error_sq_le_conditionNumber` propagates a normal-equation perturbation into
the fitted pair `(slope, intercept)` with the factor `κ + 1` (slope channel `κ`, intercept channel
`1`), and `temp_rel_error_le_sqrt_conditionNumber` carries `√κ` into the relative temperature
error through the exact identity `ErrorBudget.temp_rel_error_eq`.

## Composition with the refusal threshold (no duplication)

The repo already refuses on small energy spread (`Certificates.energySpreadCert`,
`ErrorBudget.requiredEnergySpread_sufficient`). Here that gate is *re-read* as a condition-number
budget rather than being joined by a separate knob:
`conditionCeiling_of_requiredEnergySpread` turns the existing spread threshold `SS_E ≥ ε²·n/τ²`
into the explicit ceiling `κ ≤ (τ/ε)²`, and `conditionRoute_slope_target` walks the κ route back to
the very same conclusion `|Δβ| ≤ τ` that `requiredEnergySpread_sufficient` reaches directly.
Two honesty caveats on that sentence, both of which the individual docstrings repeat: the ceiling
is proved only in the direction spread-threshold ⟹ κ-ceiling (no `iff` is formalized), and the
chain needs the extra branch hypothesis `SS_E ≤ n` that `requiredEnergySpread_sufficient` does not
need. So `κ` is a (branch-conditional, one-directional) *reading* of the existing threshold, never
a new or stronger refusal criterion.

## Line selection

`conditionNumber_antitone_of_spread` is a *pairwise* comparison: for two candidate energy
assignments on the same index type (so `LineSelection`'s fixed line count `n`), on the
spread-starved branch, more spread means smaller `κ`. That the D-optimal candidate of
`LineSelection.exists_dOptimal_lineSet` is therefore also the minimum-`κ` candidate of a family
follows immediately, but is a corollary about argmax that is **not** stated as a theorem below.
`conditionNumber_disagrees_with_dOptimality` is the honest converse witness: off that branch the
two criteria genuinely diverge.

## Literature and scope

The condition-number/perturbation reading (`λ_min = min(SS_E, n)`, `λ_max = max(SS_E, n)`,
`κ = λ_max/λ_min`) is textbook numerical linear algebra — Golub & Van Loan, *Matrix Computations*,
§2.6 — not a LIBS-specific result; the diagonal exhibition it is applied to is
`OLS.centeredDesignNormalMatrix_eq_diagonal`. The measurement-noise chain it is composed with
(`olsSlope_stable_l2`, `temp_rel_error_eq/le`, `olsIntercept_stable_centered`) is the
least-squares Boltzmann-plot error budget of Tognoni et al. 2010; statements carrying that
Boltzmann-plot reading (slope = inverse temperature, ordinate = log-scaled line intensity) are
tagged REDUCED with that citation, and the purely algebraic `max/min` facts are tagged PURE-MATH.

## Honest limitations

* **`κ` here is the raw, unit-carrying ratio.** `SS_E` has units of energy², `n` is a bare count,
  so `boltzmannConditionNumber` is not scale-invariant — the caveat already recorded at
  `OLS.centeredScaledDesign_orthonormal` (M6), which proves the *scaled* centered design is
  orthonormal (`κ_scaled = 1`). Consequently "is real data on the branch `SS_E ≤ n`?" is a
  question about the chosen energy unit, not a unit-free physical fact, and nothing below claims
  otherwise. Every theorem here that needs the branch takes `SS_E ≤ n` as an explicit hypothesis;
  the headline `olsSlope_error_le_sqrt_conditionNumber` does not need it and is stated without it
  (at the price of being loose when `SS_E > n`).
* **Upper bounds, not attained.** `olsSlope_stable_l2` is a Cauchy–Schwarz bound (tight only when
  the ordinate errors are proportional to `Eₖ − Ē`), so `ε·√κ` is not claimed sharp. No statement
  below asserts attainment.
* **Deterministic worst case, not a variance.** As in `ErrorBudget.lean`, `ε` is a hard per-line
  error bound; these are not Gauss–Markov variance statements and `√κ` is not a standard
  deviation multiplier.
* **No new physics.** Nothing here is a new physical constant or a new refusal criterion; every
  physical hypothesis (positive spread, slope-to-temperature identification) is imported verbatim
  from `OLS.lean` / `ErrorBudget.lean`.
* **Two channels only.** The `(slope, intercept)` pair is the whole fitted parameter vector of the
  two-column design; the three-column joint Saha–Boltzmann design
  (`OLS.jointDesignNormalMatrix`) has no condition-number analysis here — only its rank/positivity
  criterion `OLS.jointDesign_det_pos_iff` exists.
-/

namespace CflibsFormal

open Finset Real
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-! ## The `max/min` algebra of `boltzmannConditionNumber` -/

/-- **Closed form on the spread-starved branch.** When the energy spread does not exceed the line
count, `SS_E ≤ n`, the condition number of the centered design is exactly `κ = n / SS_E`. Immediate
from `max_eq_right` / `min_eq_left` on the diagonal entries exhibited by
`OLS.centeredDesignNormalMatrix_eq_diagonal`. Pure `max/min` algebra; no physics content. -/
theorem boltzmannConditionNumber_eq_of_spread_le (E : ι → ℝ)
    (hle : (∑ k, (E k - mean E) ^ 2) ≤ (Fintype.card ι : ℝ)) :
    boltzmannConditionNumber E
      = (Fintype.card ι : ℝ) / (∑ k, (E k - mean E) ^ 2) := by
  unfold boltzmannConditionNumber
  rw [max_eq_right hle, min_eq_left hle]

/-- **`n / SS_E ≤ κ` unconditionally.** The ratio `n/SS_E` — the constant that actually appears in
the `ℓ²` noise bound `ErrorBudget.olsSlope_stable_l2` — never exceeds the condition number, for
*any* positive spread. On the branch `SS_E ≤ n` the two coincide
(`boltzmannConditionNumber_eq_of_spread_le`); on the branch `n < SS_E` the left side drops below
`1` while `κ ≥ 1`, so the inequality is strict and loose there. Pure `max/min` algebra. -/
theorem card_div_spread_le_conditionNumber [Nonempty ι] (E : ι → ℝ)
    (hvar : 0 < ∑ k, (E k - mean E) ^ 2) :
    (Fintype.card ι : ℝ) / (∑ k, (E k - mean E) ^ 2) ≤ boltzmannConditionNumber E := by
  have hcard : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  unfold boltzmannConditionNumber
  rcases le_total (∑ k, (E k - mean E) ^ 2) (Fintype.card ι : ℝ) with h | h
  · rw [max_eq_right h, min_eq_left h]
  · rw [max_eq_left h, min_eq_right h]
    have h1 : (Fintype.card ι : ℝ) / (∑ k, (E k - mean E) ^ 2) ≤ 1 :=
      (div_le_one hvar).mpr h
    have h2 : (1 : ℝ) ≤ (∑ k, (E k - mean E) ^ 2) / (Fintype.card ι : ℝ) := by
      rw [le_div_iff₀ hcard, one_mul]; exact h
    linarith

/-- **A spread floor is a condition-number ceiling.** If the design's spread is at least `SSmin`
(the runtime `min_energy_spread` knob, `Certificates.energySpreadCert` sharpened to a number) and
lies on the branch `SS_E ≤ n`, then `κ ≤ n / SSmin`. This is the sense in which the repo's
existing refusal threshold already *is* a conditioning gate rather than a separate criterion.
Pure `max/min` algebra. -/
theorem conditionNumber_le_of_spread_floor (E : ι → ℝ) {SSmin : ℝ}
    (hmin : 0 < SSmin) (hfloor : SSmin ≤ ∑ k, (E k - mean E) ^ 2)
    (hle : (∑ k, (E k - mean E) ^ 2) ≤ (Fintype.card ι : ℝ)) :
    boltzmannConditionNumber E ≤ (Fintype.card ι : ℝ) / SSmin := by
  have hcard : (0 : ℝ) ≤ (Fintype.card ι : ℝ) := Nat.cast_nonneg _
  rw [boltzmannConditionNumber_eq_of_spread_le E hle]
  exact div_le_div_of_nonneg_left hcard hmin hfloor

/-- **On the spread-starved branch, D-optimal = best-conditioned.** For two candidate line sets
`A`, `B` indexed by the *same* finite set (so the line count `n` is shared), if `A`'s spread is
positive and no larger than `B`'s, and `B` still sits on the branch `SS_B ≤ n`, then `B`'s
condition number is no larger than `A`'s. So `LineSelection`'s D-optimality objective (maximize
`energySpread`) and conditioning-optimality (minimize `κ`) rank candidates the same way *on that
branch* — see `conditionNumber_disagrees_with_dOptimality` for the honest failure off it. Pure
`max/min` algebra. -/
theorem conditionNumber_antitone_of_spread (A B : ι → ℝ)
    (hA : 0 < ∑ k, (A k - mean A) ^ 2)
    (hAB : (∑ k, (A k - mean A) ^ 2) ≤ ∑ k, (B k - mean B) ^ 2)
    (hB : (∑ k, (B k - mean B) ^ 2) ≤ (Fintype.card ι : ℝ)) :
    boltzmannConditionNumber B ≤ boltzmannConditionNumber A := by
  have hcard : (0 : ℝ) ≤ (Fintype.card ι : ℝ) := Nat.cast_nonneg _
  rw [boltzmannConditionNumber_eq_of_spread_le A (hAB.trans hB),
    boltzmannConditionNumber_eq_of_spread_le B hB]
  exact div_le_div_of_nonneg_left hcard hA hAB

/-- **Honest converse witness: off the branch the two criteria genuinely disagree.** Two-line
designs `A = (0, 2)` and `B = (0, 10)` on `ι = Fin 2` (so `n = 2`): `energySpread A = 2` and
`energySpread B = 50`, so D-optimality strictly prefers `B`; but `κ A = max(2,2)/min(2,2) = 1`
while `κ B = max(50,2)/min(50,2) = 25`, so conditioning strictly prefers `A`. Hence
`conditionNumber_antitone_of_spread`'s branch hypothesis `SS_B ≤ n` is load-bearing and cannot be
dropped, and "minimize `κ`" is NOT a drop-in replacement for the D-optimality objective. (The
disagreement is a unit artifact — `SS_E` is an energy² and `n` a count — exactly the caveat of
`OLS.centeredScaledDesign_orthonormal`.) Pure arithmetic. -/
theorem conditionNumber_disagrees_with_dOptimality :
    energySpread (ι := Fin 2) ![0, 2] < energySpread (ι := Fin 2) ![0, 10]
      ∧ boltzmannConditionNumber (ι := Fin 2) ![0, 10]
          > boltzmannConditionNumber (ι := Fin 2) ![0, 2] := by
  constructor
  · simp only [energySpread, mean, Fin.sum_univ_two, Fintype.card_fin]
    norm_num
  · simp only [boltzmannConditionNumber, mean, Fin.sum_univ_two, Fintype.card_fin]
    norm_num

/-! ## The payoff: `√κ` as the noise-to-slope amplification factor -/

/-- **HEADLINE (REDUCED).** Per-line ordinate errors bounded by `ε` on the Boltzmann plot
propagate to the fitted slope with amplification at most `√κ`:

  `|olsSlope E ŷ − olsSlope E y| ≤ ε · √(boltzmannConditionNumber E)`.

Composes `ErrorBudget.olsSlope_stable_l2` (`|Δβ| ≤ ε·√n/√SS_E`, Cauchy–Schwarz over the
Gauss–Markov weights) with `card_div_spread_le_conditionNumber` (`n/SS_E ≤ κ`). No branch
hypothesis is needed; on the spread-starved branch `SS_E ≤ n` the composition is an equality of
constants, so `√κ` is then exactly the `ℓ²` amplification factor. Physics reading: `olsSlope` is
the (sign-normalized) Boltzmann-plot slope `1/(k_B T)` and `ε` is the log-intensity measurement
budget, so this is the statement that ill-conditioning of the line-energy design — the
small-`SS_E` regime the pipeline already refuses on — amplifies the temperature error by `√κ`.
The bound is an upper bound only (Cauchy–Schwarz is not attained in general). -/
theorem olsSlope_error_le_sqrt_conditionNumber [Nonempty ι] {E y yHat : ι → ℝ} {eps : ℝ}
    (hvar : 0 < ∑ k, (E k - mean E) ^ 2)
    (hδ : ∀ k, |yHat k - y k| ≤ eps) :
    |olsSlope E yHat - olsSlope E y| ≤ eps * Real.sqrt (boltzmannConditionNumber E) := by
  have heps0 : 0 ≤ eps := (abs_nonneg _).trans (hδ (Classical.arbitrary ι))
  have hcardnn : (0 : ℝ) ≤ (Fintype.card ι : ℝ) := Nat.cast_nonneg _
  have hkey : Real.sqrt (Fintype.card ι : ℝ) / Real.sqrt (∑ k, (E k - mean E) ^ 2)
      ≤ Real.sqrt (boltzmannConditionNumber E) := by
    rw [← Real.sqrt_div hcardnn]
    exact Real.sqrt_le_sqrt (card_div_spread_le_conditionNumber E hvar)
  calc |olsSlope E yHat - olsSlope E y|
      ≤ eps * Real.sqrt (Fintype.card ι) / Real.sqrt (∑ k, (E k - mean E) ^ 2) :=
        olsSlope_stable_l2 hvar hδ
    _ = eps * (Real.sqrt (Fintype.card ι) / Real.sqrt (∑ k, (E k - mean E) ^ 2)) := by
        ring
    _ ≤ eps * Real.sqrt (boltzmannConditionNumber E) :=
        mul_le_mul_of_nonneg_left hkey heps0

/-- **The fitted parameter pair (REDUCED).** In the standard centered Boltzmann-plot
normalization `mean E = 0` — the convention under which the design normal matrix is
`diagonal ![SS_E, n]` — an ordinate perturbation of size `ε` moves the whole fitted pair
`(slope, intercept)` by at most `ε²·(κ + 1)` in squared 2-norm:

  `(Δβ)² + (Δb)² ≤ ε²·(boltzmannConditionNumber E + 1)`.

The two summands are the two diagonal channels: the slope channel contributes `κ`
(`olsSlope_error_le_sqrt_conditionNumber`) and the intercept channel contributes `1`
(`ErrorBudget.olsIntercept_stable_centered`, whose gain is `1` per unit ordinate error). This is
the perturbation-to-solution statement the conditioning analysis was for: a perturbation of the
observed ordinates — hence of the normal-equation right-hand side — propagates to the fitted
`(slope, intercept)` with a factor controlled by the condition number. Squared form throughout,
so no square roots enter the statement. -/
theorem olsFit_error_sq_le_conditionNumber [Nonempty ι] {E y yHat : ι → ℝ} {eps : ℝ}
    (hvar : 0 < ∑ k, (E k - mean E) ^ 2) (hcent : mean E = 0)
    (hδ : ∀ k, |yHat k - y k| ≤ eps) :
    (olsSlope E yHat - olsSlope E y) ^ 2 + (olsIntercept E yHat - olsIntercept E y) ^ 2
      ≤ eps ^ 2 * (boltzmannConditionNumber E + 1) := by
  have hκ0 : 0 ≤ boltzmannConditionNumber E :=
    le_trans zero_le_one (boltzmannConditionNumber_ge_one E hvar)
  have h1 := olsSlope_error_le_sqrt_conditionNumber hvar hδ
  have h2 := olsIntercept_stable_centered hcent hδ
  have hs1 : (olsSlope E yHat - olsSlope E y) ^ 2
      ≤ eps ^ 2 * boltzmannConditionNumber E := by
    have hp := pow_le_pow_left₀ (abs_nonneg (olsSlope E yHat - olsSlope E y)) h1 2
    rwa [sq_abs, mul_pow, Real.sq_sqrt hκ0] at hp
  have hs2 : (olsIntercept E yHat - olsIntercept E y) ^ 2 ≤ eps ^ 2 := by
    have hp := pow_le_pow_left₀ (abs_nonneg (olsIntercept E yHat - olsIntercept E y)) h2 2
    rwa [sq_abs] at hp
  nlinarith [hs1, hs2]

/-- **Temperature channel (REDUCED).** Under the Boltzmann-plot identification of the fitted slope
with the inverse temperature (`olsSlope E y = 1/(k_B T)`, `olsSlope E ŷ = 1/(k_B T̂)` — the
sign-normalized slope; the physical slope is `−1/(k_B T)`, immaterial since only `|·|` enters, the
same convention as `ErrorBudget.temp_rel_error_hetero`), the `√κ` amplification carries through the
*exact* identity `ErrorBudget.temp_rel_error_eq` to the relative temperature error:

  `|T̂ − T|/T ≤ k_B · T̂ · ε · √(boltzmannConditionNumber E)`.

So a condition-number budget on the line-energy design is directly a temperature-accuracy budget.
No linearization is used: the only inequality is the slope bound. -/
theorem temp_rel_error_le_sqrt_conditionNumber [Nonempty ι] {E y yHat : ι → ℝ}
    {eps kB T THat : ℝ}
    (hkB : 0 < kB) (hT : 0 < T) (hTHat : 0 < THat)
    (hvar : 0 < ∑ k, (E k - mean E) ^ 2)
    (hδ : ∀ k, |yHat k - y k| ≤ eps)
    (hβ : olsSlope E y = 1 / (kB * T))
    (hβHat : olsSlope E yHat = 1 / (kB * THat)) :
    |THat - T| / T ≤ kB * THat * (eps * Real.sqrt (boltzmannConditionNumber E)) := by
  have hslope := olsSlope_error_le_sqrt_conditionNumber hvar hδ
  rw [hβHat, hβ] at hslope
  exact temp_rel_error_le hkB hT hTHat hslope

/-! ## Composition with the existing refusal threshold -/

/-- **The existing spread threshold IS a condition-number ceiling.**
`ErrorBudget.requiredEnergySpread_sufficient` refuses unless `SS_E ≥ ε²·n/τ²` (the derived
`min_energy_spread` knob for a target inverse-temperature accuracy `τ`). On the branch
`SS_E ≤ n`, that very hypothesis *implies* the explicit condition-number ceiling

  `boltzmannConditionNumber E ≤ (τ/ε)²`.

So the pipeline's spread gate is at least as strong as a `κ` gate, read in two units — no new knob
is introduced. **Only this direction is formalized.** The converse also holds on the branch (there
`κ = n/SS_E` by `boltzmannConditionNumber_eq_of_spread_le`, and the two inequalities are then the
same inequality divided through), but no `iff` is proved below, so do not read the name or this
docstring as asserting a formalized equivalence. Pure algebra of `max/min` and division. -/
theorem conditionCeiling_of_requiredEnergySpread (E : ι → ℝ) {eps tauBeta : ℝ}
    (heps : 0 < eps) (htau : 0 < tauBeta) [Nonempty ι]
    (hle : (∑ k, (E k - mean E) ^ 2) ≤ (Fintype.card ι : ℝ))
    (hSS : eps ^ 2 * (Fintype.card ι) / tauBeta ^ 2 ≤ ∑ k, (E k - mean E) ^ 2) :
    boltzmannConditionNumber E ≤ tauBeta ^ 2 / eps ^ 2 := by
  have hcard : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hlow : 0 < eps ^ 2 * (Fintype.card ι : ℝ) / tauBeta ^ 2 := by positivity
  have hstep : (Fintype.card ι : ℝ) / (∑ k, (E k - mean E) ^ 2)
      ≤ (Fintype.card ι : ℝ) / (eps ^ 2 * (Fintype.card ι : ℝ) / tauBeta ^ 2) :=
    div_le_div_of_nonneg_left hcard.le hlow hSS
  have hval : (Fintype.card ι : ℝ) / (eps ^ 2 * (Fintype.card ι : ℝ) / tauBeta ^ 2)
      = tauBeta ^ 2 / eps ^ 2 := by
    field_simp
  rw [boltzmannConditionNumber_eq_of_spread_le E hle, ← hval]
  exact hstep

/-- **The `κ` route reaches the same conclusion (REDUCED).** From a condition-number ceiling
`κ ≤ (τ/ε)²` and per-line ordinate errors bounded by `ε`, the slope error obeys the target:
`|Δβ| ≤ τ`. This statement itself needs no branch hypothesis. Chaining
`conditionCeiling_of_requiredEnergySpread` into it recovers
`ErrorBudget.requiredEnergySpread_sufficient`'s conclusion from that theorem's own hypothesis
**plus the branch hypothesis `SS_E ≤ n`**, which `requiredEnergySpread_sufficient` does not need —
so the κ route is the weaker route, and the agreement of the two is branch-conditional. That
agreement is why `κ` is offered here as a *reading* of the existing refusal threshold rather than
as a competing criterion; it is not a claim that the κ route subsumes the direct one. -/
theorem conditionRoute_slope_target [Nonempty ι] {E y yHat : ι → ℝ} {eps tauBeta : ℝ}
    (heps : 0 < eps) (htau : 0 < tauBeta)
    (hvar : 0 < ∑ k, (E k - mean E) ^ 2)
    (hδ : ∀ k, |yHat k - y k| ≤ eps)
    (hκ : boltzmannConditionNumber E ≤ tauBeta ^ 2 / eps ^ 2) :
    |olsSlope E yHat - olsSlope E y| ≤ tauBeta := by
  have hsq : Real.sqrt (boltzmannConditionNumber E) ≤ tauBeta / eps := by
    have h := Real.sqrt_le_sqrt hκ
    rwa [Real.sqrt_div (sq_nonneg tauBeta), Real.sqrt_sq htau.le, Real.sqrt_sq heps.le] at h
  calc |olsSlope E yHat - olsSlope E y|
      ≤ eps * Real.sqrt (boltzmannConditionNumber E) :=
        olsSlope_error_le_sqrt_conditionNumber hvar hδ
    _ ≤ eps * (tauBeta / eps) := mul_le_mul_of_nonneg_left hsq heps.le
    _ = tauBeta := by field_simp

/-! ## Non-vacuity witnesses on explicit two-line data -/

/-- Two lines at upper-level energies `E = (0, 1)`: `mean E = 1/2`, `SS_E = 1/2`, `n = 2`. -/
private def nvCondE : Fin 2 → ℝ := ![0, 1]

/-- Noiseless reference ordinates (a flat Boltzmann plot, true slope `0`). -/
private def nvCondY : Fin 2 → ℝ := ![0, 0]

/-- Measured ordinates: line `0` exact, line `1` off by `ε = 1/10`. -/
private noncomputable def nvCondYhat : Fin 2 → ℝ := ![0, 1 / 10]

/-- **Non-vacuity part 1: the condition number is a concrete number `> 1`.** For `E = (0, 1)`,
`SS_E = 1/2 ≤ 2 = n`, so the design is on the spread-starved branch and
`κ = n/SS_E = 2/(1/2) = 4`. The amplification factor `√κ = 2` is therefore a genuine
amplification (not the trivial `κ = 1` of a perfectly conditioned design), so every `κ`-bound
below is exercised non-trivially. -/
theorem nonvacuity_conditionNumber_value :
    boltzmannConditionNumber nvCondE = 4 := by
  simp only [boltzmannConditionNumber, nvCondE, mean, Fin.sum_univ_two, Fintype.card_fin]
  norm_num

/-- **Non-vacuity part 2: both sides of the headline bound are nonzero and distinct.** On
`E = (0, 1)`, `y = (0, 0)`, `ŷ = (0, 1/10)` the measured slope is `1/10` and the true slope is
`0`, so the left-hand side of `olsSlope_error_le_sqrt_conditionNumber` is `1/10`; the right-hand
side is `ε·√κ = (1/10)·2 = 1/5`. Neither side collapses to `0`, and they are not equal, so the
theorem's conclusion is a genuine strict inequality `1/10 ≤ 1/5` on real data. -/
theorem nonvacuity_slope_error_values :
    |olsSlope nvCondE nvCondYhat - olsSlope nvCondE nvCondY| = 1 / 10
      ∧ (1 / 10 : ℝ) * Real.sqrt (boltzmannConditionNumber nvCondE) = 1 / 5 := by
  constructor
  · simp only [olsSlope, nvCondE, nvCondY, nvCondYhat, mean, Fin.sum_univ_two,
      Fintype.card_fin]
    norm_num
  · rw [nonvacuity_conditionNumber_value,
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num

/-- **Non-vacuity part 3: the headline theorem fires on this data.** Instantiating
`olsSlope_error_le_sqrt_conditionNumber` at `E = (0, 1)`, `y = (0, 0)`, `ŷ = (0, 1/10)` with
`ε = 1/10` (the per-line budget is met with equality on line `1` and slack on line `0`) yields the
concrete true inequality `1/10 ≤ 1/5`. -/
theorem nonvacuity_slope_error_fires :
    |olsSlope nvCondE nvCondYhat - olsSlope nvCondE nvCondY| ≤ 1 / 5 := by
  have hvar : 0 < ∑ k, (nvCondE k - mean nvCondE) ^ 2 := by
    simp only [nvCondE, mean, Fin.sum_univ_two, Fintype.card_fin]
    norm_num
  have hδ : ∀ k, |nvCondYhat k - nvCondY k| ≤ 1 / 10 := by
    intro k
    fin_cases k <;> simp only [nvCondY, nvCondYhat] <;> norm_num
  have h := olsSlope_error_le_sqrt_conditionNumber (eps := 1 / 10) hvar hδ
  rw [(nonvacuity_slope_error_values).2] at h
  exact h

/-- Two lines at *centered* upper-level energies `E = (−1/2, 1/2)`. Shifting `nvCondE` by its own
mean leaves `SS_E = 1/2` and `n = 2` (both are shift-invariant), so `κ = 4` is unchanged, but now
`mean E = 0` — which is the extra hypothesis `hcent` of `olsFit_error_sq_le_conditionNumber`. -/
private noncomputable def nvFitE : Fin 2 → ℝ := ![-(1 / 2), 1 / 2]

/-- **Non-vacuity for the fitted-pair bound: the hypotheses are jointly satisfiable and both
channels are live.** `olsFit_error_sq_le_conditionNumber` carries two hypotheses that could in
principle conflict — `0 < SS_E` and `mean E = 0`. They do not: on `E = (−1/2, 1/2)` we have
`mean E = 0` *and* `κ = 4`, i.e. the centering normalization costs no conditioning at all (both
`SS_E` and `n` are shift-invariant). With `y = (0, 0)` and `ŷ = (0, 1/10)` the slope moves by
`1/10` and the intercept by `1/20`, so the theorem's left-hand side is
`(1/10)² + (1/20)² = 1/80` — **neither** channel contributes zero, and the two contributions are
not equal, so the `κ`-channel and the `1`-channel are separately exercised. -/
theorem nonvacuity_fit_error_values :
    mean nvFitE = 0 ∧ boltzmannConditionNumber nvFitE = 4
      ∧ (olsSlope nvFitE nvCondYhat - olsSlope nvFitE nvCondY) ^ 2
          + (olsIntercept nvFitE nvCondYhat - olsIntercept nvFitE nvCondY) ^ 2 = 1 / 80 := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [mean, nvFitE, Fin.sum_univ_two, Fintype.card_fin]
    norm_num
  · simp only [boltzmannConditionNumber, mean, nvFitE, Fin.sum_univ_two, Fintype.card_fin]
    norm_num
  · simp only [olsIntercept, olsSlope, mean, nvFitE, nvCondY, nvCondYhat, Fin.sum_univ_two,
      Fintype.card_fin]
    norm_num

/-- **Non-vacuity part 4: the fitted-pair theorem fires on this data.** Instantiating
`olsFit_error_sq_le_conditionNumber` at `E = (−1/2, 1/2)`, `y = (0, 0)`, `ŷ = (0, 1/10)` with
`ε = 1/10` gives the concrete true inequality `1/80 ≤ (1/10)²·(4 + 1) = 1/20`
(`nonvacuity_fit_error_values` supplies both numbers). The gap is a factor `4`, so the bound is
neither vacuous nor attained here — consistent with the module's disclaimer that
Cauchy–Schwarz is not claimed sharp. -/
theorem nonvacuity_fit_error_fires :
    (olsSlope nvFitE nvCondYhat - olsSlope nvFitE nvCondY) ^ 2
      + (olsIntercept nvFitE nvCondYhat - olsIntercept nvFitE nvCondY) ^ 2
      ≤ (1 / 10 : ℝ) ^ 2 * (boltzmannConditionNumber nvFitE + 1) := by
  have hvar : 0 < ∑ k, (nvFitE k - mean nvFitE) ^ 2 := by
    simp only [nvFitE, mean, Fin.sum_univ_two, Fintype.card_fin]
    norm_num
  have hδ : ∀ k, |nvCondYhat k - nvCondY k| ≤ 1 / 10 := by
    intro k
    fin_cases k <;> simp only [nvCondY, nvCondYhat] <;> norm_num
  exact olsFit_error_sq_le_conditionNumber (eps := 1 / 10) hvar
    (nonvacuity_fit_error_values).1 hδ

end CflibsFormal
