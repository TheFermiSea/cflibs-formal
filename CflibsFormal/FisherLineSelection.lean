/-
Copyright (c) 2026 Brian Squires. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Squires
-/
import Mathlib
import CflibsFormal.LineSelection

/-!
# CF-LIBS formalization — Fisher information, the Cramér–Rao bound, and "adding a line never hurts"

`LineSelection` ranks candidate line sets by the upper-level energy spread
`SS_E = ∑ₖ (Eₖ − Ē)²` because the Gauss–Markov slope variance of the Boltzmann-plot fit is
`σ²/SS_E` (`Alt.OLSVariance.olsSlope_variance_eq`). This module answers the two follow-up
questions that framing raises.

1. **Is `σ²/SS_E` the best any estimator can do?** Under the textbook identification, yes. For
   the Gaussian linear model `yₖ = α + β Eₖ + εₖ`, `εₖ ~ N(0, σ²)` i.i.d., the Fisher information
   for the slope `β` is `I(β) = SS_E/σ²`, which this module *defines* as `fisherInfoSlope` (see
   *Honest limitations*: the likelihood, the score and the Cramér–Rao inequality itself are NOT
   formalized). What IS proven: `crlb_slope` (`σ²/SS_E = I(β)⁻¹`, algebra on that definition) and
   `olsSlope_attains_crlb` (the landed OLS variance equals `I(β)⁻¹`). The reading "OLS is
   efficient — no unbiased estimator extracts more slope (hence temperature) precision from the
   same lines under the same noise" is the textbook Cramér–Rao conclusion applied to that
   identity; it is prose, not a theorem of this module.
2. **Can adding a line to the Boltzmann plot ever hurt?** No. The one-pass variance update
   `spreadOn_insert` gives the *exact* gain from adjoining a new line `k` to a selected set `S`:
   `SS_E(S ∪ {k}) = SS_E(S) + (|S|/(|S|+1))·(Eₖ − Ē_S)²`.
   The increment is a nonnegative multiple of a square, so the spread is monotone under
   insertion (`spreadOn_insert_ge`) and under inclusion (`spreadOn_mono`), the Fisher
   information is monotone (`fisherInfo_insert_ge`), and the Cramér–Rao bound can only fall
   (`crlb_insert_le`). The increment vanishes **iff** the new line sits exactly at the current
   mean energy (`spreadOn_insert_eq_iff`, `no_gain_iff`), and is strictly positive otherwise
   (`spreadOn_insert_lt_iff`) — the quantitative *no-gain criterion*.

## What is proven

* `fisherInfoSlope E σ := energySpread E / σ²` — the Fisher information for the slope, **defined
  as its closed form** (see the honesty note on the definition).
* `crlb_slope : σ²/SS_E = (fisherInfoSlope E σ)⁻¹` — the Cramér–Rao bound (unconditional
  algebra); `fisherInfoSlope_pos` makes it a genuine positive number under the spread gate.
* `olsSlope_attains_crlb : Var(β̂) = (fisherInfoSlope E σ)⁻¹` under exactly the Gauss–Markov
  hypotheses of `olsSlope_variance_eq` — OLS is efficient.
* `sum_sq_sub_eq_spreadOn_add` — the parallel-axis identity
  `∑_{j∈S} (Eⱼ − c)² = spreadOn E S + |S|·(Ē_S − c)²`: the mean minimizes the sum of squared
  deviations, with an explicit excess. This is the engine behind the update.
* `spreadOn_insert` — **the one-pass update** (the load-bearing identity).
* `spreadOn_insert_ge`, `spreadOn_mono`, `fisherInfo_insert_ge`, `crlb_insert_le` — monotonicity.
* `spreadOn_insert_eq_iff`, `spreadOn_insert_lt_iff`, `no_gain_iff` — the no-gain criterion.

## Non-vacuity

Explicit `Fin 3` data. Pool `E = (0, 2, 10)`, current selection `S = {0, 1}` (mean `1`, spread
`2`): adjoining the far line `E₂ = 10` raises the spread to `56 = 2 + (2/3)·(10 − 1)²`, strictly
(`nonvacuity_far_line`). Pool `E' = (0, 2, 1)`: the candidate `E'₂ = 1` sits at the mean of
`{0, 1}` and adjoining it leaves the spread at `2` (`nonvacuity_line_at_mean`, an instance of
`spreadOn_insert_eq_iff`). The Cramér–Rao bound is attained with numbers on a genuine probability
space: on the fair-coin Rademacher model of `LineSelection` (`σ = 1`) with the wide pair
`E = (0, 3)`, `fisherInfoSlope = 9/2` and the OLS slope variance equals its inverse `2/9`
(`nonvacuity_crlb_attained`, an instance of `olsSlope_attains_crlb`).

## Literature and scope

**Scope: PURE-MATH throughout.** No spectroscopic quantity appears in any statement. Every result
is a statement about the finite-sample variance of an ordinary-least-squares slope and about the
sum of squared deviations of a finite family of abscissae. The *physics reading* is prose only:
for the Boltzmann plot `yₖ = log(Iₖ/(gₖAₖ))` against upper-level energy `Eₖ` the slope is
`β = −1/(k_B T)`, so `(fisherInfoSlope)⁻¹ = σ²/SS_E` is the Cramér–Rao floor on the variance of
the inverse temperature, and "a candidate line adds temperature information iff its upper-level
energy differs from the mean of the lines already used" is the actionable no-gain rule.

Citation: **—** (pure mathematics). The information inequality is due to
H. Cramér, *Mathematical Methods of Statistics*, Princeton Mathematical Series **9**, Princeton
University Press (1946), ISBN 9780691005478, and to C. R. Rao, "Information and the accuracy
attainable in the estimation of statistical parameters," *Bulletin of the Calcutta Mathematical
Society* **37** (1945) 81–91 (reprinted in *Breakthroughs in Statistics*, Springer (1992),
doi:10.1007/978-1-4612-0919-5_16). The one-pass update for the sum of squared deviations is
B. P. Welford, "Note on a Method for Calculating Corrected Sums of Squares and Products,"
*Technometrics* **4** (1962) 419–420, doi:10.1080/00401706.1962.10490022. The
"information-content" framing of design selection that `no_gain_iff` is the one-parameter
analogue of is N. E. Batalha and M. R. Line, "Information Content Analysis for Selection of
Optimal JWST Observing Modes for Transiting Exoplanet Atmospheres," *The Astronomical Journal*
**153** (2017) 151, doi:10.3847/1538-3881/aa5faa. The Gauss–Markov variance law this module builds
on is `Alt.OLSVariance.olsSlope_variance_eq` (Aitken 1935, cited there).

## Honest limitations

* **Fisher information is defined, not derived.** `fisherInfoSlope` is the closed form
  `SS_E/σ²`; no likelihood, density, score or Cramér–Rao regularity condition is formalized in
  measure theory. The theorems are exact identities *about that closed form*. The link between
  the closed form and "the variance of the score" is the standard derivation reproduced in the
  docstring of `fisherInfoSlope`, not a Lean proof.
* **Gaussianity enters only the interpretation.** `olsSlope_variance_eq` needs only second-moment
  (Gauss–Markov) hypotheses, so `olsSlope_attains_crlb` is proven under those. The reading of
  `SS_E/σ²` as *the* Fisher information — and hence of `σ²/SS_E` as a floor for *all* unbiased
  estimators — is specific to Gaussian noise; for non-Gaussian noise of the same variance the
  Fisher information can exceed `SS_E/σ²` and a nonlinear unbiased estimator can beat OLS.
* **Design monotonicity, not line usability.** "Adding a line never hurts" ranks designs under a
  common homoscedastic noise law. A line that is self-absorbed, blended, or has an unreliable
  `gA` violates the model, not the theorem; whether a candidate is *admissible* is decided by the
  pipeline's other gates, exactly as in `LineSelection`.
* **The mean is the current selection's mean.** `no_gain_iff` compares `Eₖ` with `Ē_S`, the mean
  of the lines *already selected*, not with any fixed reference energy; the criterion is
  sequential and depends on `S`.
-/

namespace CflibsFormal

open CflibsFormal.Alt
open MeasureTheory ProbabilityTheory
open Finset Real
open scoped BigOperators ProbabilityTheory

variable {ι : Type*}

/-! ## Fisher information for the slope and the Cramér–Rao bound -/

section FisherInfo

variable [Fintype ι]

/-- **Fisher information for the Boltzmann-plot slope**, `I(β) = SS_E/σ²`, in the Gaussian
linear model `yₖ = α + β Eₖ + εₖ` with `εₖ ~ N(0, σ²)` i.i.d.

*Derivation (prose, not formalized).* The log-likelihood is
`ℓ(α, β) = −∑ₖ (yₖ − α − β Eₖ)²/(2σ²) + const`. The full Fisher matrix is `(1/σ²)·XᵀX` for the
design `X = [𝟙 | E]`, i.e. `(1/σ²)·[[n, ∑E], [∑E, ∑E²]]`; its `(β, β)` entry after eliminating
the nuisance intercept `α` (the Schur complement) is `(∑E² − (∑E)²/n)/σ² = SS_E/σ²`.
Equivalently, the profile score in `β` is `∂ℓ/∂β = ∑ₖ (Eₖ − Ē) εₖ/σ²`, whose variance is
`∑ₖ (Eₖ − Ē)² σ²/σ⁴ = SS_E/σ²`.

**Honesty note.** This module does **not** formalize densities, likelihoods, or the regularity
conditions of the Cramér–Rao theorem in measure theory. `fisherInfoSlope` is *defined* as the
closed form the derivation above produces, and every theorem below is an exact algebraic
consequence of that definition together with the landed Gauss–Markov variance law. The statement
"OLS attains the Cramér–Rao bound" is therefore the identity `Var(β̂) = (SS_E/σ²)⁻¹`
(`olsSlope_attains_crlb`); the identification of `SS_E/σ²` with Fisher information is supplied by
the textbook derivation, not by a Lean proof. -/
noncomputable def fisherInfoSlope (E : ι → ℝ) (σ : ℝ) : ℝ := energySpread E / σ ^ 2

/-- The Fisher information is nonnegative: a nonnegative sum of squares over a square. -/
theorem fisherInfoSlope_nonneg (E : ι → ℝ) (σ : ℝ) : 0 ≤ fisherInfoSlope E σ :=
  div_nonneg (energySpread_nonneg E) (sq_nonneg σ)

/-- The Fisher information is strictly positive under the spread gate (`0 < SS_E`, the pipeline's
C1 certificate `energySpreadCert_iff`) and nondegenerate noise (`σ ≠ 0`). -/
theorem fisherInfoSlope_pos (E : ι → ℝ) (σ : ℝ) (hE : 0 < energySpread E) (hσ : σ ≠ 0) :
    0 < fisherInfoSlope E σ :=
  div_pos hE (by positivity)

/-- **The Cramér–Rao lower bound for the slope**: `σ²/SS_E = I(β)⁻¹`. This is unconditional
field algebra (`(a/b)⁻¹ = b/a`; in the degenerate cases `SS_E = 0` or `σ = 0` Lean's `x/0 = 0`
convention makes both sides `0`). The *meaningful* case is `0 < SS_E` and `σ ≠ 0`, where
`fisherInfoSlope_pos` makes the bound a genuine positive number. -/
theorem crlb_slope (E : ι → ℝ) (σ : ℝ) : σ ^ 2 / energySpread E = (fisherInfoSlope E σ)⁻¹ := by
  rw [fisherInfoSlope, inv_div]

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **OLS attains the Cramér–Rao bound — OLS is efficient.** Under the Gauss–Markov hypotheses of
`Alt.OLSVariance.olsSlope_variance_eq`, carried here verbatim (zero-mean is not needed for the
variance; `L²`, pairwise uncorrelated, homoscedastic with common `σ²`), the variance of the OLS
slope equals `(fisherInfoSlope E σ)⁻¹ = σ²/SS_E`. **What this theorem proves** is that identity
(`olsSlope_variance_eq` composed with `crlb_slope`). **What it does not prove** is the Cramér–Rao
inequality — that no unbiased estimator of the slope (hence, via `β = −1/(k_B T)`, of the inverse
temperature) can have smaller variance; `fisherInfoSlope` is a definition, not a derived Fisher
information, so "OLS is efficient" is the textbook conclusion read off this identity, not a
formal consequence (see the module's *Honest limitations*). -/
theorem olsSlope_attains_crlb [Nonempty ι] (E : ι → ℝ) (α β σ : ℝ) (ε : ι → Ω → ℝ)
    (hvar : 0 < ∑ k, (E k - mean E) ^ 2)
    (hL2 : ∀ k, MemLp (ε k) 2 μ)
    (huncorr : ∀ i j, i ≠ j → covariance (ε i) (ε j) μ = 0)
    (hhom : ∀ k, variance (ε k) μ = σ ^ 2) :
    variance (betaHat E α β ε) μ = (fisherInfoSlope E σ)⁻¹ := by
  rw [olsSlope_variance_eq E α β σ ε hvar hL2 huncorr hhom]
  exact crlb_slope E σ

end FisherInfo

/-! ## The one-pass update: adding a line to the selected set -/

/-- The subset spread is a sum of squares, hence nonnegative. -/
theorem spreadOn_nonneg (E : ι → ℝ) (S : Finset ι) : 0 ≤ spreadOn E S :=
  energySpread_nonneg _

/-- The spread of the empty selection is `0`. -/
theorem spreadOn_empty (E : ι → ℝ) : spreadOn E (∅ : Finset ι) = 0 := by
  rw [spreadOn_eq, Finset.sum_empty]

/-- The centered sum over a nonempty selected set vanishes: `∑_{j∈S} (Eⱼ − Ē_S) = 0`. -/
theorem sum_sub_finsetMean (E : ι → ℝ) (S : Finset ι) (hS : S.Nonempty) :
    ∑ j ∈ S, (E j - (∑ i ∈ S, E i) / (S.card : ℝ)) = 0 := by
  have hc : (S.card : ℝ) ≠ 0 := by exact_mod_cast hS.card_pos.ne'
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_div_cancel₀ _ hc, sub_self]

/-- **The parallel-axis (variational) identity for the subset spread.** For any pivot `c`,
`∑_{j∈S} (Eⱼ − c)² = spreadOn E S + |S|·(Ē_S − c)²`. In particular the mean `Ē_S` minimizes
`c ↦ ∑_{j∈S} (Eⱼ − c)²`, and the excess over that minimum is exactly `|S|·(Ē_S − c)²`. This is
the engine behind the one-pass update `spreadOn_insert`. -/
theorem sum_sq_sub_eq_spreadOn_add (E : ι → ℝ) (S : Finset ι) (hS : S.Nonempty) (c : ℝ) :
    ∑ j ∈ S, (E j - c) ^ 2
      = spreadOn E S + (S.card : ℝ) * ((∑ i ∈ S, E i) / (S.card : ℝ) - c) ^ 2 := by
  rw [spreadOn_eq]
  have h : ∀ j ∈ S, (E j - c) ^ 2
      = (E j - (∑ i ∈ S, E i) / (S.card : ℝ)) ^ 2
        + 2 * ((∑ i ∈ S, E i) / (S.card : ℝ) - c) * (E j - (∑ i ∈ S, E i) / (S.card : ℝ))
        + ((∑ i ∈ S, E i) / (S.card : ℝ) - c) ^ 2 :=
    fun j _ => by ring
  rw [Finset.sum_congr rfl h, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    sum_sub_finsetMean E S hS, Finset.sum_const, nsmul_eq_mul]
  ring

section InsertLine

variable [DecidableEq ι]

/-- **THE ONE-PASS VARIANCE UPDATE — the exact gain from adding a line.** For a nonempty selected
set `S` and a new line `k ∉ S`,
`spreadOn E (insert k S) = spreadOn E S + (|S|/(|S|+1)) · (Eₖ − Ē_S)²`,
where `Ē_S = (∑_{j∈S} Eⱼ)/|S|` is the mean upper-level energy of the lines already selected. The
increment is a nonnegative multiple of the squared distance of the new line's energy from the
current mean: a far line adds much, a line at the mean adds nothing (Welford's recurrence for the
corrected sum of squares). Proof: the parallel-axis identity `sum_sq_sub_eq_spreadOn_add` on
`insert k S` with pivot `Ē_S`, then field algebra in `|S|` and `|S| + 1`. -/
theorem spreadOn_insert (E : ι → ℝ) (S : Finset ι) (k : ι) (hk : k ∉ S) (hS : S.Nonempty) :
    spreadOn E (insert k S)
      = spreadOn E S
        + ((S.card : ℝ) / ((S.card : ℝ) + 1)) * (E k - (∑ j ∈ S, E j) / (S.card : ℝ)) ^ 2 := by
  have hc : (S.card : ℝ) ≠ 0 := by exact_mod_cast hS.card_pos.ne'
  have hc1 : (S.card : ℝ) + 1 ≠ 0 := by positivity
  have h1 := sum_sq_sub_eq_spreadOn_add E (insert k S) (Finset.insert_nonempty k S)
    ((∑ j ∈ S, E j) / (S.card : ℝ))
  rw [Finset.sum_insert hk, Finset.sum_insert hk, Finset.card_insert_of_notMem hk,
    ← spreadOn_eq, Nat.cast_add, Nat.cast_one] at h1
  have h2 : spreadOn E (insert k S)
      = (E k - (∑ j ∈ S, E j) / (S.card : ℝ)) ^ 2 + spreadOn E S
        - ((S.card : ℝ) + 1)
          * ((E k + ∑ j ∈ S, E j) / ((S.card : ℝ) + 1) - (∑ j ∈ S, E j) / (S.card : ℝ)) ^ 2 := by
    linear_combination -h1
  rw [h2]
  field_simp
  ring

/-- **Adding a line never decreases the energy spread.** No hypothesis at all: if `k ∈ S` nothing
changes; if `S = ∅` both spreads vanish; otherwise `spreadOn_insert` adds a nonnegative
increment. -/
theorem spreadOn_insert_ge (E : ι → ℝ) (S : Finset ι) (k : ι) :
    spreadOn E S ≤ spreadOn E (insert k S) := by
  by_cases hk : k ∈ S
  · rw [Finset.insert_eq_of_mem hk]
  · rcases S.eq_empty_or_nonempty with hS | hS
    · rw [hS, spreadOn_empty]
      exact spreadOn_nonneg _ _
    · rw [spreadOn_insert E S k hk hS]
      have : 0 ≤ ((S.card : ℝ) / ((S.card : ℝ) + 1))
          * (E k - (∑ j ∈ S, E j) / (S.card : ℝ)) ^ 2 := by positivity
      linarith

omit [DecidableEq ι] in
/-- **Monotonicity under inclusion: a superset of lines never has less spread.** Iterate
`spreadOn_insert_ge` over `T \ S`. (Decidable equality is needed only inside the proof, so it is
introduced there with `classical` rather than carried in the statement.) -/
theorem spreadOn_mono (E : ι → ℝ) {S T : Finset ι} (hST : S ⊆ T) :
    spreadOn E S ≤ spreadOn E T := by
  classical
  have key : ∀ U : Finset ι, spreadOn E S ≤ spreadOn E (S ∪ U) := by
    intro U
    induction U using Finset.induction_on with
    | empty => rw [Finset.union_empty]
    | insert a U _ ih =>
      rw [Finset.union_insert]
      exact ih.trans (spreadOn_insert_ge E (S ∪ U) a)
  have h := key T
  rwa [Finset.union_eq_right.mpr hST] at h

/-- **Adding a line never decreases the Fisher information** of the selected sub-design
(`fisherInfoSlope` of the restriction of `E` to the selected lines). -/
theorem fisherInfo_insert_ge (E : ι → ℝ) (S : Finset ι) (k : ι) (σ : ℝ) :
    fisherInfoSlope (fun j : ↥S => E j.1) σ
      ≤ fisherInfoSlope (fun j : ↥(insert k S) => E j.1) σ :=
  div_le_div_of_nonneg_right (spreadOn_insert_ge E S k) (sq_nonneg σ)

/-- **Adding a line never increases the Cramér–Rao bound.** Under the spread gate on the current
selection (`0 < spreadOn E S`, i.e. `S` already has two distinct upper-level energies — the
pipeline's C1 certificate), the Cramér–Rao floor `(fisherInfoSlope)⁻¹ = σ²/SS_E` of the enlarged
selection is at most that of the current one. The gate is genuinely needed: for a degenerate `S`
the true bound is infinite while Lean's `σ²/0 = 0`. -/
theorem crlb_insert_le (E : ι → ℝ) (S : Finset ι) (k : ι) (σ : ℝ) (hS : 0 < spreadOn E S) :
    (fisherInfoSlope (fun j : ↥(insert k S) => E j.1) σ)⁻¹
      ≤ (fisherInfoSlope (fun j : ↥S => E j.1) σ)⁻¹ := by
  rw [← crlb_slope, ← crlb_slope]
  exact div_le_div_of_nonneg_left (sq_nonneg σ) hS (spreadOn_insert_ge E S k)

/-! ## The no-gain criterion -/

/-- **The no-gain criterion.** For a nonempty selection `S` and a candidate `k ∉ S`, adding line
`k` leaves the spread unchanged **iff** its upper-level energy equals the mean energy of the lines
already selected. Immediate from `spreadOn_insert`: the increment `(|S|/(|S|+1))·(Eₖ − Ē_S)²`
vanishes iff `Eₖ = Ē_S`. -/
theorem spreadOn_insert_eq_iff (E : ι → ℝ) (S : Finset ι) (k : ι) (hk : k ∉ S)
    (hS : S.Nonempty) :
    spreadOn E (insert k S) = spreadOn E S ↔ E k = (∑ j ∈ S, E j) / (S.card : ℝ) := by
  have hc : (S.card : ℝ) ≠ 0 := by exact_mod_cast hS.card_pos.ne'
  have hq : (S.card : ℝ) / ((S.card : ℝ) + 1) ≠ 0 := div_ne_zero hc (by positivity)
  rw [spreadOn_insert E S k hk hS, add_eq_left, mul_eq_zero, pow_eq_zero_iff two_ne_zero,
    sub_eq_zero, or_iff_right hq]

/-- **Strict gain iff off the mean.** The complementary form of the no-gain criterion: adding
line `k` *strictly* increases the spread iff `Eₖ ≠ Ē_S`. -/
theorem spreadOn_insert_lt_iff (E : ι → ℝ) (S : Finset ι) (k : ι) (hk : k ∉ S)
    (hS : S.Nonempty) :
    spreadOn E S < spreadOn E (insert k S) ↔ E k ≠ (∑ j ∈ S, E j) / (S.card : ℝ) := by
  rw [lt_iff_le_and_ne, and_iff_right (spreadOn_insert_ge E S k)]
  exact ne_comm.trans (spreadOn_insert_eq_iff E S k hk hS).ne

/-- **`no_gain_iff` — a candidate line carries zero slope information iff its energy equals the
current mean.** With nondegenerate noise (`σ ≠ 0`), the Fisher information of the enlarged
selection equals that of the current selection **iff** `Eₖ = Ē_S`. This is the quantitative
no-gain criterion: a line at the current mean upper-level energy, however bright or clean, adds
nothing to the temperature precision; a line off the mean always adds
`(|S|/(|S|+1))·(Eₖ − Ē_S)²/σ²` of information. -/
theorem no_gain_iff (E : ι → ℝ) (S : Finset ι) (k : ι) (σ : ℝ) (hk : k ∉ S) (hS : S.Nonempty)
    (hσ : σ ≠ 0) :
    fisherInfoSlope (fun j : ↥(insert k S) => E j.1) σ = fisherInfoSlope (fun j : ↥S => E j.1) σ
      ↔ E k = (∑ j ∈ S, E j) / (S.card : ℝ) := by
  rw [← spreadOn_insert_eq_iff E S k hk hS]
  exact div_left_inj' (pow_ne_zero 2 hσ)

end InsertLine

/-! ## Non-vacuity on explicit `Fin 3` data -/

/-- **Non-vacuity — a far line strictly increases the spread, by exactly the predicted amount.**
Pool `E = (0, 2, 10)`, current selection `S = {0, 1}` (`Ē_S = 1`, `spreadOn = 2`). Adjoining the
far line `k = 2` (`E₂ = 10`) gives `spreadOn = 56 = 2 + (2/3)·(10 − 1)²`, a strict increase. The
value `56` is obtained *through* `spreadOn_insert`, so the identity is exercised on data. -/
theorem nonvacuity_far_line :
    spreadOn (ι := Fin 3) ![0, 2, 10] {0, 1} = 2 ∧
      spreadOn (ι := Fin 3) ![0, 2, 10] (insert 2 {0, 1}) = 56 ∧
      spreadOn (ι := Fin 3) ![0, 2, 10] {0, 1}
        < spreadOn (ι := Fin 3) ![0, 2, 10] (insert 2 {0, 1}) := by
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  have h2 : spreadOn (ι := Fin 3) ![0, 2, 10] {0, 1} = 2 := by
    rw [spreadOn_eq, Finset.sum_pair h01,
      Finset.sum_pair h01, Finset.card_pair h01]
    norm_num
  have h56 : spreadOn (ι := Fin 3) ![0, 2, 10] (insert 2 {0, 1}) = 56 := by
    rw [spreadOn_insert _ _ _ (by decide) (Finset.insert_nonempty _ _), h2,
      Finset.sum_pair h01, Finset.card_pair h01]
    simp only [Matrix.cons_val]
    norm_num
  exact ⟨h2, h56, by rw [h2, h56]; norm_num⟩

/-- **Non-vacuity — a line at the current mean adds nothing.** Pool `E' = (0, 2, 1)`, current
selection `S = {0, 1}` (`Ē_S = 1`, `spreadOn = 2`). The candidate `k = 2` has `E'₂ = 1 = Ē_S`, so
by `spreadOn_insert_eq_iff` adjoining it leaves the spread unchanged. The no-gain criterion is
exercised in its `←` direction on data. -/
theorem nonvacuity_line_at_mean :
    spreadOn (ι := Fin 3) ![0, 2, 1] (insert 2 {0, 1}) = spreadOn (ι := Fin 3) ![0, 2, 1] {0, 1} ∧
      spreadOn (ι := Fin 3) ![0, 2, 1] {0, 1} = 2 := by
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  have hmean : (![0, 2, 1] : Fin 3 → ℝ) 2
      = (∑ j ∈ ({0, 1} : Finset (Fin 3)), ![0, 2, 1] j) / (({0, 1} : Finset (Fin 3)).card : ℝ) := by
    rw [Finset.sum_pair h01, Finset.card_pair h01]
    simp only [Matrix.cons_val]
    norm_num
  refine ⟨(spreadOn_insert_eq_iff _ _ _ (by decide) (Finset.insert_nonempty _ _)).mpr hmean, ?_⟩
  rw [spreadOn_eq, Finset.sum_pair h01,
    Finset.sum_pair h01, Finset.card_pair h01]
  norm_num

/-- **Non-vacuity — the Cramér–Rao bound is attained, with numbers, on a genuine probability
space.** On the fair-coin Rademacher model of `LineSelection` (`σ = 1`, a real
`IsProbabilityMeasure` with nondegenerate noise) and the wide pair `E = (0, 3)`, the Fisher
information is `9/2` and the OLS slope variance equals its inverse, `2/9` (the value computed
independently in `nonvacuity_rademacher_values`). Every hypothesis of `olsSlope_attains_crlb` is
discharged by an explicit construction. -/
theorem nonvacuity_crlb_attained (α β : ℝ) :
    fisherInfoSlope (ι := Fin 2) ![0, 3] 1 = 9 / 2 ∧
      variance (betaHat ![0, 3] α β radNoise) fairCoins
        = (fisherInfoSlope (ι := Fin 2) ![0, 3] 1)⁻¹ ∧
      (fisherInfoSlope (ι := Fin 2) ![0, 3] 1)⁻¹ = 2 / 9 := by
  have hE : energySpread (ι := Fin 2) ![0, 3] = 9 / 2 := nonvacuity_energySpread_values.2.1
  have hI : fisherInfoSlope (ι := Fin 2) ![0, 3] 1 = 9 / 2 := by
    rw [fisherInfoSlope, hE]; norm_num
  have h3 : (0 : ℝ) < energySpread (ι := Fin 2) ![0, 3] := by rw [hE]; norm_num
  refine ⟨hI, ?_, by rw [hI]; norm_num⟩
  exact olsSlope_attains_crlb ![0, 3] α β 1 radNoise h3 radNoise_memLp radNoise_uncorr
    radNoise_variance

end CflibsFormal
