/-
Copyright (c) 2026 Brian Squires. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Squires
-/
import Mathlib

/-!
# CF-LIBS formalization — the rank-counting step behind split-conformal coverage

**What this module proves is a counting bound, not a coverage theorem.** No probability measure
appears in any statement. Read the rest of this header with that in mind.

The pipeline's reliability gates (`Certificates.lean`) are *sufficient conditions*: each certifies
that a specific modelling premise holds, and each is only as good as the model it is stated in.
Split-conformal prediction offers a guarantee of a different kind — **distribution-free** and
finite-sample: given calibration scores that are exchangeable with the test score, a threshold
read off the calibration scores covers the test score with probability at least `1 − α`, whatever
the underlying distribution and however wrong the forward model is. That is the one guarantee that
survives simulator misspecification, which is why it is the right shape for a refuse-to-report
gate: *report* when the conformal interval is narrow enough, *abstain* otherwise. No such gate
exists yet on either side: the 2026-09-24 audit found the companion's conformal code exercised
only by its tests.

The companion pipeline's `split_conformal` (`cflibs/inversion/physics/conformal.py`) returns,
from `n` calibration nonconformity scores, the `k`-th **smallest calibration** score with

  `k = ⌈(1 − α)·(n + 1)⌉`   (`conformal_rank`),

deliberately in preference to an interpolating quantile, and `+∞` when `k > n`. This module
proves the counting fact that choice rests on, with one difference in the threshold: here it is
the `k`-th smallest of **all** `N = n + 1` scores, the test score included. The bridge lemma (for
`k ≤ n`, the test score is at most the `k`-th smallest calibration score iff it is at most the
`k`-th smallest of all `N` scores) and the `k = n + 1` (`+∞`) branch are **not** proved here.

## What is proven, and what is assumed

Write `N = n + 1` for the *total* number of exchangeable scores (the `n` calibration scores
together with the one test score). The argument splits cleanly in two, and only the first half is
mathematics:

1. **The counting core (proved here).** Order the `N` scores. If the threshold is the `k`-th
   smallest, then *at least `k` of the `N` scores lie at or below it* — `card_le_card_covered`.
   Dividing by `N` and using `k = ⌈(1 − α)N⌉ ≥ (1 − α)N` gives
   `covered/N ≥ 1 − α` — `conformal_coverage_fraction`.
2. **Exchangeability (not formalized).** The step from "a fraction `≥ 1 − α` of the `N`
   positions are covered" to "the *test* score is covered with probability `≥ 1 − α`" uses the
   assumption that the test score is equally likely to occupy any of the `N` positions. Under
   that assumption the coverage probability is the *expected* covered fraction over the random
   draw, and it is `≥ 1 − α` because the fraction is `≥ 1 − α` for every realization. None of
   this is formalized: there is no measure, no random draw and no distinguished test index here.
   `ExchangeableRank` is only a stand-in — it sets a real number `p` equal to the covered fraction
   of one fixed score vector — so `conformal_coverage_of_exchangeable` is
   `conformal_coverage_fraction` restated for any `p` equal to that fraction.

So the honest reading is: **the counting step used in split-conformal coverage is correct for the
all-scores threshold; the probabilistic step, and the bridge to `split_conformal`'s
calibration-only threshold, are not proved; and whether the guarantee applies to a given LIBS
deployment is an empirical question about exchangeability.** For this pipeline that question has
teeth — calibration spectra cluster by matrix and by instrument mode, so a per-matrix-class
calibration set (or an explicit covariate-shift correction) is what makes the hypothesis
defensible. Nothing here certifies that.

## Literature and scope

**Scope: PURE-MATH.** Every statement is finite combinatorics over a linear order; no
spectroscopic quantity, no measure theory, no distributional assumption appears. A measure-theoretic
coverage theorem (permutation-invariant law on the `N` scores) is future work; mathlib has no
exchangeability API to build it on. Split conformal
prediction is due to Vovk, Gammerman & Shafer, *Algorithmic Learning in a Random World*, Springer
(2005), and the split/inductive form used by the companion follows Lei, G'Sell, Rinaldo,
Tibshirani & Wasserman, "Distribution-Free Predictive Inference for Regression", *JASA* **113**
(2018) 1094–1111, doi:10.1080/01621459.2017.1307116 (the DOI is recorded in the companion's
`conformal.py`; the primary source has NOT been opened here — the whitelist row is
`UNVERIFIED`, and no constant, inequality direction, or attributed result is taken from it: the
counting core below is proved from scratch).

**Honest limitations.**
* The coverage guarantee this counting step serves (itself not proved here) is **marginal**, not
  conditional: it is over the joint draw, not per matrix class or per element. A per-class
  guarantee needs a per-class calibration set.
* The bound is one-sided. The companion's docstring notes the matching upper bound
  `≤ 1 − α + 1/(n+1)` for distinct scores; that direction is *not* proved here.
* Ties are handled the conservative way: `card_le_card_covered` counts *at least* `k`, which is
  what the coverage direction needs; with ties the covered set can be strictly larger.
* Nothing here says the conformal interval is *narrow*. A gate that abstains whenever the
  interval is too wide would be sound by the coverage theorem (once proved) and useless if it
  abstains always; usefulness is an empirical property (the companion's coverage/width
  bookkeeping), not a theorem.
-/

namespace CflibsFormal

open Finset

variable {N : ℕ}

/-! ## The counting core -/

/-- **The `k`-th smallest score covers at least `k` of the scores.**

`Tuple.sort s` is the permutation of the index set that sorts `s` (`Tuple.monotone_sort`), so
`s (Tuple.sort s k)` is the `(k+1)`-st smallest value of the family `s` (zero-indexed `k`). The
theorem says that at least `k + 1` of the `N` indices carry a value at or below it.

Proof: the `k + 1` indices `Tuple.sort s j` for `j ≤ k` are distinct (a permutation is injective)
and each satisfies `s (Tuple.sort s j) ≤ s (Tuple.sort s k)` by monotonicity of the sorted family,
so they inject into the covered set. Ties only enlarge the covered set, which is why the statement
is an inequality. -/
theorem card_le_card_covered (s : Fin N → ℝ) (k : Fin N) :
    (k : ℕ) + 1 ≤ #{i | s i ≤ s (Tuple.sort s k)} := by
  have hmono : Monotone (s ∘ (Tuple.sort s)) := Tuple.monotone_sort s
  have hsub : (Finset.Iic k).image (Tuple.sort s)
      ⊆ Finset.univ.filter (fun i => s i ≤ s (Tuple.sort s k)) := by
    intro i hi
    simp only [Finset.mem_image, Finset.mem_Iic] at hi
    obtain ⟨j, hj, rfl⟩ := hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    simpa using hmono hj
  calc (k : ℕ) + 1 = (Finset.Iic k).card := (Fin.card_Iic k).symm
    _ = ((Finset.Iic k).image (Tuple.sort s)).card :=
        (Finset.card_image_of_injective _ (Equiv.injective _)).symm
    _ ≤ #{i | s i ≤ s (Tuple.sort s k)} := Finset.card_le_card hsub

/-- **The covered fraction is at least `1 − α`.**

For any `N` real scores (no exchangeability or other assumption is used) and the conformal rank
`k = ⌈(1 − α)·N⌉` (the companion's `conformal_rank`, here as the zero-indexed `k` with
`(k : ℕ) + 1 = ⌈(1 − α)·N⌉`), the fraction of positions whose score lies at or below the `k`-th
smallest of all `N` scores is at least `1 − α`.

This is `card_le_card_covered` divided by `N`, together with `(1 − α)·N ≤ ⌈(1 − α)·N⌉`
(`Nat.le_ceil`) — the *only* place the ceiling matters, and the reason `split_conformal` takes an
attained calibration score rather than an interpolating quantile. -/
theorem conformal_coverage_fraction (s : Fin N → ℝ) (α : ℝ) (k : Fin N)
    (hk : (k : ℕ) + 1 = ⌈(1 - α) * (N : ℝ)⌉₊) :
    1 - α ≤ (#{i | s i ≤ s (Tuple.sort s k)} : ℝ) / (N : ℝ) := by
  have hN : (0 : ℝ) < (N : ℝ) := by
    have : 0 < N := k.pos
    exact_mod_cast this
  rw [le_div_iff₀ hN]
  calc (1 - α) * (N : ℝ) ≤ (⌈(1 - α) * (N : ℝ)⌉₊ : ℝ) := Nat.le_ceil _
    _ = ((k : ℕ) + 1 : ℕ) := by rw [hk]
    _ ≤ (#{i | s i ≤ s (Tuple.sort s k)} : ℝ) := by
        exact_mod_cast card_le_card_covered s k

/-! ## A stand-in for exchangeability (not a probabilistic statement) -/

/-- **A stand-in for the exchangeability step: `p` equals the covered fraction of one fixed score
vector.**

`ExchangeableRank s k p` says only that the real number `p` equals the fraction of the `N`
positions of the fixed vector `s` whose score is at or below the threshold `s (Tuple.sort s k)`.
It is **not** exchangeability. No probability measure, random draw or test index appears. The
intended reading is that `p` is the probability that the test score is covered. Under genuine
exchangeability that probability is the *expected* covered fraction over the random draw, not
the fraction for one realized `s`.

It is meant as a hypothesis about the data-generating process, and this module makes no attempt
to derive it. In a LIBS deployment the underlying assumption is that a new spectrum is
exchangeable with the calibration spectra, which matrix clustering and instrument drift can break.
Naming it keeps that assumption visible, but the predicate does not formalize it. -/
def ExchangeableRank (s : Fin N → ℝ) (k : Fin N) (p : ℝ) : Prop :=
  p = (#{i | s i ≤ s (Tuple.sort s k)} : ℝ) / (N : ℝ)

/-- **Rank-counting bound: any `p` equal to the covered fraction is at least `1 − α`.** With the
conformal rank `k = ⌈(1 − α)N⌉` and `ExchangeableRank s k p` (that is, `p` equals the covered
fraction of the fixed score vector `s`), `1 − α ≤ p`.

This is `conformal_coverage_fraction` after rewriting with `hex`; it adds no probabilistic
content. It is **not** split-conformal marginal coverage: no measure appears, `ExchangeableRank`
is not exchangeability, and the threshold is the `k`-th smallest of all `N` scores rather than of
the `n` calibration scores that the companion's `split_conformal`
(`cflibs/inversion/physics/conformal.py`) uses. The coverage theorem a conformal refuse-to-report
gate would rest on needs the probabilistic step and the calibration-threshold bridge, neither of
which is proved here (see the module header). -/
theorem conformal_coverage_of_exchangeable (s : Fin N → ℝ) (α p : ℝ) (k : Fin N)
    (hk : (k : ℕ) + 1 = ⌈(1 - α) * (N : ℝ)⌉₊) (hex : ExchangeableRank s k p) :
    1 - α ≤ p := by
  rw [hex]
  exact conformal_coverage_fraction s α k hk

/-! ## Non-vacuity -/

/-- Non-vacuity of the rank hypothesis `hk`: with `N = 5` and `α = 1/5` the conformal rank is
`⌈(4/5)·5⌉ = 4` — the 4th smallest score, i.e. zero-indexed `k = 3`. This example checks only that
arithmetic; no scores appear in it. For five distinct scores the covered set would be the four
smallest positions, a covered fraction of `4/5 = 1 − α`; the next example checks the count on
explicit scores. -/
example :
    ((3 : Fin 5) : ℕ) + 1 = ⌈(1 - (1 : ℝ) / 5) * (5 : ℝ)⌉₊ := by
  norm_num

/-- Non-vacuity: the counting core fires on explicit data. For `s = (10, 20, 30, 40, 50)` the
threshold at zero-indexed `k = 3` is the 4th smallest (`40`), and at least `4` of the `5` scores
lie at or below it. -/
private def nvScores : Fin 5 → ℝ := ![10, 20, 30, 40, 50]

example : ((3 : Fin 5) : ℕ) + 1
    ≤ #{i | nvScores i ≤ nvScores (Tuple.sort nvScores 3)} :=
  card_le_card_covered nvScores 3

end CflibsFormal
