/-
Copyright (c) 2026 Brian Squires. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Squires
-/
import Mathlib

/-!
# CF-LIBS formalization — split-conformal coverage (the refuse-to-report gate)

The pipeline's reliability gates (`Certificates.lean`) are *sufficient conditions*: each certifies
that a specific modelling premise holds, and each is only as good as the model it is stated in.
Split-conformal prediction offers a guarantee of a different kind — **distribution-free** and
finite-sample: given calibration scores that are exchangeable with the test score, a threshold
read off the calibration scores covers the test score with probability at least `1 − α`, whatever
the underlying distribution and however wrong the forward model is. That is the one guarantee that
survives simulator misspecification, which is why it is the right shape for a refuse-to-report
gate: *report* when the conformal interval is narrow enough, *abstain* otherwise.

The companion pipeline implements exactly this (`cflibs/inversion/physics/conformal.py`,
`split_conformal`): from `n` calibration nonconformity scores it returns the `k`-th **smallest**
score with

  `k = ⌈(1 − α)·(n + 1)⌉`   (`conformal_rank`),

deliberately in preference to an interpolating quantile. This module certifies the arithmetic that
choice rests on.

## What is proven, and what is assumed

Write `N = n + 1` for the *total* number of exchangeable scores (the `n` calibration scores
together with the one test score). The argument splits cleanly in two, and only the first half is
mathematics:

1. **The counting core (proved here).** Order the `N` scores. If the threshold is the `k`-th
   smallest, then *at least `k` of the `N` scores lie at or below it* — `card_le_card_covered`.
   Dividing by `N` and using `k = ⌈(1 − α)N⌉ ≥ (1 − α)N` gives
   `covered/N ≥ 1 − α` — `conformal_coverage_fraction`.
2. **Exchangeability (assumed, not proved).** The step from "a fraction `≥ 1 − α` of the `N`
   positions are covered" to "the *test* score is covered with probability `≥ 1 − α`" is exactly
   the assumption that the test score is equally likely to occupy any of the `N` positions. That
   is the exchangeability hypothesis, and it is a statement about the data-generating process, not
   a theorem: it is stated here as `ExchangeableRank` and *carried*, never discharged.
   `conformal_coverage_of_exchangeable` composes the two.

So the honest reading is: **the rank arithmetic of `split_conformal` is correct; whether the
guarantee applies to a given LIBS deployment is an empirical question about exchangeability.** For
this pipeline that question has teeth — calibration spectra cluster by matrix and by instrument
mode, so a per-matrix-class calibration set (or an explicit covariate-shift correction) is what
makes the hypothesis defensible. Nothing here certifies that.

## Literature and scope

**Scope: PURE-MATH.** Every statement is finite combinatorics over a linear order; no
spectroscopic quantity, no measure theory, no distributional assumption appears. Split conformal
prediction is due to Vovk, Gammerman & Shafer, *Algorithmic Learning in a Random World*, Springer
(2005), and the split/inductive form used by the companion follows Lei, G'Sell, Rinaldo,
Tibshirani & Wasserman, "Distribution-Free Predictive Inference for Regression", *JASA* **113**
(2018) 1094–1111, doi:10.1080/01621459.2017.1307116 (the DOI is recorded in the companion's
`conformal.py`; the primary source has NOT been opened here — the whitelist row is
`UNVERIFIED`, and no constant, inequality direction, or attributed result is taken from it: the
counting core below is proved from scratch).

**Honest limitations.**
* Coverage is **marginal**, not conditional: the guarantee is over the joint draw, not per
  matrix class or per element. A per-class guarantee needs a per-class calibration set.
* The bound is one-sided. The companion's docstring notes the matching upper bound
  `≤ 1 − α + 1/(n+1)` for distinct scores; that direction is *not* proved here.
* Ties are handled the conservative way: `card_le_card_covered` counts *at least* `k`, which is
  what the coverage direction needs; with ties the covered set can be strictly larger.
* Nothing here says the conformal interval is *narrow*. A gate that abstains whenever the
  interval is too wide is sound by this theorem and useless if it abstains always; usefulness is
  an empirical property (the companion's coverage/width bookkeeping), not a theorem.
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

With `N` exchangeable scores and the conformal rank `k = ⌈(1 − α)·N⌉` (the companion's
`conformal_rank`, here as the zero-indexed `k` with `(k : ℕ) + 1 = ⌈(1 − α)·N⌉`), the fraction of
positions whose score lies at or below the `k`-th smallest is at least `1 − α`.

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

/-! ## Exchangeability: the hypothesis that is carried, never discharged -/

/-- **The exchangeability hypothesis, stated explicitly.**

`ExchangeableRank s k p` says: the probability `p` that the *test* score is covered by the
threshold `s (Tuple.sort s k)` equals the *fraction of positions* that are covered. This is the
content of exchangeability — the test score is equally likely to occupy any of the `N` positions,
so its chance of landing in the covered set is that set's relative size.

It is a hypothesis about the data-generating process, **not** a theorem, and this module makes no
attempt to derive it: in a LIBS deployment it is exactly the claim that a new spectrum is
exchangeable with the calibration spectra, which matrix clustering and instrument drift can break.
Stating it as a named predicate is the point — it keeps the assumption visible in every downstream
statement instead of hiding inside a probabilistic model. -/
def ExchangeableRank (s : Fin N → ℝ) (k : Fin N) (p : ℝ) : Prop :=
  p = (#{i | s i ≤ s (Tuple.sort s k)} : ℝ) / (N : ℝ)

/-- **Split-conformal marginal coverage.** Under exchangeability, the conformal rank
`k = ⌈(1 − α)N⌉` gives test-point coverage at least `1 − α`, distribution-free and finite-sample.

The mathematical content is `conformal_coverage_fraction`; `ExchangeableRank` is the bridge from
a counting fact about the `N` positions to a probability about the test point, and it is supplied,
not proved. This is the theorem behind the companion's `split_conformal`
(`cflibs/inversion/physics/conformal.py`) and the guarantee a conformal refuse-to-report gate
would rest on. -/
theorem conformal_coverage_of_exchangeable (s : Fin N → ℝ) (α p : ℝ) (k : Fin N)
    (hk : (k : ℕ) + 1 = ⌈(1 - α) * (N : ℝ)⌉₊) (hex : ExchangeableRank s k p) :
    1 - α ≤ p := by
  rw [hex]
  exact conformal_coverage_fraction s α k hk

/-! ## Non-vacuity -/

/-- Non-vacuity: five distinct scores, `α = 1/5`, so the conformal rank is
`⌈(4/5)·5⌉ = 4` — the 4th smallest score, i.e. zero-indexed `k = 3`. The covered set is genuinely
`{0, 1, 2, 3}`: four of the five positions, a covered fraction of `4/5 = 1 − α` exactly. Nothing
degenerates — the threshold is an interior score, and the count is strictly less than `N`. -/
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
