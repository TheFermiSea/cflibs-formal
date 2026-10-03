/-
Copyright (c) 2026 Brian Squires. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Squires
-/
import Mathlib

/-!
# CF-LIBS formalization — the refuse-to-report policy (certified abstention)

The companion pipeline scores a solver by a PAS loss in which each spectrum is either answered
(it pays its realised loss `l i`) or refused (it pays a fixed reference cost `λ`). Given
certified bounds `L i ≤ l i ≤ U i` on the loss, a three-branch policy answers when `U i ≤ λ`,
refuses when `λ < L i`, and makes an explicit choice on the ambiguous rest. This module states
that policy and its guarantees (frontier FT-03 of the 2026-09-24 audit).

## Main definitions

* `pasPolicy`: the weighted PAS value of the three-branch policy, with the choice on the
  ambiguous set `A = {i | L i ≤ λ ∧ λ < U i}` as an explicit argument.

## Main results

* `pasPolicy_guarantees`: refusing on `A` is never worse than always abstaining, and its regret
  against the loss-aware oracle is at most `∑_{i ∈ A} w i (λ − L i)`; answering on `A` is never
  worse than always answering. No single choice rule on `A` that sees only `(L, U, λ)` carries
  both guarantees, so both instantiations are stated.

A loss bound `U i` for the Aitchison PAS loss comes from per-species log-ratio error bounds via
`AitchisonIsometry.aitchisonDist_le_logErr`.

## Scope

`PURE-MATH`: finite decision-rule arithmetic. Every guarantee is conditional on the
certification premise `L i ≤ l i ≤ U i`, an assumed input that this module does not supply.

## Literature

No physics citation applies: PAS is the companion's own objective, and the results are
pure decision-rule arithmetic.
-/

open Finset

namespace CflibsFormal

/-- **Three-branch refuse-to-report policy: weighted PAS value.** Items `i : Fin N` (spectra)
carry a realised loss `l i`, certified loss bounds `L i`, `U i` (the certification premise
`L i ≤ l i ≤ U i` is a hypothesis of the theorems that use this definition, not part of it), and
a group weight `w i`; `lam` is the fixed reference (abstention) cost `λ_d`, chosen before scoring.
Per item the policy

* **answers** (cost `l i`) when the certified upper bound clears the reference, `U i ≤ lam`;
* **refuses** (cost `lam`) when the certified lower bound exceeds it, `lam < L i`;
* otherwise answers iff `ansA i`. The items reaching this last branch are exactly the ambiguous
  set `A = {i | L i ≤ lam ∧ lam < U i}`, so `ansA` is the explicit answer/refuse choice on `A`.

The value is `∑ i, w i * cost i`. The companion pipeline's PAS is a grouped mean (the mean over
groups of the group mean of `a_i ℓ_i + (1 − a_i) λ_d`), i.e. this form with
`w i = 1/(G · n_{g(i)}) > 0` (companion `docs/overhaul/objective-and-splits.md`); that binding is
not proved
here. Pure decision-rule arithmetic: no physics enters. -/
noncomputable def pasPolicy {N : ℕ} (w l L U : Fin N → ℝ) (lam : ℝ) (ansA : Fin N → Prop)
    [DecidablePred ansA] : ℝ :=
  ∑ i, w i * (if U i ≤ lam then l i else if lam < L i then lam else if ansA i then l i else lam)

/-- per-item (a): refusing on the ambiguous set never costs more than `lam`. -/
private theorem item_refuse_le {l L U lam : ℝ} (hU : l ≤ U) :
    (if U ≤ lam then l else if lam < L then lam else if False then l else lam) ≤ lam := by
  split_ifs with h1 <;> first | exact hU.trans h1 | exact le_rfl | contradiction

/-- per-item (b): regret of refuse-on-A against the oracle. -/
private theorem item_refuse_regret {l L U lam : ℝ} (hL : L ≤ l) (hU : l ≤ U) :
    (if U ≤ lam then l else if lam < L then lam else if False then l else lam) - min l lam
      ≤ (if L ≤ lam ∧ lam < U then lam - L else 0) := by
  by_cases h1 : U ≤ lam
  · rw [if_pos h1, min_eq_left (hU.trans h1), if_neg (fun h => absurd h.2 (not_lt.mpr h1))]
    simp
  · by_cases h2 : lam < L
    · rw [if_neg h1, if_pos h2, min_eq_right (by linarith),
        if_neg (fun h => absurd h.1 (not_le.mpr h2))]
      simp
    · rw [if_neg h1, if_neg h2, if_neg (not_false), if_pos ⟨not_lt.mp h2, not_le.mp h1⟩]
      have : L ≤ min l lam := le_min hL (not_lt.mp h2)
      linarith

/-- per-item (c): answering on the ambiguous set never costs more than answering. -/
private theorem item_answer_le {l L U lam : ℝ} (hL : L ≤ l) :
    (if U ≤ lam then l else if lam < L then lam else if True then l else lam) ≤ l := by
  split_ifs with h1 h2 <;> first | exact le_rfl | exact (le_of_lt (lt_of_lt_of_le h2 hL))

/-- **Guarantees of the three-branch refuse-to-report policy (weighted).** Under certified loss
bounds `L i ≤ l i ≤ U i` and nonnegative weights (the grouped-mean weights `1/(G·n_g)` are
positive), with `A = {i | L i ≤ lam ∧ lam < U i}`:

* **(a) refuse on `A` is never worse than always abstaining:**
  `pasPolicy … (fun _ => False) ≤ (∑ i, w i) * lam`. Answered items have `l i ≤ U i ≤ lam`.
* **(b) regret of refuse-on-`A` against the oracle** `∑ i, w i * min (l i) lam` (the policy that
  knows `l`) is at most `∑_{i ∈ A} w i * (lam − L i)`: off `A` the policy matches the oracle
  exactly, and on `A` the oracle pays `min (l i) lam ≥ L i`.
* **(c) answer on `A` is never worse than always answering** (gate value
  `G = PAS_forced − PAS_gated ≥ 0`): `pasPolicy … (fun _ => True) ≤ ∑ i, w i * l i`. Refused items
  have `lam < L i ≤ l i`.

No choice rule on `A` that depends only on `(L, U, lam)` carries both (a) and (c) (the two
witnesses share `(L, U, lam) = (0, 2, 1)`): one item with `(l, L, U, lam) = (1/2, 0, 2, 1)` makes
refusing cost `1 > l`, and `(3/2, 0, 2, 1)` makes answering cost `3/2 > lam` (Lean-checked
witnesses, audit evidence `frontier-verifier/Verify.lean`). The `l`-aware oracle choice does
carry both. Hence the explicit `ansA` and the two instantiations in one statement.

Hypotheses: `hU` is used by (a) and (b), `hL` by (b) and (c); both are the certification premise,
an assumed (R1-epistemic) input that this theorem does not supply, so every conclusion is
conditional on it. `hw` (nonnegative weights) makes the per-item comparisons survive weighting.
`lam` is fixed before scoring, so these are deterministic finite-sample statements.

Scope: relation PURE-MATH; the only definition used, `pasPolicy`, is a decision rule with no
model tag; published PURE-MATH. No citation: PAS is the companion's own objective. -/
theorem pasPolicy_guarantees {N : ℕ} {w l L U : Fin N → ℝ} {lam : ℝ} (hw : ∀ i, 0 ≤ w i)
    (hL : ∀ i, L i ≤ l i) (hU : ∀ i, l i ≤ U i) :
    pasPolicy w l L U lam (fun _ => False) ≤ (∑ i, w i) * lam ∧
    pasPolicy w l L U lam (fun _ => False) - ∑ i, w i * min (l i) lam
      ≤ ∑ i, w i * (if L i ≤ lam ∧ lam < U i then lam - L i else 0) ∧
    pasPolicy w l L U lam (fun _ => True) ≤ ∑ i, w i * l i := by
  refine ⟨?_, ?_, ?_⟩
  · unfold pasPolicy
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (item_refuse_le (hU i)) (hw i)
  · unfold pasPolicy
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [← mul_sub]
    exact mul_le_mul_of_nonneg_left (item_refuse_regret (hL i) (hU i)) (hw i)
  · unfold pasPolicy
    exact Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (item_answer_le (U := U i) (hL i)) (hw i)

end CflibsFormal
