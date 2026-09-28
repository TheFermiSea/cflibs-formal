import Mathlib

/-!
# Queue target FT03-pasPolicy-guarantees (deep audit 2026-09-24, FT-03 item 1)

Weighted three-branch refuse-to-report policy on the PAS loss, with the two instantiations of
the ambiguous-set choice (refuse on it / answer on it) and their three guarantees. Statement file
for the proof queue: one new definition, one target theorem, one `sorry`.
-/

open Finset

namespace Plan.FT03

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
`w i = 1/(G · n_{g(i)}) > 0`; that binding is recorded at landing, not proved here. Pure
decision-rule arithmetic: no physics enters. -/
noncomputable def pasPolicy {N : ℕ} (w l L U : Fin N → ℝ) (lam : ℝ) (ansA : Fin N → Prop)
    [DecidablePred ansA] : ℝ :=
  ∑ i, w i * (if U i ≤ lam then l i else if lam < L i then lam else if ansA i then l i else lam)

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

Scope (two-axis): relation PURE-MATH; the only definition used, `pasPolicy`, is a PURE-MATH
decision rule; published PURE-MATH. Citation: — (PAS is the companion's own definition). -/
theorem pasPolicy_guarantees {N : ℕ} {w l L U : Fin N → ℝ} {lam : ℝ} (hw : ∀ i, 0 ≤ w i)
    (hL : ∀ i, L i ≤ l i) (hU : ∀ i, l i ≤ U i) :
    pasPolicy w l L U lam (fun _ => False) ≤ (∑ i, w i) * lam ∧
    pasPolicy w l L U lam (fun _ => False) - ∑ i, w i * min (l i) lam
      ≤ ∑ i, w i * (if L i ≤ lam ∧ lam < U i then lam - L i else 0) ∧
    pasPolicy w l L U lam (fun _ => True) ≤ ∑ i, w i * l i := by
  sorry

end Plan.FT03
