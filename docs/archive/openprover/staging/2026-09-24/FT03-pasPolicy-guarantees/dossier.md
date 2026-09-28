# FT03-pasPolicy-guarantees: planning dossier

*Source: deep audit 2026-09-24 (`docs/research/audit-2026-09-24/REPORT.md` §5 FT-03, queue
decomposition item 1), with the audit verifier's revision (REVISE, grade A): no choice rule on the
ambiguous set that depends only on `(L, U, lam)` carries both guarantees, so the choice on that set
is an explicit argument. Statement audit (2026-09-24): `hw` weakened from `0 < w i` to `0 ≤ w i`
(only nonnegativity is used; the strict form needlessly excluded zero-weight items), docstring
tightened. Group g3, priority 4. Toolchain: Lean / mathlib v4.33.1 (the built `lean-main`
checkout). Every Lean snippet below was compiled against that checkout on 2026-09-24 unless marked
otherwise.*

## 1. Goal

Statement file: `statement.lean`, namespace `Plan.FT03`, imports **`Mathlib` only**, `open Finset`.
It contains one new definition (`pasPolicy`, §2) and the target:

```lean
theorem pasPolicy_guarantees {N : ℕ} {w l L U : Fin N → ℝ} {lam : ℝ} (hw : ∀ i, 0 ≤ w i)
    (hL : ∀ i, L i ≤ l i) (hU : ∀ i, l i ≤ U i) :
    pasPolicy w l L U lam (fun _ => False) ≤ (∑ i, w i) * lam ∧
    pasPolicy w l L U lam (fun _ => False) - ∑ i, w i * min (l i) lam
      ≤ ∑ i, w i * (if L i ≤ lam ∧ lam < U i then lam - L i else 0) ∧
    pasPolicy w l L U lam (fun _ => True) ≤ ∑ i, w i * l i
```

Three conjuncts: (a) refuse-on-ambiguous is never worse than always abstaining; (b) its regret
against the oracle `∑ w·min(l, λ)` is at most `∑_{i∈A} w_i(λ − L_i)`; (c) answer-on-ambiguous is
never worse than always answering. `A = {i | L i ≤ lam ∧ lam < U i}`.

## 2. Definitions (verbatim; the candidate must reproduce `pasPolicy` character for character)

```lean
noncomputable def pasPolicy {N : ℕ} (w l L U : Fin N → ℝ) (lam : ℝ) (ansA : Fin N → Prop)
    [DecidablePred ansA] : ℝ :=
  ∑ i, w i * (if U i ≤ lam then l i else if lam < L i then lam else if ansA i then l i else lam)
```

Per item: answer (`l i`) if `U i ≤ lam`; refuse (`lam`) if `lam < L i`; otherwise answer iff
`ansA i`. With `ansA := fun _ => False` the last branch refuses; with `fun _ => True` it answers.
After `unfold pasPolicy` the summand contains `if (fun _ => False) i then …`; it is definitionally
`if False then …`, and the per-item lemmas below apply to it by `exact` without any `simp`.

## 3. Why it is true (per item, then sum with nonnegative weights)

| case | refuse-on-A cost | answer-on-A cost | oracle `min l λ` |
|---|---|---|---|
| `U ≤ λ` | `l` (`≤ U ≤ λ`) | `l` | `l` (since `l ≤ U ≤ λ`) |
| `λ < L` | `λ` | `λ` (`< L ≤ l`) | `λ` (since `λ < L ≤ l`) |
| `L ≤ λ < U` (A) | `λ` | `l` | `≥ L` (both `l ≥ L` and `λ ≥ L`) |

(a) every refuse-on-A cost is `≤ λ`; (b) the refuse-on-A cost minus the oracle cost is `0` off A
and `≤ λ − L` on A; (c) every answer-on-A cost is `≤ l`. Multiply by `w i ≥ 0` (exactly `hw`) and
sum.

## 4. Proof route (all pieces compiled)

Paste these per-item lemmas **before** the target, inside `namespace Plan.FT03` (names are free;
do not name a helper `pasPolicy_guarantees'`, see §7):

```lean
/-- per-item (a): refusing on the ambiguous set never costs more than `lam`. -/
theorem item_refuse_le {l L U lam : ℝ} (hU : l ≤ U) :
    (if U ≤ lam then l else if lam < L then lam else if False then l else lam) ≤ lam := by
  split_ifs with h1 <;> first | exact hU.trans h1 | exact le_rfl | contradiction

/-- per-item (b): regret of refuse-on-A against the oracle. -/
theorem item_refuse_regret {l L U lam : ℝ} (hL : L ≤ l) (hU : l ≤ U) :
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
theorem item_answer_le {l L U lam : ℝ} (hL : L ≤ l) :
    (if U ≤ lam then l else if lam < L then lam else if True then l else lam) ≤ l := by
  split_ifs with h1 h2 <;> first | exact le_rfl | exact (le_of_lt (lt_of_lt_of_le h2 hL))
```

Assembly of each conjunct (each compiled as a separate theorem):

```lean
  -- (a)
  unfold pasPolicy
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (item_refuse_le (hU i)) (hw i)
  -- (b)
  unfold pasPolicy
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [← mul_sub]
  exact mul_le_mul_of_nonneg_left (item_refuse_regret (hL i) (hU i)) (hw i)
  -- (c)
  unfold pasPolicy
  exact Finset.sum_le_sum fun i _ =>
    mul_le_mul_of_nonneg_left (item_answer_le (U := U i) (hL i)) (hw i)
```

Recommended shape: prove the three conjuncts as three helper theorems (with the target's
hypotheses) and close the target with `exact ⟨hA, hB, hC⟩`, or use `refine ⟨?_, ?_, ?_⟩` and run
the three blocks in order. `unfold pasPolicy` inside a conjunct unfolds both occurrences in (b);
that is fine.

## 5. Audit evidence (unweighted forms, compiled here under `import Mathlib` alone)

From `evidence/uncertainty/Scratch.lean` and `evidence/frontier-proposer/Proofs.lean:56`; they are
the `w ≡ 1` two-branch ancestors and show the case-analysis style:

```lean
theorem pas_certified_le_lambda {N : ℕ} (l U : Fin N → ℝ) (lam : ℝ) (hU : ∀ i, l i ≤ U i) :
    ∑ i, (if U i ≤ lam then l i else lam) ≤ N * lam := by
  calc ∑ i, (if U i ≤ lam then l i else lam) ≤ ∑ _i : Fin N, lam := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        split_ifs with h
        · exact (hU i).trans h
        · exact le_rfl
    _ = N * lam := by simp

theorem pas_gate_value_nonneg {N : ℕ} (l L : Fin N → ℝ) (lam : ℝ) (hL : ∀ i, L i ≤ l i) :
    (∑ i, if lam < L i then lam else l i) ≤ ∑ i, l i := by
  refine Finset.sum_le_sum fun i _ => ?_
  split_ifs with h
  · exact le_of_lt (lt_of_lt_of_le h (hL i))
  · exact le_rfl
```

(`pas_interval_regret`, the unweighted regret with the looser width `U − L`, also compiles; not
needed.)

## 6. Why the choice on A is explicit (verifier's Lean witnesses, `frontier-verifier/Verify.lean:102-106`)

```lean
-- answer-iff-U≤λ (refuse on A) can be worse than always answering (violates (c))
example : ∃ l L U lam : ℝ, L ≤ l ∧ l ≤ U ∧ l < (if U ≤ lam then l else lam) :=
  ⟨1 / 2, 0, 2, 1, by norm_num, by norm_num, by norm_num⟩
-- refuse-iff-L>λ (answer on A) can be worse than always refusing (violates (a))
example : ∃ l L U lam : ℝ, L ≤ l ∧ l ≤ U ∧ lam < (if lam < L then lam else l) :=
  ⟨3 / 2, 0, 2, 1, by norm_num, by norm_num, by norm_num⟩
```

The two witnesses share `(L, U, lam) = (0, 2, 1)` and differ only in `l`, so no choice rule on A
that depends only on `(L, U, lam)` carries both (a) and (c); the `l`-aware oracle choice does. So
the statement pairs (a), (b) with `ansA := fun _ => False` and (c) with `fun _ => True`; do not
try to prove (a) or (b) for the answering policy.

## 7. Mathlib lemmas used (all resolved in v4.33.1)

`Finset.sum_le_sum`, `Finset.sum_mul`, `Finset.sum_sub_distrib`, `mul_sub`,
`mul_le_mul_of_nonneg_left`, `min_eq_left`, `min_eq_right`, `le_min`, `if_pos`, `if_neg`,
`not_lt`, `not_le`, `not_false`, `lt_of_lt_of_le`, `le_of_lt`; tactics `split_ifs`, `by_cases`,
`linarith`, `simp`.

## 8. Pitfalls and verifier rules

- Keep the statement file's header verbatim: `import Mathlib` only (no new imports), `open Finset`,
  `namespace Plan.FT03`, the `pasPolicy` definition character for character, and the target
  signature text identical up to `:=`. State the target with the keyword `theorem`.
- The verifier locates the target by the regex `theorem\s+pasPolicy_guarantees\b`; a helper named
  `pasPolicy_guarantees'` would match first. Use names like `item_refuse_le`.
- Forbidden anywhere in the candidate: `sorry`, `admit`, `native_decide`, `axiom`, `macro`,
  `syntax`, `elab`, `#`-commands (`#check`, `#print`, `#eval`, …), `set_option` other than
  `maxHeartbeats` / `maxRecDepth` / `synthInstance.maxHeartbeats`.
- `push_neg` is deprecated in this mathlib (use `push Not`, or `not_lt.mp` / `not_le.mp` as above);
  it is a warning, not an error. Do not define a `push_neg` macro (forbidden).
- `DecidablePred (fun _ => False)` and `(fun _ => True)` are found by instance search; the
  statement elaborates.
- Weights: `hw i : 0 ≤ w i` is passed directly to `mul_le_mul_of_nonneg_left` (no `.le`).

## 9. Scope and consumers

PURE-MATH (relation and definition); published PURE-MATH. Conditional on the certified bounds
`L ≤ l ≤ U` (R1-epistemic, assumed). Consumers: BL-02 (critical), G2 TS-01 (critical), F8
`abstention_policy`, G1 SC-03/SC-04/SC-05. Loss-bound sources: `FT03-aitchisonDist-le-logErr`
(U from per-species log errors) and `FT07-classicComposition-atomicData-error-rel`.

Not in this target (statement-audit follow-up F4, a separate target): the general per-item
statement for an arbitrary `ansA`, including the answer-on-A regret bound
`∑_{i ∈ A} w i * (U i − lam)`; this statement uses `ansA` only at the two constants.

Statement-audit evidence (2026-09-24): `staging/2026-09-24/_statement-audit/ft03_weak_hw.lean`
(the proof with `0 ≤ w i`, non-degenerate witness `(l, L, U, lam) = (1/2, 0, 2, 1)`, `w = 1`, and
the swapped-instantiation and zero-width counterexamples; exit 0, axiom-clean).
