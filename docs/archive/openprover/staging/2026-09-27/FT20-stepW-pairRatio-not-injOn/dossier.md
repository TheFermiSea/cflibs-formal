# FT20-stepW-pairRatio-not-injOn: the two-step pair ratio is not injective (closed form)

Planning dossier for the proof queue (frontier FT-20 (b), decomposition items 2-4; audit verdict
REVISE, revision applied). Written for a planner who cannot open the repository. There are no
repo definitions: this is pure real analysis on Mathlib. Every Mathlib name was checked with
`#check` (Mathlib v4.33.1, `lean-main`), and every snippet in §4 compiled in a scratch file on
2026-09-27. Only the glue (unfolding `f 1`, `f 3`, `f 10` to the `a, b` form) was not compiled.

## 1. Goal

```lean
import Mathlib

namespace Plan.FT20

noncomputable def stepW (η M τ : ℝ) : ℝ :=
  (1 - Real.exp (-(τ * (1 + η)))) + (M - 1) * (1 - Real.exp (-(τ * η)))

theorem stepW_pairRatio_not_injOn :
    ¬ Set.InjOn (fun n : ℝ => stepW (1 / 100) 20 (2 * n) / stepW (1 / 100) 20 n)
      (Set.Ioi 0) := by
  sorry
```

Keep `stepW` and the signature verbatim; helper lemmas are fine; import only `Mathlib`.
`stepW η M τ` is verbatim the right-hand side of sibling target `equivWidth_stepProfile`
(the equivalent width of `1_[0,1] + η·1_[0,M]`); that sibling does the bridging, not this one.

## 2. Mathematics

Write `f n := stepW (1/100) 20 (2n) / stepW (1/100) 20 n`, `a := exp (-(101/100))`,
`b := exp (-(1/100))`. For a natural `n`, `exp (-(n (1 + 1/100))) = a^n` and
`exp (-(n/100)) = b^n`, so
`f n = ((1 - a^(2n)) + 19 (1 - b^(2n))) / ((1 - a^n) + 19 (1 - b^n))`.

Values (float): `f 1 = 1.50766`, `f 3 = 1.39051`, `f 10 = 1.58264`; interior minimum 1.3822 at
`n ≈ 2.42`. Threshold `c = 29/20`. With the enclosures `a ∈ [0.3642, 0.3643]`,
`b ∈ [0.99, 0.9901]` (true values 0.364219, 0.990050), exact rational interval arithmetic gives
`f 1 ∈ [1.5035, 1.5119]`, `f 3 ∈ [1.3843, 1.3967]`, `f 10 ∈ [1.5721, 1.5932]`: margin ≥ 0.05
around `29/20` everywhere. (Numerator decreases in `a^(2n), b^(2n)`, denominator decreases in
`a^n, b^n`, so corner evaluation is rigorous.)

Then: `f` is continuous on `[1,10]` (denominator > 0 for `n > 0`), `f 3 < 29/20 < f 1` gives
`x ∈ [1,3]` with `f x = 29/20` (IVT), `f 3 < 29/20 < f 10` gives `y ∈ [3,10]` with `f y = 29/20`;
injectivity forces `x = y = 3`, contradicting `f 3 < 29/20`.

Non-vacuity control: with `η = 0`, `f n = 1 + exp (-n)` is strictly decreasing, so the
statement is false for the flat kernel (repo `cogRatio_injOn`).

## 3. Mathlib lemmas (checked)

- `Real.add_one_le_exp (x) : x + 1 ≤ Real.exp x`; `Real.add_one_lt_exp : x ≠ 0 → x + 1 < exp x`
- `Real.exp_one_gt_d9 : 2.7182818283 < Real.exp 1`; `Real.exp_one_lt_d9 : Real.exp 1 < 2.7182818286`
- `Real.exp_nat_mul (x) (n : ℕ) : Real.exp (↑n * x) = Real.exp x ^ n`; `Real.exp_sub`,
  `Real.exp_neg`, `Real.exp_add`, `Real.exp_pos`, `Real.exp_lt_exp`,
  `Real.exp_lt_one_iff : Real.exp x < 1 ↔ x < 0`; also `Real.exp_bound`,
  `Real.quadratic_le_exp_of_nonneg : 0 ≤ x → 1 + x + x ^ 2 / 2 ≤ exp x` (not needed)
- `pow_le_pow_left₀`, `div_lt_iff₀`, `lt_div_iff₀`, `le_div_iff₀`, `div_le_iff₀`, `inv_le_comm₀`
- `intermediate_value_Icc : a ≤ b → ContinuousOn f (Icc a b) → Icc (f a) (f b) ⊆ f '' Icc a b`;
  `intermediate_value_Icc'` (same with `Icc (f b) (f a)`)
- alternative: `ContinuousOn.strictMonoOn_of_injOn_Icc' : a ≤ b → ContinuousOn f (Icc a b) →
  InjOn f (Icc a b) → StrictMonoOn f (Icc a b) ∨ StrictAntiOn f (Icc a b)`
- `ContinuousOn.div`, `ContinuousOn.mono`, `Set.Icc_subset_Icc`, `Real.continuous_exp`, `fun_prop`

## 4. Route (each block compiled)

Enclosure of `b` and `a`:
```lean
have hb : 0.99 ≤ Real.exp (-(1/100)) ∧ Real.exp (-(1/100)) ≤ 0.9901 := by
  constructor
  · have := Real.add_one_le_exp (-(1/100)); linarith
  · have h := Real.add_one_le_exp (1/100)
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]; linarith
-- given hb1 hb2:
have e : Real.exp (-(101/100)) = Real.exp (-(1/100)) / Real.exp 1 := by
  rw [← Real.exp_sub]; norm_num
have h1 := Real.exp_one_gt_d9; have h2 := Real.exp_one_lt_d9
rw [e]; constructor
· rw [le_div_iff₀ (by linarith)]; nlinarith   -- 0.3642 ≤ a
· rw [div_le_iff₀ (by linarith)]; nlinarith   -- a ≤ 0.3643
```
Power identities (12 exps: `n ∈ {1,2,3,6,10,20}` for `a` and `b`), e.g.
```lean
example : Real.exp (-(2 * 3 * (1 + 1/100))) = Real.exp (-(101/100)) ^ 6 := by
  rw [← Real.exp_nat_mul]; norm_num
```
Ratio step (same pattern for `n = 1` with `lt_div_iff₀` directly, and `n = 10` with
`u = a^10 ∈ [0, 0.3643^10]`, `v = b^10`):
```lean
example (a b : ℝ) (ha1 : 0.3642 ≤ a) (ha2 : a ≤ 0.3643) (hb1 : 0.99 ≤ b) (hb2 : b ≤ 0.9901) :
    ((1 - a^6) + 19*(1 - b^6)) / ((1 - a^3) + 19*(1 - b^3)) < 29/20 := by
  have hu1 : 0.3642^3 ≤ a^3 := pow_le_pow_left₀ (by norm_num) ha1 3
  have hu2 : a^3 ≤ 0.3643^3 := pow_le_pow_left₀ (by linarith) ha2 3
  have hv1 : 0.99^3 ≤ b^3 := pow_le_pow_left₀ (by norm_num) hb1 3
  have hv2 : b^3 ≤ 0.9901^3 := pow_le_pow_left₀ (by linarith) hb2 3
  have e6a : a^6 = (a^3)^2 := by ring
  have e6b : b^6 = (b^3)^2 := by ring
  rw [e6a, e6b]
  generalize a^3 = u at *; generalize b^3 = v at *
  norm_num at hu1 hu2 hv1 hv2
  rw [div_lt_iff₀ (by nlinarith)]; nlinarith
```
Continuity on `[1,10]`:
```lean
  apply ContinuousOn.div (by unfold stepW; fun_prop) (by unfold stepW; fun_prop)
  intro n hn
  unfold stepW
  have h1 : Real.exp (-(n * (1 + 1/100))) < 1 := Real.exp_lt_one_iff.2 (by nlinarith [hn.1])
  have h2 : Real.exp (-(n * (1/100))) < 1 := Real.exp_lt_one_iff.2 (by nlinarith [hn.1])
  nlinarith
```
Assembly (for any `f` with `hc : ContinuousOn f (Icc 1 10)`, `h1 : 29/20 < f 1`,
`h3 : f 3 < 29/20`, `h10 : 29/20 < f 10`):
```lean
  intro hinj
  obtain ⟨x, hx, hfx⟩ := intermediate_value_Icc' (by norm_num : (1:ℝ) ≤ 3)
    (hc.mono (Set.Icc_subset_Icc le_rfl (by norm_num))) ⟨h3.le, h1.le⟩
  obtain ⟨y, hy, hfy⟩ := intermediate_value_Icc (by norm_num : (3:ℝ) ≤ 10)
    (hc.mono (Set.Icc_subset_Icc (by norm_num) le_rfl)) ⟨h3.le, h10.le⟩
  have hxy : x = y := hinj (show (0:ℝ) < x by linarith [hx.1]) (show (0:ℝ) < y by linarith [hy.1])
    (hfx.trans hfy.symm)
  have hx3 : x = 3 := le_antisymm hx.2 (hxy ▸ hy.1)
  rw [hx3] at hfx; linarith
```
Suggested structure: helper lemmas `hb_encl`, `ha_encl`, `f_one`, `f_three`, `f_ten` (each
`29/20 < f k` or `f 3 < 29/20`), `f_contOn`, then the main theorem via the assembly block.

## 5. Pitfalls

- Glue: to evaluate `f 3`, first `show stepW (1/100) 20 (2*3) / stepW (1/100) 20 3 < 29/20`, then
  `simp only [stepW]`, then rewrite the four exps to `a^6, b^6, a^3, b^3` with `have` equations
  stated in the *current syntactic form* (check with `lean_goal`) BEFORE any `norm_num`, which
  turns `1/100` into `100⁻¹` and `2*3*(1+1/100)` into `303/50` and breaks the rewrites. Or prove
  each power identity against the normalized form, again via `rw [← Real.exp_nat_mul]; norm_num`.
- `(20 - 1)` appears as `M - 1`; `norm_num` gives `19`.
- `nlinarith` fails on raw degree-6/20 polynomials; generalize the powers first (as above).
- `Real.exp_lt_one`, `Real.exp_lt_one_of_neg`, `Real.one_sub_exp_neg_pos` do NOT exist.
- `rw [div_eq_mul_inv, ...]` also hits the literal `101/100`; use `← Real.exp_sub`.
- Do not try to prove global monotonicity facts on `(0,∞)`; only `[1,10]` and three points.

## 6. Scope reading

PURE-MATH: a counterexample about an explicit real function (`η = 1/100`, `M = 20`, `r = 2`).
It is the analytic core of FT-20 (b). It says nothing about Voigt profiles (numerics only,
dropped by the audit) and does not prove the log-slope criterion (dropped, grade C).
