# FT13-inv-sub-inv-expm1-bounds: `0 < 1/τ - 1/(e^τ - 1) < 1/2` for `τ > 0`

Planning dossier for the proof queue (2026-09-24 audit, frontier FT-13 (b), queue item 3, split
out as its own real-analysis leaf). Mathlib only; no repo definitions. Every Mathlib name was
checked with `#check` against the pinned Mathlib (v4.33.1) on 2026-09-24.

## 1. Goal

```lean
import Mathlib

namespace Plan.FT13

theorem inv_sub_inv_exp_sub_one_mem {τ : ℝ} (hτ : 0 < τ) :
    0 < 1 / τ - 1 / (Real.exp τ - 1) ∧ 1 / τ - 1 / (Real.exp τ - 1) < 1 / 2 := by
  sorry
```

The audited file is `statement.lean` here; keep the signature verbatim; helper lemmas may be
added above it; no imports beyond `Mathlib`.

Context (not needed for the proof): for `τ > 0`, `d/dτ log((1 - e^(-τ))/τ) = 1/(e^τ - 1) - 1/τ`,
so this is the statement that the log of the slab self-absorption factor has slope in
`(-1/2, 0)`. Numerics: the middle expression is 0.49999992 at `τ = 1e-6`, 0.418 at `τ = 1`,
0.0333 at `τ = 30`. Both bounds are strict and sharp in the limit, so no slack is available: a
proof must go through an exact inequality, not a numerical estimate.

## 2. Mathematical proof

Let `E := e^τ - 1`. `E > τ > 0` because `τ + 1 < e^τ` (`Real.add_one_lt_exp`, needs `τ ≠ 0`).

**Lower bound.** `τ < E` with `0 < τ` gives `1/E < 1/τ` (`one_div_lt_one_div_of_lt`), so the
difference is positive.

**Upper bound.** Multiply by `2τE > 0`: `1/τ - 1/E < 1/2 ⟺ 2E - 2τ < τE
⟺ e^τ (2 - τ) < 2 + τ ⟺ f τ > 0` where

    f t := Real.exp t * (t - 2) + t + 2.

`f 0 = 1·(-2) + 0 + 2 = 0`, and `f' t = e^t (t - 2) + e^t + 1 = e^t (t - 1) + 1`.
For `t > 0`: `1 - t < e^(-t)` (`Real.one_sub_lt_exp_neg`, `t ≠ 0`); multiplying by `e^t > 0`,
`e^t (1 - t) < 1`, i.e. `f' t > 0`. So `f` is strictly increasing on `[0, ∞)`
(`strictMonoOn_of_hasDerivWithinAt_pos` with `D = Set.Ici 0`, `interior (Set.Ici 0) =
Set.Ioi 0`), hence `f τ > f 0 = 0`.

Then close the upper bound by clearing denominators: with `hτ : 0 < τ`, `hE : 0 < E`,
`rw [div_sub_div _ _ hτ.ne' hE.ne', div_lt_div_iff₀ (by positivity) two_pos]` (or prove
`1/τ - 1/E = (E - τ)/(τ * E)` by `field_simp`) and finish with `nlinarith [f τ > 0, …]`.

Alternative for the upper bound (no derivatives): for `τ ≥ 2`, `f τ ≥ τ + 2 > 0` directly
(`e^τ (τ - 2) ≥ 0`). For `0 < τ < 2`, with `u = τ/2 ∈ (0, 1)`,
`Real.hasSum_log_sub_log_of_abs_lt_one` gives
`log(1 + u) - log(1 - u) = ∑ 2 u^(2k+1)/(2k+1) > 2u = τ` (keep two terms of the positive series),
so `(1 + u)/(1 - u) > e^τ`, i.e. `e^τ (2 - τ) < 2 + τ`. The derivative route is shorter.

## 3. Suggested Lean decomposition

1. `exp_mul_one_sub_lt_one {x : ℝ} (hx : 0 < x) : Real.exp x * (1 - x) < 1`
   (this exact lemma exists on main in `CflibsFormal/CurveOfGrowth.lean`, which this target does
   NOT import; re-prove it, the proof is four lines):

```lean
theorem exp_mul_one_sub_lt_one {x : ℝ} (hx : 0 < x) :
    Real.exp x * (1 - x) < 1 := by
  have h1 : 1 - x < Real.exp (-x) := Real.one_sub_lt_exp_neg hx.ne'
  have h2 : Real.exp x * (1 - x) < Real.exp x * Real.exp (-x) :=
    mul_lt_mul_of_pos_left h1 (Real.exp_pos x)
  rwa [← Real.exp_add, add_neg_cancel, Real.exp_zero] at h2
```

2. `f_hasDerivAt (t : ℝ) : HasDerivAt (fun t => Real.exp t * (t - 2) + t + 2)
   (Real.exp t * (t - 2) + Real.exp t * 1 + 1) t`, from
   `((Real.hasDerivAt_exp t).mul ((hasDerivAt_id t).sub_const 2)).add_const …` style
   composition (the exact shape Lean produces may differ; use `convert … using 1; ring`).
3. `f_strictMonoOn : StrictMonoOn (fun t => Real.exp t * (t - 2) + t + 2) (Set.Ici 0)` via
   `strictMonoOn_of_hasDerivWithinAt_pos (convex_Ici 0) (by fun_prop / continuity)
   (fun x hx => (f_hasDerivAt x).hasDerivWithinAt) (fun x hx => …)`, rewriting
   `interior_Ici` in `hx` to get `0 < x`, then `nlinarith [exp_mul_one_sub_lt_one hx]`.
4. `f_pos (hτ : 0 < τ) : 0 < Real.exp τ * (τ - 2) + τ + 2` from step 3 at `0 < τ` and
   `Real.exp_zero`.
5. Main: `constructor`; lower bound as in §2; upper bound by clearing denominators and
   `nlinarith [f_pos hτ]`.

## 4. Mathlib lemmas (signatures checked)

- `Real.add_one_lt_exp : x ≠ 0 → x + 1 < Real.exp x`
- `Real.one_sub_lt_exp_neg : x ≠ 0 → 1 - x < Real.exp (-x)`
- `Real.one_lt_exp_iff : 1 < Real.exp x ↔ 0 < x`
- `one_div_lt_one_div_of_lt : 0 < a → a < b → 1 / b < 1 / a`
- `strictMonoOn_of_hasDerivWithinAt_pos {D : Set ℝ} (hD : Convex ℝ D) {f f' : ℝ → ℝ}
  (hf : ContinuousOn f D) (hf' : ∀ x ∈ interior D, HasDerivWithinAt f (f' x) (interior D) x)
  (hf'₀ : ∀ x ∈ interior D, 0 < f' x) : StrictMonoOn f D`
  (`Mathlib/Analysis/Calculus/Deriv/MeanValue.lean:395`)
- `strictMonoOn_of_deriv_pos {D} (hD : Convex ℝ D) (hf : ContinuousOn f D)
  (hf' : ∀ x ∈ interior D, 0 < deriv f x) : StrictMonoOn f D` (alternative with `deriv`)
- `interior_Ici : interior (Set.Ici a) = Set.Ioi a`; `convex_Ici`.
- `Real.hasDerivAt_exp`, `hasDerivAt_id`, `HasDerivAt.mul`, `HasDerivAt.add`,
  `HasDerivAt.sub_const`, `HasDerivAt.add_const`, `HasDerivAt.hasDerivWithinAt`.
- `div_lt_div_iff₀ : 0 < b → 0 < d → (a / b < c / d ↔ a * d < c * b)`, `div_sub_div`.
- `Real.hasSum_log_sub_log_of_abs_lt_one {x : ℝ} (h : |x| < 1) : HasSum (fun k : ℕ =>
  2 * (1 / (2 * k + 1)) * x ^ (2 * k + 1)) (log (1 + x) - log (1 - x))` (alternative route).
- There is NO `Real.tanh_lt_self` in this Mathlib (checked); do not search for it.

## 5. Pitfalls

- Lean's `1 / 0 = 0`: keep `hτ.ne'` and `(E > 0).ne'` in context before `field_simp`.
- `nlinarith` alone cannot see `exp`-facts; always pass the transcendental inequality
  (`Real.add_one_lt_exp hτ.ne'`, `f_pos hτ`) as a hint term.
- The derivative-sign step `0 < e^x (x - 1) + 1` is exactly `exp_mul_one_sub_lt_one` rearranged
  (`e^x (1 - x) < 1`).
- Budget: moderate. The only analytic content is one monotonicity-from-derivative argument.
