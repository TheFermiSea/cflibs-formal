# FT04-fe-identifiable-iff: the common slope of a fixed-effects design is identifiable iff SS_W > 0

*Planning dossier for the proof queue. Source: 2026-09-24 deep audit, frontier FT-04, queue
items 4-6 (`withinCross_groupConst`, `withinSS_eq_zero_iff`, `fe_identifiable_iff`); verifier
verdict KEEP, grade A. Priority 1 in group g1. Every lemma name below was checked with `#check`
against the pinned toolchain (Lean/mathlib v4.33.1) on 2026-09-24. A complete candidate
following the route below passed `verify.py` (compile, leanchecker kernel replay, axioms
`[Classical.choice, Quot.sound, propext]`, elaborated type identical) on 2026-09-24:
`staging/2026-09-24/_g1-scratch-proofs/FT04-fe-identifiable-iff.lean`.*

## 1. Goal

```lean
theorem fe_identifiable_iff (grp : ι → κ) (w x : ι → ℝ) (hw : ∀ k, 0 < w k) :
    (∀ (a a' : κ → ℝ) (β β' : ℝ),
        (∀ k, a (grp k) + β * x k = a' (grp k) + β' * x k) → β = β')
      ↔ 0 < withinSS grp w x
```

in `namespace Plan.FT04`, with `variable {ι κ : Type*} [Fintype ι] [DecidableEq κ]` and
`open Finset`. Fully qualified name: `Plan.FT04.fe_identifiable_iff`. The file imports only
`Mathlib`. **`κ` is NOT a `Fintype`** (only `DecidableEq`).

Informally: lines `k` belong to groups `grp k` (elements); the noiseless model is
`y k = a (grp k) + β * x k` with one intercept per group and one common slope. The slope is
determined by the noiseless ordinates iff the weighted within-group sum of squares of `x` is
positive, i.e. iff `x` is not constant on every group.

## 2. Definitions (verbatim from the statement file; must be kept verbatim)

```lean
noncomputable def gMean (grp : ι → κ) (w f : ι → ℝ) (e : κ) : ℝ :=
  (∑ k ∈ univ.filter (fun k => grp k = e), w k * f k) /
    ∑ k ∈ univ.filter (fun k => grp k = e), w k

noncomputable def withinCross (grp : ι → κ) (w x y : ι → ℝ) : ℝ :=
  ∑ k, w k * (x k - gMean grp w x (grp k)) * (y k - gMean grp w y (grp k))

noncomputable def withinSS (grp : ι → κ) (w x : ι → ℝ) : ℝ := withinCross grp w x x

noncomputable def feSlope (grp : ι → κ) (w x y : ι → ℝ) : ℝ :=
  withinCross grp w x y / withinSS grp w x
```

`feSlope` is not used by this theorem (it is part of the shared FT-04 block). In goals, Lean
prints `∑ k ∈ univ.filter (fun k => grp k = e), f k` as `∑ k with grp k = e, f k`.

## 3. Proof route

Write `x̄ k := gMean grp w x (grp k)` and `d k := x k - x̄ k`.

**Helper A (tested, compiles, axiom-clean):** within each group, weighted deviations from the
group mean sum to zero.

```lean
theorem fiber_dev_sum_zero (grp : ι → κ) (w f : ι → ℝ) (hw : ∀ k, 0 < w k) (e : κ) :
    ∑ k ∈ univ.filter (fun k => grp k = e), w k * (f k - gMean grp w f e) = 0 := by
  rcases (univ.filter (fun k => grp k = e)).eq_empty_or_nonempty with h | h
  · rw [h, sum_empty]
  · have hpos : 0 < ∑ k ∈ univ.filter (fun k => grp k = e), w k :=
      sum_pos (fun k _ => hw k) h
    simp only [mul_sub, sum_sub_distrib, ← sum_mul, gMean]
    rw [mul_div_cancel₀ _ hpos.ne', sub_self]
```

**Helper B, the crux (tested, compiles, axiom-clean):** weighted within-deviations are
orthogonal to every group-constant function.

```lean
theorem sum_dev_mul_groupConst (grp : ι → κ) (w f : ι → ℝ) (hw : ∀ k, 0 < w k)
    (h : κ → ℝ) :
    ∑ k, w k * (f k - gMean grp w f (grp k)) * h (grp k) = 0 := by
  rw [← sum_fiberwise_of_maps_to (s := univ) (t := univ.image grp)
    (fun i _ => mem_image_of_mem grp (mem_univ i))]
  refine sum_eq_zero (fun e _ => ?_)
  have : ∀ k ∈ univ.filter (fun k => grp k = e),
      w k * (f k - gMean grp w f (grp k)) * h (grp k)
        = (w k * (f k - gMean grp w f e)) * h e := by
    intro k hk
    rw [(mem_filter.mp hk).2]
  rw [sum_congr rfl this, ← sum_mul, fiber_dev_sum_zero grp w f hw e, zero_mul]
```

Both helpers go in the candidate file (after the definitions, before the theorem).

**(⇐) `0 < withinSS → identifiable`.** Assume `hS : 0 < withinSS grp w x` and
`heq : ∀ k, a (grp k) + β * x k = a' (grp k) + β' * x k`. Put `δ := β - β'` and
`c e := a' e - a e`, so `δ * x k = c (grp k)` for every `k` (from `heq` by `linarith`).
Then

```
δ * withinSS = ∑ k, w k * d k * (δ * x k) - δ * ∑ k, w k * d k * x̄ k
             = ∑ k, w k * d k * c (grp k) - δ * ∑ k, w k * d k * gMean grp w x (grp k)
             = 0 - δ * 0                       (Helper B twice: h := c, h := gMean grp w x)
```

(the first line is termwise `w*d*d*δ = w*d*(δ*x) - δ*(w*d*x̄)` since `d = x - x̄`; use
`Finset.mul_sum`, `Finset.sum_sub_distrib`, `Finset.sum_congr` + `ring`). So `δ * withinSS = 0`
with `withinSS ≠ 0`, hence `δ = 0` (`mul_eq_zero`, or `mul_right_cancel₀`), i.e. `β = β'`.
This direction never needs "the mean of a constant is the constant".

**(⇒) identifiable → `0 < withinSS`**, by contraposition. Suppose `¬ 0 < withinSS grp w x`.
1. `0 ≤ withinSS`: unfold `withinSS withinCross`; each term is `w k * d k * d k`, nonnegative
   by `mul_nonneg (hw k).le (mul_self_nonneg _)` after reassociating (`mul_assoc`).
2. So `withinSS = 0`, and by `Finset.sum_eq_zero_iff_of_nonneg` every term vanishes:
   `w k * d k * d k = 0`, hence `d k = 0` (`w k ≠ 0`; `mul_self_eq_zero`), i.e.
   `x k = gMean grp w x (grp k)` for all `k`.
3. Apply the hypothesis with `a := fun e => -gMean grp w x e`, `β := 1`, `a' := fun _ => 0`,
   `β' := 0`. Its premise is `∀ k, -gMean grp w x (grp k) + 1 * x k = 0 + 0 * x k`, which holds
   by step 2 (`simp` / `linarith`). The conclusion `1 = 0` is false (`one_ne_zero`).

Main body (checked; place helpers A and B before the theorem):

```lean
  constructor
  · intro hid
    by_contra hneg
    have hnn : 0 ≤ withinSS grp w x := by
      unfold withinSS withinCross
      exact Finset.sum_nonneg (fun k _ => by
        rw [mul_assoc]; exact mul_nonneg (hw k).le (mul_self_nonneg _))
    have h0 : withinSS grp w x = 0 := le_antisymm (not_lt.mp hneg) hnn
    unfold withinSS withinCross at h0
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun k _ => by
      rw [mul_assoc]; exact mul_nonneg (hw k).le (mul_self_nonneg _))] at h0
    have hx : ∀ k, x k = gMean grp w x (grp k) := by
      intro k
      have := h0 k (Finset.mem_univ k)
      rw [mul_assoc] at this
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h (hw k).ne'
      · have := mul_self_eq_zero.mp h; linarith
    have := hid (fun e => -gMean grp w x e) (fun _ => 0) 1 0 (fun k => by rw [← hx k]; ring)
    exact one_ne_zero this
  · intro hS a a' β β' heq
    have hc : ∀ k, (β - β') * x k = a' (grp k) - a (grp k) := fun k => by linarith [heq k]
    have hB1 := sum_dev_mul_groupConst grp w x hw (fun e => a' e - a e)
    have hB2 := sum_dev_mul_groupConst grp w x hw (gMean grp w x)
    have key : (β - β') * withinSS grp w x = 0 := by
      have : (β - β') * withinSS grp w x
          = ∑ k, w k * (x k - gMean grp w x (grp k)) * (a' (grp k) - a (grp k))
            - (β - β') * ∑ k, w k * (x k - gMean grp w x (grp k)) * gMean grp w x (grp k) := by
        unfold withinSS withinCross
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [← hc k]; ring
      rw [this, hB1, hB2]; ring
    rcases mul_eq_zero.mp key with h | h
    · linarith
    · exact absurd h hS.ne'
```

Total size: about 55 lines including the two helpers.

## 4. Lemmas (all checked with `#check`)

mathlib:
- `Finset.sum_fiberwise_of_maps_to : (∀ i ∈ s, g i ∈ t) → ∀ f, ∑ j ∈ t, ∑ i ∈ s with g i = j, f i = ∑ i ∈ s, f i`
  (needs `[DecidableEq κ]`, no `Fintype κ`).
- `Finset.sum_fiberwise` requires `[Fintype κ]`, **not available here**; use the `_of_maps_to`
  form with `t := univ.image grp` and `Finset.mem_image_of_mem`.
- `Finset.mem_filter : a ∈ Finset.filter p s ↔ a ∈ s ∧ p a`
- `Finset.eq_empty_or_nonempty`, `Finset.sum_empty`, `Finset.sum_pos : (∀ i ∈ s, 0 < f i) → s.Nonempty → 0 < ∑ i ∈ s, f i`
- `Finset.sum_eq_zero_iff_of_nonneg : (∀ i ∈ s, 0 ≤ f i) → (∑ i ∈ s, f i = 0 ↔ ∀ i ∈ s, f i = 0)`
- `Finset.sum_eq_zero`, `Finset.sum_congr`, `Finset.sum_add_distrib`, `Finset.sum_sub_distrib`,
  `Finset.mul_sum : a * ∑ i ∈ s, f i = ∑ i ∈ s, a * f i`, `Finset.sum_mul`, `Finset.sum_nonneg`
- `mul_div_cancel₀`-style cancellation: in helper A the goal after `simp only` is
  `A - B * (A / B) = 0`; `mul_div_cancel₀ _ hB` rewrites `B * (A / B)` to `A`
  (the `div_mul_cancel₀` form `A / B * B` does NOT match; this was tried).
- `mul_self_nonneg`, `mul_nonneg`, `mul_self_eq_zero`, `mul_eq_zero`, `one_ne_zero`

Repo: nothing is imported besides Mathlib. The nearest in-repo pattern is
`CflibsFormal.OLS.centered_sum_zero` (ungrouped, unweighted), which cannot be imported here.

## 5. Pitfalls

- `κ` has no `Fintype` instance: `∑ e : κ, …` does not typecheck; fibre over `univ.image grp`.
- Empty groups: `gMean` of an empty group is `0/0 = 0`. It never matters at `e = grp k`
  (that group contains `k`), and helper A handles the empty case separately.
- Do not `unfold gMean` globally at the start: the goal becomes unreadable. Keep `gMean`
  folded and reason with helpers A/B.
- `withinSS grp w x` unfolds to `withinCross grp w x x`, i.e. terms `w k * d k * d k`
  (not `w k * d k ^ 2`); rewrite with `sq` or `pow_two` if needed.
- The candidate may not add imports and must keep the four definitions and the theorem
  signature verbatim; extra helper lemmas are allowed.

## 6. Scope and provenance

- Two-axis tag prediction: relation PURE-MATH; definitions PURE-MATH; published PURE-MATH.
- The physics binding (`x = E + IP·(z−1)`, groups = elements, LTE, one `T`, IPD off/frozen) is
  REDUCED and belongs to the landing docstring.
- Non-vacuity witnesses: `x = (3,3,5,5)`, `grp = (0,0,1,1)`, `w = 1` gives `withinSS = 0`
  (not identifiable) while the pooled spread is `4`; `x = (1,2,3,4)` with the same groups gives
  `withinSS = 1 > 0` (identifiable).
- Pipeline consumer: companion `_fit_common_boltzmann_plane`
  (`cflibs/inversion/solve/iterative.py`, main b142ae25, ~l.1703-1806) computes
  `∑ w x̃ ỹ / ∑ w x̃²` with per-element weighted centring and returns no fit when the
  denominator is not positive; the wired certificates C1-C3 (`Certificates.lean:74, 97, 125`)
  test the pooled design instead (audit RF-16).
- Literature (whitelist rows 48, 50): Aguilera & Aragón 2007, Spectrochim. Acta B 62, 378;
  Aitken 1935, Proc. Roy. Soc. Edinburgh 55, 42.
- Novelty: `rg -c -i 'gMean|withinCross|withinSS|feSlope|fe_identifiable|fixed.effect'` over
  `CflibsFormal/` and `upstream/` on main (fb1681d): 0 hits (positive control
  `rg -c olsSlope CflibsFormal/OLS.lean` = 24).
