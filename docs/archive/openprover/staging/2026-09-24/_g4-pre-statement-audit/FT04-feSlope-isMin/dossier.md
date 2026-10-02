# FT04-feSlope-isMin: the fixed-effects slope and its group intercepts minimize the weighted RSS

*Planning dossier for the proof queue. Source: 2026-09-24 deep audit, frontier FT-04 queue
item 7 (`feSlope_isMin`); verifier verdict KEEP, grade A. Priority 23 in group g1. Names checked
with `#check` on the pinned toolchain (Lean/mathlib v4.33.1), 2026-09-24. A complete candidate
following the route below passed `verify.py` (compile, leanchecker kernel replay, axioms
`[Classical.choice, Quot.sound, propext]`, elaborated type identical) on 2026-09-24:
`staging/2026-09-24/_g1-scratch-proofs/FT04-feSlope-isMin.lean`.*

## 1. Goal

```lean
theorem feSlope_isMin (grp : ι → κ) (w x y : ι → ℝ) (hw : ∀ k, 0 < w k)
    (hSS : 0 < withinSS grp w x) (a : κ → ℝ) (β : ℝ) :
    ∑ k, w k * (y k - (gMean grp w y (grp k) - feSlope grp w x y * gMean grp w x (grp k))
        - feSlope grp w x y * x k) ^ 2
      ≤ ∑ k, w k * (y k - a (grp k) - β * x k) ^ 2
```

in `namespace Plan.FT04`, `variable {ι κ : Type*} [Fintype ι] [DecidableEq κ]`, `open Finset`.
Fully qualified name: `Plan.FT04.feSlope_isMin`. Imports: `Mathlib` only. `κ` is NOT a
`Fintype`.

Meaning: with `β̂ = feSlope` and group intercepts `â_e = ȳ_e − β̂ x̄_e`, the weighted residual sum
of squares of the model `y k = a (grp k) + β x k` is minimal at `(â, β̂)`.

## 2. Definitions (verbatim; must be kept verbatim)

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

## 3. Proof route (Pythagorean split; checked)

Notation: `x̃ k = x k − gMean grp w x (grp k)`, `ỹ k = y k − gMean grp w y (grp k)`,
`C = withinCross grp w x y = ∑ w x̃ ỹ`, `S = withinSS grp w x = ∑ w x̃ x̃`, `b̂ = C / S`,
`δ e = gMean grp w y e − a e − β * gMean grp w x e`.

1. Left side: termwise `y − (ȳ − b̂ x̄) − b̂ x = ỹ − b̂ x̃` (`Finset.sum_congr` + `ring`).
2. Right side: termwise `y − a − β x = (ỹ − β x̃) + δ(grp k)`, so
   `RSS(a, β) = ∑ w (ỹ − β x̃)² + 2 (∑ w ỹ δ(grp k) − β ∑ w x̃ δ(grp k)) + ∑ w δ(grp k)²`.
3. Cross terms vanish by the crux (helper B) with `f := y` and `f := x`, `h := δ`.
4. Quadratic: `∑ w (ỹ − b x̃)² = ∑ w ỹ² − 2 b C + b² S` for every `b` (helper C).
5. With `b̂ S = C` (from `feSlope`, `div_mul_cancel₀`, `hSS.ne'`):
   `Q(β) − Q(b̂) = S (β − b̂)² ≥ 0`, and `∑ w δ² ≥ 0`; `nlinarith` closes it.

Helpers (all checked):

```lean
theorem fiber_dev_sum_zero (grp : ι → κ) (w f : ι → ℝ) (hw : ∀ k, 0 < w k) (e : κ) :
    ∑ k ∈ univ.filter (fun k => grp k = e), w k * (f k - gMean grp w f e) = 0 := by
  rcases (univ.filter (fun k => grp k = e)).eq_empty_or_nonempty with h | h
  · rw [h, sum_empty]
  · have hpos : 0 < ∑ k ∈ univ.filter (fun k => grp k = e), w k :=
      sum_pos (fun k _ => hw k) h
    simp only [mul_sub, sum_sub_distrib, ← sum_mul, gMean]
    rw [mul_div_cancel₀ _ hpos.ne', sub_self]

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

theorem within_quad (grp : ι → κ) (w x y : ι → ℝ) (b : ℝ) :
    ∑ k, w k * ((y k - gMean grp w y (grp k)) - b * (x k - gMean grp w x (grp k))) ^ 2
      = ∑ k, w k * (y k - gMean grp w y (grp k)) ^ 2 - 2 * b * withinCross grp w x y
        + b ^ 2 * withinSS grp w x := by
  unfold withinSS withinCross
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun k _ => by ring)
```

Main body (checked):

```lean
  set bh := feSlope grp w x y with hbh
  have hC : bh * withinSS grp w x = withinCross grp w x y := by
    rw [hbh, feSlope, div_mul_cancel₀ _ hSS.ne']
  have hL : ∑ k, w k * (y k - (gMean grp w y (grp k) - bh * gMean grp w x (grp k)) - bh * x k) ^ 2
      = ∑ k, w k * ((y k - gMean grp w y (grp k)) - bh * (x k - gMean grp w x (grp k))) ^ 2 :=
    Finset.sum_congr rfl (fun k _ => by ring)
  set δ : κ → ℝ := fun e => gMean grp w y e - a e - β * gMean grp w x e with hδ
  have hR : ∑ k, w k * (y k - a (grp k) - β * x k) ^ 2
      = ∑ k, (w k * ((y k - gMean grp w y (grp k)) - β * (x k - gMean grp w x (grp k))) ^ 2
        + 2 * (w k * (y k - gMean grp w y (grp k)) * δ (grp k)
          - β * (w k * (x k - gMean grp w x (grp k)) * δ (grp k)))
        + w k * δ (grp k) ^ 2) :=
    Finset.sum_congr rfl (fun k _ => by simp only [hδ]; ring)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib,
    ← Finset.mul_sum] at hR
  rw [hL, hR, sum_dev_mul_groupConst grp w y hw δ, sum_dev_mul_groupConst grp w x hw δ,
    within_quad, within_quad]
  have hδnn : 0 ≤ ∑ k, w k * δ (grp k) ^ 2 :=
    Finset.sum_nonneg (fun k _ => mul_nonneg (hw k).le (sq_nonneg _))
  rw [← hC]
  nlinarith [mul_nonneg hSS.le (sq_nonneg (β - bh))]
```

## 4. Lemmas (checked)

- `Finset.sum_fiberwise_of_maps_to : (∀ i ∈ s, g i ∈ t) → ∀ f, ∑ j ∈ t, ∑ i ∈ s with g i = j, f i = ∑ i ∈ s, f i`
  (`Finset.sum_fiberwise` needs `[Fintype κ]`, which is absent)
- `Finset.mem_image_of_mem`, `Finset.mem_filter`, `Finset.eq_empty_or_nonempty`, `Finset.sum_pos`,
  `Finset.sum_eq_zero`, `Finset.sum_congr`, `Finset.sum_add_distrib`, `Finset.sum_sub_distrib`,
  `Finset.mul_sum`, `Finset.sum_mul`, `Finset.sum_nonneg`
- `mul_div_cancel₀` (for `B * (A / B) = A`), `div_mul_cancel₀ : b ≠ 0 → a / b * b = a`
- tactics: `ring`, `nlinarith`, `set … with`

## 5. Pitfalls

- `β̂` (with a combining hat) is NOT a valid Lean identifier; name the slope `bh`.
- Expanding the right side: build the termwise identity first, then distribute the sum
  (`sum_add_distrib`, `← mul_sum`, `sum_sub_distrib`) in the hypothesis; rewriting the goal in
  the other direction fails to match (`?a * ∑ …` pattern not found; this was hit).
- Keep `gMean` folded; never unfold it in the main proof.
- `hSS` is used only to cancel `b̂ S = C`. The inequality is expected to hold at `SS_W = 0` too
  (0/0 convention), but that is not part of the statement.
- Candidate may not add imports; keep definitions and signature verbatim; helpers are allowed.

## 6. Scope and provenance

- Two-axis tag prediction: relation PURE-MATH; definitions PURE-MATH; published PURE-MATH.
- Pipeline link: companion `_fit_common_boltzmann_plane` (`cflibs/inversion/solve/iterative.py`,
  main b142ae25, ~l.1703-1806) centres each element's lines on their weighted means and returns
  `∑ w x̃ ỹ / ∑ w x̃²`, refusing when the denominator is not positive. With capped weights the
  statement is WLS for the capped weights. This closes audit gap RF-16 (the certificates C1-C3
  certify the pooled design, not the estimator the solver runs).
- Numerics (orchestrator, `_plan/numcheck2.py`): 0 violations over 3000 random grouped designs ×
  20 competitors.
- Literature (whitelist rows 50, 48): Aitken 1935, Proc. Roy. Soc. Edinburgh 55, 42-48;
  Aguilera & Aragón 2007, Spectrochim. Acta B 62, 378.
- Novelty: 0 hits for `gMean|withinCross|withinSS|feSlope` in `CflibsFormal/`, `upstream/` on main
  (fb1681d). Nearest ungrouped analogue: `CflibsFormal.ols_minimizes_rss`
  (`LeastSquaresFit.lean:145`, via `rss_decomposition`), not importable here.
- Tactic battery (simp, linarith, positivity, nlinarith, field_simp, aesop, exact?,
  unfold+simp+ring_nf): none closes it.
