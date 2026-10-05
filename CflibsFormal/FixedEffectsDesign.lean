/-
Copyright (c) 2026 Brian Squires. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Squires
-/
import Mathlib

/-!
# CF-LIBS formalization — the fixed-effects (element-dummy) weighted Boltzmann design

The companion solver fits one common Boltzmann (Saha–Boltzmann) plane to the lines of several
elements with one free intercept per element: each element's lines are centred on their own
weighted means and one slope is fitted to the pooled centred points
(`_fit_common_boltzmann_plane`). The certificates C1–C3 of `Certificates` test the *pooled*
energy spread, which can be positive while the within-element spread is zero. This module
formalizes the grouped, weighted design the solver actually runs (frontier FT-04 of the
2026-09-24 audit).

## Main definitions

* `gMean`: the weighted mean over the lines of one group (element).
* `withinCross`, `withinSS`: the weighted within-group cross product and sum of squares `SS_W`.
* `feSlope`: the fixed-effects slope `withinCross / withinSS`.

## Main results

* `fe_identifiable_iff`: with positive weights, the common slope is identifiable from noiseless
  ordinates `a (grp k) + β * x k` exactly when `0 < SS_W`.
* `feSlope_add_smul`: `feSlope` is linear in the ordinates (no hypotheses).
* `feSlope_isMin`: `feSlope` with its implied group intercepts minimizes the weighted residual
  sum of squares of the one-intercept-per-group model.
* `feSlope_rss_split`: the residual sum of squares of any competitor is the estimator's plus
  `SS_W·(β − β̂)²` plus the weighted squared intercept offsets.
* `feSlope_unique_min`: so the minimizer is unique, on the slope and on the intercept of every
  group that contains a line (the intercept of a group with no line is free).

## Scope

All five results are `PURE-MATH`: weighted regression algebra over a grouped finite design; no
physics definition is used. The physics reading (abscissa `E + IP·(z − 1)`, groups = elements,
LTE with one temperature, IPD off or frozen) is a reduced model and is not part of any statement
here.

## Literature

Aguilera & Aragón 2007 (Spectrochim. Acta B 62, 378) for the multi-element common-slope
Saha–Boltzmann plot; Aitken 1935 (Proc. Roy. Soc. Edinburgh 55, 42) for weighted (generalized)
least squares.
-/

open Finset

namespace CflibsFormal

variable {ι κ : Type*} [Fintype ι] [DecidableEq κ]

/-- **Weighted group mean.**
`gMean grp w f e = (∑_{k : grp k = e} w k * f k) / ∑_{k : grp k = e} w k`,
the `w`-weighted mean of `f` over the lines `k` assigned to group `e`.
CF-LIBS reading: `ι` indexes the emission lines kept by the solver, `grp` assigns each line to its
element (optionally element and ionization stage), `w` are the per-line weights (the pipeline uses
capped inverse variances `1/σ_y²`, all strictly positive), and `f` is an abscissa (upper-level
energy, or the IP-shifted `E + IP·(z−1)`) or a Boltzmann-plot ordinate.
Convention: for a group containing no line the quotient is `0/0 = 0` (Lean's totalized division).
When every weight is positive, a group that contains some line has a positive weight sum, so the
convention is never used at `e = grp k`. -/
noncomputable def gMean (grp : ι → κ) (w f : ι → ℝ) (e : κ) : ℝ :=
  (∑ k ∈ univ.filter (fun k => grp k = e), w k * f k) /
    ∑ k ∈ univ.filter (fun k => grp k = e), w k

/-- **Weighted within-group cross product.**
`withinCross grp w x y = ∑_k w k * (x k − x̄_{grp k}) * (y k − ȳ_{grp k})`, where `x̄_e`, `ȳ_e` are
the weighted group means (`gMean`). This is the numerator of the fixed-effects (element-dummy)
least-squares slope: each line is centred on the mean of its own group, so any per-group intercept
drops out. -/
noncomputable def withinCross (grp : ι → κ) (w x y : ι → ℝ) : ℝ :=
  ∑ k, w k * (x k - gMean grp w x (grp k)) * (y k - gMean grp w y (grp k))

/-- **Weighted within-group sum of squares** `SS_W = ∑_k w k * (x k − x̄_{grp k})²`, i.e.
`withinCross grp w x x`. It is the denominator of the fixed-effects slope and, with positive
weights, it vanishes exactly when `x` is constant on every group. -/
noncomputable def withinSS (grp : ι → κ) (w x : ι → ℝ) : ℝ := withinCross grp w x x

/-- **Fixed-effects (within-element) slope** `β̂ = withinCross grp w x y / withinSS grp w x`: the
weighted least-squares common slope of the model `y k = a (grp k) + β * x k` with one free
intercept per group. It is the formula of the companion solver's common Boltzmann plane
(`_fit_common_boltzmann_plane`, `cflibs/inversion/solve/iterative.py`, per-element weighted
centring, then `∑ w x̃ ỹ / ∑ w x̃²`). Totalized division: `β̂ = 0` when `SS_W = 0`. -/
noncomputable def feSlope (grp : ι → κ) (w x y : ι → ℝ) : ℝ :=
  withinCross grp w x y / withinSS grp w x


/-- helper 1: on each group, weighted deviations from the group mean sum to zero. -/
private theorem fiber_dev_sum_zero (grp : ι → κ) (w f : ι → ℝ) (hw : ∀ k, 0 < w k) (e : κ) :
    ∑ k ∈ univ.filter (fun k => grp k = e), w k * (f k - gMean grp w f e) = 0 := by
  rcases (univ.filter (fun k => grp k = e)).eq_empty_or_nonempty with h | h
  · rw [h, sum_empty]
  · have hpos : 0 < ∑ k ∈ univ.filter (fun k => grp k = e), w k :=
      sum_pos (fun k _ => hw k) h
    simp only [mul_sub, sum_sub_distrib, ← sum_mul, gMean]
    rw [mul_div_cancel₀ _ hpos.ne', sub_self]

/-- helper 2 (the crux): weighted within-deviations are orthogonal to any group-constant. -/
private theorem sum_dev_mul_groupConst (grp : ι → κ) (w f : ι → ℝ) (hw : ∀ k, 0 < w k)
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

/-- **The common slope of a fixed-effects design is identifiable iff `SS_W > 0`.**

Model: each line `k` has a noiseless ordinate `a (grp k) + β * x k`, with an arbitrary intercept
per group (`a : κ → ℝ`, one per element) and one common slope `β`. The left-hand side says the
slope is identifiable: any two parameter sets `(a, β)` and `(a', β')` that produce the same
ordinate on every line have the same slope. The theorem says this holds exactly when the weighted
within-group sum of squares of the abscissa is positive, `0 < withinSS grp w x`. The left-hand
side does not mention `w`, so the result also says the rank condition is the same for every
choice of positive weights.

Why it matters: the pipeline fits a within-element design, but the wired certificates C1–C3
test the pooled spread `∑ (E k − mean E)²`. A pooled spread can be positive while
`SS_W = 0`, e.g. `E = (3,3,5,5)` in groups `(0,0,1,1)` (each element has one distinct energy);
the 2026-09-24 audit executed this false positive (C1 = C3 = 4.0 with `SS_W = 0`). This theorem
is the design-rank fact behind a grouped certificate that tests `SS_W > 0` instead.

Hypotheses. `hw : ∀ k, 0 < w k` is needed for (⇒) only: with `w ≡ 0`, `withinSS = 0` although
`x = (1,2)` in one group is identifiable, and with `w = (−1,−1)` it is `−1/2`. (⇐) holds for
every real weight vector, because a group-constant abscissa has `withinSS = 0` under any weights
(a zero-sum group contributes `x_e² · 0` via `0/0 = 0`). `hw` is kept as the single hypothesis
of the iff. With zero or signed weights the equivalence fails.
No `Nonempty ι` is needed: for empty `ι` both sides are false.

Scope: relation PURE-MATH; the definitions used (`gMean`, `withinCross`, `withinSS`) are
regression objects with no model tag; published PURE-MATH. Physics reading (REDUCED, not part of
the statement): `x k = E k + IP·(z − 1)` the IP-shifted upper-level energy, groups = elements,
LTE with one temperature, IPD off or frozen; the slope is then `−1/(k_B T)`.

Literature: Aguilera & Aragón 2007 (Spectrochim. Acta B 62, 378) for the multi-element
common-slope Saha–Boltzmann plot; Aitken 1935 (Proc. Roy. Soc. Edinburgh 55, 42) for weighted
least squares. -/
theorem fe_identifiable_iff (grp : ι → κ) (w x : ι → ℝ) (hw : ∀ k, 0 < w k) :
    (∀ (a a' : κ → ℝ) (β β' : ℝ),
        (∀ k, a (grp k) + β * x k = a' (grp k) + β' * x k) → β = β')
      ↔ 0 < withinSS grp w x := by
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


/-- The weighted group mean is linear in the response. -/
private theorem gMean_add_smul (grp : ι → κ) (w y s : ι → ℝ) (c : ℝ) (e : κ) :
    gMean grp w (fun k => y k + c * s k) e = gMean grp w y e + c * gMean grp w s e := by
  unfold gMean
  have : ∑ k ∈ univ.filter (fun k => grp k = e), w k * (y k + c * s k)
      = ∑ k ∈ univ.filter (fun k => grp k = e), w k * y k
        + c * ∑ k ∈ univ.filter (fun k => grp k = e), w k * s k := by
    rw [mul_sum, ← sum_add_distrib]
    exact sum_congr rfl (fun k _ => by ring)
  rw [this, add_div, mul_div_assoc]

/-- The within-group cross product is linear in its second argument. -/
private theorem withinCross_add_smul (grp : ι → κ) (w x y s : ι → ℝ) (c : ℝ) :
    withinCross grp w x (fun k => y k + c * s k)
      = withinCross grp w x y + c * withinCross grp w x s := by
  unfold withinCross
  simp only [gMean_add_smul]
  rw [mul_sum, ← sum_add_distrib]
  exact sum_congr rfl (fun k _ => by ring)


/-- **The fixed-effects slope is linear in the ordinates.**
For every grouping `grp`, weights `w`, abscissa `x`, ordinates `y`, covariate `s` and scalar `c`,
`feSlope grp w x (y + c • s) = feSlope grp w x y + c * feSlope grp w x s`.

Why it matters: in the pipeline's reduced outer loop (audit frontier FT-01) the ordinates of the
multi-element Saha–Boltzmann plot move by `c * s k` when the electron-density offset changes
(`s` is the ion-stage indicator and `c` the change in the `ln n_e` offset). This identity shows
that such a shift moves the fitted common slope by exactly `c` times the slope fitted to `s`,
which is the offset-affinity step FT-01's physics binding needs.

Hypotheses: none. The identity holds for all real weights, including zero or negative ones, and
also when `withinSS grp w x = 0`: the weighted group mean is linear in the averaged function
(the same denominator appears in every term, and `(A + c * B) / D = A / D + c * (B / D)` holds in
Lean even for `D = 0`), `withinCross` is linear in its last argument, and the final division by
`withinSS grp w x` is by one common number.

Scope: relation PURE-MATH; no physics definition is used; published PURE-MATH. The reading of
`s` and `c` above is a REDUCED physics binding (IPD off, one median piece of the outer map) that
belongs to FT-01, not to this statement.

Literature: Aguilera & Aragón 2007 (Spectrochim. Acta B 62, 378) for the common-slope
multi-element plot; Aitken 1935 (Proc. Roy. Soc. Edinburgh 55, 42) for weighted least squares. -/
theorem feSlope_add_smul (grp : ι → κ) (w x y s : ι → ℝ) (c : ℝ) :
    feSlope grp w x (fun k => y k + c * s k) = feSlope grp w x y + c * feSlope grp w x s := by
  unfold feSlope
  rw [withinCross_add_smul, add_div, mul_div_assoc]


/-- helper 3: the within quadratic in the slope. -/
private theorem within_quad (grp : ι → κ) (w x y : ι → ℝ) (b : ℝ) :
    ∑ k, w k * ((y k - gMean grp w y (grp k)) - b * (x k - gMean grp w x (grp k))) ^ 2
      = ∑ k, w k * (y k - gMean grp w y (grp k)) ^ 2 - 2 * b * withinCross grp w x y
        + b ^ 2 * withinSS grp w x := by
  unfold withinSS withinCross
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun k _ => by ring)


/-- **The fixed-effects estimator is the weighted least-squares fit.**
Let `β̂ = feSlope grp w x y` and, for each group `e`, `â_e = ȳ_e − β̂ * x̄_e` (weighted group
means, `gMean`). Then for every per-group intercept `a : κ → ℝ` and every slope `β`,
`∑_k w k * (y k − â_{grp k} − β̂ * x k)² ≤ ∑_k w k * (y k − a (grp k) − β * x k)²`.
That is, the within-centred slope computed by the companion solver, with the group intercepts it
implies, minimizes the weighted residual sum of squares of the model
`y k = a (grp k) + β * x k` (one free intercept per element, one common slope). This certifies
that the solver's formula is the weighted least-squares fixed-effects estimator, not merely a
plausible ratio.

Hypotheses.
* `hw : ∀ k, 0 < w k`: positive weights make the objective a weighted sum of squares. With
  signed weights the objective need not be bounded below and the inequality can fail. Positivity
  also gives each non-empty group a positive weight sum, so weighted within-group deviations sum
  to zero on each group, which kills the cross term in the Pythagorean split.
* `hSS : 0 < withinSS grp w x`: the identifiable case (see `fe_identifiable_iff`), where
  `feSlope` is the genuine ratio `withinCross / withinSS`; this theorem shows it is a minimizer
  (uniqueness is `feSlope_unique_min`). The inequality itself is
  expected to survive `SS_W = 0` under the `0/0 = 0` convention, but that case is not claimed
  here and the solver refuses it (it returns no fit when the denominator is not positive).

Scope: relation PURE-MATH; no physics definition is used; published PURE-MATH. The pipeline
caps weights per element; the statement then concerns weighted least squares for the capped
weights.

Literature: Aitken 1935 (Proc. Roy. Soc. Edinburgh 55, 42) for weighted least squares;
Aguilera & Aragón 2007 (Spectrochim. Acta B 62, 378) for the common-slope multi-element plot. -/
theorem feSlope_isMin (grp : ι → κ) (w x y : ι → ℝ) (hw : ∀ k, 0 < w k)
    (hSS : 0 < withinSS grp w x) (a : κ → ℝ) (β : ℝ) :
    ∑ k, w k * (y k - (gMean grp w y (grp k) - feSlope grp w x y * gMean grp w x (grp k))
        - feSlope grp w x y * x k) ^ 2
      ≤ ∑ k, w k * (y k - a (grp k) - β * x k) ^ 2 := by
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

/-- **Pythagorean split of the fixed-effects residual sum of squares.** With
`β̂ = feSlope grp w x y` and `â_e = ȳ_e − β̂·x̄_e`, every competitor `(a, β)` satisfies
`RSS(a, β) = RSS(â, β̂) + SS_W·(β − β̂)² + ∑_k w k·δ_{grp k}²`,
where `δ_e = ȳ_e − a e − β·x̄_e` is the competitor's intercept offset in group `e`. The two
extra terms are nonnegative, which gives `feSlope_isMin`; they vanish only at the estimator,
which gives `feSlope_unique_min`.

Hypotheses as in `feSlope_isMin`: `hw` (positive weights) kills the cross terms between
within-group deviations and group constants; `hSS` makes `feSlope` the genuine ratio, so that
`β̂·SS_W = withinCross`. Scope: PURE-MATH (weighted regression algebra, no physics definition).

Literature: Aitken 1935 (Proc. Roy. Soc. Edinburgh 55, 42) for weighted least squares. -/
theorem feSlope_rss_split (grp : ι → κ) (w x y : ι → ℝ) (hw : ∀ k, 0 < w k)
    (hSS : 0 < withinSS grp w x) (a : κ → ℝ) (β : ℝ) :
    ∑ k, w k * (y k - a (grp k) - β * x k) ^ 2
      = ∑ k, w k * (y k - (gMean grp w y (grp k) - feSlope grp w x y * gMean grp w x (grp k))
          - feSlope grp w x y * x k) ^ 2
        + withinSS grp w x * (β - feSlope grp w x y) ^ 2
        + ∑ k, w k * (gMean grp w y (grp k) - a (grp k) - β * gMean grp w x (grp k)) ^ 2 := by
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
    within_quad, within_quad, ← hC]
  ring

/-- **The fixed-effects minimizer is unique, up to the intercepts of groups with no line.** Let
`β̂ = feSlope grp w x y` and
`â_e = ȳ_e − β̂·x̄_e` (weighted group means). If a slope `β` and per-group intercepts `a` do at
least as well as the estimator, i.e. their weighted residual sum of squares is at most the
estimator's, then `β = β̂` and `a` agrees with `â` on every group that contains a line.

With `feSlope_isMin` this says the weighted least-squares problem
`min ∑_k w k (y k − a (grp k) − β x k)²` has exactly one solution up to the intercepts of groups
with no line, which the objective does not see; that is why the conclusion is stated at
`grp k`.

Hypotheses. Both are needed. Without `hSS` the slope is not determined: one line with
`x = y = 0` gives residual `0` for every slope, while `feSlope = 0/0 = 0`. Without `hw` a
zero-weight line leaves the intercept of its group free. Scope: PURE-MATH.

Literature: Aitken 1935 (Proc. Roy. Soc. Edinburgh 55, 42) for weighted least squares. -/
theorem feSlope_unique_min (grp : ι → κ) (w x y : ι → ℝ) (hw : ∀ k, 0 < w k)
    (hSS : 0 < withinSS grp w x) (a : κ → ℝ) (β : ℝ)
    (hmin : ∑ k, w k * (y k - a (grp k) - β * x k) ^ 2
        ≤ ∑ k, w k * (y k - (gMean grp w y (grp k) - feSlope grp w x y * gMean grp w x (grp k))
            - feSlope grp w x y * x k) ^ 2) :
    β = feSlope grp w x y ∧
      ∀ k, a (grp k) = gMean grp w y (grp k) - feSlope grp w x y * gMean grp w x (grp k) := by
  rw [feSlope_rss_split grp w x y hw hSS a β] at hmin
  have hnn : ∀ k ∈ (univ : Finset ι),
      0 ≤ w k * (gMean grp w y (grp k) - a (grp k) - β * gMean grp w x (grp k)) ^ 2 :=
    fun k _ => mul_nonneg (hw k).le (sq_nonneg _)
  have hsq : 0 ≤ withinSS grp w x * (β - feSlope grp w x y) ^ 2 :=
    mul_nonneg hSS.le (sq_nonneg _)
  have h1 : withinSS grp w x * (β - feSlope grp w x y) ^ 2 = 0 := by
    linarith [Finset.sum_nonneg hnn]
  have h2 : ∑ k, w k * (gMean grp w y (grp k) - a (grp k) - β * gMean grp w x (grp k)) ^ 2
      = 0 := by linarith [Finset.sum_nonneg hnn]
  have hβ : β = feSlope grp w x y :=
    sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp
      ((mul_eq_zero.mp h1).resolve_left hSS.ne'))
  refine ⟨hβ, fun k => ?_⟩
  have hk := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp h2 k (mem_univ k)
  have hd := pow_eq_zero_iff two_ne_zero |>.mp ((mul_eq_zero.mp hk).resolve_left (hw k).ne')
  rw [hβ] at hd
  linarith

/-- Non-vacuity of `feSlope_rss_split` and `feSlope_unique_min`: three lines in two groups
(`grp = ![0, 0, 1]`), unit weights, abscissae `![0, 1, 5]`. Group `0` has two distinct
abscissae, so the within-group spread is `1/2 > 0` and both hypotheses hold; the estimator
itself then satisfies `hmin`, for any ordinates. -/
example (y : Fin 3 → ℝ) :
    0 < withinSS (![0, 0, 1] : Fin 3 → Fin 2) (fun _ => 1) ![0, 1, 5] ∧
    feSlope (![0, 0, 1] : Fin 3 → Fin 2) (fun _ => 1) ![0, 1, 5] y
      = feSlope (![0, 0, 1] : Fin 3 → Fin 2) (fun _ => 1) ![0, 1, 5] y := by
  have hSS : withinSS (![0, 0, 1] : Fin 3 → Fin 2) (fun _ => 1) ![0, 1, 5] = 1 / 2 := by
    simp only [withinSS, withinCross, gMean, Finset.sum_filter, Fin.sum_univ_three]
    norm_num [show (![0, 0, 1] : Fin 3 → Fin 2) 2 = 1 from rfl,
      show (![0, 1, 5] : Fin 3 → ℝ) 2 = 5 from rfl]
  have hpos : 0 < withinSS (![0, 0, 1] : Fin 3 → Fin 2) (fun _ => 1) ![0, 1, 5] := by
    rw [hSS]; norm_num
  exact ⟨hpos, (feSlope_unique_min _ _ _ y (fun _ => one_pos) hpos
    (fun e => gMean _ (fun _ => 1) y e - feSlope _ (fun _ => 1) ![0, 1, 5] y
      * gMean _ (fun _ => 1) ![0, 1, 5] e) _ le_rfl).1⟩

end CflibsFormal
