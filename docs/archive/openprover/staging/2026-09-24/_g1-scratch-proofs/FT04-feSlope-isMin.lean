import Mathlib

/-!
# FT-04 (item 7): the fixed-effects slope and group intercepts minimize the weighted RSS

Staged queue target, 2026-09-24 audit, frontier FT-04. Pure regression algebra over a grouped,
weighted design. The four definitions below are shared verbatim by the three FT-04 targets
(`fe_identifiable_iff`, `feSlope_add_smul`, `feSlope_isMin`).
-/

open Finset

namespace Plan.FT04

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
theorem fiber_dev_sum_zero (grp : ι → κ) (w f : ι → ℝ) (hw : ∀ k, 0 < w k) (e : κ) :
    ∑ k ∈ univ.filter (fun k => grp k = e), w k * (f k - gMean grp w f e) = 0 := by
  rcases (univ.filter (fun k => grp k = e)).eq_empty_or_nonempty with h | h
  · rw [h, sum_empty]
  · have hpos : 0 < ∑ k ∈ univ.filter (fun k => grp k = e), w k :=
      sum_pos (fun k _ => hw k) h
    simp only [mul_sub, sum_sub_distrib, ← sum_mul, gMean]
    rw [mul_div_cancel₀ _ hpos.ne', sub_self]

/-- helper 2 (the crux): weighted within-deviations are orthogonal to any group-constant. -/
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

/-- helper 3: the within quadratic in the slope. -/
theorem within_quad (grp : ι → κ) (w x y : ι → ℝ) (b : ℝ) :
    ∑ k, w k * ((y k - gMean grp w y (grp k)) - b * (x k - gMean grp w x (grp k))) ^ 2
      = ∑ k, w k * (y k - gMean grp w y (grp k)) ^ 2 - 2 * b * withinCross grp w x y
        + b ^ 2 * withinSS grp w x := by
  unfold withinSS withinCross
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun k _ => by ring)

/-- **FT-04: the fixed-effects estimator is the weighted least-squares fit.**
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
  (unique by strict convexity under `hSS`, not claimed here). The inequality itself is
  expected to survive `SS_W = 0` under the `0/0 = 0` convention, but that case is not claimed
  here and the solver refuses it (it returns no fit when the denominator is not positive).

Scope, two-axis prediction: relation PURE-MATH; the definitions used are PURE-MATH regression
objects; published tag PURE-MATH. The pipeline caps weights per element; the statement then
concerns weighted least squares for the capped weights.

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

end Plan.FT04
