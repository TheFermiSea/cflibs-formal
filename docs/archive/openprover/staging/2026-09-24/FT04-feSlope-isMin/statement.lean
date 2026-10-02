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
  sorry

end Plan.FT04
