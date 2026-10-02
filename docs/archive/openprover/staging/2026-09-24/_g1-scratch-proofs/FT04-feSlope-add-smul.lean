import Mathlib

/-!
# FT-04 (items 1-3): the fixed-effects slope is linear in the ordinates

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

theorem gMean_add_smul (grp : ι → κ) (w y s : ι → ℝ) (c : ℝ) (e : κ) :
    gMean grp w (fun k => y k + c * s k) e = gMean grp w y e + c * gMean grp w s e := by
  unfold gMean
  have : ∑ k ∈ univ.filter (fun k => grp k = e), w k * (y k + c * s k)
      = ∑ k ∈ univ.filter (fun k => grp k = e), w k * y k
        + c * ∑ k ∈ univ.filter (fun k => grp k = e), w k * s k := by
    rw [mul_sum, ← sum_add_distrib]
    exact sum_congr rfl (fun k _ => by ring)
  rw [this, add_div, mul_div_assoc]

theorem withinCross_add_smul (grp : ι → κ) (w x y s : ι → ℝ) (c : ℝ) :
    withinCross grp w x (fun k => y k + c * s k)
      = withinCross grp w x y + c * withinCross grp w x s := by
  unfold withinCross
  simp only [gMean_add_smul]
  rw [mul_sum, ← sum_add_distrib]
  exact sum_congr rfl (fun k _ => by ring)

/-- **FT-04: the fixed-effects slope is linear in the ordinates.**
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

Scope, two-axis prediction: relation PURE-MATH; the definitions used are PURE-MATH regression
objects; published tag PURE-MATH. The reading of `s` and `c` above is a REDUCED physics binding
(IPD off, one median piece of the outer map) that belongs to FT-01, not to this statement.

Literature: Aguilera & Aragón 2007 (Spectrochim. Acta B 62, 378) for the common-slope
multi-element plot; Aitken 1935 (Proc. Roy. Soc. Edinburgh 55, 42) for weighted least squares. -/
theorem feSlope_add_smul (grp : ι → κ) (w x y s : ι → ℝ) (c : ℝ) :
    feSlope grp w x (fun k => y k + c * s k) = feSlope grp w x y + c * feSlope grp w x s := by
  unfold feSlope
  rw [withinCross_add_smul, add_div, mul_div_assoc]

end Plan.FT04
