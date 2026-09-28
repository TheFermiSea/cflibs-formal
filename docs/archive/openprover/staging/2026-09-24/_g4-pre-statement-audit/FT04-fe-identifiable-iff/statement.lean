import Mathlib

/-!
# FT-04 (items 4-6): identifiability of the common slope in a fixed-effects design

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

/-- **FT-04: the common slope of a fixed-effects design is identifiable iff `SS_W > 0`.**

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

Hypotheses. `hw : ∀ k, 0 < w k` is needed in both directions. For (⇐) it makes the weight sum of
the group of `k` positive, so the weighted mean of a group-constant function is that constant.
For (⇒) it gives `SS_W ≥ 0`, and `SS_W = 0` then forces `x` to be constant on each group. With
zero or signed weights the equivalence fails.
No `Nonempty ι` is needed: for empty `ι` both sides are false.

Scope, two-axis prediction: relation PURE-MATH; the definitions used (`gMean`, `withinCross`,
`withinSS`) are PURE-MATH regression objects; published tag PURE-MATH. The physics binding
(`x = E + IP·(z−1)`, groups = elements, LTE, one temperature, IPD off or frozen) is REDUCED and
belongs in the landing docstring, not here.

Literature: Aguilera & Aragón 2007 (Spectrochim. Acta B 62, 378) for the multi-element
common-slope Saha–Boltzmann plot; Aitken 1935 (Proc. Roy. Soc. Edinburgh 55, 42) for weighted
least squares. -/
theorem fe_identifiable_iff (grp : ι → κ) (w x : ι → ℝ) (hw : ∀ k, 0 < w k) :
    (∀ (a a' : κ → ℝ) (β β' : ℝ),
        (∀ k, a (grp k) + β * x k = a' (grp k) + β' * x k) → β = β')
      ↔ 0 < withinSS grp w x := by
  sorry

end Plan.FT04
