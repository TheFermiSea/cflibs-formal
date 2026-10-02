import Mathlib

/-!
# FT-20 (b), part 2a: the two-step pair ratio is not injective (closed-form level)

Staged queue target, 2026-09-27, frontier FT-20 (b), decomposition items 2-4 (audit verdict
REVISE, revision applied). Pure real analysis: no repo definitions. `stepW η M τ` is,
verbatim, the right-hand side of the sibling target `Plan.FT20.equivWidth_stepProfile`, which
bridges this statement to `equivWidth (stepProfile η M)` (sibling target
`Plan.FT20.stepProfile_pairRatio_not_injOn`).
-/

namespace Plan.FT20

/-- **Closed-form curve of growth of the two-step profile**
`W(τ) = (1 - exp (-(τ (1 + η)))) + (M - 1) (1 - exp (-(τ η)))`, the equivalent width of
`1_[0,1] + η · 1_[0,M]` for `M ≥ 1` (sibling target `equivWidth_stepProfile`). -/
noncomputable def stepW (η M τ : ℝ) : ℝ :=
  (1 - Real.exp (-(τ * (1 + η)))) + (M - 1) * (1 - Real.exp (-(τ * η)))

/-- **The `r = 2` pair ratio of the two-step curve of growth is not injective.** With
`η = 1/100` and `M = 20`, the map `n ↦ W(2n) / W(n)` on `(0, ∞)` takes some value twice.
Numerically `R(1) ≈ 1.5077`, `R(3) ≈ 1.3905`, `R(10) ≈ 1.5826` (interior minimum `≈ 1.3822` at
`n ≈ 2.42`), so by continuity every level in `(R(3), min (R(1), R(10)))`, for instance `29/20`,
is attained once in `(1,3)` and once in `(3,10)`.

Contrast: with `η = 0` the ratio is `1 + exp (-n)`, strictly decreasing, so the statement is
false there (this is the flat-kernel `cogRatio_injOn`). Non-injectivity is therefore a property
of the broad weak wing, not of the ratio construction.

Scope: PURE-MATH (a counterexample about an explicit real function). -/
theorem stepW_pairRatio_not_injOn :
    ¬ Set.InjOn (fun n : ℝ => stepW (1 / 100) 20 (2 * n) / stepW (1 / 100) 20 n)
      (Set.Ioi 0) := by
  sorry

end Plan.FT20
