import Mathlib

/-!
# FT-13 (b) crux: `0 < 1/τ - 1/(e^τ - 1) < 1/2` for `τ > 0`

Staged queue target, 2026-09-24 audit, frontier FT-13 (b), queue item 3, split out as its own
target (the analytic core of the `½`-Lipschitz bound for `log selfAbsorptionFactor`, with no
measure theory). Real-number inequality only; no definitions.
-/

namespace Plan.FT13

/-- **The slope of `log SA` lies in `(-1/2, 0)`: `0 < 1/τ - 1/(e^τ - 1) < 1/2` for `τ > 0`.**
Why it matters: for `τ > 0` the flat-slab self-absorption factor is `SA τ = (1 - e^(-τ)) / τ`,
and `d/dτ (log (SA τ)) = 1/(e^τ - 1) - 1/τ`. So this inequality says exactly that `log SA` is
strictly decreasing with slope greater than `-1/2`, the crux of the `½`-Lipschitz bound for
`log SA` (FT-13 (b)). The statement itself mentions no physics.

Equivalent forms: the lower bound is `τ < e^τ - 1`; the upper bound is
`e^τ * (τ - 2) + τ + 2 > 0`, i.e. `tanh (τ/2) < τ/2`.

Sharpness: `1/τ - 1/(e^τ - 1) → 1/2` as `τ → 0⁺` (numerically 0.49999992 at `τ = 1e-6`, 0.418 at
`τ = 1`, 0.0333 at `τ = 30`), so no constant below `1/2` works, and the lower bound `0` is
approached as `τ → ∞`.

Hypothesis `hτ` is needed: at `τ = 0` the expression is `0` in Lean's totalized division, and for
`τ < 0` the upper bound fails (`τ = -1` gives about 0.582).

Scope, two-axis prediction (owner rule 2026-09-24): PURE-MATH on both axes (no definitions are
used); published tag PURE-MATH. -/
theorem inv_sub_inv_exp_sub_one_mem {τ : ℝ} (hτ : 0 < τ) :
    0 < 1 / τ - 1 / (Real.exp τ - 1) ∧ 1 / τ - 1 / (Real.exp τ - 1) < 1 / 2 := by
  sorry

end Plan.FT13
