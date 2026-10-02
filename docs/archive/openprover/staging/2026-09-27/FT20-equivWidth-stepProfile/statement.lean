import Mathlib
import CflibsFormal.EquivalentWidth

/-!
# FT-20 (b), part 1: closed-form equivalent width of the two-step profile

Staged queue target, 2026-09-27, frontier FT-20 (b), decomposition item 1 (audit verdict REVISE,
revision applied: only the step-profile counterexample is kept; the log-slope criterion and the
Voigt claim are dropped). `equivWidth` (`EquivalentWidth.lean`) is used as it stands on main; the
only new definition is the two-step profile `stepProfile`.
-/

open CflibsFormal

namespace Plan.FT20

/-- **Two-step line profile** `ψ = 1_[0,1] + η · 1_[0,M]`: a unit-height core on `[0,1]` plus a
wing of height `η` on `[0,M]`. For `M ≥ 1` the two indicators overlap on `[0,1]`, so `ψ = 1 + η`
on `[0,1]`, `ψ = η` on `(1,M]` and `ψ = 0` elsewhere. A PURE-MATH surrogate kernel (not a
physical line shape), used as a counterexample to pair-ratio injectivity beyond the flat
kernel. -/
noncomputable def stepProfile (η M : ℝ) : ℝ → ℝ := fun x =>
  Set.indicator (Set.Icc 0 1) (fun _ => 1) x + η * Set.indicator (Set.Icc 0 M) (fun _ => 1) x

/-- **Equivalent width of the two-step profile.** For `M ≥ 1`, and every real `η` and `τ`,
`equivWidth (stepProfile η M) τ = (1 - exp (-(τ (1 + η)))) + (M - 1) (1 - exp (-(τ η)))`:
the core `[0,1]` contributes length `1` times the deficit at height `1 + η`, and the bare wing
`(1,M]` contributes length `M - 1` times the deficit at height `η`. The integral runs over all of
`ℝ`; off `[0,M]` the integrand is `1 - exp 0 = 0`.

`M ≥ 1` is needed (for `M < 1` the wing sits inside the core and the formula changes). No sign
condition on `η` or `τ` is needed: the integrand is a finite sum of constants on bounded
intervals, hence integrable for every `η, τ`. With `η = 0` this reduces to
`equivWidth_rectangular` (`1 - exp (-τ)`).

Scope: PURE-MATH (an exact integral identity for a surrogate kernel). Curve of growth:
Gornushkin et al. 1999; equivalent width: Mihalas 1978. -/
theorem equivWidth_stepProfile {η M τ : ℝ} (hM : 1 ≤ M) :
    equivWidth (stepProfile η M) τ
      = (1 - Real.exp (-(τ * (1 + η)))) + (M - 1) * (1 - Real.exp (-(τ * η))) := by
  sorry

end Plan.FT20
