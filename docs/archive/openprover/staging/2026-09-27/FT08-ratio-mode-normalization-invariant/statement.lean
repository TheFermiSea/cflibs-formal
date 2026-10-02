import Mathlib
import CflibsFormal.Closure

/-!
# FT-08 (a1): ratio mode is invariant under a common-mode normalization

Staged queue target, frontier FT-08 (a), decomposition step 1. No new definitions:
`composition` (`Closure.lean`) is used as it stands on main.
-/

open CflibsFormal

namespace Plan.FT08

variable {κ : Type*} [Fintype κ]

/-- **Ratio mode ignores every common-mode normalization.** For any density vector `N` and any
nonzero scale `c`, the ratio of the number fractions of `c • N` for species `a` and `b` is the
raw density ratio `N a / N b`: `composition (c • N) a / composition (c • N) b = N a / N b`.

Reading: whatever common factor (calibration `Fcal`, closure normalization, neutrality
normalization) multiplies every species' recovered density, the pairwise ratios are unchanged, so
no choice of normalization can improve or spoil a ratio-mode estimate. This is algebra on an
arbitrary real vector; it says nothing about how `N` is recovered.

Hypotheses (both needed, totalized division): `hc` (at `c = 0` the left side is `0`); `hsum` (at
`∑ N = 0` both fractions are `0`, so the left side is `0` while `N a / N b` need not be).

Scope: PURE-MATH (FT-08 audit verdict 2026-09-24). -/
theorem ratio_mode_normalization_invariant {N : κ → ℝ} {c : ℝ} (hc : c ≠ 0)
    (hsum : ∑ t, N t ≠ 0) (a b : κ) :
    composition (fun t => c * N t) a / composition (fun t => c * N t) b = N a / N b := by
  sorry

end Plan.FT08
