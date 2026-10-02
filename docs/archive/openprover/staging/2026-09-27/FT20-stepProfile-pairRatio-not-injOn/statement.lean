import Mathlib
import CflibsFormal.EquivalentWidth

/-!
# FT-20 (b), part 2b: pair-ratio injectivity fails for the two-step profile

Staged queue target, 2026-09-27, frontier FT-20 (b), the headline counterexample (audit verdict
REVISE, revision applied). Bridge corollary: the closed form `Plan.FT20.equivWidth_stepProfile`
(sibling target, part 1) turns this into `Plan.FT20.stepW_pairRatio_not_injOn` (sibling target,
part 2a). Neither sibling is on main, so a proof must inline both or reuse their landed proofs.
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

/-- **Pair-ratio identifiability is not profile-generic.** For the two-step profile
`ψ = 1_[0,1] + (1/100) · 1_[0,20]`, the `r = 2` pair ratio `n ↦ W(2n) / W(n)` of equivalent
widths `W = equivWidth ψ` is not injective on column densities `n ∈ (0, ∞)`:
`R(1) ≈ 1.5077 > R(3) ≈ 1.3905 < R(10) ≈ 1.5826`, so levels just above the interior minimum
(`≈ 1.3822` at `n ≈ 2.42`) are attained at two column densities.

For the flat kernel `1_[0,1]` the same ratio is `cogRatio 2 1` (`W(τ) = 1 - exp (-τ)`,
`equivWidth_rectangular`), which is injective on `(0, ∞)` (`cogRatio_injOn`). So `cogRatio_injOn`
and the C13 certificate `saDistinct_certificate_sound` certify uniqueness for the flat kernel
only; this result is the counterexample behind retagging them REDUCED (flat-kernel slab).

Scope: PURE-MATH (a counterexample for a surrogate kernel, not a physical line shape; the Voigt
behaviour is numerics only and is not claimed here). Curve of growth: Gornushkin et al. 1999. -/
theorem stepProfile_pairRatio_not_injOn :
    ¬ Set.InjOn (fun n : ℝ => equivWidth (stepProfile (1 / 100) 20) (2 * n)
        / equivWidth (stepProfile (1 / 100) 20) n) (Set.Ioi 0) := by
  sorry

end Plan.FT20
