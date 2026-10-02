import Mathlib
import CflibsFormal.EquivalentWidth

/-!
# FT-14 (ii): the equivalent width is strictly increasing in the optical-depth scale

Staged target, 2026-09-24 audit, frontier FT-14 (ii), decomposition item 3 (verdict REVISE;
(ii) kept). No new definitions: `equivWidth` (`EquivalentWidth.lean`) is used as it stands on
main, where only the non-strict `equivWidth_mono` exists.
-/

open CflibsFormal MeasureTheory

namespace Plan.FT14

/-- **The curve of growth is strictly increasing.** For a nonnegative integrable line profile
`ψ` of positive area, `τ ↦ W ψ τ = ∫ (1 - exp (-(τ · ψ x))) dx` is strictly increasing on
`[0, ∞)`. Pointwise, `exp (-(τ₁ ψ x)) - exp (-(τ₂ ψ x))` is `> 0` exactly where `ψ x > 0`, and
that set has positive measure because `∫ ψ > 0`.

Physical reading (homogeneous slab, one common profile): with a Kirchhoff source `S > 0` and
`τ = κ · L`, `κ > 0`, the emergent integrated intensity `S · W ψ (κ L)` is strictly increasing in
the path length `L` and, at fixed `L`, in the absorber density. That composition
(`slabIntegrated_strictMono_L`) is a three-line corollary and is not staged separately.

`hpos` excludes the profile `ψ = 0` a.e. (then `W ≡ 0`). `hint` is implied by `hpos` (a
non-integrable function has integral `0` in Lean) and is kept to match `equivWidth_mono`.

Scope: PURE-MATH (strict monotonicity of a parametric integral); physics reading REDUCED
(homogeneous slab, common profile). Literature: Gornushkin 1999 (curve of growth). -/
theorem equivWidth_strictMonoOn {ψ : ℝ → ℝ} (hψ0 : 0 ≤ ψ) (hint : Integrable ψ)
    (hpos : 0 < ∫ x, ψ x) : StrictMonoOn (equivWidth ψ) (Set.Ici 0) := by
  sorry

end Plan.FT14
