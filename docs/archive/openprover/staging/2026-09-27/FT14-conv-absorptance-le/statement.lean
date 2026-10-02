import Mathlib

/-!
# FT-14 (v), pointwise step: instrument after transfer never exceeds instrument in the opacity

Staged target, 2026-09-24 audit, frontier FT-14 (v), decomposition item 7 only. The verdict
requires (v) to be split; the integrated form `equivWidth φ τ ≤ equivWidth (R ⋆ φ) τ` (item 8,
Fubini with `∫ R = 1`) is NOT this target. No repo imports.
-/

open MeasureTheory

namespace Plan.FT14

/-- **Pointwise Jensen for the slab absorptance.** Let `R ≥ 0` with `∫ R = 1` be an instrument
kernel, `φ ≥ 0` a line profile and `τ ≥ 0`. At a point `x` where `y ↦ R (x - y) · φ y` is
integrable,
`∫ R (x - y) · (1 - exp (-(τ φ y))) dy ≤ 1 - exp (-(τ · ∫ R (x - y) · φ y dy))`.
The left side is the absorptance convolved with the instrument (transfer first, then the
instrument, as in nature); the right side folds the instrument into the opacity profile. So the
folded model overstates the emergent intensity `S · (…)` at every pixel, i.e. understates
self-absorption. Reason: `t ↦ 1 - exp (-(τ t))` is concave and `R (x - ·)` is a probability
density.

`hRφ` is needed: without it the right side is `1 - exp 0 = 0` (Lean's junk integral) while the
left side can be positive. `hφ` is needed for the left integrand to be integrable (bounded by
`R (x - ·)`).

Scope: PURE-MATH (Jensen's inequality); physics reading REDUCED (homogeneous slab, common source
function, linear shift-invariant instrument). Literature: Griem 1974 (instrument convolution),
Gornushkin 1999 (slab emission `S · (1 - exp (-τ))`). -/
theorem conv_absorptance_le {R φ : ℝ → ℝ} {τ x : ℝ} (hR : ∀ y, 0 ≤ R y) (hR1 : ∫ y, R y = 1)
    (hφ : 0 ≤ φ) (hτ : 0 ≤ τ) (hRφ : Integrable (fun y => R (x - y) * φ y)) :
    ∫ y, R (x - y) * (1 - Real.exp (-(τ * φ y)))
      ≤ 1 - Real.exp (-(τ * ∫ y, R (x - y) * φ y)) := by
  sorry

end Plan.FT14
