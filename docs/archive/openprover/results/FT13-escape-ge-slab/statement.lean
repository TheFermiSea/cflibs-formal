import Mathlib
import CflibsFormal.SelfAbsorption
import CflibsFormal.EquivalentWidth

/-!
# FT-13 (a): the profile escape factor is at least the flat-slab factor

Staged queue target, 2026-09-24 audit, frontier FT-13 (a), queue item 2 (`integral_mono`).
No new definitions: `selfAbsorptionFactor` (`SelfAbsorption.lean`) and `equivWidth`
(`EquivalentWidth.lean`) are used as they stand on main.
-/

open CflibsFormal MeasureTheory

namespace Plan.FT13

/-- **The profile escape factor is at least the flat-slab factor at the line-centre depth.**
Let `ψ` be a line profile normalized to its PEAK, `0 ≤ ψ ≤ 1`, so that `τ0 * ψ x` is the optical
depth at frequency offset `x` and `τ0 > 0` is the line-centre optical depth; let its area `∫ ψ` be
finite. Then the equivalent width `equivWidth ψ τ0 = ∫ x, (1 - exp (-(τ0 * ψ x)))` (defined in
`EquivalentWidth.lean` as the absorption deficit; read here, as in FT-13, as the integrated
emission of a homogeneous slab in units of its source function) is at least the flat-slab
prediction `selfAbsorptionFactor τ0 * (τ0 * ∫ ψ)`, where
`selfAbsorptionFactor τ = (1 - exp (-τ)) / τ` and `τ0 * ∫ ψ` is the optically thin value.
In ratio form, the profile escape factor `equivWidth ψ τ0 / (τ0 * ∫ ψ)` is at least the slab
factor at the line-centre depth. Consequence (prose, not part of the statement): dividing a
measured integrated intensity by `selfAbsorptionFactor τ0` with `τ0` the physical line-centre
depth over-corrects. The audit's numerics for a Gaussian profile give 0.447 against 0.317 at
`τ0 = 3`. The inequality is sharp: the rectangular profile gives equality
(`equivWidth_rectangular`).

Proof idea: `selfAbsorptionFactor τ0 * τ0 = 1 - exp (-τ0)`; the chord of the convex `exp` gives
`(1 - exp (-τ0)) * t ≤ 1 - exp (-(τ0 * t))` for `t ∈ [0, 1]`; apply it at `t = ψ x` and integrate
once (`integral_mono`).

Hypotheses. `hψ0` (nonnegative profile) is needed by the chord step, which reverses for `t < 0`,
and by integrability of the integrand. `hψ1` is the peak normalization that makes `τ0` the
line-centre depth; without it the statement is false (`ψ = 2` on `[0, 1/2]`, `0` elsewhere, has
`∫ ψ = 1` and gives `(1 - exp (-2 τ0)) / 2 < 1 - exp (-τ0)`). `hint` makes `∫ ψ` and the
equivalent width genuine (a Bochner integral of a non-integrable function is `0`). `hτ` selects
the `τ ≠ 0` branch of `selfAbsorptionFactor`; at `τ0 = 0` both sides are `0`.

Scope, two-axis prediction (owner rule 2026-09-24): relation tag PURE-MATH (an inequality between
two defined quantities); model tags of the definitions used: `selfAbsorptionFactor` REDUCED
(homogeneous slab, flat profile; RF-03 policy), `equivWidth` exact within the homogeneous-slab
model with a known profile shape. Published tag: the weaker, REDUCED (RF-27 pending). Curve of
growth: Gornushkin 1999; the SA correction this inequality bears on: Bulajic 2002. -/
theorem escape_ge_slab {ψ : ℝ → ℝ} {τ0 : ℝ} (hψ0 : 0 ≤ ψ) (hψ1 : ∀ x, ψ x ≤ 1)
    (hint : Integrable ψ) (hτ : 0 < τ0) :
    selfAbsorptionFactor τ0 * (τ0 * ∫ x, ψ x) ≤ equivWidth ψ τ0 := by
  sorry

end Plan.FT13
