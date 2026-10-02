import Mathlib
import CflibsFormal.InhomogeneityBias

/-!
# FT-19 (b): a reweighting antitone in `b` lowers the tilted mean

Staged queue target, 2026-09-24 audit, frontier FT-19 (weighted Chebyshev step), REVISE
applied. No new definitions: `tiltMean`, `tiltWeight`, `mixture` (`InhomogeneityBias.lean`) are
used as they stand on main.
-/

open CflibsFormal

namespace Plan.FT19

/-- **Reweighting by a factor antitone in `b` lowers the tilted mean.** Let `w z > 0` be zone
masses, `b z` zone inverse temperatures, and `ρ z > 0` a reweight that is antitone in `b`
(`b i < b j → ρ j ≤ ρ i`, i.e. `Antivary ρ b`: hotter zones get at least as much extra
weight). Then at every anchor energy `a`, the tilted mean inverse temperature of the
reweighted masses `w · ρ` is at most that of `w`.

This is the weighted Chebyshev sum inequality for the tilted probability `p = tiltWeight w b a`:
`tiltMean (w·ρ) b a = (∑ p ρ b)/(∑ p ρ)` and `∑ z, ∑ z', p z p z' (ρ z − ρ z')(b z − b z') ≤ 0`.

Physics reading (FT-19): with `ρ = ionReweight` evaluated at the zone temperatures, `w · ρ` is
the ion-stage zone weight, so the ion tilted mean sits below the neutral one at a common
anchor. Scope: PURE-MATH (finite positive mixtures); the application is REDUCED. -/
theorem tiltMean_reweight_le {ζ : Type*} [Fintype ζ] [Nonempty ζ] {w b ρ : ζ → ℝ}
    (hw : ∀ z, 0 < w z) (hρ : ∀ z, 0 < ρ z) (hanti : ∀ i j, b i < b j → ρ j ≤ ρ i) (a : ℝ) :
    tiltMean (fun z => w z * ρ z) b a ≤ tiltMean w b a := by
  sorry

end Plan.FT19
