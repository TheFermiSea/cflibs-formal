import Mathlib

/-!
# FT-14 (i): a Kirchhoff-consistent line opacity has the Planck source function

Staged target, 2026-09-24 audit, frontier FT-14 (i) (verdict REVISE; this part kept, grade A).
Two local definitions, no repo imports. The coefficients `κ0`, `ε0`, `B0` stay abstract (owner
decision D19: the frequency form is canonical, `x = hν/(k_B T)`; no numeric Planck constants).
-/

namespace Plan.FT14

/-- **LTE line opacity with stimulated emission** `κ = κ0 · n_l · (1 - exp (-x))`, where
`x = hν/(k_B T)` and `κ0` is the abstract absorption coefficient per lower-level particle
(frequency form: `κ0 ∝ hν · B_lu · φ`). The factor `1 - exp (-x)` is the negative-absorption
correction that `CflibsFormal.opticalDepth` omits (`OpticalDepth.lean`, scope block). -/
noncomputable def lineOpacity (κ0 nl x : ℝ) : ℝ := κ0 * nl * (1 - Real.exp (-x))

/-- **Line emissivity** `ε = ε0 · n_u`, with `ε0 ∝ hν · A_ul · φ` kept abstract. -/
noncomputable def lineEmissivity (ε0 nu : ℝ) : ℝ := ε0 * nu

/-- **Kirchhoff: the line source function is the Planck function.** If the level populations
are in the LTE Boltzmann ratio `n_u / n_l = (g_u / g_l) · exp (-x)` (`hpop`) and the emission and
absorption coefficients obey the Einstein-Milne relation `ε0 · g_u / g_l = κ0 · B0` (`hein`, with
`B0 = 2hν³/c²` in the frequency form), then `ε / κ = B0 / (exp x - 1)`, i.e. `B_ν(T)`.

The right side is free of the total density, the partition function, `A_ul` and the path
length: all of that cancels. All the physics is in `hpop` and `hein`; the identity is algebra.
This is the relation the repo's Wien-limit `lteSourceStrength` does not satisfy (finding LF-02).

Hypotheses `hx`, `hκ`, `hnl` are the physical domain (`hν > 0`, an absorbing line, a populated
lower level). Under Lean's `a / 0 = 0` the identity also holds at `x = 0` and `n_l = 0` (both
sides `0`), so these guards are not logically sharp; they are kept because the verified audit
statement uses them and the natural proof clears denominators with them.

Scope: EXACT given `hpop` and `hein` (LTE, a single transition, coefficients abstract).
Literature: Griem 1997 (LTE emission and absorption, Kirchhoff's law). -/
theorem source_eq_planck {κ0 ε0 B0 nl nu x gu gl : ℝ} (hx : 0 < x) (hκ : 0 < κ0) (hnl : 0 < nl)
    (hpop : nu / nl = gu / gl * Real.exp (-x)) (hein : ε0 * gu / gl = κ0 * B0) :
    lineEmissivity ε0 nu / lineOpacity κ0 nl x = B0 / (Real.exp x - 1) := by
  sorry

end Plan.FT14
