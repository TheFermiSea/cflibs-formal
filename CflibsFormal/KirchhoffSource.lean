/-
Copyright (c) 2026 Brian Squires. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Squires
-/
import Mathlib

/-!
# Kirchhoff-consistent line opacity and the Planck source function

`OpticalDepth.opticalDepth` omits the stimulated-emission (negative-absorption) factor
`1 − exp(−hν/(k_B T))`, so its source function `lteSourceStrength` is the Wien limit of the line
source function (the `OpticalDepth` module scope block). This module states the opacity WITH the
factor and proves Kirchhoff's law for it:

* `lineOpacity` — `κ = κ0 · n_l · (1 − exp(−x))`, `x = hν/(k_B T)`;
* `lineEmissivity` — `ε = ε0 · n_u`;
* `source_eq_planck` — under LTE populations and the Einstein–Milne relation, `ε/κ` is the Planck
  function `B0/(exp x − 1)`.

The coefficients `κ0`, `ε0` and `B0` stay abstract (owner decision D19: the frequency form is
canonical; no numeric Planck constant enters). The two definitions are not wired into
`opticalDepth`, which is unchanged. The module imports only Mathlib, so its EXACT result does not
sit on any approximation-tagged module.

## Literature

* H. R. Griem, *Principles of Plasma Spectroscopy*, Cambridge University Press (1997) — LTE line
  emission and absorption with the stimulated-emission (negative-absorption) factor, and
  Kirchhoff's law. The coefficients stay abstract here, so no constant is taken from the source.
-/

namespace CflibsFormal

/-- **LTE line opacity with stimulated emission** `κ = κ0 · n_l · (1 - exp (-x))`, where
`x = hν/(k_B T)` and `κ0` is the abstract absorption coefficient per lower-level particle
(frequency form: `κ0 ∝ hν · B_lu · φ`). The factor `1 - exp (-x)` is the negative-absorption
correction that `opticalDepth` omits (`OpticalDepth` module scope block). Writing the correction
through `x` alone presupposes LTE level populations; `source_eq_planck` states that as `hpop`. -/
noncomputable def lineOpacity (κ0 nl x : ℝ) : ℝ := κ0 * nl * (1 - Real.exp (-x))

/-- **Line emissivity** `ε = ε0 · n_u`, with `ε0 ∝ hν · A_ul · φ` kept abstract. -/
noncomputable def lineEmissivity (ε0 nu : ℝ) : ℝ := ε0 * nu

/-- **Kirchhoff: the line source function is the Planck function.** If the level populations
are in the LTE Boltzmann ratio `n_u / n_l = (g_u / g_l) · exp (-x)` (`hpop`) and the emission and
absorption coefficients obey the Einstein-Milne relation `ε0 · g_u / g_l = κ0 · B0` (`hein`, with
`B0 = 2hν³/c²` in the frequency form), then `ε / κ = B0 / (exp x - 1)`, i.e. `B_ν(T)`.

The right side is free of the total density, the partition function, `A_ul` and the path
length: all of that cancels. All the physics is in `hpop` and `hein`; the identity is algebra.
This is the relation the Wien-limit `lteSourceStrength` does not satisfy (audit finding LF-02).

Hypotheses. `hκ` is load-bearing: at `κ0 = 0` the left side is `0` (Lean's `a / 0 = 0`) while
`hein` leaves `B0` free. `hx` and `hnl` are kept as physical-regime guards (`hν > 0`, a populated
lower level). They are not logically sharp: at `x = 0` or `n_l = 0` both sides are `0` by
`a / 0 = 0`, so dropping them buys only such junk values.

Scope: EXACT given `hpop` and `hein` (LTE, a single transition, coefficients abstract).
Literature: Griem 1997 (LTE emission and absorption, Kirchhoff's law). -/
theorem source_eq_planck {κ0 ε0 B0 nl nu x gu gl : ℝ} (hx : 0 < x) (hκ : 0 < κ0) (hnl : 0 < nl)
    (hpop : nu / nl = gu / gl * Real.exp (-x)) (hein : ε0 * gu / gl = κ0 * B0) :
    lineEmissivity ε0 nu / lineOpacity κ0 nl x = B0 / (Real.exp x - 1) := by
  have hnu : nu = gu / gl * Real.exp (-x) * nl := (div_eq_iff hnl.ne').mp hpop
  have hnum : ε0 * nu = κ0 * B0 * nl * Real.exp (-x) := by
    rw [hnu]; linear_combination (nl * Real.exp (-x)) * hein
  have h1 : Real.exp x - 1 ≠ 0 := by
    have := Real.add_one_lt_exp hx.ne'; exact (by linarith : (0 : ℝ) < Real.exp x - 1).ne'
  have hκ' : κ0 ≠ 0 := hκ.ne'
  have hnl' : nl ≠ 0 := hnl.ne'
  unfold lineEmissivity lineOpacity
  rw [hnum, Real.exp_neg]
  field_simp

end CflibsFormal
