import Mathlib

/-!
# FT-01 (a, revised): the T-damped outer loop converges for gains in `(0, 1)`

Staged queue target, 2026-09-24 audit, frontier FT-01, verifier revision (a): the pipeline damps
`T`, not `u = 1/T`. The definition `dampedMap` is shared verbatim (definition line and body) with
the sibling target `dampedMap_contracts`. Real analysis only.
-/

open Filter Topology

namespace Plan.FT01

/-- Krasnoselskii–Mann damped map `u ↦ (1−λ)u + λ g(u)` (the pipeline uses `λ = 1/2`).
One relaxation step of the fixed-point iteration for `g` with damping `lam` (`lam = 1` is plain
substitution). The CF-LIBS pipeline relaxes its outer temperature update with `lam = 1/2`,
`T_K = 0.5 * T_prev + 0.5 * T_new` (CF-LIBS-improved `cflibs/inversion/solve/iterative.py`,
lines 908 and 2454), so there the damped coordinate `u` is the temperature `T` itself. -/
def dampedMap (lam : ℝ) (g : ℝ → ℝ) (u : ℝ) : ℝ := (1 - lam) * u + lam * g u

/-- **The T-damped Möbius iteration converges from every positive start when `0 < g < 1`.**
Model: suppose the undamped outer update is affine in inverse temperature, `u ↦ g * u + c` with
`u = 1/T` (`k_B` absorbed; everything dimensionless). In temperature this is the Möbius map
`φ T = T / (g + c * T)`, whose positive fixed point is `T* = (1 - g) / c`. The pipeline damps `T`:
it iterates `H := dampedMap lam φ`, `T ↦ (1 - lam) * T + lam * φ T`. For gain `0 < g < 1`,
`c > 0` and damping `0 < lam ≤ 1`, the `H`-iterates converge to `T*` from every `T0 > 0`.

This replaces the u-damped idealization for the pipeline: there `u ↦ (1 - lam) * u +
lam * (g * u + c)` is affine with rate `1 - lam + lam * g` and converges from every start iff
`1 - 2/lam < g < 1`, but that window is false for T-damping (the audit's verifier found that at
`g = -1` the T-iterates go negative), so this statement keeps `g > 0`.

Proof idea (the statement asserts convergence only): `H T - T = lam * T * (1 - g - c * T) /
(g + c * T)`, and `H` is increasing on `T > 0` with `H T* = T*` (this uses `lam ≤ 1`), so the orbit
is monotone (upward from below `T*`, downward from above) and bounded; its limit
`L ≥ min T0 T* > 0` is a fixed point of `H`, hence of `φ`, hence `L = T*`.

Hypotheses. `hg0` keeps `g + c * T > 0` for all `T > 0` (for `g < 0` the Möbius map has a pole at
`T = -g/c > 0`; the boundary case `g = 0`, a constant map, is excluded for simplicity). `hg1` is
needed: for `g ≥ 1` there is no positive fixed point (`(1 - g) / c ≤ 0`). `hc` makes `T*`
positive. `hl0`, `hl1` put the damping in `(0, 1]`; `lam ≤ 1` keeps `H` order-preserving (no
overshoot). `hT0` is a positive starting temperature.

Scope, two-axis prediction (owner rule 2026-09-24): PURE-MATH on both axes (no model definitions);
published tag PURE-MATH. The binding "the reduced outer map of `iterative.py` is `u ↦ g * u + c`
on one median piece, IPD off" is REDUCED, is NOT proved here, and is pre-registered separately
(FT-01 step 10). The Saha–Boltzmann outer loop that the binding models is described in
Aguilera & Aragón 2007 and Yalcin 1999; this statement itself is pure mathematics. -/
theorem tDamped_mobius_converges {g c lam : ℝ} (hg0 : 0 < g) (hg1 : g < 1) (hc : 0 < c)
    (hl0 : 0 < lam) (hl1 : lam ≤ 1) (T0 : ℝ) (hT0 : 0 < T0) :
    Tendsto (fun n => (dampedMap lam (fun T => T / (g + c * T)))^[n] T0) atTop
      (𝓝 ((1 - g) / c)) := by
  sorry

end Plan.FT01
