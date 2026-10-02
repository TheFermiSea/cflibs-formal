import Mathlib
import CflibsFormal.SelfAbsorption

/-!
# FT-13 (b): `log selfAbsorptionFactor` is `½`-Lipschitz on `[0, ∞)`

Staged queue target, 2026-09-24 audit, frontier FT-13 (b), queue items 4-5 (derivative of
`log SA`, mean value theorem, the endpoint `τ = 0`). No new definitions: `selfAbsorptionFactor`
(`SelfAbsorption.lean`) is used as it stands on main.
-/

open CflibsFormal

namespace Plan.FT13

/-- **`log SA` is `½`-Lipschitz on `[0, ∞)`.** For optical depths `τ, τ' ≥ 0`,
`|log (SA τ) - log (SA τ')| ≤ |τ - τ'| / 2`, where `SA = selfAbsorptionFactor` is the flat-slab
self-absorption (escape) factor, `SA τ = (1 - exp (-τ)) / τ` for `τ ≠ 0` and `SA 0 = 1`.

Reading: if the optical depth used in the curve-of-growth correction is off by at most `Δ`, the
corrected log intensity `log (I_meas / SA τ)` moves by at most `Δ / 2`. The error `Δ` is an
ASSUMED input (the C14 refusal pattern): this theorem does not bound `|τ̂ - τ|`, and it says
nothing about the escape factor of a non-flat line profile (that is FT-13 (c), a separate
target).

Sharpness: the constant `1/2` cannot be lowered, since `d/dτ (log (SA τ)) = 1/(e^τ - 1) - 1/τ`
tends to `-1/2` as `τ → 0⁺` (audit numerics: largest ratio 0.999995 over 200000 random pairs).

Proof idea: for `τ > 0` the derivative of `log SA` lies in `(-1/2, 0)` (equivalently
`0 < 1/τ - 1/(e^τ - 1) < 1/2`); apply the mean value theorem on `(0, ∞)`; the endpoint `τ = 0`
follows from `SA 0 = 1`, `SA ≤ 1` and `SA τ ≥ exp (-τ/2)` (i.e. `sinh (τ/2) ≥ τ/2`).

Hypotheses `hτ`, `hτ'` restrict to physical optical depths and are needed: on the negative axis
`SA (-a) = (e^a - 1) / a` and the slope of `log SA` tends to `-1` as `τ → -∞`, so the bound fails
there.

Scope, two-axis prediction (owner rule 2026-09-24): relation tag PURE-MATH (a Lipschitz bound for
a real function); model tag of `selfAbsorptionFactor`: REDUCED (homogeneous slab, flat profile;
RF-03 policy). Published tag: the weaker, REDUCED (RF-27 pending). Curve of growth:
Gornushkin 1999; SA correction procedure: Bulajic 2002. -/
theorem log_selfAbsorptionFactor_lipschitz {τ τ' : ℝ} (hτ : 0 ≤ τ) (hτ' : 0 ≤ τ') :
    |Real.log (selfAbsorptionFactor τ) - Real.log (selfAbsorptionFactor τ')|
      ≤ |τ - τ'| / 2 := by
  sorry

end Plan.FT13
