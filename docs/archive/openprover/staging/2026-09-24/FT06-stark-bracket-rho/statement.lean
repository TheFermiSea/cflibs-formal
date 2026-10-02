import Mathlib
import CflibsFormal.StarkBroadening

/-!
# Queue target FT06-stark-bracket-rho (deep audit 2026-09-24, FT-06 item 2)

Stark electron-density bracket under a graded Stark width parameter and an opacity-broadening
budget: the Stark-side premise of the two-diagnostic (Stark and Saha) McWhirter certificate.
Statement file for the proof queue: one target theorem, one `sorry`.
-/

open CflibsFormal

namespace Plan.FT06

/-- **Stark electron-density bracket with a Stark-parameter grade and an opacity budget.** Under
the linear electron-impact width law `FWHM = 2·w_true·n_e/n_ref` (`starkFWHM`), suppose the
analyst's tabulated width parameter `w` is graded to within a factor `ρ_w ≥ 1` of the true one
(`w/ρ_w ≤ w_true ≤ w·ρ_w`), and the measured width is at least the true Stark width (opacity only
broadens) and at most `kOpac` times it. Then the Stark estimate `n_S = starkDensity w nRef
widthMeas = nRef·widthMeas/(2w)` brackets the true density:
  `n_S/(kOpac·ρ_w) ≤ n_e ≤ n_S·ρ_w`.
With `ρ_w = 1` and `n_e ≥ 0` this is `starkDensity_brackets_true` (`StarkOpacityGuard`, prior
art), which at `ρ_w = 1` does not need `n_e ≥ 0`; `hne` is needed only once `ρ_w > 1`. A certified
lower end of this bracket above `C·√T·ΔE³` implies McWhirter at the true `n_e`
(`starkOpacity_certificate_sound` is the `ρ_w = 1` case).

Hypotheses: `hw` (the inverse divides by `w`); `hρ` (a grade is a factor `ρ_w ≥ 1`; for
`0 < ρ_w < 1` the interval `hwT` is unsatisfiable, and `ρ_w = 0` must be excluded because Lean's
`w/0 = 0` then admits `w_true = 0`, which breaks the upper end at `n_e = 1`, Lean-checked);
`hk` (only `0 < kOpac` is used; physically `kOpac ≥ 1`; it is not load-bearing, since for
`n_e > 0` `hopac` and `hbudget` force it and at `n_e = 0` both ends hold for any `kOpac`,
Lean-checked, and it is kept for readability); `hnRef` and `hne` are load-bearing: without
`hnRef` (all other hypotheses, including `hne`, kept) the lower end fails at `(w, ρ_w, kOpac,
w_true, nRef, n_e, widthMeas) = (1, 1, 1/2, 1, −1, 1, −2)`, and `nRef = 0` (Lean's `x/0 = 0`)
breaks the upper end at `(1, 1, 1, 1, 0, 1, 0)`; with `hnRef` but without `hne` the upper end
fails at `(1, 2, 1, 1, 1, −1, −2)` (all Lean-checked; both guards are physically trivial,
`n_ref > 0` and `n_e ≥ 0`, and were missing from the audit verifier's revised statement).
`hwT`, `hopac` and `hbudget` are assumed inputs, not measurements (a C14-style refusal): `ρ_w`
comes from the Stark-parameter grade and `kOpac` from an independent optical-thinness test. All
quantities are dimensionless reals; `w` and `widthMeas` share a wavelength unit, `nRef` and
`neTrue` a density unit, and the conclusion is homogeneous in each.

Scope (two-axis): relation PURE-MATH (algebra given the premises); definitions used: `starkFWHM`
REDUCED (linear electron-impact law; the ion contribution is not modelled), `starkDensity` its
inverse; published REDUCED. Citation: Griem 1974 (as for `starkDensity_brackets_true`). -/
theorem stark_bracket_rho {w ρw kOpac wTrue nRef neTrue widthMeas : ℝ} (hw : 0 < w)
    (hρ : 1 ≤ ρw) (hk : 0 < kOpac) (hnRef : 0 < nRef) (hne : 0 ≤ neTrue)
    (hwT : w / ρw ≤ wTrue ∧ wTrue ≤ w * ρw)
    (hopac : starkFWHM wTrue nRef neTrue ≤ widthMeas)
    (hbudget : widthMeas ≤ kOpac * starkFWHM wTrue nRef neTrue) :
    starkDensity w nRef widthMeas / (kOpac * ρw) ≤ neTrue ∧
      neTrue ≤ starkDensity w nRef widthMeas * ρw := by
  sorry

end Plan.FT06
