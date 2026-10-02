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
With `ρ_w = 1` this is `starkDensity_brackets_true` (`StarkOpacityGuard`, prior art). A certified
lower end of this bracket above `C·√T·ΔE³` implies McWhirter at the true `n_e`
(`starkOpacity_certificate_sound` is the `ρ_w = 1` case).

Hypotheses: `hw` (the inverse divides by `w`); `hρ` (a grade is a factor `ρ_w ≥ 1`; for
`0 < ρ_w < 1` the interval `hwT` is unsatisfiable, and `ρ_w = 0` must be excluded because Lean's
`w/0 = 0` then admits `w_true = 0`, which breaks the upper end at `n_e = 1`, Lean-checked);
`hk` (only `0 < kOpac` is used; physically `kOpac ≥ 1`); `hnRef` and `hne` are
load-bearing: without `hnRef` the lower end fails at `(w, ρ_w, kOpac, w_true, nRef, n_e,
widthMeas) = (1, 1, 2, 1, −1, −1, 2)`, and with `hnRef` but without `hne` the upper end fails at
`(1, 2, 1, 1, 1, −1, −2)` (Lean-checked; both guards are physically trivial, `n_ref > 0` and
`n_e ≥ 0`, and were missing from the audit verifier's revised statement). `hwT`, `hopac` and
`hbudget` are assumed inputs, not measurements (a C14-style refusal): `ρ_w` comes from the
Stark-parameter grade and `kOpac` from an independent optical-thinness test. All quantities are
dimensionless reals; `w` and `widthMeas` share a wavelength unit, `nRef` and `neTrue` a density
unit, and the conclusion is homogeneous in each.

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
  obtain ⟨h1, h2⟩ := hwT
  have hρ0 : 0 < ρw := by linarith
  have hwT0 : 0 < wTrue := lt_of_lt_of_le (div_pos hw hρ0) h1
  have h1' : w ≤ wTrue * ρw := by rwa [div_le_iff₀ hρ0] at h1
  unfold starkDensity
  unfold starkFWHM at hopac hbudget
  have hA : 2 * wTrue * neTrue ≤ widthMeas * nRef := by
    have := mul_le_mul_of_nonneg_right hopac hnRef.le
    rwa [mul_assoc, div_mul_cancel₀ _ hnRef.ne'] at this
  have hB : widthMeas * nRef ≤ kOpac * (2 * wTrue * neTrue) := by
    have := mul_le_mul_of_nonneg_right hbudget hnRef.le
    rwa [mul_assoc kOpac, mul_assoc (2 * wTrue), div_mul_cancel₀ _ hnRef.ne'] at this
  constructor
  · rw [div_le_iff₀ (by positivity), div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right h2 hne, hk]
  · rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right h1' hne]

end Plan.FT06
