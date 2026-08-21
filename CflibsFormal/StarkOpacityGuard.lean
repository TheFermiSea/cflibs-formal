/-
Copyright (c) 2026 Brian Squires. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Squires
-/
import Mathlib
import CflibsFormal.StarkBroadening
import CflibsFormal.Certificates

/-!
# CF-LIBS formalization — opacity guard for the Stark electron-density diagnostic

This module documents, and then repairs, a **one-directional soundness hole** in the
shipped Stark/LTE gate. It adds no new physics: it makes an existing hazard legible as
a theorem, exhibits a numerical witness that the hazard is real, and supplies a
conservative replacement predicate whose soundness *is* proven.

## The hole

`StarkBroadening.starkDensity w nRef width = nRef·width/(2·w)` inverts the Griem
electron-impact relation on a **measured** FWHM. Nothing in `StarkBroadening.lean` or
`Certificates.lean` requires that measured width to be Stark-only. An optically thick
line is *opacity broadened*: self-absorption saturates the line core (see
`SelfAbsorption.selfAbsorptionFactor`, which dims the core hardest), so the measured
FWHM **exceeds** the true Stark width. That width-inflation step is a **modeling
premise here, not a derived fact** — `SelfAbsorption` is an intensity-domain model, so
the repo proves no width–opacity relation (see the REFUSAL note below), and the
inflation enters every result below only as the explicit hypothesis `hopac`. Granted it,
`starkDensity` on a self-absorbed line is biased **high** — `starkDensity_biased_high`.

The McWhirter criterion is a **lower** bound (`StarkBroadening.mcWhirterBound`,
`lteValid`, and `Certificates.mcWhirterCert`), so an inflated `nₑ` makes the LTE gate
*easier* to pass. `stark_lte_gate_one_directional` exhibits explicit numbers on which
the shipped predicates `lteValid` and `mcWhirterCert` hold at the inflated estimate and
**fail** at the true electron density. That is a negative result about the existing
gate: it can be falsely satisfied, precisely in the high-concentration regime where
self-absorption is worst and the gate is needed most.

## The repair

`starkOpacityLteCert` uses the measured width only as an **upper** bound on `nₑ`: given
an opacity-broadening budget `kOpac ≥ 1` (measured width at most `kOpac` times the true
Stark width), the conservative *lower* estimate is `starkDensity …/kOpac`, and McWhirter
is demanded there. `starkOpacity_certificate_sound` proves that this certifies the
McWhirter condition **at the true electron density**; `starkDensity_brackets_true`
records the underlying two-sided statement, `nₑ ∈ [starkDensity/kOpac, starkDensity]`,
which says that the raw diagnostic reports the TOP of a bracket, not its centre.
`starkOpacityLteCert_imp_mcWhirterCert` shows the repaired predicate implies the old
one, i.e. it is a strict tightening, never a weakening; and
`stark_lte_gate_sound_of_opticallyThin` isolates a *sufficient* side condition
(`kOpac = 1`, an independent optical-thinness witness) under which the existing gate
*is* sound. Sufficiency is what is proven; necessity is not claimed.

REFUSAL (epistemic input, in the style of the `Certificates` C14 note): `kOpac` is an
**assumed** budget, not a measured quantity. The link from optical depth `τ` to width
inflation is *not* formalized anywhere in this repo — `SelfAbsorption` /
`CurveOfGrowth` model the intensity domain, not the profile width. So `kOpac` must come
from an independent optical-thinness test (a duplicate-line / branching-ratio check, or
the `Certificates` C12/C13 route), and the guarantee is exactly as honest as that input.
This module therefore *documents* a limitation of `Certificates.mcWhirterCert` and
`StarkBroadening.stark_saha_lte_consistent`; it does not silently patch them, and both
are left untouched.

## Literature and scope

The Stark relation being inverted is that of H. R. Griem, *Spectral Line Broadening by
Plasmas*, Academic Press (1974): `Δλ = 2·w·(nₑ/n_ref)` for an isolated electron-impact
broadened line — the linearity that makes the bias-direction argument here a pure
monotonicity statement. The McWhirter lower bound `nₑ ≥ 1.6·10¹²·√T·(ΔE)³` and the
warning that a self-absorbed line corrupts LTE diagnostics are taken as recalled by
G. Cristoforetti, A. De Giacomo, M. Dell'Aglio, S. Legnaioli, E. Tognoni, V. Palleschi,
N. Omenetto, "Local Thermodynamic Equilibrium in Laser-Induced Breakdown Spectroscopy:
Beyond the McWhirter criterion," *Spectrochimica Acta Part B* **65** (2010) 86. Scope:
the monotonicity results are PURE-MATH; the bias-direction, gate-failure and repaired
certificate statements are REDUCED (they inherit the Griem linear-width idealization and
the McWhirter prefactor, and the opacity budget `kOpac` is an assumed input).
-/

namespace CflibsFormal

/-- **Monotonicity of the Stark diagnostic in the measured width.** `starkDensity` is
increasing in the width it is fed: a broader measured line is read as a denser plasma.
Pure arithmetic — `nRef·(·)/(2·w)` with a nonnegative slope. -/
theorem starkDensity_mono_width {w nRef width₁ width₂ : ℝ} (hw : 0 < w) (hnRef : 0 ≤ nRef)
    (hle : width₁ ≤ width₂) :
    starkDensity w nRef width₁ ≤ starkDensity w nRef width₂ := by
  unfold starkDensity
  gcongr

/-- **Bias direction of the Stark diagnostic under opacity broadening.** Hypothesis
`hopac` is the opacity-broadening premise: the measured FWHM is at least the true Stark
FWHM of the true electron density (self-absorption saturates the core and *widens* the
observed profile; it never narrows it). Conclusion: the diagnostic value read off the
measured width is at least the true electron density — the Stark `nₑ` is biased **high**,
never low. Sign-definite, and the reason the McWhirter gate below is unsound. -/
theorem starkDensity_biased_high {w nRef neTrue widthMeas : ℝ} (hw : 0 < w) (hnRef : 0 < nRef)
    (hopac : starkFWHM w nRef neTrue ≤ widthMeas) :
    neTrue ≤ starkDensity w nRef widthMeas := by
  have h := starkDensity_mono_width hw hnRef.le hopac
  rwa [starkDensity_recovers hw.ne' hnRef.ne'] at h

/-- **The opacity budget bounds the true density from below.** If the measured FWHM
exceeds the true Stark FWHM by at most a factor `kOpac > 0` (the assumed
opacity-broadening budget), then the true electron density is at least the *deflated*
Stark estimate `starkDensity w nRef widthMeas / kOpac`. This is the half of the bracket
that the raw diagnostic cannot supply, and it is what makes the repaired certificate
below sound. -/
theorem starkDensity_div_budget_le {w nRef kOpac neTrue widthMeas : ℝ} (hw : 0 < w)
    (hnRef : 0 < nRef) (hk : 0 < kOpac)
    (hbudget : widthMeas ≤ kOpac * starkFWHM w nRef neTrue) :
    starkDensity w nRef widthMeas / kOpac ≤ neTrue := by
  have h1 : starkDensity w nRef widthMeas
      ≤ starkDensity w nRef (kOpac * starkFWHM w nRef neTrue) :=
    starkDensity_mono_width hw hnRef.le hbudget
  have h2 : starkDensity w nRef (kOpac * starkFWHM w nRef neTrue) = kOpac * neTrue := by
    simp only [starkDensity, starkFWHM]
    field_simp
  rw [h2] at h1
  rw [div_le_iff₀ hk]
  linarith

/-- **Two-sided bracket for the true electron density.** Combining the bias direction
with the opacity budget: an opacity-broadened Stark measurement pins the true `nₑ` into
`[starkDensity/kOpac, starkDensity]`. The measured width alone gives only the UPPER end
(`starkDensity_biased_high`); the lower end costs an assumed budget `kOpac`. Reporting
the raw `starkDensity` as a point estimate is therefore reporting the top of a bracket
as if it were its centre. -/
theorem starkDensity_brackets_true {w nRef kOpac neTrue widthMeas : ℝ} (hw : 0 < w)
    (hnRef : 0 < nRef) (hk : 0 < kOpac)
    (hopac : starkFWHM w nRef neTrue ≤ widthMeas)
    (hbudget : widthMeas ≤ kOpac * starkFWHM w nRef neTrue) :
    starkDensity w nRef widthMeas / kOpac ≤ neTrue
      ∧ neTrue ≤ starkDensity w nRef widthMeas :=
  ⟨starkDensity_div_budget_le hw hnRef hk hbudget, starkDensity_biased_high hw hnRef hopac⟩

/-- **The shipped LTE gate is one-directional (NEGATIVE result).** There are physically
ordinary data — a Griem width parameter `w = 0.02` (nm at `n_ref = 10¹⁶ cm⁻³`), a true
electron density `nₑ = 10¹⁵ cm⁻³`, a measured FWHM of `0.008` nm (a factor-2
opacity-broadened version of the true Stark width `0.004` nm), a plasma at `T = 10⁴ K`
and an energy gap `ΔE = 2` eV — on which

* the opacity-broadening premise `starkFWHM w nRef nₑ ≤ widthMeas` holds,
* the shipped predicates `lteValid` (used as `hlte` in
  `StarkBroadening.stark_saha_lte_consistent`) and `Certificates.mcWhirterCert` **hold**
  at the inflated Stark estimate `starkDensity w nRef widthMeas = 2·10¹⁵`, yet
* both **fail** at the true electron density `10¹⁵ < 1.28·10¹⁵ = 1.6·10¹²·√T·ΔE³`.

So passing the Stark→McWhirter gate is *not* evidence that the true plasma satisfies
McWhirter: the gate is sound only in the direction "true density passes ⇒ measured
estimate passes". This is a statement about the predicates, not a claim that any
particular measurement is self-absorbed. -/
theorem stark_lte_gate_one_directional :
    ∃ w nRef neTrue widthMeas T dE : ℝ,
      0 < w ∧ 0 < nRef ∧ 0 < neTrue
        ∧ starkFWHM w nRef neTrue ≤ widthMeas
        ∧ lteValid T dE (starkDensity w nRef widthMeas)
        ∧ ¬ lteValid T dE neTrue
        ∧ mcWhirterCert 1.6e12 T dE (starkDensity w nRef widthMeas)
        ∧ ¬ mcWhirterCert 1.6e12 T dE neTrue := by
  have hs : Real.sqrt 10000 = 100 := by
    rw [show (10000 : ℝ) = 100 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 100)]
  refine ⟨0.02, 1e16, 1e15, 0.008, 10000, 2, by norm_num, by norm_num, by norm_num,
    by norm_num [starkFWHM], ?_, ?_, ?_, ?_⟩
  · simp only [lteValid, mcWhirterBound, starkDensity, hs]
    norm_num
  · simp only [lteValid, mcWhirterBound, hs]
    norm_num
  · simp only [mcWhirterCert, starkDensity, hs]
    norm_num
  · simp only [mcWhirterCert, hs]
    norm_num

/-- **Repaired Stark/LTE certificate (opacity-aware).** Runtime-checkable predicate over
the pipeline's floats: a positive Griem width parameter and reference density, an opacity
budget `kOpac ≥ 1`, and the McWhirter condition demanded at the **conservative lower**
density estimate `starkDensity w nRef widthMeas / kOpac`. Reading: the measured width is
treated only as an upper bound on `nₑ` (the excess being at most a factor `kOpac`), so
the certified McWhirter test is run at the smallest density the measurement allows.
`kOpac` is an assumed input, not a measurement — see the module REFUSAL note. -/
def starkOpacityLteCert (C T dE w nRef widthMeas kOpac : ℝ) : Prop :=
  0 < w ∧ 0 < nRef ∧ 1 ≤ kOpac
    ∧ mcWhirterCert C T dE (starkDensity w nRef widthMeas / kOpac)

/-- **Soundness of the repaired certificate.** Given the opacity budget
`hbudget : widthMeas ≤ kOpac · starkFWHM w nRef neTrue` (the assumed statement that
opacity broadening inflates the measured FWHM by at most `kOpac`), the certificate
implies the McWhirter condition at the **true** electron density `neTrue` — not merely at
the inflated Stark estimate. This is the guarantee `Certificates.mcWhirterCert` on a raw
Stark estimate does not provide. -/
theorem starkOpacity_certificate_sound {C T dE w nRef widthMeas kOpac neTrue : ℝ}
    (hbudget : widthMeas ≤ kOpac * starkFWHM w nRef neTrue)
    (hcert : starkOpacityLteCert C T dE w nRef widthMeas kOpac) :
    mcWhirterCert C T dE neTrue := by
  obtain ⟨hw, hnRef, hk, hmc⟩ := hcert
  have hk0 : (0 : ℝ) < kOpac := lt_of_lt_of_le zero_lt_one hk
  exact le_trans hmc (starkDensity_div_budget_le hw hnRef hk0 hbudget)

/-- **The repaired certificate is a tightening, not a weakening.** Whenever the
opacity-aware certificate holds, the original `Certificates.mcWhirterCert` on the raw
Stark estimate holds too (dividing by `kOpac ≥ 1` only lowers a nonnegative estimate).
So, for nonnegative measured widths, replacing the shipped gate by `starkOpacityLteCert`
accepts nothing the shipped gate rejects; it rejects strictly more, the extra rejections
being witnessed by the refusal example below. -/
theorem starkOpacityLteCert_imp_mcWhirterCert {C T dE w nRef widthMeas kOpac : ℝ}
    (hwidth : 0 ≤ widthMeas)
    (hcert : starkOpacityLteCert C T dE w nRef widthMeas kOpac) :
    mcWhirterCert C T dE (starkDensity w nRef widthMeas) := by
  obtain ⟨hw, hnRef, hk, hmc⟩ := hcert
  have hd : 0 ≤ starkDensity w nRef widthMeas := by
    unfold starkDensity
    positivity
  exact le_trans hmc (div_le_self hd hk)

/-- **A sufficient side condition that rescues the shipped gate.** With an *independent*
optical-thinness witness — formalized as `hthin`, the measured width does not exceed the
true Stark width, i.e. no opacity broadening — the raw `Certificates.mcWhirterCert` on
the Stark estimate does certify McWhirter at the true density. This is the `kOpac = 1`
corner of `starkOpacity_certificate_sound`, and it names what the existing certificate is
missing: an optical-thinness premise, which must be supplied from outside the width
measurement. Only sufficiency is proven — no claim that `hthin` is *necessary*. -/
theorem stark_lte_gate_sound_of_opticallyThin {C T dE w nRef widthMeas neTrue : ℝ}
    (hw : 0 < w) (hnRef : 0 < nRef)
    (hthin : widthMeas ≤ starkFWHM w nRef neTrue)
    (hcert : mcWhirterCert C T dE (starkDensity w nRef widthMeas)) :
    mcWhirterCert C T dE neTrue := by
  refine starkOpacity_certificate_sound (kOpac := 1) (by simpa using hthin) ?_
  exact ⟨hw, hnRef, le_rfl, by simpa using hcert⟩

/-! ### Non-vacuity witnesses

`stark_lte_gate_one_directional` is itself a witness on explicit, physically ordinary
numbers: the hazard is realized, not hypothetical. The three examples below exercise the
repaired certificate on the same data family: it *accepts* an honestly wide line, its
soundness then delivers McWhirter at the true density (with a `kOpac = 2` correction that
genuinely bites), and it *refuses* exactly the falsely-passing case of
`stark_lte_gate_one_directional`. -/

-- Non-vacuity (certificate satisfiable): `w = 0.02`, `n_ref = 10¹⁶`, measured FWHM
-- `0.016` nm, opacity budget `kOpac = 2`. Raw estimate `4·10¹⁵`, conservative estimate
-- `2·10¹⁵ ≥ 1.28·10¹⁵` — passes with a genuine margin after a factor-2 haircut.
example : starkOpacityLteCert 1.6e12 10000 2 0.02 1e16 0.016 2 := by
  have hs : Real.sqrt 10000 = 100 := by
    rw [show (10000 : ℝ) = 100 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 100)]
  refine ⟨by norm_num, by norm_num, by norm_num, ?_⟩
  simp only [mcWhirterCert, starkDensity, hs]
  norm_num

-- Non-vacuity (guarantee exercised): with the true density `nₑ = 2·10¹⁵` the budget is
-- tight — `0.016 = 2 · starkFWHM 0.02 1e16 2e15 = 2 · 0.008` — so the certificate above
-- delivers McWhirter *at the true density*, `1.28·10¹⁵ ≤ 2·10¹⁵`, a strict margin.
example : mcWhirterCert 1.6e12 10000 2 2e15 := by
  have hs : Real.sqrt 10000 = 100 := by
    rw [show (10000 : ℝ) = 100 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 100)]
  refine starkOpacity_certificate_sound (w := 0.02) (nRef := 1e16) (widthMeas := 0.016)
    (kOpac := 2) (by norm_num [starkFWHM]) ?_
  refine ⟨by norm_num, by norm_num, by norm_num, ?_⟩
  simp only [mcWhirterCert, starkDensity, hs]
  norm_num

-- Non-vacuity (the repair actually blocks the hazard): on the falsely-passing data of
-- `stark_lte_gate_one_directional` (measured FWHM `0.008`, budget `kOpac = 2`) the
-- conservative estimate is `10¹⁵ < 1.28·10¹⁵`, so the repaired certificate REFUSES —
-- while `mcWhirterCert` on the raw Stark estimate accepts.
example : ¬ starkOpacityLteCert 1.6e12 10000 2 0.02 1e16 0.008 2 := by
  have hs : Real.sqrt 10000 = 100 := by
    rw [show (10000 : ℝ) = 100 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 100)]
  rintro ⟨-, -, -, hmc⟩
  rw [mcWhirterCert, starkDensity, hs] at hmc
  norm_num at hmc

end CflibsFormal
