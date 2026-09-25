/-
Copyright (c) 2026 Brian Squires. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Squires
-/
import Mathlib

/-!
# CF-LIBS formalization — self-reversal (the two-zone line dip)

`SelfAbsorption.lean` / `CurveOfGrowth.lean` model **single-zone** self-absorption: an optically
thick *homogeneous* slab whose line peak is suppressed (escape factor, curve of growth). This module
formalizes the genuinely **two-zone** effect — a hot emitting **core** seen through a cooler
absorbing **shell** at the *same* transition — that produces a central line **dip**
("self-reversal"), which a single homogeneous zone cannot.

With core/shell source functions `S_core, S_shell` and core/shell optical depths `τ_core, τ_shell`
(both wavelength-dependent, peaking at line center), the emergent intensity is

`I = S_core·(1 − e^{−τ_core})·e^{−τ_shell} + S_shell·(1 − e^{−τ_shell})`

— the core emission `S_core(1−e^{−τc})` attenuated by the shell `e^{−τs}`, plus the shell's own
emission `S_shell(1−e^{−τs})`.

* `emergentIntensity` — the two-zone forward map, nonnegative.
* `selfReversal_noShell` — **exact** `τ_shell = 0` limit: recovers the single-zone core line
  `S_core·(1 − e^{−τ_core})`.
* `selfReversal_uniformSource` — **exact** `S_shell = S_core` limit: collapses to a *single* zone of
  combined depth, `S_core·(1 − e^{−(τ_core+τ_shell)})` — pure saturation, **no** dip.
* `emergentIntensity_strictAnti_shell` — **shell absorption darkens a fixed wavelength**: at a
  wavelength where the shell source function lies below the core's emergent intensity
  (`S_shell < S_core·(1 − e^{−τ_core})`, easiest to meet at line center where `τ_core` is
  largest), the emergent intensity is *strictly decreasing* in the shell optical depth `τ_shell`.
  This is one step toward a dip, not a dip criterion: it compares shell depths at one wavelength
  and says nothing about the line profile across wavelengths (Honest scope).

## Honest scope

This is the idealized **two-homogeneous-zone** model (a hot core + one cool shell), evaluated at a
single wavelength; real plasmas have continuous gradients (cf. `RadiativeTransferDepth`'s `N`-zone
stack and `SpatialForward`'s onion-peeling). The two limit laws and the monotonicity in
`τ_shell` are **exact for this model**; the two-zone reduction itself is the idealization.

The condition `S_shell < S_core·(1 − e^{−τc})` at line center is **necessary, not sufficient**,
for a central dip. Neither half below is formalized here.

* *Necessary* (for `S_core ≥ 0` and depths that peak at line center): if the condition fails at
  the center, then at every wavelength where both depths are no larger, the intensity is no larger
  than at the center, so the center is not a minimum. This follows from the rewriting
  `I = S_shell + (S_core(1 − e^{−τc}) − S_shell)·e^{−τs}`.
* *Not sufficient*: let both zones share one profile `ψ ≤ 1` (`τc = a·ψ`, `τs = b·ψ`). Then
  `dI/dψ = e^{−bψ}·[S_core·a·e^{−aψ} − b·(S_core(1 − e^{−aψ}) − S_shell)]`. The center (`ψ = 1`)
  is a dip when `b·(S_core(1 − e^{−a}) − S_shell) > S_core·a·e^{−a}` and is not one when the
  reverse strict inequality holds. For example `S_core = 1`, `S_shell = 0`, `a = 1`, `b = 0.1`
  meets the condition, yet the intensity is largest at the center.

Out of scope: the full self-reversed line *profile* `I(λ)` over the Stark/Voigt `τ(λ)`, the exact
center-dip criterion above, the Cowan–Dieke inhomogeneity-parameter source-function fit, and
inversion of `(T,n_e)` from a measured reversed profile.

## Literature

R. D. Cowan, G. H. Dieke, "Self-Absorption of Spectrum Lines," *Rev. Mod. Phys.* **20** (1948) 418 —
the classic two-layer treatment predicting self-absorption, self-reversal, and line disappearance.
The two-zone emergent-intensity form is standard radiative transfer through a non-isothermal medium
(cf. Griem, *Principles of Plasma Spectroscopy*, Cambridge 1997).
-/

namespace CflibsFormal

/-- **Two-zone emergent intensity.** Hot core (source `Score`, optical depth `τc`) seen through a
cooler shell (source `Sshell`, optical depth `τs`) at the same transition:
`I = Score·(1 − e^{−τc})·e^{−τs} + Sshell·(1 − e^{−τs})`. -/
noncomputable def emergentIntensity (Score Sshell τc τs : ℝ) : ℝ :=
  Score * (1 - Real.exp (-τc)) * Real.exp (-τs) + Sshell * (1 - Real.exp (-τs))

/-- The two-zone emergent intensity is nonnegative for nonnegative source functions and optical
depths. -/
lemma emergentIntensity_nonneg {Score Sshell τc τs : ℝ}
    (hScore : 0 ≤ Score) (hSshell : 0 ≤ Sshell) (hτc : 0 ≤ τc) (hτs : 0 ≤ τs) :
    0 ≤ emergentIntensity Score Sshell τc τs := by
  unfold emergentIntensity
  have h1 : 0 ≤ 1 - Real.exp (-τc) := by
    have : Real.exp (-τc) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    linarith
  have h2 : 0 ≤ 1 - Real.exp (-τs) := by
    have : Real.exp (-τs) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    linarith
  have h3 : 0 ≤ Real.exp (-τs) := (Real.exp_pos _).le
  exact add_nonneg (mul_nonneg (mul_nonneg hScore h1) h3) (mul_nonneg hSshell h2)

/-- **No-shell limit (exact).** With no absorbing shell (`τ_shell = 0`) the two-zone model recovers
the single-zone optically-thick core line `S_core·(1 − e^{−τ_core})`. -/
theorem selfReversal_noShell (Score Sshell τc : ℝ) :
    emergentIntensity Score Sshell τc 0 = Score * (1 - Real.exp (-τc)) := by
  unfold emergentIntensity
  simp [Real.exp_zero]

/-- **Uniform-source limit (exact).** With equal core and shell source functions
(`S_shell = S_core`, an isothermal medium) the two zones collapse to a single zone of combined
optical depth:
`I = S_core·(1 − e^{−(τ_core+τ_shell)})` — pure saturation. For `S_core ≥ 0` this increases with
the combined depth, so it peaks where the depths do, at line center: **no** central dip. -/
theorem selfReversal_uniformSource (Score τc τs : ℝ) :
    emergentIntensity Score Score τc τs = Score * (1 - Real.exp (-(τc + τs))) := by
  have hexp : Real.exp (-(τc + τs)) = Real.exp (-τc) * Real.exp (-τs) := by
    rw [← Real.exp_add]; congr 1; ring
  unfold emergentIntensity
  rw [hexp]; ring

/-- **Shell absorption darkens a fixed wavelength.** At a wavelength where the shell source
function lies *below* the core's emergent intensity, `S_shell < S_core·(1 − e^{−τ_core})`, the
emergent intensity is **strictly decreasing** in the shell optical depth `τ_shell`. (Rewriting
`I = S_shell + (S_core(1−e^{−τc}) − S_shell)·e^{−τs}` makes this the strict antitonicity of
`e^{−τ_shell}` scaled by a positive coefficient.) The condition is easiest to meet at line center,
where `τ_core` is largest. It is necessary for a central self-reversal dip but not sufficient:
whether the center ends up darker than nearby wavelengths depends on how both depths vary across
the profile, which this fixed-wavelength statement does not see (module Honest scope). -/
theorem emergentIntensity_strictAnti_shell {Score Sshell τc : ℝ}
    (hdip : Sshell < Score * (1 - Real.exp (-τc))) :
    StrictAnti (fun τs => emergentIntensity Score Sshell τc τs) := by
  have hA : 0 < Score * (1 - Real.exp (-τc)) - Sshell := by linarith
  intro a b hab
  have hexp : Real.exp (-b) < Real.exp (-a) := Real.exp_lt_exp.mpr (by linarith)
  have hrw : ∀ t : ℝ, emergentIntensity Score Sshell τc t
      = Sshell + (Score * (1 - Real.exp (-τc)) - Sshell) * Real.exp (-t) := by
    intro t; unfold emergentIntensity; ring
  simp only [hrw]
  have hmul := mul_lt_mul_of_pos_left hexp hA
  linarith

end CflibsFormal
