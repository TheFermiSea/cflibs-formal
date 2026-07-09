/-
Copyright (c) 2026 Brian Squires. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Squires
-/
import Mathlib
import CflibsFormal.SahaEquilibrium
import CflibsFormal.SahaStability
import CflibsFormal.ErrorBudget

/-!
# CF-LIBS formalization — the outer temperature iteration, Model B headline (Frontier 04)

This module gives the abstract two-leg box-contraction spine `outerContraction_box`
(`SahaEquilibrium`, Frontier 04 M1) its **content** by instantiating it with the two concrete
CF-LIBS legs:

* the density reader `legNe : T ↦ n_e(T) = S(T)/R` (`electronDensityFromRatio`, `Saha`),
  whose `T`-Lipschitz constant `L₁ = sahaFactorLipConst/R₀` is discharged from the published
  sensitivity lemma `electronDensityFromRatio_lipschitz_temp` (`SahaStability`);
* the temperature update `legT : n_e ↦ 1/(k_B·slope(n_e))` (`combinedSlopeTempUpdate`,
  `ErrorBudget`), built from the **combined Saha–Boltzmann slope** of Aguilera & Aragón 2007,
  whose `n_e`-Lipschitz constant `L₂` is discharged from `combinedSlopeTempUpdate_lipschitz`.

The composite outer sweep `Φ = legT ∘ legNe` on the temperature box `[Tmin,Tmax]` then has a
**unique self-consistent fixed point** `T⋆` and iterates converge to it geometrically, gated
by the runtime-checkable product certificate `L₁·L₂ < 1`.

**Why "Model B".** ("Model B" is this repo's own Frontier-04 designation for the
non-degenerate loop built on the combined Saha–Boltzmann slope of Aguilera & Aragón 2007 —
the paper itself does not use the name; it is defined here by contrast with the refuted
"Model A" single-stage loop.) The single-stage two-line temperature is composition-independent
(`ForwardMap.temperature_from_two_lines`), so a `T`-leg built from it is a *constant* map and
the outer loop would be degenerate (`L = 0`, headline true-but-vacuous). The combined
Saha–Boltzmann slope is `n_e`-dependent through the Saha offset (non-degeneracy witnessed in
`ErrorBudget`), so this headline is about a **real** loop. (The `n_e` leg here is the Saha
stage-ratio reader; the abstract spine is agnostic to the `n_e` source — a Stark-broadening
`n_e` leg would instantiate it equally well.)

**Honest scope (`REDUCED`).** The two interval invariances `hmapsNe`, `hmapsT` and the slope
floor `hslopeFloor` are carried as explicit hypotheses (genuine side conditions, exactly as
the inner-loop `sahaIter_mapsTo` carries `√(S·Ntot) ≤ b`; they are not derivable for free).
The product gate `L₁·L₂ < 1` is a **sufficient**, not necessary, convergence certificate: the
constants `sahaFactorLipConst` and `L₂` are deliberately non-sharp box over-estimates, so the
gate may fail to certify a loop that nonetheless converges (real CF-LIBS loops are often
under-relaxed). No concrete end-to-end witness satisfying all hypotheses simultaneously is
constructed here; the component non-degeneracy (`ErrorBudget` witnesses) and the abstract
spine's witnesses cover the non-vacuity of the pieces.
-/

namespace CflibsFormal

open Finset Real
open scoped NNReal BigOperators

section OuterLoopModelB
variable {ιe : Type*} [Fintype ιe] [Nonempty ιe]
variable {κe : Type*} [Fintype κe] [Nonempty κe]
variable {ιl : Type*} [Fintype ιl] [Nonempty ιl]

/-- **The CF-LIBS outer temperature loop contracts** (`REDUCED`; Aguilera & Aragón 2007,
Model B). Instantiating the abstract two-leg spine `outerContraction_box` with the concrete
CF-LIBS legs — the Saha density reader `legNe T = electronDensityFromRatio … T … R` and the
combined-slope temperature update `legT ne = combinedSlopeTempUpdate … ne` — the outer sweep
`Φ = legT ∘ legNe` on `[Tmin,Tmax]` has a **unique** self-consistent fixed point `T⋆` and the
iterates `Φ^[n] T₀` converge to `T⋆` from every start in the box.

The density leg's `T`-Lipschitz constant is `L₁ = sahaFactorLipConst/R₀`
(`electronDensityFromRatio_lipschitz_temp`); the temperature leg's `n_e`-Lipschitz constant is
`L₂ = (|∑ₖ (Eₖ − Ē)·sₖ|/SS_E)/(k_B·smin²·nemin)` (`combinedSlopeTempUpdate_lipschitz`). The
hypothesis `hgate : L₁·L₂ < 1` is the runtime-checkable convergence certificate the solver
flag gates on; `hmapsNe`, `hmapsT` are the two interval invariances and `hslopeFloor` the
combined-slope floor (genuine side conditions, cf. `sahaIter_mapsTo`). Non-degenerate via the
combined Saha–Boltzmann slope (contrast the composition-independent two-line temperature). -/
theorem outerLoop_contracts
    {kB me h chi R0 R : ℝ} {gZ EZ : ιe → ℝ} {gZ1 EZ1 : κe → ℝ}
    {E yb svec : ιl → ℝ} {offConst Tmin Tmax nemin nemax smin : ℝ}
    (hTle : Tmin ≤ Tmax)
    (hkB : 0 < kB) (hme : 0 < me) (hh : 0 < h) (hchi : 0 ≤ chi) (hTmin : 0 < Tmin)
    (hgZ : ∀ k, 0 < gZ k) (hEZ : ∀ k, 0 ≤ EZ k) (hgZ1 : ∀ k, 0 < gZ1 k) (hEZ1 : ∀ k, 0 ≤ EZ1 k)
    (hR0 : 0 < R0) (hR : R0 ≤ R)
    (hvar : 0 < ∑ k, (E k - mean E) ^ 2) (hnemin : 0 < nemin) (hsmin : 0 < smin)
    (hmapsNe : ∀ T ∈ Set.Icc Tmin Tmax,
        electronDensityFromRatio kB T me h chi gZ EZ gZ1 EZ1 R ∈ Set.Icc nemin nemax)
    (hmapsT : ∀ ne ∈ Set.Icc nemin nemax,
        combinedSlopeTempUpdate kB E yb svec offConst ne ∈ Set.Icc Tmin Tmax)
    (hslopeFloor : ∀ ne ∈ Set.Icc nemin nemax,
        smin ≤ combinedSahaBoltzmannSlope E yb svec offConst ne)
    (hL1nn : 0 ≤ sahaFactorLipConst kB Tmin Tmax me h chi gZ EZ gZ1 EZ1 / R0)
    (hgate : (sahaFactorLipConst kB Tmin Tmax me h chi gZ EZ gZ1 EZ1 / R0)
              * ((|∑ k, (E k - mean E) * svec k| / (∑ k, (E k - mean E) ^ 2))
                  / (kB * smin ^ 2 * nemin)) < 1) :
    ∃ Tstar ∈ Set.Icc Tmin Tmax,
      outerMap (fun T => electronDensityFromRatio kB T me h chi gZ EZ gZ1 EZ1 R)
          (fun ne => combinedSlopeTempUpdate kB E yb svec offConst ne) Tstar = Tstar ∧
      (∀ T ∈ Set.Icc Tmin Tmax,
          outerMap (fun T => electronDensityFromRatio kB T me h chi gZ EZ gZ1 EZ1 R)
            (fun ne => combinedSlopeTempUpdate kB E yb svec offConst ne) T = T → T = Tstar) ∧
      ∀ T0 ∈ Set.Icc Tmin Tmax,
        Filter.Tendsto (fun n => (outerMap
            (fun T => electronDensityFromRatio kB T me h chi gZ EZ gZ1 EZ1 R)
            (fun ne => combinedSlopeTempUpdate kB E yb svec offConst ne))^[n] T0)
          Filter.atTop (nhds Tstar) := by
  have hL2nn : (0:ℝ) ≤ (|∑ k, (E k - mean E) * svec k| / (∑ k, (E k - mean E) ^ 2))
      / (kB * smin ^ 2 * nemin) := by positivity
  refine outerContraction_box (nemin := nemin) (nemax := nemax) hTle hmapsNe hmapsT ?_ ?_
    hgate hL1nn hL2nn
  · -- density leg `L₁`-Lipschitz, discharged from the published sensitivity lemma
    intro T hT T' hT'
    obtain ⟨hT1, hT1M⟩ := hT
    obtain ⟨hT2, hT2M⟩ := hT'
    exact electronDensityFromRatio_lipschitz_temp hkB hme hh hchi hTmin hT1 hT2 hT1M hT2M
      hgZ hEZ hgZ1 hEZ1 hR0 hR
  · -- temperature leg `L₂`-Lipschitz, discharged from the combined-slope update (M5)
    intro ne hne ne' hne'
    exact combinedSlopeTempUpdate_lipschitz kB E yb svec hvar hkB hnemin hsmin hne.1 hne'.1
      (hslopeFloor ne hne) (hslopeFloor ne' hne')

end OuterLoopModelB

end CflibsFormal
