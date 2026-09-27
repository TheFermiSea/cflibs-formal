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
(`SahaEquilibrium`, Frontier 04 M1) its **content** by instantiating it with two concrete legs:

* the density reader `legNe : T ↦ n_e(T) = S(T)/R` (`electronDensityFromRatio`, `Saha`) with a
  **fixed** stage ratio `R`, whose `T`-Lipschitz constant `L₁ = sahaFactorLipConst/R₀` is
  discharged from the sensitivity lemma `electronDensityFromRatio_lipschitz_temp`
  (`SahaStability`);
* the temperature update `legT : n_e ↦ 1/(k_B·slope(n_e))` (`combinedSlopeTempUpdate`,
  `ErrorBudget`), built from a single-element **combined Saha–Boltzmann slope** after
  Aguilera & Aragón 2007 with a **frozen** Saha offset `offConst`, whose `n_e`-Lipschitz
  constant `L₂` is discharged from `combinedSlopeTempUpdate_lipschitz`.

Under the gate `L₁·L₂ < 1` and the carried side conditions, the composite sweep
`Φ = legT ∘ legNe` on the temperature box `[Tmin,Tmax]` has a **unique** fixed point `T⋆` in the
box, and the iterates converge to it geometrically from every start in the box.

**Why "Model B".** ("Model B" is this repo's own Frontier-04 designation for the loop built on
the combined Saha–Boltzmann slope of Aguilera & Aragón 2007 — the paper itself does not use the
name; it is defined here by contrast with the refuted "Model A" single-stage loop.) This
Frontier-04 "Model B" is UNRELATED to the refuted 2DCOS "Model B" (the nₑ-elimination /
"standardless" method audited unsound and removed; see `docs/2dcos/ERRATA.md`) — the name
collision is coincidental. The single-stage two-line temperature is composition-independent
(`ForwardMap.temperature_from_two_lines`), so a `T`-leg built from it is a *constant* map and
the outer loop would be degenerate (`L = 0`, headline true-but-vacuous). The combined slope
depends on `n_e` through the Saha offset `offConst − log n_e` (witnessed in `ErrorBudget`), so
at a *fixed* `offConst` the composite `Φ` is not constant. That non-degeneracy comes from
freezing the offset; see the scope section. (The abstract spine is agnostic to the `n_e`
source — a Stark-broadening `n_e` leg would instantiate it equally well.)

## Scope: the model the theorem is about (`REDUCED`)

The theorem is exact for the map it states. The reduction is in what that map models.

* **Frozen Saha offset.** `offConst` is one real number. Its physical reading is the
  `n_e`-independent part `log S(T_ref) + log U_z(T_ref) − log U_{z+1}(T_ref)` of the Saha
  offset at a reference temperature `T_ref`, while `legNe` evaluates `S(T)` at the current `T`.
  If the offset is instead evaluated at the current `T`, its `log S(T)` cancels the one in
  `log n_e(T) = log S(T) − log R`, and the offset becomes `log R + log U_z(T) − log U_{z+1}(T)`.
  `Φ` then depends on `T` only through the partition-function ratio; with
  `offConst = log S(T)` it is constant:
  `combinedSlopeTempUpdate … (log S(T)) (S(T)/R) = combinedSlopeTempUpdate … (log R) 1` for
  every `T > 0`. The 2026-09-24 audit (finding INV-01) proved this identity axiom-clean in
  scratch as `modelB_consistent_offset_degenerate`; it is not yet stated in this library. So
  the Saha coupling that makes `Φ` non-constant here exists only because the offset is frozen.
* **Fixed stage ratio.** `legNe` reads `n_e` from a fixed measured stage-population ratio `R`.
  It does not re-derive `R` from Boltzmann-plot intercepts at the current `T`.
* **Single-element, unshifted plot.** The slope is one unweighted OLS fit with a single
  intercept on the unshifted abscissa `E`; the `−χ/(k_B T)` term rides in the offset (see
  `combinedSahaBoltzmannSlope`).
* **Not `iterative.py`.** The companion pipeline's outer loop differs on every point above: its
  `n_e` leg re-derives the stage ratio from intercepts at the current `T`, it shifts ion
  abscissae by the ionization energy, it fits one intercept per element, and it iterates a
  0.5-damped Gauss–Seidel scheme with holds. This theorem neither certifies nor diagnoses that
  loop and is not acceptance material for it.

**Side conditions.** The two interval invariances `hmapsNe`, `hmapsT` and the slope floor
`hslopeFloor` are explicit hypotheses (genuine side conditions, as the inner-loop
`sahaIter_mapsTo` carries `√(S·Ntot) ≤ b`). `outerLoop_contracts_apriori`
(`SahaRangeEnclosure`) discharges `hmapsNe` from the box endpoints; `hmapsT` and `hslopeFloor`
stay a-posteriori.

**The gate does not fire on real data.** `L₁·L₂ < 1` is a **sufficient**, not necessary,
condition. It is arithmetic on known quantities, but its constants are loose:
`sahaFactorLipConst` exceeds the true `sup |dS/dT|` by factors of 7.7×10⁵ to 9.7×10⁷ on
production atomic data (audit finding PS-03: Fe, Ti, Al, Ca and V, levels below the ionization
energy, `T ∈ [0.8, 1.2]` eV). On a Ti-like test case (audit finding INV-03: `χ = 6.83` eV,
single-level partition functions, six neutral and six ion lines, fixed point `T⋆ = 11 000` K at
`n_e = 10¹⁷ cm⁻³`) the gate evaluates to `L₁·L₂ ≈ 6×10³`–`5×10⁴` on boxes of half-width
500–2000 K, and `Φ`'s own derivative there is `|Φ′(T⋆)| ≈ 2.39`. Since `L₁·L₂` bounds the
Lipschitz constant of `Φ` on the box, no box with `T⋆` in its interior can pass the gate in that
case, however tight the constants. No concrete end-to-end witness satisfying all hypotheses
simultaneously is constructed here; the component non-degeneracy (`ErrorBudget` witnesses) and
the abstract spine's witnesses cover the non-vacuity of the pieces.
-/

namespace CflibsFormal

open Finset Real
open scoped NNReal BigOperators

section OuterLoopModelB
variable {ιe : Type*} [Fintype ιe] [Nonempty ιe]
variable {κe : Type*} [Fintype κe] [Nonempty κe]
variable {ιl : Type*} [Fintype ιl] [Nonempty ιl]

/-- **The frozen-offset Model-B outer loop contracts** (`REDUCED`; Aguilera & Aragón 2007,
Model B). Instantiate the abstract two-leg spine `outerContraction_box` with the density reader
`legNe T = electronDensityFromRatio … T … R` (fixed stage ratio `R`) and the combined-slope
temperature update `legT ne = combinedSlopeTempUpdate … offConst ne` (fixed offset `offConst`).
Then the sweep `Φ = legT ∘ legNe` on `[Tmin,Tmax]` has a **unique** fixed point `T⋆` in the box,
and the iterates `Φ^[n] T₀` converge to `T⋆` from every start in the box.

The density leg's `T`-Lipschitz constant is `L₁ = sahaFactorLipConst/R₀`
(`electronDensityFromRatio_lipschitz_temp`); the temperature leg's `n_e`-Lipschitz constant is
`L₂ = (|∑ₖ (Eₖ − Ē)·sₖ|/SS_E)/(k_B·smin²·nemin)` (`combinedSlopeTempUpdate_lipschitz`). The
hypothesis `hgate : L₁·L₂ < 1` is a sufficient convergence condition; `hmapsNe`, `hmapsT` are the
two interval invariances and `hslopeFloor` the combined-slope floor (genuine side conditions, cf.
`sahaIter_mapsTo`).

Reduction (why `REDUCED`): the Saha offset is frozen at a reference `T` while `legNe` uses `S(T)`
at the current `T`, and `legNe` reads a fixed measured stage ratio `R`. With the offset evaluated
at the current `T` the Saha coupling cancels: `Φ` then depends on `T` only through
`U_z(T)/U_{z+1}(T)`, and is constant when `offConst = log S(T)` (module docstring, audit finding
INV-01). The map is not the companion's `iterative.py` loop, and on real atomic data `hgate`
fails by orders of magnitude (module docstring). -/
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
