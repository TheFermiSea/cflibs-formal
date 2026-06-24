/-
Copyright (c) 2026 Brian Squires. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Squires
-/
import Mathlib

/-!
# CF-LIBS formalization — the hydrogen-line (Balmer) Stark electron-density diagnostic

The **most common** electron-density diagnostic in LIBS: the Stark width of a hydrogen Balmer line
(Hα 656.3 nm, Hβ 486.1 nm) whose Stark parameter is tabulated from theory/simulation. This is
physically **distinct** from `StarkBroadening.lean`'s non-hydrogenic diagnostic. Hydrogen exhibits
the **linear** Stark effect, so the line width tracks the Holtsmark plasma microfield
`F₀ ∝ n_e^(2/3)`; hence the Balmer FWHM scales as `Δλ ∝ n_e^(2/3)` and, inverted, `n_e ∝ Δλ^(3/2)`.
Contrast `StarkBroadening.starkFWHM = 2w·(n_e/n_ref)`, which is **linear** in `n_e` (the *quadratic*
Stark effect of non-hydrogenic lines). The non-linear `2/3` power is the whole point.

* `hydrogenStarkFWHM w nRef ne = w·(n_e/n_ref)^(2/3)` — forward map (electron density → Balmer
  FWHM), with `w` the reference Stark width at `n_ref`.
* `densityFromHydrogenStark w nRef width = n_ref·(Δλ/w)^(3/2)` — the inverse diagnostic: read `n_e`
  off a *measured* Balmer width.
* `densityFromHydrogenStark_recovers` — soundness: the diagnostic exactly inverts the forward map
  (the `(2/3)·(3/2) = 1` exponent identity).
* `hydrogenStarkFWHM_strictMonoOn` / `hydrogenStarkFWHM_injOn` — strictly increasing in `n_e`, so
  `n_e` is identifiable from the measured width.

## Honest scope

The `2/3` exponent (linear Stark effect via `F₀ ∝ n_e^(2/3)`) is the faithful, distinguishing
content. The reduced Stark width parameter `α_(1/2)(n_e,T)` is only *weakly* density/temperature
dependent; folding it into the constant `w` (so the relation is a clean power law) is the standard
**leading-order operational approximation** — exact only in the limit of a constant reduced width.
Out of scope: ion-dynamic corrections (significant for Hα; Hβ is preferred for diagnostics), the
asymmetric double-peaked Stark *profile* `I(λ)` (only the FWHM↔`n_e` scalar relation is modeled),
and lower-state / fine-structure effects.

## Literature

The linear Stark effect of hydrogen and the `Δλ ∝ n_e^(2/3)` scaling are from H. R. Griem, *Spectral
Line Broadening by Plasmas*, Academic Press (1974), and *Principles of Plasma Spectroscopy*
(Cambridge, 1997). The modern tabulated Balmer Stark-width ↔ `n_e` relations (the practically used
`α_(1/2)` values) are from M. A. Gigosos, M. Á. González, V. Cardeñoso, "Computer simulated
Balmer-α, -β and -γ Stark line profiles for non-equilibrium plasmas diagnostics," *Spectrochim. Acta
B* **58** (2003) 1489–1504, the standard reference for hydrogen-line plasma diagnostics.
-/

namespace CflibsFormal

/-- **Hydrogen Balmer-line Stark FWHM (forward map).** For the linear Stark effect of hydrogen the
width tracks the Holtsmark microfield `F₀ ∝ n_e^(2/3)`, so `Δλ = w·(n_e/n_ref)^(2/3)`, with `w` the
reference Stark width at electron density `n_ref`. The `2/3` power (not `1`) distinguishes this from
the non-hydrogenic `StarkBroadening.starkFWHM`. -/
noncomputable def hydrogenStarkFWHM (w nRef ne : ℝ) : ℝ :=
  w * (ne / nRef) ^ (2 / 3 : ℝ)

/-- **Hydrogen-line electron-density diagnostic (inverse map).** Inverting
`Δλ = w·(n_e/n_ref)^(2/3)` gives `n_e = n_ref·(Δλ/w)^(3/2)` — reading `n_e` off a *measured* Balmer
width. A function of the
observation, never of the true `n_e`. -/
noncomputable def densityFromHydrogenStark (w nRef width : ℝ) : ℝ :=
  nRef * (width / w) ^ (3 / 2 : ℝ)

/-- The hydrogen-line Stark width is strictly positive for positive width parameter, reference
density, and electron density. -/
lemma hydrogenStarkFWHM_pos {w nRef ne : ℝ} (hw : 0 < w) (hnRef : 0 < nRef) (hne : 0 < ne) :
    0 < hydrogenStarkFWHM w nRef ne := by
  unfold hydrogenStarkFWHM
  have hbase : 0 < ne / nRef := div_pos hne hnRef
  positivity

/-- **Soundness of the hydrogen-line diagnostic.** The diagnostic exactly inverts the forward map:
the electron density read off the measured Balmer width equals the true `n_e`. The key step is the
exponent identity `(2/3)·(3/2) = 1`. -/
theorem densityFromHydrogenStark_recovers {w nRef ne : ℝ}
    (hw : 0 < w) (hnRef : 0 < nRef) (hne : 0 ≤ ne) :
    densityFromHydrogenStark w nRef (hydrogenStarkFWHM w nRef ne) = ne := by
  have hwne : w ≠ 0 := hw.ne'
  have hnRefne : nRef ≠ 0 := hnRef.ne'
  have hbase : (0 : ℝ) ≤ ne / nRef := div_nonneg hne hnRef.le
  unfold densityFromHydrogenStark hydrogenStarkFWHM
  rw [show w * (ne / nRef) ^ (2 / 3 : ℝ) / w = (ne / nRef) ^ (2 / 3 : ℝ) by field_simp,
    ← Real.rpow_mul hbase, show (2 / 3 : ℝ) * (3 / 2) = 1 by norm_num, Real.rpow_one]
  field_simp

/-- **Strict monotonicity of the Balmer width in `n_e`.** A denser plasma broadens the hydrogen line
more (the `n_e^(2/3)` map is strictly increasing on the nonnegative reals). With `injOn` this gives
identifiability of `n_e` from the measured width. -/
theorem hydrogenStarkFWHM_strictMonoOn {w nRef : ℝ} (hw : 0 < w) (hnRef : 0 < nRef) :
    StrictMonoOn (hydrogenStarkFWHM w nRef) (Set.Ici 0) := by
  intro a ha b _hb hab
  have ha0 : 0 ≤ a := ha
  unfold hydrogenStarkFWHM
  have hlt : (a / nRef) ^ (2 / 3 : ℝ) < (b / nRef) ^ (2 / 3 : ℝ) :=
    Real.rpow_lt_rpow (by positivity) (by gcongr) (by norm_num)
  exact mul_lt_mul_of_pos_left hlt hw

/-- **Identifiability of `n_e` from the Balmer width.** Distinct densities give distinct widths: the
forward map is injective on the nonnegative reals. -/
theorem hydrogenStarkFWHM_injOn {w nRef : ℝ} (hw : 0 < w) (hnRef : 0 < nRef) :
    Set.InjOn (hydrogenStarkFWHM w nRef) (Set.Ici 0) :=
  (hydrogenStarkFWHM_strictMonoOn hw hnRef).injOn

end CflibsFormal
