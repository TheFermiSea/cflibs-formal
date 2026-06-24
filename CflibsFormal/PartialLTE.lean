/-
Copyright (c) 2026 Brian Squires. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Squires
-/
import Mathlib
import CflibsFormal.StarkBroadening

/-!
# CF-LIBS formalization — the partial-LTE thermalization limit

A principled relaxation of the spec's core LTE assumption. `StarkBroadening.mcWhirterBound` gives a
*lower bound on the electron density* required for LTE for a transition of energy gap `ΔE`:
`n_e ≥ 1.6·10¹²·√T·(ΔE)³`. This module inverts that criterion into a *threshold on the energy gap*:
the **thermalization (collision) limit** `E* = (n_e/(C·√T))^(1/3)`, the largest gap a plasma of
electron density `n_e` at temperature `T` can collisionally thermalize. A transition is
LTE-admissible iff its gap lies at or below `E*`; equivalently, levels near the ionization limit
(small gaps, high absolute energy) thermalize while low-lying large-gap levels deviate
(**partial LTE**).

* `thermalizationLimit` — `E* = (n_e/(C·√T))^(1/3)` (cube root via `Real.rpow`), positive.
* `mcwhirter_iff_thermalizationLimit` — **the headline**: for a gap `ΔE ≥ 0` and `n_e ≥ 0`,
  `(C·√T·ΔE³ ≤ n_e) ⟺ (ΔE ≤ E*)`. The McWhirter density bound and the thermalization-limit energy
  are provably the *same criterion expressed two ways*.
* `lteValid_iff_thermalized` — the bridge in the project's own vocabulary:
  `StarkBroadening.lteValid T ΔE n_e ⟺ thermalized 1.6·10¹² T n_e ΔE`.
* `thermalizationLimit_mono_ne` / `thermalizationLimit_antitone_T` — `E*` increases with `n_e` (a
  denser plasma thermalizes more levels) and decreases with `T`.
* `thermalized_recovers_gap` — round-trip: feeding `E*` back as the gap saturates the McWhirter
  bound exactly.

## Honest scope

McWhirter's criterion is **necessary, not sufficient**, for LTE (collisional dominance, a factor-10
rate ratio); we formalize its *algebra and inversion*, not its derivation, and assert nothing about
LTE actually holding (cf. `StarkBroadening.lteValid`). `ΔE` is the **energy gap** (conventionally
the largest adjacent-level / resonance gap), *not* a level's absolute energy. The companion
pipeline cuts lines on the absolute lower-level energy `E_i ≥ E*`; that is the collision-limit
picture's *approximation* (gap ≈ absolute energy, exact only near the ionization limit where levels
pack together) — it is **documented here, never proven** (no theorem equates `E_i` with `ΔE`). Out
of scope: the full collisional–radiative model, Cristoforetti et al.'s relaxation-time /
diffusion-length refinements (their advance beyond McWhirter), and level departure coefficients.

## Literature

R. W. P. McWhirter, "Spectral Intensities," in R. H. Huddlestone, S. L. Leonard (eds.), *Plasma
Diagnostic Techniques*, Academic Press (1965), ch. 5 — the criterion `n_e ≥ 1.6×10¹²·√T·(ΔE)³`. Its
use and the partial-LTE direction (only levels near the ionization limit attain Saha–Boltzmann
equilibrium) follow G. Cristoforetti et al., "Local Thermodynamic Equilibrium in Laser-Induced
Breakdown Spectroscopy: Beyond the McWhirter criterion," *Spectrochim. Acta B* **65** (2010) 86–95,
and H. R. Griem, *Principles of Plasma Spectroscopy* (Cambridge, 1997). The `1.6·10¹²` prefactor and
the `√T`, `(ΔE)³` scalings are the dimensionless content, matching `StarkBroadening.mcWhirterBound`.
-/

namespace CflibsFormal

open Real

/-- **Partial-LTE thermalization (collision) limit energy** `E* = (n_e/(C·√T))^(1/3)`: the McWhirter
criterion inverted for the largest energy gap a plasma of electron density `n_e` at temperature `T`
can collisionally thermalize. `C` is the McWhirter prefactor (`1.6·10¹²` in CGS), kept an explicit
argument so the general algebra stays `C`-parametric. A transition of gap `ΔE` is LTE-admissible iff
`ΔE ≤ E*`; levels at or above `E*` (near the ionization limit, small gaps) thermalize, levels below
deviate. -/
noncomputable def thermalizationLimit (C T ne : ℝ) : ℝ :=
  (ne / (C * Real.sqrt T)) ^ (1 / 3 : ℝ)

/-- **Partial-LTE membership.** A transition of energy gap `dE` is collisionally thermalized
(Saha–Boltzmann populated) when its gap lies at or below the thermalization limit. The direction is
load-bearing: small gaps (high levels near the ionization limit) thermalize. -/
def thermalized (C T ne dE : ℝ) : Prop :=
  dE ≤ thermalizationLimit C T ne

/-- The thermalization limit is strictly positive for positive prefactor, temperature, and
density. -/
lemma thermalizationLimit_pos {C T ne : ℝ} (hC : 0 < C) (hT : 0 < T) (hne : 0 < ne) :
    0 < thermalizationLimit C T ne := by
  unfold thermalizationLimit
  have hbase : 0 < ne / (C * Real.sqrt T) := div_pos hne (mul_pos hC (Real.sqrt_pos.mpr hT))
  exact Real.rpow_pos_of_pos hbase _

/-- **The McWhirter bound and the thermalization limit are the same criterion, two ways.** For a
nonnegative energy gap `dE` and nonnegative density `ne`, the McWhirter density condition
`C·√T·dE³ ≤ n_e` holds iff the gap is within the thermalization limit, `dE ≤ E*`. The `0 ≤ ne`
hypothesis is load-bearing: for `ne < 0` the cube root `(ne/(C√T))^(1/3)` is not a real cube root
and the equivalence fails. -/
theorem mcwhirter_iff_thermalizationLimit {C T ne dE : ℝ}
    (hC : 0 < C) (hT : 0 < T) (hdE : 0 ≤ dE) (hne : 0 ≤ ne) :
    C * Real.sqrt T * dE ^ 3 ≤ ne ↔ dE ≤ thermalizationLimit C T ne := by
  have hB : 0 < C * Real.sqrt T := mul_pos hC (Real.sqrt_pos.mpr hT)
  unfold thermalizationLimit
  rw [one_div,
    Real.le_rpow_inv_iff_of_pos hdE (by positivity) (by norm_num : (0 : ℝ) < 3),
    show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
    le_div_iff₀ hB, mul_comm (dE ^ 3) (C * Real.sqrt T)]

/-- **The same criterion in the project's own vocabulary.** `StarkBroadening.lteValid` (the
McWhirter density admissibility predicate) is equivalent to the transition being `thermalized` at
the McWhirter prefactor `1.6·10¹²`. -/
theorem lteValid_iff_thermalized {T dE ne : ℝ} (hT : 0 < T) (hdE : 0 ≤ dE) (hne : 0 ≤ ne) :
    lteValid T dE ne ↔ thermalized 1.6e12 T ne dE := by
  unfold lteValid mcWhirterBound thermalized
  exact mcwhirter_iff_thermalizationLimit (by norm_num) hT hdE hne

/-- **A denser plasma thermalizes more levels.** The thermalization limit increases with electron
density (`E* ↑ in n_e`), so the collisionally-equilibrated energy range reaches down to lower
levels. -/
lemma thermalizationLimit_mono_ne {C T : ℝ} (hC : 0 < C) (hT : 0 < T) {ne₁ ne₂ : ℝ}
    (hne₁ : 0 ≤ ne₁) (hne : ne₁ ≤ ne₂) :
    thermalizationLimit C T ne₁ ≤ thermalizationLimit C T ne₂ := by
  unfold thermalizationLimit
  gcongr

/-- **A hotter plasma thermalizes fewer levels.** The thermalization limit decreases with
temperature (`E* ↓ in T`): the McWhirter density bound rises with `√T`, so at fixed `n_e` only
higher levels remain thermalized. -/
lemma thermalizationLimit_antitone_T {C ne : ℝ} (hC : 0 < C) (hne : 0 ≤ ne) {T₁ T₂ : ℝ}
    (hT₁ : 0 < T₁) (hT : T₁ ≤ T₂) :
    thermalizationLimit C T₂ ne ≤ thermalizationLimit C T₁ ne := by
  have hsqrt : Real.sqrt T₁ ≤ Real.sqrt T₂ := Real.sqrt_le_sqrt hT
  have hden : 0 < C * Real.sqrt T₁ := mul_pos hC (Real.sqrt_pos.mpr hT₁)
  unfold thermalizationLimit
  gcongr

/-- **Round-trip: the thermalization limit saturates the McWhirter bound.** Feeding `E*` itself back
as the energy gap exactly attains the McWhirter density bound — the boundary case of the
equivalence. -/
lemma thermalized_recovers_gap {C T ne : ℝ} (hC : 0 < C) (hT : 0 < T) (hne : 0 ≤ ne) :
    C * Real.sqrt T * (thermalizationLimit C T ne) ^ 3 = ne := by
  have hB : 0 < C * Real.sqrt T := mul_pos hC (Real.sqrt_pos.mpr hT)
  unfold thermalizationLimit
  rw [show (1 / 3 : ℝ) = ((3 : ℕ) : ℝ)⁻¹ by norm_num,
    Real.rpow_inv_natCast_pow (by positivity) (by norm_num : (3 : ℕ) ≠ 0),
    mul_div_cancel₀ ne hB.ne']

end CflibsFormal
