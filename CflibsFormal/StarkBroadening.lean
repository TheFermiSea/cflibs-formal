/-
Copyright (c) 2026 Brian Squires. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Squires
-/
import Mathlib
import CflibsFormal.Boltzmann
import CflibsFormal.Saha
import CflibsFormal.SahaInverse

/-!
# Saha–Boltzmann formalization — Stark broadening + the McWhirter LTE criterion

This module formalizes a *second, physically independent* electron-density
diagnostic — the **electron-impact (Stark) line width** — and the **McWhirter
lower bound** on the electron density that the assumption of local thermodynamic
equilibrium (LTE) requires. It then ties the two together with a genuine
two-diagnostic cross-check.

* `starkFWHM` — the forward map (electron density → Stark full width at half
  maximum). For an isolated Lorentzian line broadened by electron impacts,
  Griem's theory makes the Stark FWHM *linear* in the electron density:
  `Δλ = 2·w·(n_e/n_ref)`, with `w` the electron-impact width parameter tabulated
  at a reference electron density `n_ref`.
* `starkDensity` — the inverse (diagnostic) map: it reads `n_e` off a *measured*
  Stark width `n_e = n_ref·Δλ/(2·w)`. It is a genuine function of the
  OBSERVATION (the width), never of the true `n_e`.
* `starkDensity_recovers` — soundness: the diagnostic exactly inverts the forward
  map.
* `starkFWHM_strictMono` / `starkFWHM_injective` — the width strictly increases
  with `n_e`, so `n_e` is identifiable from the measured width.
* `starkFWHM_additive` / `starkFWHM_homogeneous` — the Griem linearity: the Stark
  width is additive and positively homogeneous in `n_e` (full ℝ-linearity). NB:
  these are algebraic identities; at the unphysical edge `n_ref = 0` both sides
  collapse to `0` (Lean's `x/0 = 0`) and the identities hold vacuously — they
  carry physical meaning only for `n_ref ≠ 0`.
* `mcWhirterBound` / `lteValid` — the McWhirter lower bound
  `n_e ≥ 1.6·10¹²·√T·(ΔE)³` and the LTE-admissibility predicate.
* `mcWhirterBound_mono_T` / `mcWhirterBound_mono_dE` — a hotter plasma or a larger
  energy gap demands a higher electron density for LTE.
* `stark_saha_lte_consistent` — **the cross-check.** A *conditional bundling*
  theorem: IF the Stark route (n_e from a measured line WIDTH) and the Saha route
  (n_e from a measured stage-intensity RATIO `R`, reusing `Saha.lean`) yield the
  SAME electron density AND that value clears the McWhirter bound, THEN a single
  `n_e` is simultaneously consistent with BOTH independent forward laws (the
  Griem width via `starkFWHM` and the Saha law via `saha_relation`) and LTE.
  Because the two diagnostics consume genuinely DIFFERENT observations (a width
  vs a stage ratio), their agreement is real evidence, not `n_e = n_e` by
  construction. Honest scoping: agreement (`hagree`) is *assumed*, not proven —
  the two diagnostics are NOT shown to necessarily coincide; clauses 1–3 of the
  conclusion restate the hypotheses, and only clauses 4–5 carry forward-law
  content.

## Literature

The electron-impact (Stark) linear-width relation is that of H. R. Griem,
*Spectral Line Broadening by Plasmas*, Academic Press, New York (1974): for an
isolated line broadened by electron impacts the Stark FWHM is linear in the
electron density, `Δλ = 2·w·(n_e/n_ref)`, with `w` the electron-impact width
parameter tabulated at a reference electron density `n_ref`. The McWhirter
criterion `n_e ≥ 1.6×10¹²·√T·(ΔE)³` for the lower bound on the electron density
required for LTE is taken as recalled by G. Cristoforetti, A. De Giacomo,
M. Dell'Aglio, S. Legnaioli, E. Tognoni, V. Palleschi and N. Omenetto, "Local
Thermodynamic Equilibrium in Laser-Induced Breakdown Spectroscopy: Beyond the
McWhirter criterion," *Spectrochimica Acta Part B* **65** (2010) 86. The Saha
route reused (not reproved) in the cross-check is that of `Saha.lean` /
`SahaInverse.lean`, after S. Yalcin, D. R. Crosley, G. P. Smith, G. W. Faris,
*Applied Physics B* **68** (1999) 121 and J. A. Aguilera, C. Aragón,
*Spectrochimica Acta Part B* **62** (2007) 378. The definitions and equations
below match the cited methods.
-/

namespace CflibsFormal

open Finset Real
open scoped BigOperators

variable {ι : Type*} [Fintype ι]
variable {κ : Type*} [Fintype κ]

/-- **Electron-impact (Stark) full width at half maximum.** For a Lorentzian line
broadened by electron impacts, Griem's theory gives a Stark FWHM that is *linear*
in the electron density: `Δλ = 2·w·(n_e / n_ref)`, with `w` the electron-impact
width parameter tabulated at a reference electron density `n_ref`. This is the
forward map (electron density → measured line width). -/
noncomputable def starkFWHM (w nRef ne : ℝ) : ℝ :=
  2 * w * (ne / nRef)

/-- **Stark electron-density diagnostic (inverse map).** Solving the Griem
electron-impact relation `Δλ = 2·w·(n_e/n_ref)` for `n_e` gives
`n_e = n_ref · Δλ / (2·w)`. This reads the electron density off a *measured*
Stark FWHM `width` — a genuine function of the observation, never of the true
`n_e`. -/
noncomputable def starkDensity (w nRef width : ℝ) : ℝ :=
  nRef * width / (2 * w)

/-- **McWhirter lower bound on electron density for LTE.** The classical
McWhirter criterion (as recalled by Cristoforetti et al. 2010) requires, for the
upper level energy gap `dE` (the largest relevant gap) at temperature `T`,
`n_e ≥ 1.6·10¹² · √T · (ΔE)³` for collisional (LTE) processes to dominate
radiative ones. The numerical prefactor and the `√T`, `(ΔE)³` scalings are the
dimensionless content of the criterion. -/
noncomputable def mcWhirterBound (T dE : ℝ) : ℝ :=
  1.6e12 * Real.sqrt T * dE ^ 3

/-- **LTE-validity predicate.** Local thermodynamic equilibrium is admissible
(by the McWhirter criterion) when the electron density is at least the McWhirter
bound for the given temperature and energy gap: `mcWhirterBound T dE ≤ n_e`. -/
def lteValid (T dE ne : ℝ) : Prop :=
  mcWhirterBound T dE ≤ ne

/-- **Soundness of the Stark diagnostic.** The diagnostic exactly inverts the
Griem forward map: the electron density read off the measured Stark width equals
the true `n_e`. Both hypotheses `w ≠ 0`, `n_ref ≠ 0` are load-bearing (with
`w = 0` the inverse divides by zero and the round-trip fails). -/
theorem starkDensity_recovers {w nRef ne : ℝ} (hw : w ≠ 0) (hnRef : nRef ≠ 0) :
    starkDensity w nRef (starkFWHM w nRef ne) = ne := by
  simp only [starkDensity, starkFWHM]
  field_simp

/-- **Strict monotonicity of the Stark width in `n_e`.** A denser plasma broadens
the line more: the Stark width is strictly increasing in the electron density.
With `strictMono.injective` this yields identifiability of `n_e` from the width.
The positivity hypotheses are load-bearing (with `w = 0` the map is constant). -/
theorem starkFWHM_strictMono {w nRef : ℝ} (hw : 0 < w) (hnRef : 0 < nRef) :
    StrictMono (starkFWHM w nRef) := by
  intro a b hab
  simp only [starkFWHM]
  gcongr

/-- **Identifiability of `n_e` from the Stark width.** Distinct densities give
distinct widths: the forward map is injective. The identifiability companion to
`starkDensity_recovers`. -/
theorem starkFWHM_injective {w nRef : ℝ} (hw : 0 < w) (hnRef : 0 < nRef) :
    Function.Injective (starkFWHM w nRef) :=
  (starkFWHM_strictMono hw hnRef).injective

/-- **Additivity of the Stark width in `n_e` (Griem linearity).** The
electron-impact width is additive in the electron density — the defining
linearity of the electron-impact (Lorentzian) mechanism. Holds unconditionally
(at the unphysical edge `n_ref = 0` both sides are `0`). -/
theorem starkFWHM_additive (w nRef a b : ℝ) :
    starkFWHM w nRef (a + b) = starkFWHM w nRef a + starkFWHM w nRef b := by
  unfold starkFWHM; ring

/-- **Positive homogeneity of the Stark width in `n_e` (Griem linearity).** The
Stark width scales linearly in the electron density: doubling `n_e` doubles the
width. With additivity this is full ℝ-linearity in `n_e`. Unconditional. -/
theorem starkFWHM_homogeneous (w nRef c ne : ℝ) :
    starkFWHM w nRef (c * ne) = c * starkFWHM w nRef ne := by
  unfold starkFWHM; ring

/-- **McWhirter bound increases with temperature.** A hotter plasma demands a
higher electron density for LTE (the bound scales as `√T`). Only `hdE : 0 ≤ dE`
is load-bearing (so `dE³ ≥ 0` preserves the order); `Real.sqrt` is monotone on
all of ℝ, so no nonnegativity premise on `T` is needed. -/
theorem mcWhirterBound_mono_T {dE T₁ T₂ : ℝ} (hdE : 0 ≤ dE) (hT : T₁ ≤ T₂) :
    mcWhirterBound T₁ dE ≤ mcWhirterBound T₂ dE := by
  unfold mcWhirterBound
  gcongr

/-- **McWhirter bound increases with the energy gap.** A larger energy gap demands
a higher electron density for LTE (the bound scales as `(ΔE)³`). Only
`hdE₁ : 0 ≤ dE₁` is load-bearing (the cube is order-preserving only for a nonneg
base); `√T ≥ 0` holds unconditionally (`Real.sqrt_nonneg`), so the prefactor
nonnegativity needs no premise on `T`. `_hT : 0 ≤ T` is kept only as physical
documentation that the bound is intended for nonnegative temperatures. -/
theorem mcWhirterBound_mono_dE {T dE₁ dE₂ : ℝ} (_hT : 0 ≤ T)
    (hdE₁ : 0 ≤ dE₁) (hdE : dE₁ ≤ dE₂) :
    mcWhirterBound T dE₁ ≤ mcWhirterBound T dE₂ := by
  unfold mcWhirterBound
  gcongr

/-- **Stark–Saha LTE cross-check (conditional bundling).** A genuine two-diagnostic
consistency theorem. The Stark route recovers `n_e` from a measured line WIDTH
(`starkDensity`), the Saha route recovers `n_e` from a measured stage-intensity
RATIO `R` (`electronDensityFromRatio`, reused from `Saha.lean`) — two physically
INDEPENDENT diagnostics consuming genuinely DIFFERENT observations. The theorem
certifies: IF the two estimates agree (`hagree`) AND the common value clears the
McWhirter bound (`hlte`), THEN there exists a single `n_e` that

* (1) equals the Stark estimate, (2) equals the Saha estimate, (3) is LTE-valid —
  these three restate the hypotheses; and
* (4) re-derives the observed width through the Griem forward map
  `width = starkFWHM w nRef ne` (the inversion content, needs `hw`, `hnRef`), and
  (5) satisfies the structural Saha law `R·n_e = sahaFactor` (via `saha_relation`,
  needs `hR`).

Honest scoping: agreement (`hagree`) is *assumed*, not proven — the two
diagnostics are NOT shown to necessarily coincide. The substance is that the two
sides feed DIFFERENT observations (a WIDTH vs a stage RATIO `R`), so their
equality is empirical evidence rather than a definitional identity, and clauses
4–5 tie the single recovered `n_e` back to both independent forward laws. -/
theorem stark_saha_lte_consistent {w nRef width : ℝ}
    {kB T me h chi : ℝ} {gZ EZ : ι → ℝ} {gZ1 EZ1 : κ → ℝ} {R dE : ℝ}
    (hw : w ≠ 0) (hnRef : nRef ≠ 0) (hR : R ≠ 0)
    (hagree :
      starkDensity w nRef width
        = electronDensityFromRatio kB T me h chi gZ EZ gZ1 EZ1 R)
    (hlte : lteValid T dE (starkDensity w nRef width)) :
    ∃ ne : ℝ,
      ne = starkDensity w nRef width
        ∧ ne = electronDensityFromRatio kB T me h chi gZ EZ gZ1 EZ1 R
        ∧ mcWhirterBound T dE ≤ ne
        ∧ width = starkFWHM w nRef ne
        ∧ R * ne = sahaFactor kB T me h chi gZ EZ gZ1 EZ1 := by
  refine ⟨starkDensity w nRef width, rfl, hagree, hlte, ?_, ?_⟩
  · -- width = starkFWHM w nRef (starkDensity w nRef width) — the inversion.
    simp only [starkFWHM, starkDensity]
    field_simp
  · -- R · n_e = sahaFactor, via the Saha structural law and the agreement bridge.
    exact (saha_relation hR).mp hagree

end CflibsFormal
