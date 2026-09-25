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
lower bound** on the electron density, a necessary (not sufficient) condition for
local thermodynamic equilibrium (LTE). It then states a *conditional bundling* of
the Stark width, the Saha route and the McWhirter test.

* `starkFWHM` — the forward map (electron density → Stark full width at half
  maximum). For an isolated Lorentzian line broadened by electron impacts,
  Griem's theory makes the Stark FWHM *linear* in the electron density:
  `Δλ = 2·w·(n_e/n_ref)`, with `w` the electron-impact width parameter tabulated
  at a reference electron density `n_ref`. Electron-impact term only (see
  *Scope* below).
* `starkDensity` — the inverse (diagnostic) map: it reads `n_e` off a *measured*
  Stark width `n_e = n_ref·Δλ/(2·w)`. It is a genuine function of the
  OBSERVATION (the width), never of the true `n_e`.
* `starkDensity_recovers` — soundness: the diagnostic exactly inverts the forward
  map.
* `starkFWHM_strictMono` / `starkFWHM_injective` — the width strictly increases
  with `n_e`, so `n_e` is identifiable from the measured width.
* `starkFWHM_isLinear` — the Griem linearity, bundled: `starkFWHM w nRef` is an
  `ℝ`-**linear map** in `n_e` (`IsLinearMap`). The linear dependence of the Stark
  width on the electron density is the defining feature of the electron-impact
  (Lorentzian) mechanism; stating it as `IsLinearMap` (rather than separate
  distributivity identities) makes that the single, meaningful claim.
* `mcWhirterBound` / `lteValid` — the McWhirter lower bound
  `n_e ≥ 1.6·10¹²·√T·(ΔE)³`, in the units `n_e` [cm⁻³], `T` [K], `ΔE` [eV], and the
  McWhirter-admissibility predicate. Despite its name, `lteValid` is only the McWhirter
  test: necessary, not sufficient, for LTE (see the scope note in `PartialLTE`).
* `mcWhirterBound_mono_T` / `mcWhirterBound_mono_dE` — a hotter plasma or a larger
  energy gap raises the McWhirter bound.
* `stark_saha_lte_consistent` — a *conditional bundling* theorem, not a cross-check
  that can fail. IF the Stark estimate (n_e from a measured line WIDTH) and the Saha
  estimate (n_e from a stage population ratio `R = n_{z+1}/n_z`, reusing `Saha.lean`)
  are EXACTLY equal as real numbers AND that value clears the McWhirter bound, THEN
  one `n_e` satisfies both forward laws (the Griem width via `starkFWHM` and the Saha
  law via `saha_relation`) and the McWhirter test. Agreement (`hagree`) is *assumed*,
  never derived: the two diagnostics are NOT shown to coincide, and no disagreement
  bound or tolerance form is proved. Clauses 1–3 of the conclusion restate the
  hypotheses; clauses 4–5 are the algebraic inversions of `starkFWHM` and of the
  Saha relation. The hypothesis is not vacuous (the two sides consume different
  observations, a width and a stage ratio), but the conclusion adds no physics
  beyond the definitions.

## Scope

* **Electron-impact width only.** The quasi-static ion-broadening correction, which
  makes the width nonlinear in `n_e` (in the companion pipeline its ion parameter
  scales as `n_e^{1/4}`), is out of scope here, as it is in `StarkShift`.
  `starkDensity_recovers` therefore inverts a forward model that includes the ion
  term only when that term is zero.
* **Units.** `mcWhirterBound` is not unit-free: its prefactor `1.6·10¹²` fixes `n_e` in
  cm⁻³, `T` in K and `ΔE` in eV (see its docstring). The Stark and Saha maps are
  unit-agnostic, so every statement that combines them with `lteValid` needs the same
  convention.

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
forward map (electron density → measured line width).

REDUCED model: the electron-impact term only, linear in `n_e`, with `w` fixed at its
reference-density value. The quasi-static ion-broadening correction, which makes the
width nonlinear in `n_e`, is not modelled. -/
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
radiative ones. The criterion is necessary, not sufficient, for LTE.

**Units.** The prefactor `1.6·10¹²` fixes the units: the bound is a density in cm⁻³,
`T` is in K and `dE` in eV. The bound is not unit-free, and this mixed convention (eV
is not a CGS unit) is not covered by the `Dimensions` layer, whose `siToCgs` rescales
only length and mass. In other units it is wrong by
orders of magnitude: `T` in eV instead of K makes the bound about 108 times too small
(`√11604.5 ≈ 107.7`), and comparing it against `n_e` in m⁻³ makes the test 10⁶ times
too lax. -/
noncomputable def mcWhirterBound (T dE : ℝ) : ℝ :=
  1.6e12 * Real.sqrt T * dE ^ 3

/-- **McWhirter-admissibility predicate** (the name `lteValid` overstates it). The
electron density is at least the McWhirter bound for the given temperature and energy
gap: `mcWhirterBound T dE ≤ n_e`, with `n_e` in cm⁻³, `T` in K and `dE` in eV (the
units of `mcWhirterBound`). This is necessary, not sufficient, for LTE: it does not
test the relaxation-time or diffusion-length conditions a transient, inhomogeneous
plasma also needs (see the scope note in `PartialLTE`). Passing it does not establish
LTE. -/
def lteValid (T dE ne : ℝ) : Prop :=
  mcWhirterBound T dE ≤ ne

/-- **Soundness of the Stark diagnostic.** The diagnostic exactly inverts the
Griem forward map: the electron density read off the measured Stark width equals
the true `n_e`. Both hypotheses `w ≠ 0`, `n_ref ≠ 0` are load-bearing (with
`w = 0` the inverse divides by zero and the round-trip fails). The forward map is the
electron-impact width only: a width that also carries the quasi-static ion term is
inverted exactly only when that term is zero. -/
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

/-- **Griem linearity, bundled (`IsLinearMap`).** For fixed `w`, `n_ref`, the Stark
width `starkFWHM w nRef : ℝ → ℝ` is an `ℝ`-linear map in the electron density — the
defining linear dependence of the electron-impact (Lorentzian) mechanism. Folds the
additivity and homogeneity facts into the single meaningful structural claim. (As a
linear map it is, in particular, additive and homogeneous; at the unphysical edge
`n_ref = 0` it degenerates to the zero map, still linear.) -/
theorem starkFWHM_isLinear (w nRef : ℝ) : IsLinearMap ℝ (starkFWHM w nRef) where
  map_add a b := by simp only [starkFWHM]; ring
  map_smul c ne := by simp only [starkFWHM, smul_eq_mul]; ring

/-- **McWhirter bound increases with temperature.** A hotter plasma demands a
higher electron density to pass the McWhirter test (the bound scales as `√T`). Only
`hdE : 0 ≤ dE` is load-bearing (so `dE³ ≥ 0` preserves the order); `Real.sqrt` is
monotone on all of ℝ, so no nonnegativity premise on `T` is needed. -/
theorem mcWhirterBound_mono_T {dE T₁ T₂ : ℝ} (hdE : 0 ≤ dE) (hT : T₁ ≤ T₂) :
    mcWhirterBound T₁ dE ≤ mcWhirterBound T₂ dE := by
  unfold mcWhirterBound
  gcongr

/-- **McWhirter bound increases with the energy gap.** A larger energy gap demands
a higher electron density to pass the McWhirter test (the bound scales as `(ΔE)³`).
Only `hdE₁ : 0 ≤ dE₁` is load-bearing (the cube is order-preserving only for a nonneg
base); `√T ≥ 0` holds unconditionally (`Real.sqrt_nonneg`), so the prefactor
nonnegativity needs no premise on `T`. `_hT : 0 ≤ T` is kept only as physical
documentation that the bound is intended for nonnegative temperatures. -/
theorem mcWhirterBound_mono_dE {T dE₁ dE₂ : ℝ} (_hT : 0 ≤ T)
    (hdE₁ : 0 ≤ dE₁) (hdE : dE₁ ≤ dE₂) :
    mcWhirterBound T dE₁ ≤ mcWhirterBound T dE₂ := by
  unfold mcWhirterBound
  gcongr

/-- **Stark–Saha–McWhirter conditional bundling.** The Stark route recovers `n_e` from
a measured line WIDTH (`starkDensity`); the Saha route recovers `n_e` from a stage
population ratio `R = n_{z+1}/n_z` (`electronDensityFromRatio`, reused from
`Saha.lean`; `R` must itself be recovered from line intensities first). The two
consume different observations. The theorem states: IF the two estimates are EXACTLY
equal as real numbers (`hagree`) AND the common value clears the McWhirter bound
(`hlte`), THEN there exists a single `n_e` that

* (1) equals the Stark estimate, (2) equals the Saha estimate, (3) passes the
  McWhirter test — these three restate the hypotheses; and
* (4) re-derives the observed width through the Griem forward map
  `width = starkFWHM w nRef ne` (the algebraic inversion of `starkDensity`, needs
  `hw`, `hnRef`), and (5) satisfies the structural Saha law `R·n_e = sahaFactor`
  (via `saha_relation`, needs `hR`).

Scope. Agreement is *assumed*, never derived: the two diagnostics are NOT shown to
coincide, and nothing here bounds their disagreement. Exact real equality of two
measured estimates is an idealization; the theorem does not cover a tolerance test
such as `|Δn_e|/mean ≤ rtol`. The hypothesis is not vacuous (a width and a stage ratio
are different data), but the conclusion adds no physics beyond the definitions of the
two forward laws. Clause (3) is the McWhirter test only: necessary, not sufficient,
for LTE. Units: clause (3) fixes `n_e` in cm⁻³, `T` in K and `dE` in eV (see
`mcWhirterBound`), so the conclusion is physically meaningful only when `nRef` is in
cm⁻³ and `sahaFactor` returns cm⁻³ at `T` in kelvin (e.g. CGS `me`, `h`, `kB`, with
`chi` and the level energies in the energy unit of `kB·T`). The Stark side is the
electron-impact width only; the ion-broadening term is out of scope. -/
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
