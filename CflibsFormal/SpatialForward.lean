/-
Copyright (c) 2026 Brian Squires. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Squires
-/
import Mathlib

/-!
# Saha–Boltzmann formalization — spatially-resolved (discrete Abel / onion-peeling) forward model

Every other module in this development assumes a **single, homogeneous** plasma
zone: one temperature, one electron density, one composition. This module
**relaxes that single-zone homogeneity assumption** by modelling the plasma as
`N` concentric cylindrical shells, each with its own emissivity, and proving that
the *full radial emissivity profile* is uniquely recovered from the measured
lateral chord intensities.

## Physics

For a cylindrically symmetric emitting plasma the lateral (chord) intensity
`I(y)` at impact parameter `y` is the **Abel transform** of the radial emissivity
`ε(r)`:

  `I(y) = 2 ∫_y^R ε(r) · r / sqrt(r² − y²) dr`,

with formal continuous inverse

  `ε(r) = −(1/π) ∫_r^R I′(y) / sqrt(y² − r²) dy`.

The **onion-peeling** numerical method discretizes this into `N` concentric
shells of constant emissivity `ε : Fin N → ℝ`. A chord at radius index `i`
crosses only the shells `j ≥ i` lying *outside* its turning radius, so the
measured chord-intensity vector is

  `I = L · ε`,   `I i = ∑ j, L i j · ε j`,

where `L i j` is the geometric path length of chord `i` through shell `j`.
Geometry forces two facts:

* `L` is **upper-triangular**: `j < i → L i j = 0` (a chord at index `i` never
  reaches the inner shells `j < i`);
* the diagonal is **strictly positive**: `L i i > 0` (every chord has a
  positive path length through its own outermost shell).

These are exactly the conditions under which the triangular system is solved by
back-substitution ("peeling" shells from the outside in), and — proven here —
under which the forward map is injective, so the radial profile is identifiable.

* `chordIntensity L ε := L.mulVec ε` — the discrete Abel forward map. The
  single-zone model of every other module is exactly the `N = 1` case, where `L`
  is `1×1` and `chordIntensity` collapses to `I 0 = L 0 0 · ε 0`.
* `ChordGeometry N` — packages the path-length matrix `L` with its two
  geometric hypotheses (`upper`, `diag_pos`).
* `chordGeometry_det_ne_zero` / `chordGeometry_isUnit` — the path-length matrix
  is nonsingular (det = product of positive diagonal entries) hence invertible.
* `chord_profile_identifiable` — **the spatial identifiability theorem**: equal
  chord-intensity vectors force equal radial emissivity profiles. The full
  inhomogeneous profile `ε : Fin N → ℝ` is recovered, not just a single zone.
* `singleZone_identifiable` — the `N = 1` homogeneous case as the trivial
  specialization, documenting that this formalization strictly generalizes the
  single-zone baseline used everywhere else in the repo.

## Scope / not covered (honest scoping)

This module formalizes **only** the *discrete* onion-peeling Abel inversion: a
finite upper-triangular linear system solved by back-substitution, which is the
standard numerical discretization used in practice. The **continuous**
Abel-transform inversion identity
`ε(r) = −(1/π) ∫_r^R I′(y) / sqrt(y² − r²) dy` (a singular improper integral, the
analytic inverse of the forward integral transform) is **not** formalized — it is
a substantially harder analysis result (improper/singular integrals,
differentiation under the integral sign) and is stated above as background and
motivation only.

This module has no CF-LIBS code dependency beyond mathlib's linear algebra: the
emissivity `ε i` of a shell would, in a fuller pipeline, be the Boltzmann/Saha
line emission of that shell's local `(T, n_e, composition)`, but the
identifiability result here is purely the invertibility of the geometric
path-length system and so depends only on `Matrix` API.

## Literature

* C. Parigger, G. Gautam, D. M. Surmick, "Radial electron density measurements in
  laser-induced plasma from Abel inverted hydrogen Balmer beta line profiles"
  (2016) — the onion-peeling / discrete Abel inversion applied in LIBS:
  concentric-shell back-substitution of a triangular path-length system to obtain
  radial electron-density profiles. This module formalizes the well-posedness
  (identifiability) of exactly that triangular system.
* Abel transform (cylindrically-symmetric emission): forward
  `I(y) = 2 ∫_y^R ε(r) r / sqrt(r² − y²) dr`, inverse
  `ε(r) = −(1/π) ∫_r^R I′(y) / sqrt(y² − r²) dy`. The discrete onion-peeling
  shells are the standard numerical discretization of this transform pair; the
  continuous inversion identity itself is cited as background only and is not
  formalized here (see "Scope / not covered").
-/

namespace CflibsFormal

open Finset
open scoped BigOperators

/-- The line-of-sight forward map for the onion-peeling discretization of the
Abel transform: the lateral chord-intensity vector `I = L · ε`, where
`ε : Fin N → ℝ` is the radial emissivity profile over `N` concentric shells and
`L i j` is the geometric path length of chord `i` through shell `j`.

This is the **discrete Abel forward transform**. The single-zone model used by
every other module is exactly `N = 1`, where `L` is a `1×1` matrix and this
collapses to scalar multiplication `I 0 = L 0 0 · ε 0`. Kept as a thin wrapper
over `Matrix.mulVec` so that all of mathlib's `mulVec` API applies verbatim. -/
noncomputable def chordIntensity {N : ℕ} (L : Matrix (Fin N) (Fin N) ℝ)
    (eps : Fin N → ℝ) : Fin N → ℝ :=
  L.mulVec eps

/-- A discrete onion-peeling chord geometry over `N` concentric shells.
`L` is the path-length matrix; `upper` says a chord at radius index `i`
crosses only shells `j ≥ i` (outer shells), i.e. `L` is upper-triangular;
`diag_pos` says each chord has strictly positive path length through its own
shell, `L i i > 0`. These are the two physically-forced facts that make the
discrete Abel system uniquely invertible by back-substitution.

`BlockTriangular id` unfolds to `∀ ⦃i j⦄, id j < id i → L i j = 0`, i.e.
`j < i → L i j = 0`: entries strictly below the diagonal vanish, so nonzero
entries have `j ≥ i` — exactly "chord `i` crosses only shells `j ≥ i`". -/
structure ChordGeometry (N : ℕ) where
  /-- The geometric path-length matrix: `L i j` is the path length of chord `i`
  through shell `j`. -/
  L : Matrix (Fin N) (Fin N) ℝ
  /-- Upper-triangular: a chord at index `i` never reaches the inner shells
  `j < i`, so those path lengths vanish. -/
  upper : L.BlockTriangular id
  /-- Each chord has strictly positive path length through its own shell. -/
  diag_pos : ∀ i : Fin N, 0 < L i i

/-- The path-length matrix of a physical onion-peeling geometry is nonsingular:
its determinant is the product of the (positive) self-path-lengths, hence
nonzero. This is the linear-algebraic heart that makes the discrete Abel
inversion well-posed. -/
theorem chordGeometry_det_ne_zero {N : ℕ} (G : ChordGeometry N) :
    G.L.det ≠ 0 := by
  rw [Matrix.det_of_upperTriangular G.upper]
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => (G.diag_pos i).ne')

/-- The path-length matrix is invertible. Over the field `ℝ`, `IsUnit` of the
determinant is equivalent to `IsUnit` of the matrix, so the nonzero determinant
of `chordGeometry_det_ne_zero` promotes to invertibility — the precondition for
the forward map to be injective. -/
theorem chordGeometry_isUnit {N : ℕ} (G : ChordGeometry N) :
    IsUnit G.L := by
  rw [Matrix.isUnit_iff_isUnit_det]
  exact (chordGeometry_det_ne_zero G).isUnit

/-- **Spatial identifiability — relaxing single-zone homogeneity.**

Equal measured chord-intensity vectors force equal radial emissivity profiles:
the *full* radial profile `ε : Fin N → ℝ` over all `N` shells (not a single
homogeneous zone) is uniquely recovered from the lateral intensities, so the
discrete onion-peeling Abel inversion is well-posed.

This is the spatial analogue of `saha_joint_identifiability` /
`temperature_from_two_levels` for an inhomogeneous plasma. It is
**non-tautological**: the hypothesis is an equality of *observed* chord-intensity
vectors (`chordIntensity`, i.e. `L.mulVec` of each profile); the conclusion is
equality of the *underlying physical* profiles `ε`. Neither `eps` nor `eps'` is
fed as a known answer — both are free, and equality is *deduced* from
observation-equality via injectivity of the (invertible) forward map. -/
theorem chord_profile_identifiable {N : ℕ} (G : ChordGeometry N)
    {eps eps' : Fin N → ℝ}
    (h : chordIntensity G.L eps = chordIntensity G.L eps') :
    eps = eps' :=
  Matrix.mulVec_injective_of_isUnit (chordGeometry_isUnit G) h

/-- The single-zone homogeneous model (`N = 1`) obtained by **instantiating the
general spatial identifiability** at `N = 1`. This documents that the
inhomogeneous formalization strictly generalizes every single-zone module in the
repo: the homogeneous case is the `1×1` specialization, not an independently
proved scalar-injectivity fact. -/
theorem singleZone_identifiable (G : ChordGeometry 1)
    {eps eps' : Fin 1 → ℝ}
    (h : chordIntensity G.L eps = chordIntensity G.L eps') :
    eps = eps' :=
  chord_profile_identifiable G h

/-- Non-vacuity witness: a concrete 2-shell geometry `L = !![1, 1; 0, 1]`
(upper-triangular with positive diagonal). -/
example : ChordGeometry 2 :=
  { L := !![1, 1; 0, 1]
    upper := by
      intro i j h
      fin_cases i <;> fin_cases j <;> simp_all (config := { decide := true })
    diag_pos := by
      intro i
      fin_cases i <;> norm_num }

/-- Non-vacuity / non-tautology witness: for that 2-shell geometry the two
*distinct* profiles `![0, 0]` and `![1, -1]` produce *distinct* chord
intensities, so the identifiability hypothesis is genuinely falsifiable (it is
not satisfied by every pair of profiles) — the implication in
`chord_profile_identifiable` is substantive, not vacuous. -/
example :
    chordIntensity (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) ![0, 0]
      ≠ chordIntensity (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) ![1, -1] := by
  intro hcontra
  have h1 := congrFun hcontra 1
  simp [chordIntensity, Matrix.mulVec_eq_sum, Fin.sum_univ_two] at h1

end CflibsFormal
