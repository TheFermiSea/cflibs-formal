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

/-! ## Constructive recovery, peeling recursion, and error amplification

The results above prove the discrete Abel inversion is *well-posed* (the profile is
uniquely identifiable) but say nothing *constructive* or *quantitative*. The
following deepen that: `peeling_identity` exposes the back-substitution algorithm
as an exact identity; `onionPeel` names the recovery map; `peeling_single_step` and
`peeling_amplification` quantify how a chord-intensity error is amplified into a
radial-profile error, compounding geometrically toward the plasma core. -/

/-- Split the chord intensity of shell `i` at the diagonal: the self-term
`Lᵢᵢ · εᵢ` plus the outer-shell terms `j > i`; the inner terms `j < i` vanish by
upper-triangularity (`G.upper`). Private helper for `peeling_identity` /
`peeling_single_step`. -/
private theorem chordIntensity_split {N : ℕ} (G : ChordGeometry N) (eps : Fin N → ℝ)
    (i : Fin N) :
    chordIntensity G.L eps i
      = G.L i i * eps i + ∑ j ∈ Finset.univ.filter (i < ·), G.L i j * eps j := by
  have hmv : chordIntensity G.L eps i = ∑ j, G.L i j * eps j := by
    simp [chordIntensity, Matrix.mulVec, dotProduct]
  rw [hmv, ← Finset.add_sum_erase Finset.univ (fun j => G.L i j * eps j) (Finset.mem_univ i)]
  congr 1
  refine (Finset.sum_subset ?_ ?_).symm
  · intro x hx
    rw [Finset.mem_filter] at hx
    rw [Finset.mem_erase]
    exact ⟨ne_of_gt hx.2, Finset.mem_univ x⟩
  · intro x hx hxnot
    rw [Finset.mem_erase] at hx
    have hnlt : ¬ i < x := fun h => hxnot (Finset.mem_filter.mpr ⟨Finset.mem_univ x, h⟩)
    have hxi : x < i := lt_of_le_of_ne (not_lt.mp hnlt) hx.1
    change G.L i x * eps x = 0
    rw [G.upper hxi, zero_mul]

/-- **The onion-peeling recursion as an exact pointwise identity.**

Solving the row `Iᵢ = Lᵢᵢ·εᵢ + ∑_{j>i} Lᵢⱼ·εⱼ` of the discrete Abel system for
`εᵢ` (legal since `Lᵢᵢ > 0`) recovers the back-substitution the practitioner runs:
the true emissivity of shell `i` equals its measured chord intensity minus the
already-peeled outer shells `j > i`, all divided by the self-path `Lᵢᵢ`. This is
the *constructive* content behind `chord_profile_identifiable`'s abstract
injectivity — it names the recovered value rather than merely asserting uniqueness.
It is an unconditional identity: every true profile `ε` satisfies it at every `i`,
so no well-founded recursion is needed to state it. -/
theorem peeling_identity {N : ℕ} (G : ChordGeometry N) (eps : Fin N → ℝ) (i : Fin N) :
    eps i = (chordIntensity G.L eps i
        - ∑ j ∈ Finset.univ.filter (i < ·), G.L i j * eps j) / G.L i i := by
  have hne := (G.diag_pos i).ne'
  rw [chordIntensity_split, add_sub_cancel_right]
  field_simp

/-- The explicit **onion-peeling recovery map**: the left inverse of the forward
map `chordIntensity`, `onionPeel G I = L⁻¹ · I`. `chord_profile_identifiable`
proved the radial profile is *uniquely* recovered; this *names* the map that
recovers it. -/
noncomputable def onionPeel {N : ℕ} (G : ChordGeometry N) (I : Fin N → ℝ) : Fin N → ℝ :=
  G.L⁻¹.mulVec I

/-- `onionPeel` inverts the discrete Abel forward map exactly:
`onionPeel G (chordIntensity G.L ε) = ε` for every radial profile `ε`. Exact
recovery, from `L⁻¹(L·ε) = ε` with `L` invertible (`chordGeometry_isUnit`). -/
theorem onionPeel_chordIntensity {N : ℕ} (G : ChordGeometry N) (eps : Fin N → ℝ) :
    onionPeel G (chordIntensity G.L eps) = eps := by
  letI := (chordGeometry_isUnit G).invertible
  exact Matrix.inv_mulVec_eq_vec rfl

/-- The recovery is genuinely *inside-out*: `L⁻¹` is upper-triangular, so the
recovered emissivity `εᵢ = (onionPeel G I) i` depends only on the chord
intensities `Iⱼ` for `j ≥ i` (the shells at or outside radius `i`) — exactly the
physical peeling order (outermost shell first). -/
theorem onionPeel_blockTriangular {N : ℕ} (G : ChordGeometry N) :
    (G.L⁻¹).BlockTriangular id := by
  letI := (chordGeometry_isUnit G).invertible
  exact Matrix.blockTriangular_inv_of_blockTriangular G.upper

/-- **One-shell perturbation inequality.** Applying `peeling_identity` to two
profiles `ε, ε'` and subtracting (the forward map is linear, so
`ΔI = L·Δε`): the recovered-profile error at shell `i`, scaled by the self-path
`Lᵢᵢ`, is bounded by its own chord-measurement error `|ΔIᵢ|` plus the leakage of
every already-recovered outer shell `j > i` through the geometric coupling
`|Lᵢⱼ|`. This one-step amplification is the recursion that `peeling_amplification`
assembles into the geometric bound. -/
theorem peeling_single_step {N : ℕ} (G : ChordGeometry N) (eps eps' : Fin N → ℝ)
    (i : Fin N) :
    |eps i - eps' i| * G.L i i
      ≤ |chordIntensity G.L eps i - chordIntensity G.L eps' i|
          + ∑ j ∈ Finset.univ.filter (i < ·), |G.L i j| * |eps j - eps' j| := by
  have hdiff : (eps i - eps' i) * G.L i i
      = (chordIntensity G.L eps i - chordIntensity G.L eps' i)
          - ∑ j ∈ Finset.univ.filter (i < ·), G.L i j * (eps j - eps' j) := by
    rw [chordIntensity_split G eps i, chordIntensity_split G eps' i]
    simp only [mul_sub, Finset.sum_sub_distrib]
    ring
  calc |eps i - eps' i| * G.L i i
      = |(eps i - eps' i) * G.L i i| := by
        rw [abs_mul, abs_of_pos (G.diag_pos i)]
    _ = |(chordIntensity G.L eps i - chordIntensity G.L eps' i)
          - ∑ j ∈ Finset.univ.filter (i < ·), G.L i j * (eps j - eps' j)| := by rw [hdiff]
    _ ≤ |chordIntensity G.L eps i - chordIntensity G.L eps' i|
          + |∑ j ∈ Finset.univ.filter (i < ·), G.L i j * (eps j - eps' j)| :=
        abs_sub _ _
    _ ≤ |chordIntensity G.L eps i - chordIntensity G.L eps' i|
          + ∑ j ∈ Finset.univ.filter (i < ·), |G.L i j| * |eps j - eps' j| := by
        gcongr
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        apply le_of_eq
        apply Finset.sum_congr rfl
        intro j _
        rw [abs_mul]

/-- The smallest self-path-length `ℓ = ⨅ᵢ Lᵢᵢ` across the shells (the strongest
diagonal floor; `> 0` for `N ≥ 1` since the diagonal is positive). -/
noncomputable def peelDiagFloor {N : ℕ} (G : ChordGeometry N) : ℝ := ⨅ i, G.L i i

/-- The worst per-row coupling ratio `ρ = ⨆ᵢ (∑_{j>i} |Lᵢⱼ|)/Lᵢᵢ`: how strongly,
in the extremal row, the already-peeled outer shells couple back into shell `i`
relative to its own self-path. `ρ ≳ 1` is the diagonally-non-dominant regime where
the inward recursion amplifies. -/
noncomputable def peelCouplingRatio {N : ℕ} (G : ChordGeometry N) : ℝ :=
  ⨆ i, (∑ j ∈ Finset.univ.filter (i < ·), |G.L i j|) / G.L i i

/-- **Geometric-in-shell-depth error amplification (deterministic worst case).**

Given a floor `ell > 0` on the self-paths (`ell ≤ Lᵢᵢ`), a bound `emax` on the
chord-intensity error (`|ΔIᵢ| ≤ emax`), and a per-row coupling ratio `rho ≥ 0`
dominating the off-diagonal weight (`∑_{j>i} |Lᵢⱼ| ≤ rho·Lᵢᵢ`), the recovered
radial-profile error at shell `i` obeys
`|Δεᵢ| ≤ (emax/ell) · ∑_{k<N-i} rho^k`. The inward recursion compounds
already-peeled outer-shell errors geometrically: the factor grows like
`rho^{N-i}` toward the core (`i → 0`), the honest noise blow-up that
radially-resolved CF-LIBS must pre-smooth against — at the critical coupling
`rho = 1` it is exactly the shell count `N - i` (see the witness below).

**REDUCED**: an adversarial worst-case upper bound (attained only for
perfectly-correlated errors and the extremal-row geometry), in the deterministic
style of `ErrorBudget.lean` — *not* the realized amplification, and deliberately
*not* an `N`-independent stability claim. Proof: downward strong induction on the
co-index `N - i.val`, assembling `peeling_single_step`. -/
theorem peeling_amplification {N : ℕ} (G : ChordGeometry N) (eps eps' : Fin N → ℝ)
    (ell rho emax : ℝ) (hell : 0 < ell) (hrho : 0 ≤ rho)
    (hell_le : ∀ i, ell ≤ G.L i i)
    (hemax : ∀ i, |chordIntensity G.L eps i - chordIntensity G.L eps' i| ≤ emax)
    (hrho_ge : ∀ i, (∑ j ∈ Finset.univ.filter (i < ·), |G.L i j|) ≤ rho * G.L i i)
    (i : Fin N) :
    |eps i - eps' i| ≤ (emax / ell) * ∑ k ∈ Finset.range (N - i.val), rho ^ k := by
  set q : ℝ := emax / ell with hq
  have hemax_nonneg : 0 ≤ emax := le_trans (abs_nonneg _) (hemax i)
  have hq_nonneg : 0 ≤ q := div_nonneg hemax_nonneg hell.le
  suffices H : ∀ d : ℕ, ∀ i : Fin N, N - i.val ≤ d →
      |eps i - eps' i| ≤ q * ∑ k ∈ Finset.range (N - i.val), rho ^ k by
    exact H (N - i.val) i le_rfl
  intro d
  induction d with
  | zero =>
      intro i hi
      exfalso
      have := i.isLt
      omega
  | succ d ih =>
      intro i hi
      have hiN : i.val < N := i.isLt
      have hLii : 0 < G.L i i := G.diag_pos i
      have hNi : N - i.val = (N - i.val - 1) + 1 := by omega
      set B' : ℝ := q * ∑ k ∈ Finset.range (N - i.val - 1), rho ^ k with hB'
      have hB'_nonneg : 0 ≤ B' :=
        mul_nonneg hq_nonneg (Finset.sum_nonneg (fun k _ => pow_nonneg hrho k))
      have hbound_j : ∀ j ∈ Finset.univ.filter (i < ·), |eps j - eps' j| ≤ B' := by
        intro j hj
        rw [Finset.mem_filter] at hj
        have hij : i < j := hj.2
        have hijv : (i : ℕ) < (j : ℕ) := hij
        have hjd : N - j.val ≤ d := by omega
        calc |eps j - eps' j|
            ≤ q * ∑ k ∈ Finset.range (N - j.val), rho ^ k := ih j hjd
          _ ≤ q * ∑ k ∈ Finset.range (N - i.val - 1), rho ^ k := by
              apply mul_le_mul_of_nonneg_left _ hq_nonneg
              apply Finset.sum_le_sum_of_subset_of_nonneg
              · intro k hk
                rw [Finset.mem_range] at hk ⊢
                omega
              · intro k _ _
                exact pow_nonneg hrho k
          _ = B' := hB'.symm
      have hstep := peeling_single_step G eps eps' i
      have hsum_le : (∑ j ∈ Finset.univ.filter (i < ·), |G.L i j| * |eps j - eps' j|)
          ≤ B' * (rho * G.L i i) := by
        calc (∑ j ∈ Finset.univ.filter (i < ·), |G.L i j| * |eps j - eps' j|)
            ≤ ∑ j ∈ Finset.univ.filter (i < ·), |G.L i j| * B' := by
              apply Finset.sum_le_sum
              intro j hj
              exact mul_le_mul_of_nonneg_left (hbound_j j hj) (abs_nonneg _)
          _ = (∑ j ∈ Finset.univ.filter (i < ·), |G.L i j|) * B' := by
              rw [Finset.sum_mul]
          _ = B' * (∑ j ∈ Finset.univ.filter (i < ·), |G.L i j|) := by rw [mul_comm]
          _ ≤ B' * (rho * G.L i i) :=
              mul_le_mul_of_nonneg_left (hrho_ge i) hB'_nonneg
      have hstep2 : |eps i - eps' i| * G.L i i ≤ emax + B' * (rho * G.L i i) :=
        hstep.trans (add_le_add (hemax i) hsum_le)
      have hdiv : |eps i - eps' i| ≤ (emax + B' * (rho * G.L i i)) / G.L i i :=
        (le_div_iff₀ hLii).mpr hstep2
      have hsplit : (emax + B' * (rho * G.L i i)) / G.L i i = emax / G.L i i + B' * rho := by
        rw [add_div, mul_div_assoc, mul_div_assoc, div_self hLii.ne', mul_one]
      rw [hsplit, mul_comm B' rho] at hdiv
      have hfloor : emax / G.L i i ≤ q := by
        rw [hq]; gcongr; exact hell_le i
      have hfinal : |eps i - eps' i| ≤ q + rho * B' := by linarith [hdiv, hfloor]
      refine hfinal.trans (le_of_eq ?_)
      rw [hNi, Finset.sum_range_succ', hB']
      simp only [pow_succ, pow_zero]
      rw [← Finset.sum_mul]
      ring

/-- **Named-constant form of `peeling_amplification`.** With the canonical geometry
constants `peelDiagFloor G = ⨅ᵢ Lᵢᵢ` and `peelCouplingRatio G = ⨆ᵢ (∑_{j>i}
|Lᵢⱼ|)/Lᵢᵢ`, the recovered-profile error at shell `i` obeys
`|Δεᵢ| ≤ (‖ΔI‖∞ / ℓ) · ∑_{k<N-i} ρ^k`, where `‖ΔI‖∞ = ⨆ₖ |ΔIₖ|`. Instantiates
`peeling_amplification`; positivity of `ℓ` is the finite minimum of the positive
diagonal. **REDUCED** (same worst-case caveat). -/
theorem peeling_amplification_iSup {N : ℕ} (G : ChordGeometry N) (eps eps' : Fin N → ℝ)
    (i : Fin N) :
    |eps i - eps' i|
      ≤ (⨆ k, |chordIntensity G.L eps k - chordIntensity G.L eps' k|) / peelDiagFloor G
          * ∑ k ∈ Finset.range (N - i.val), peelCouplingRatio G ^ k := by
  haveI : Nonempty (Fin N) := ⟨i⟩
  have hell_pos : 0 < peelDiagFloor G := by
    obtain ⟨i₀, hi₀⟩ := Finite.exists_min (fun k => G.L k k)
    have heq : peelDiagFloor G = G.L i₀ i₀ :=
      le_antisymm (ciInf_le (Finite.bddBelow_range _) i₀) (le_ciInf hi₀)
    rw [heq]; exact G.diag_pos i₀
  have hell_le : ∀ k, peelDiagFloor G ≤ G.L k k := fun k =>
    ciInf_le (Finite.bddBelow_range _) k
  have hemax : ∀ k, |chordIntensity G.L eps k - chordIntensity G.L eps' k|
      ≤ ⨆ k, |chordIntensity G.L eps k - chordIntensity G.L eps' k| := fun k =>
    le_ciSup (f := fun k => |chordIntensity G.L eps k - chordIntensity G.L eps' k|)
      (Finite.bddAbove_range _) k
  have hrho_ge : ∀ k, (∑ j ∈ Finset.univ.filter (k < ·), |G.L k j|)
      ≤ peelCouplingRatio G * G.L k k := by
    intro k
    have h1 : (∑ j ∈ Finset.univ.filter (k < ·), |G.L k j|) / G.L k k ≤ peelCouplingRatio G :=
      le_ciSup (f := fun i => (∑ j ∈ Finset.univ.filter (i < ·), |G.L i j|) / G.L i i)
        (Finite.bddAbove_range _) k
    exact (div_le_iff₀ (G.diag_pos k)).mp h1
  have hrho_nonneg : 0 ≤ peelCouplingRatio G := by
    have h0 : (0 : ℝ) ≤ (∑ j ∈ Finset.univ.filter (i < ·), |G.L i j|) / G.L i i :=
      div_nonneg (Finset.sum_nonneg (fun j _ => abs_nonneg _)) (G.diag_pos i).le
    have h1 : (∑ j ∈ Finset.univ.filter (i < ·), |G.L i j|) / G.L i i ≤ peelCouplingRatio G :=
      le_ciSup (f := fun i => (∑ j ∈ Finset.univ.filter (i < ·), |G.L i j|) / G.L i i)
        (Finite.bddAbove_range _) i
    exact h0.trans h1
  exact peeling_amplification G eps eps' (peelDiagFloor G) (peelCouplingRatio G)
    (⨆ k, |chordIntensity G.L eps k - chordIntensity G.L eps' k|)
    hell_pos hrho_nonneg hell_le hemax hrho_ge i

/-- Non-vacuity / legibility witness for `peeling_amplification`: at the critical
coupling `ρ = 1` (off-diagonal weight rivals the diagonal) the geometric factor
`∑_{k<N} ρ^k` collapses to exactly the shell count `N`. So the worst-case
amplification grows *linearly in the number of shells* — the honest
"core-singularity" blow-up the bound encodes, confirming it is not a vacuous or
`N`-independent stability statement. -/
example (N : ℕ) : (∑ k ∈ Finset.range N, (1 : ℝ) ^ k) = N := by simp

section LinftyCondition

attribute [local instance] Matrix.linftyOpNormedAddCommGroup

/-- **Abstract ℓ∞ condition bound (cross-check).** In the ℓ∞ (max-abs-row-sum)
induced matrix norm, `‖Δε‖∞ ≤ ‖L⁻¹‖∞ · ‖ΔI‖∞`: the textbook named condition factor
`‖L⁻¹‖∞`. Complementary to `peeling_amplification`, which makes that otherwise
opaque factor legible as `(1/ℓ)·∑ρ^k`. The norm here is the *elementary* ℓ∞ induced
norm (`Matrix.linfty_opNorm_mulVec`), distinct from the L²/spectral operator norm. -/
theorem peeling_condition_linfty {N : ℕ} (G : ChordGeometry N) (eps eps' : Fin N → ℝ) :
    ‖eps - eps'‖ ≤ ‖G.L⁻¹‖ * ‖chordIntensity G.L eps - chordIntensity G.L eps'‖ := by
  letI := (chordGeometry_isUnit G).invertible
  have hΔ : chordIntensity G.L eps - chordIntensity G.L eps'
      = G.L.mulVec (eps - eps') := by
    simp [chordIntensity, Matrix.mulVec_sub]
  have hrec : eps - eps'
      = G.L⁻¹.mulVec (chordIntensity G.L eps - chordIntensity G.L eps') :=
    (Matrix.inv_mulVec_eq_vec hΔ).symm
  calc ‖eps - eps'‖
      = ‖G.L⁻¹.mulVec (chordIntensity G.L eps - chordIntensity G.L eps')‖ := by rw [hrec]
    _ ≤ ‖G.L⁻¹‖ * ‖chordIntensity G.L eps - chordIntensity G.L eps'‖ :=
        Matrix.linfty_opNorm_mulVec _ _

end LinftyCondition

end CflibsFormal
