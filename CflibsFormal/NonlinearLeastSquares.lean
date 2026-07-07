/-
Copyright (c) 2026 Brian Squires. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Squires
-/
import Mathlib
import CflibsFormal.ForwardMap
import CflibsFormal.Identifiability
import CflibsFormal.Analysis

/-!
# CF-LIBS formalization — the nonlinear joint `(T, N)` least-squares inverse (existence leg)

`LeastSquaresFit.lean` handles the **linear** projection inverse: after log-linearizing to the
Boltzmann plot `y_k = m·E_k + b`, the least-squares minimizer is the closed-form OLS estimate, so
existence of the minimizer is *exhibited* (`ols_minimizes_rss`) — no compactness needed. This
module is its **nonlinear sibling**: the joint fit of the *raw* physical parameters `(T, N)`
directly against the forward line intensities `lineIntensity kB T N Fcal g E A`, with no
log-linearization. The forward map is `Fcal·A_k · N·g_k·exp(−E_k/(k_B T)) / U(T)` — genuinely
nonlinear (and non-convex) in `(T, N)` through `exp(−E_k/(k_B T))` and the partition function
`U(T)` in the denominator — so there is no closed form and existence must be argued by the
**extreme value theorem** (compactness + continuity) instead.

We supply:

* `nlObjective` — the nonlinear least-squares objective `∑ₖ (I_k(T,N) − obs_k)²` over the *joint*
  `(T, N)`, where `I_k = lineIntensity kB T N Fcal g E A k`.
* `nlObjective_continuousOn` — the objective is `ContinuousOn` the physical box
  `Icc Tmin Tmax ×ˢ Icc Nmin Nmax`, provided `0 < Tmin` and `0 < kB` (so `k_B·T ≠ 0` on the box,
  making `exp(−E_k/(k_B T))` continuous) and `0 < g` (so the partition-function denominator is
  nonzero). Every ingredient — `p.1`, `p.2`, the Boltzmann factors, the finite partition sum, the
  finite sum of squared residuals — is a continuous combination of continuous pieces.
* `nlObjective_exists_min` — **the headline**: for `0 < Tmin ≤ Tmax`, `Nmin ≤ Nmax`, `0 < kB`, and
  **any** observation vector `obs` (noisy, off-manifold — no hypothesis on `obs`), a minimizer
  `(T̂, N̂)` of `nlObjective` exists in the box. Compactness of the box
  (`isCompact_Icc.prod isCompact_Icc`) + box nonemptiness (from the orderings) + continuity feed
  `IsCompact.exists_isMinOn`.
* `nlObjective_onManifold_min` — **on-manifold anchor**: when `obs` *is* the forward spectrum of
  some `(T0, N0)` in the box, the objective attains its global minimum value `0` there (a sum of
  squares that vanishes term-by-term at the true parameters), so `(T0, N0)` is a minimizer.

## Scope (honest)

This is **existence only**. Unlike the linear case in `LeastSquaresFit.lean` — where the minimizer
is the closed-form OLS estimate, is *unique* under nonzero energy spread, and provably coincides
with the identifiable inverse on-manifold — here we prove *only* that a minimizer exists on the
compact physical box. **Uniqueness of the minimizer, any characterization of it, and its relation
to the identifiable inverse off-manifold all remain open** (the objective is non-convex in `T`, so
local minima and boundary optima are genuinely possible). `nlObjective_onManifold_min` pins the
minimum *value* to `0` only in the noise-free case; for real (noisy) spectra the minimal residual
is positive and its argmin has no closed form. This is the **compactness leg** of the nonlinear
joint `(T, N)` fit — the residual of gap #1 in `docs/SOLVER_FORMALIZATION_GAPS.md`, and a
prerequisite for the fully-coupled multi-species `(T, n_e, composition)` inverse (gaps #6, #8).

## Literature

The joint least-squares fit of `(T, N)` (and, in the full pipeline, `n_e` and composition) to raw
line intensities is the solver step Tognoni et al. (2010) describe as the calibration-free
inversion: rather than reading a slope off a hand-drawn Boltzmann plot, the algorithm minimizes the
misfit between the measured spectrum and the LTE forward model over the physical parameters. The
existence theorem here is that fit **restricted to a compact physical box**
`[Tmin,Tmax]×[Nmin,Nmax]` — the bounded search region every practical solver imposes — so the EVT
guarantees the minimizer the solver reports is a genuine minimizer, not an artifact of early
stopping. The `0` on-manifold residual is the noise-free consistency check: the true parameters are
a global optimum of the fit (cf. the linear analogue `Alt.olsBoltzmann_forward_feasible`, Tognoni
et al. 2010). The forward model and the intensity Boltzmann-plot identity it fits are Ciucci et al.
(1999) / Tognoni et al. (2010) (see `ForwardMap.lean`).
-/

namespace CflibsFormal

open Finset Real
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- **Nonlinear least-squares objective** for the joint `(T, N)` fit:
`nlObjective kB Fcal g E A obs (T, N) = ∑ₖ (I_k(T,N) − obs_k)²`,
where `I_k(T,N) = lineIntensity kB T N Fcal g E A k` is the CF-LIBS optically-thin forward line
intensity. The parameter is the *joint* pair `p = (T, N)` (`p.1 = T`, `p.2 = N`); `obs` is the
measured (possibly noisy, off-manifold) spectrum. This is the nonlinear sibling of `rss` in
`LeastSquaresFit.lean`: `rss` fits an affine line to the log-linearized ordinates, whereas
`nlObjective` fits the raw physical `(T, N)` directly through the nonlinear forward map. -/
noncomputable def nlObjective (kB Fcal : ℝ) (g E A : ι → ℝ) (obs : ι → ℝ) (p : ℝ × ℝ) : ℝ :=
  ∑ k, (lineIntensity kB p.1 p.2 Fcal g E A k - obs k) ^ 2

/-- **Continuity on the physical box.** `nlObjective` is `ContinuousOn` the box
`Icc Tmin Tmax ×ˢ Icc Nmin Nmax` given `0 < kB`, `0 < Tmin`, and `0 < g k` for every level `k`.
The role of the hypotheses: `0 < Tmin` and `0 < kB` force `k_B·T ≠ 0` on the box (`T ≥ Tmin > 0`),
so the Boltzmann-factor arguments `−E_k/(k_B T)` are continuous; `0 < g k` (with `[Nonempty ι]`)
makes the partition-function denominator `U(T) = ∑ⱼ gⱼ·exp(−Eⱼ/(k_B T))` strictly positive, hence
nonzero, so the population quotient is continuous. `obs`, `Fcal`, `A`, `g`, `E` enter as constants.
Every piece is a continuous combination (finite sum / product / quotient with nonzero denominator /
`exp`) of the continuous coordinate projections `p.1`, `p.2`. Pure topology. -/
theorem nlObjective_continuousOn [Nonempty ι] {kB Fcal Tmin Tmax Nmin Nmax : ℝ}
    {g E A obs : ι → ℝ} (hkB : 0 < kB) (hTmin : 0 < Tmin) (hg : ∀ k, 0 < g k) :
    ContinuousOn (nlObjective kB Fcal g E A obs)
      (Set.Icc Tmin Tmax ×ˢ Set.Icc Nmin Nmax) := by
  have hkT : ∀ p ∈ Set.Icc Tmin Tmax ×ˢ Set.Icc Nmin Nmax, kB * p.1 ≠ 0 := by
    intro p hp
    simp only [Set.mem_prod, Set.mem_Icc] at hp
    exact (mul_pos hkB (lt_of_lt_of_le hTmin hp.1.1)).ne'
  have hcontDen : ContinuousOn (fun p : ℝ × ℝ => kB * p.1)
      (Set.Icc Tmin Tmax ×ˢ Set.Icc Nmin Nmax) :=
    continuousOn_const.mul continuous_fst.continuousOn
  have hbf : ∀ e : ℝ, ContinuousOn (fun p : ℝ × ℝ => boltzmannFactor kB p.1 e)
      (Set.Icc Tmin Tmax ×ˢ Set.Icc Nmin Nmax) := by
    intro e
    have harg : ContinuousOn (fun p : ℝ × ℝ => -e / (kB * p.1))
        (Set.Icc Tmin Tmax ×ˢ Set.Icc Nmin Nmax) := continuousOn_const.div hcontDen hkT
    simpa only [boltzmannFactor] using harg.rexp
  have hpf : ContinuousOn (fun p : ℝ × ℝ => partitionFunction kB p.1 g E)
      (Set.Icc Tmin Tmax ×ˢ Set.Icc Nmin Nmax) := by
    simp only [partitionFunction]
    refine continuousOn_finsetSum Finset.univ (fun j _ => ?_)
    exact continuousOn_const.mul (hbf (E j))
  unfold nlObjective
  refine continuousOn_finsetSum Finset.univ (fun k _ => ?_)
  refine ContinuousOn.pow (ContinuousOn.sub ?_ continuousOn_const) 2
  simp only [lineIntensity]
  refine continuousOn_const.mul ?_
  simp only [population]
  refine ContinuousOn.div ?_ hpf (fun p _ => (partitionFunction_pos hg).ne')
  exact (continuous_snd.continuousOn.mul continuousOn_const).mul (hbf (E k))

/-- **Existence of the joint minimizer (headline).** For `0 < Tmin ≤ Tmax`, `Nmin ≤ Nmax`,
`0 < kB`, and positive degeneracies `g`, and for **any** observation vector `obs` — with no
hypothesis on `obs`, so noisy off-manifold spectra are included — there is a parameter pair
`(T̂, N̂)` in the physical box `Icc Tmin Tmax ×ˢ Icc Nmin Nmax` that minimizes the nonlinear
least-squares objective `nlObjective` over the box. The box is compact
(`isCompact_Icc.prod isCompact_Icc`) and nonempty (from the orderings), and `nlObjective` is
continuous on it (`nlObjective_continuousOn`), so the extreme value theorem
(`IsCompact.exists_isMinOn`) delivers the minimizer. This is the nonlinear analogue of
`ols_minimizes_rss`, argued by compactness rather than a closed form. -/
theorem nlObjective_exists_min [Nonempty ι] {kB Fcal Tmin Tmax Nmin Nmax : ℝ}
    {g E A obs : ι → ℝ} (hkB : 0 < kB) (hTmin : 0 < Tmin) (hTle : Tmin ≤ Tmax)
    (hNle : Nmin ≤ Nmax) (hg : ∀ k, 0 < g k) :
    ∃ p ∈ Set.Icc Tmin Tmax ×ˢ Set.Icc Nmin Nmax,
      IsMinOn (nlObjective kB Fcal g E A obs)
        (Set.Icc Tmin Tmax ×ˢ Set.Icc Nmin Nmax) p := by
  have hcompact : IsCompact (Set.Icc Tmin Tmax ×ˢ Set.Icc Nmin Nmax) :=
    isCompact_Icc.prod isCompact_Icc
  have hne : (Set.Icc Tmin Tmax ×ˢ Set.Icc Nmin Nmax).Nonempty :=
    (Set.nonempty_Icc.mpr hTle).prod (Set.nonempty_Icc.mpr hNle)
  exact hcompact.exists_isMinOn hne (nlObjective_continuousOn hkB hTmin hg)

/-- **On-manifold anchor.** If `obs` is exactly the forward spectrum of a parameter pair
`(T0, N0)` lying in a set `S` — the noise-free case `obs_k = lineIntensity kB T0 N0 Fcal g E A k`
— then `nlObjective` attains its global minimum value `0` at `(T0, N0)`, so `(T0, N0)` is a
minimizer over `S`. The objective is a sum of squares, hence `≥ 0` everywhere, and each summand
`(I_k(T0,N0) − obs_k)²` vanishes at the true parameters; so the true parameters are a zero-residual
global optimum. For a genuine physical box `S = Icc Tmin Tmax ×ˢ Icc Nmin Nmax` with `(T0, N0)`
inside, this identifies the minimizer of `nlObjective_exists_min` as having minimal value `0`. Off
the manifold (noisy `obs`) the minimal value is positive and this anchor does not apply. -/
theorem nlObjective_onManifold_min {kB Fcal : ℝ} {g E A : ι → ℝ} {T0 N0 : ℝ} {obs : ι → ℝ}
    {S : Set (ℝ × ℝ)} (hobs : ∀ k, obs k = lineIntensity kB T0 N0 Fcal g E A k)
    (hmem : (T0, N0) ∈ S) :
    (T0, N0) ∈ S ∧ nlObjective kB Fcal g E A obs (T0, N0) = 0
      ∧ IsMinOn (nlObjective kB Fcal g E A obs) S (T0, N0) := by
  have hnonneg : ∀ p, 0 ≤ nlObjective kB Fcal g E A obs p := by
    intro p
    simp only [nlObjective]
    exact Finset.sum_nonneg (fun k _ => sq_nonneg _)
  have hzero : nlObjective kB Fcal g E A obs (T0, N0) = 0 := by
    simp only [nlObjective]
    refine Finset.sum_eq_zero (fun k _ => ?_)
    change (lineIntensity kB T0 N0 Fcal g E A k - obs k) ^ 2 = 0
    rw [hobs k, sub_self]
    norm_num
  refine ⟨hmem, hzero, ?_⟩
  rw [isMinOn_iff]
  intro x _
  rw [hzero]
  exact hnonneg x

/-! ### Non-vacuity witnesses -/

/-- Positive degeneracies for the one-line witness box. -/
private def nvNlsG : Fin 1 → ℝ := fun _ => 1

/-- Level energies for the one-line witness box (irrelevant to feasibility of the box). -/
private def nvNlsE : Fin 1 → ℝ := fun _ => 0

/-- Einstein coefficients for the one-line witness box. -/
private def nvNlsA : Fin 1 → ℝ := fun _ => 1

/-- A concrete off-manifold observation for the one-line witness box (arbitrary noisy value). -/
private def nvNlsObs : Fin 1 → ℝ := fun _ => 5

/-- **Non-vacuity of the existence theorem.** With `Tmin = 1`, `Tmax = 2`, `Nmin = 0`, `Nmax = 1`,
`kB = Fcal = 1`, one emitting level, and the arbitrary off-manifold observation `nvNlsObs ≡ 5`, all
hypotheses of `nlObjective_exists_min` are satisfied, so a minimizer of the nonlinear objective
exists in the box `Icc 1 2 ×ˢ Icc 0 1`. Confirms the box constraints
`0 < Tmin ≤ Tmax`, `Nmin ≤ Nmax`, `0 < kB`, `0 < g` are jointly satisfiable and the conclusion is
non-trivial. -/
example :
    ∃ p ∈ Set.Icc (1 : ℝ) 2 ×ˢ Set.Icc (0 : ℝ) 1,
      IsMinOn (nlObjective 1 1 nvNlsG nvNlsE nvNlsA nvNlsObs)
        (Set.Icc (1 : ℝ) 2 ×ˢ Set.Icc (0 : ℝ) 1) p :=
  nlObjective_exists_min (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun k => by norm_num [nvNlsG])

end CflibsFormal

/-!
## Variable projection (VARPRO): the forward map is linear in `N`, so the `N`-section profiles out

The joint objective `nlObjective` is nonlinear and non-convex in `T`, but it is **exactly quadratic
in `N`**: the forward line intensity is `lineIntensity kB T N Fcal g E A k = N · c_k(T)` with
`c_k(T) := lineIntensity kB T 1 Fcal g E A k` — linear in the density `N`. Hence for every *fixed*
`T` the `N`-section `N ↦ nlObjective … (T, N) = ∑ₖ (N·c_k − obs_k)²` is a 1-D ordinary least-squares
problem, solved in closed form by the **profiled density**
`N̂(T) = (∑ₖ c_k·obs_k) / (∑ₖ c_k²)` (classical variable projection). We prove:

* `lineIntensity_linear_in_N` — the exact linearity-in-`N` identity of the forward map.
* `nlObjective_Nsection_decomposition` — the Pythagorean/projection identity for the `N`-section,
  mirroring `LeastSquaresFit.rss_decomposition`: the excess of any `N` over `N̂(T)` is
  `(N − N̂(T))² · ∑ₖ c_k²`.
* `profiledDensity_isMinOn_Nsection` / `nlObjective_Nsection_lt_of_ne` /
  `Nsection_minimizer_unique` — **the headline**: `N̂(T)` is the *unique* global minimizer of the
  `N`-section, so the `N`-coordinate of any joint minimizer is determined by its `T`-coordinate. The
  2-D joint fit is thus provably 1-D in `T` — the VARPRO reduction the solver exploits.
* `profiledDensity_denom_pos` — the nondegeneracy `0 < ∑ₖ c_k²` holds for any `T` under positive
  degeneracies, Einstein coefficients, and calibration (the forward map is positive at unit
  density), so the reduction is never vacuous.

**Honest scope.** This closes the *`N`-direction* of gap #1 exactly and exposes the variable
projection. The *`T`-direction* uniqueness remains genuinely open: `nlObjective` is non-convex in
`T` through `exp(−E_k/(k_B T))` and the partition function `U(T)`, so the profiled-`T` objective
`T ↦ nlObjective … (T, N̂(T))` may have multiple local minima — none of that is addressed here.
The VARPRO structure and the calibration-free `(T, N)` inversion it accelerates are Tognoni et al.
(2010); the linearity of the forward map in `N` is Ciucci et al. (1999) (see `ForwardMap.lean`).
-/

namespace CflibsFormal

open Finset Real
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- **Linearity of the forward map in the density `N` (EXACT).**
`lineIntensity kB T N Fcal g E A k = N · lineIntensity kB T 1 Fcal g E A k`. The CF-LIBS
optically-thin line intensity `I_k = Fcal · A_k · N · g_k · exp(−E_k/(k_B T)) / U(T)` carries the
number density `N` as a bare scalar multiplier: only the `population` numerator contains `N`, and it
enters linearly, while `Fcal`, `A_k`, `g_k`, the Boltzmann factor and the partition function `U(T)`
are all independent of `N`. Pure algebra through `population`; the enabling structural fact behind
variable projection (the `N`-section is exactly quadratic). (Ciucci et al. 1999 forward map.) -/
theorem lineIntensity_linear_in_N (kB T N Fcal : ℝ) (g E A : ι → ℝ) (k : ι) :
    lineIntensity kB T N Fcal g E A k = N * lineIntensity kB T 1 Fcal g E A k := by
  simp only [lineIntensity, population]
  ring

/-- **Profiled density (variable-projection closed form).** For a fixed temperature `T`, the
density that minimizes the `N`-section `N ↦ ∑ₖ (N·c_k − obs_k)²` of `nlObjective`, where
`c_k = lineIntensity kB T 1 Fcal g E A k`:
`N̂(T) = (∑ₖ c_k·obs_k) / (∑ₖ c_k²)`. This is the ordinary-least-squares estimate of the scalar
`N` in the single-regressor model `obs_k ≈ N·c_k` — the classical VARPRO "profiling out" of the
linear parameter, leaving a reduced objective in `T` alone. -/
noncomputable def profiledDensity (kB Fcal : ℝ) (g E A obs : ι → ℝ) (T : ℝ) : ℝ :=
  (∑ k, lineIntensity kB T 1 Fcal g E A k * obs k)
    / ∑ k, (lineIntensity kB T 1 Fcal g E A k) ^ 2

/-- General 1-D least-squares Pythagorean identity for a single regressor `c`: if `N̂` satisfies the
normal equation `N̂ · ∑ c² = ∑ c·obs`, then `∑ (N·c − obs)² = ∑ (N̂·c − obs)² + (N − N̂)² · ∑ c²`.
Pure algebra; the cross term vanishes by the normal equation. -/
private lemma nsection_decomp_general (c obs : ι → ℝ) (Nhat N : ℝ)
    (hNhat : Nhat * (∑ k, (c k) ^ 2) = ∑ k, c k * obs k) :
    ∑ k, (N * c k - obs k) ^ 2
      = ∑ k, (Nhat * c k - obs k) ^ 2 + (N - Nhat) ^ 2 * ∑ k, (c k) ^ 2 := by
  have hz : ∑ k, 2 * (N - Nhat) * (c k * (Nhat * c k - obs k)) = 0 := by
    rw [← Finset.mul_sum]
    have hinner : ∑ k, c k * (Nhat * c k - obs k) = 0 := by
      have hpt : ∀ k ∈ Finset.univ,
          c k * (Nhat * c k - obs k) = Nhat * (c k) ^ 2 - c k * obs k := fun k _ => by ring
      rw [Finset.sum_congr rfl hpt, Finset.sum_sub_distrib, ← Finset.mul_sum, hNhat, sub_self]
    rw [hinner, mul_zero]
  have hpt2 : ∀ k ∈ Finset.univ,
      (N * c k - obs k) ^ 2
        = (Nhat * c k - obs k) ^ 2 + (N - Nhat) ^ 2 * (c k) ^ 2
          + 2 * (N - Nhat) * (c k * (Nhat * c k - obs k)) := fun k _ => by ring
  rw [Finset.sum_congr rfl hpt2, Finset.sum_add_distrib, Finset.sum_add_distrib, hz,
    ← Finset.mul_sum]
  ring

/-- **`N`-section decomposition (PURE-MATH).** For a fixed `T` with nondegenerate regressor energy
`0 < ∑ₖ c_k²` (`c_k = lineIntensity kB T 1 Fcal g E A k`), for every density `N`:
`nlObjective … (T, N) = nlObjective … (T, N̂(T)) + (N − N̂(T))² · ∑ₖ c_k²`, where
`N̂(T) = profiledDensity … T`. The nonlinear objective, rewritten through
`lineIntensity_linear_in_N` into the 1-D least squares `∑ₖ (N·c_k − obs_k)²`, decomposes
orthogonally: any `N`'s excess residual over the profiled minimum is exactly `(N − N̂)² · ∑ c²`.
The 2-D nonlinear analogue of `LeastSquaresFit.rss_decomposition`. -/
theorem nlObjective_Nsection_decomposition (kB Fcal T : ℝ) (g E A obs : ι → ℝ)
    (hc : 0 < ∑ k, (lineIntensity kB T 1 Fcal g E A k) ^ 2) (N : ℝ) :
    nlObjective kB Fcal g E A obs (T, N)
      = nlObjective kB Fcal g E A obs (T, profiledDensity kB Fcal g E A obs T)
        + (N - profiledDensity kB Fcal g E A obs T) ^ 2
          * ∑ k, (lineIntensity kB T 1 Fcal g E A k) ^ 2 := by
  have hrw : ∀ M : ℝ, nlObjective kB Fcal g E A obs (T, M)
      = ∑ k, (M * lineIntensity kB T 1 Fcal g E A k - obs k) ^ 2 := by
    intro M
    change ∑ k, (lineIntensity kB T M Fcal g E A k - obs k) ^ 2
        = ∑ k, (M * lineIntensity kB T 1 Fcal g E A k - obs k) ^ 2
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [lineIntensity_linear_in_N]
  have hNhat : profiledDensity kB Fcal g E A obs T
      * (∑ k, (lineIntensity kB T 1 Fcal g E A k) ^ 2)
      = ∑ k, lineIntensity kB T 1 Fcal g E A k * obs k := by
    unfold profiledDensity
    rw [div_mul_cancel₀ _ hc.ne']
  rw [hrw N, hrw (profiledDensity kB Fcal g E A obs T)]
  exact nsection_decomp_general (fun k => lineIntensity kB T 1 Fcal g E A k) obs
    (profiledDensity kB Fcal g E A obs T) N hNhat

/-- **Nondegeneracy of the profiled least squares.** For any temperature `T`, under positive
degeneracies `g`, calibration `Fcal`, and Einstein coefficients `A`, the regressor energy
`∑ₖ (lineIntensity kB T 1 Fcal g E A k)²` is strictly positive: each `c_k` is a positive observable
at unit density (`lineIntensity_pos`; the Boltzmann factor is positive for *any* `T`, so no lower
bound on `T` is needed), and a sum over the nonempty level set of positive squares is positive. This
is the hypothesis `0 < ∑ c²` of the decomposition and minimality theorems, so they are never
vacuous. -/
theorem profiledDensity_denom_pos [Nonempty ι] {kB T Fcal : ℝ} {g E A : ι → ℝ}
    (hg : ∀ k, 0 < g k) (hFcal : 0 < Fcal) (hA : ∀ k, 0 < A k) :
    0 < ∑ k, (lineIntensity kB T 1 Fcal g E A k) ^ 2 := by
  refine Finset.sum_pos (fun k _ => ?_) univ_nonempty
  exact pow_pos (lineIntensity_pos hg one_pos hFcal hA k) 2

/-- **`N`-section global minimality (headline, REDUCED).** For a fixed `T` with `0 < ∑ₖ c_k²`, the
profiled density `N̂(T) = profiledDensity … T` minimizes the `N`-section of the joint objective:
`nlObjective … (T, N̂(T)) ≤ nlObjective … (T, N)` for every `N`. Immediate from
`nlObjective_Nsection_decomposition` — the excess `(N − N̂)² · ∑ c²` is a nonnegative sum of
squares. Reduces the joint 2-D fit's `N`-direction to the closed-form VARPRO estimate (Tognoni et
al. 2010); the `T`-direction remains open (non-convex). -/
theorem profiledDensity_isMinOn_Nsection (kB Fcal T : ℝ) (g E A obs : ι → ℝ)
    (hc : 0 < ∑ k, (lineIntensity kB T 1 Fcal g E A k) ^ 2) (N : ℝ) :
    nlObjective kB Fcal g E A obs (T, profiledDensity kB Fcal g E A obs T)
      ≤ nlObjective kB Fcal g E A obs (T, N) := by
  rw [nlObjective_Nsection_decomposition kB Fcal T g E A obs hc N]
  have hexc : 0 ≤ (N - profiledDensity kB Fcal g E A obs T) ^ 2
      * ∑ k, (lineIntensity kB T 1 Fcal g E A k) ^ 2 := mul_nonneg (sq_nonneg _) hc.le
  linarith

/-- **Strict excess off the profiled density (uniqueness core, REDUCED).** For a fixed `T` with
`0 < ∑ₖ c_k²`, every density `N ≠ N̂(T)` gives *strictly* larger `N`-section residual:
`nlObjective … (T, N̂(T)) < nlObjective … (T, N)`. The excess `(N − N̂)² · ∑ c²` is a positive times
a positive, using `sq_pos_of_ne_zero`. This is what makes `N̂(T)` the *unique* `N`-section
minimizer (`Nsection_minimizer_unique`). (Tognoni et al. 2010 VARPRO reduction.) -/
theorem nlObjective_Nsection_lt_of_ne (kB Fcal T : ℝ) (g E A obs : ι → ℝ)
    (hc : 0 < ∑ k, (lineIntensity kB T 1 Fcal g E A k) ^ 2) {N : ℝ}
    (hN : N ≠ profiledDensity kB Fcal g E A obs T) :
    nlObjective kB Fcal g E A obs (T, profiledDensity kB Fcal g E A obs T)
      < nlObjective kB Fcal g E A obs (T, N) := by
  rw [nlObjective_Nsection_decomposition kB Fcal T g E A obs hc N]
  have hexc : 0 < (N - profiledDensity kB Fcal g E A obs T) ^ 2
      * ∑ k, (lineIntensity kB T 1 Fcal g E A k) ^ 2 :=
    mul_pos (sq_pos_of_ne_zero (sub_ne_zero.mpr hN)) hc
  linarith

/-- **Uniqueness of the `N`-section minimizer (headline, REDUCED).** For a fixed `T` with
`0 < ∑ₖ c_k²`, any density `N` that minimizes the `N`-section — `nlObjective … (T, N) ≤
nlObjective … (T, N')` for all `N'` — must equal the profiled density `N̂(T)`. If it did not,
`nlObjective_Nsection_lt_of_ne` would make `N̂(T)` strictly better, contradicting minimality of `N`.
So the `N`-coordinate of every joint minimizer is *pinned* to `N̂(T̂)` by its `T`-coordinate: the
joint 2-D CF-LIBS fit is provably 1-D in `T`. This is the variable-projection reduction the solver
exploits (Tognoni et al. 2010); `T`-uniqueness stays open (non-convex objective). -/
theorem Nsection_minimizer_unique (kB Fcal T : ℝ) (g E A obs : ι → ℝ)
    (hc : 0 < ∑ k, (lineIntensity kB T 1 Fcal g E A k) ^ 2) {N : ℝ}
    (hmin : ∀ N', nlObjective kB Fcal g E A obs (T, N)
      ≤ nlObjective kB Fcal g E A obs (T, N')) :
    N = profiledDensity kB Fcal g E A obs T := by
  by_contra hne
  have hlt := nlObjective_Nsection_lt_of_ne kB Fcal T g E A obs hc hne
  have hle := hmin (profiledDensity kB Fcal g E A obs T)
  linarith

/-! ### Non-vacuity witnesses -/

/-- Positive degeneracies for the one-line VARPRO witness. -/
private def nvVpG : Fin 1 → ℝ := fun _ => 1

/-- Level energies for the one-line VARPRO witness. -/
private def nvVpE : Fin 1 → ℝ := fun _ => 0

/-- Positive Einstein coefficients for the one-line VARPRO witness. -/
private def nvVpA : Fin 1 → ℝ := fun _ => 1

/-- A concrete off-manifold observation for the one-line VARPRO witness. -/
private def nvVpObs : Fin 1 → ℝ := fun _ => 5

/-- **Non-vacuity of the nondegeneracy.** With `kB = T = Fcal = 1`, one emitting level and unit
degeneracy / Einstein coefficient, the regressor energy `∑ₖ c_k²` is strictly positive, so
`profiledDensity_denom_pos`'s hypotheses are jointly satisfiable and the profiled least squares is
genuinely nondegenerate. -/
example : 0 < ∑ k, (lineIntensity 1 1 1 1 nvVpG nvVpE nvVpA k) ^ 2 :=
  profiledDensity_denom_pos (fun _ => by norm_num [nvVpG]) one_pos (fun _ => by norm_num [nvVpA])

/-- **Non-vacuity of the `N`-section minimality.** For the one-line witness (off-manifold
`obs ≡ 5`), the profiled density minimizes the `N`-section for every `N` — confirming the headline
minimality theorem is instantiable at concrete data with all hypotheses met. -/
example (N : ℝ) :
    nlObjective 1 1 nvVpG nvVpE nvVpA nvVpObs (1, profiledDensity 1 1 nvVpG nvVpE nvVpA nvVpObs 1)
      ≤ nlObjective 1 1 nvVpG nvVpE nvVpA nvVpObs (1, N) := by
  have hg : ∀ k, 0 < nvVpG k := fun _ => by norm_num [nvVpG]
  have hA : ∀ k, 0 < nvVpA k := fun _ => by norm_num [nvVpA]
  have hc : 0 < ∑ k, (lineIntensity 1 1 1 1 nvVpG nvVpE nvVpA k) ^ 2 :=
    profiledDensity_denom_pos hg one_pos hA
  exact profiledDensity_isMinOn_Nsection 1 1 1 nvVpG nvVpE nvVpA nvVpObs hc N

/-! ### Two-line profiled `T`-uniqueness (Frontier 01, milestone M1)

The VARPRO reduction above pins the `N`-coordinate of any joint minimizer to `N̂(T)`, leaving the
open question of the *`T`-direction*. For **two lines** the profiled objective collapses to an
explicit closed form and the on-manifold minimizer is provably unique in `T`.

The key cancellation: the profiled residual is the projection residual of `obs` onto the ray through
`c(T) = (c₀(T), c₁(T))`, `c_k(T) = lineIntensity kB T 1 Fcal g E A k`. The Rayleigh quotient is
invariant under positive rescaling of `c`, so the calibration `Fcal`, density, and the *entire
partition function* `U(T)` — the intimidating half of the stated non-convexity — cancel exactly,
leaving `Φ₂(T) = (obs₁·c₀ − obs₀·c₁)² / (c₀² + c₁²)`. Dividing through by `c₀²` gives the equivalent
ratio form `(obs₁ − obs₀·t)² / (1 + t²)` with `t = c₁/c₀` strictly monotone in `T` under distinct
energies; the symmetric cross form used here needs no `c₀ ≠ 0` beyond the nondegeneracy
`0 < c₀² + c₁²`.

On-manifold this upgrades `temperature_identifiability` (an *exact-fit* ratio result, Ciucci 1999)
to a *least-squares* uniqueness statement: the true temperature is the unique global
`T`-minimizer of the profiled residual, not merely a zero of the exact ratio. (Tognoni et al. 2010
VARPRO; Ciucci et al. 1999 two-line Boltzmann ratio.) The `m ≥ 3` off-manifold case is the classical
multimodal exponential-fitting problem and is *not* claimed here.
-/

/-- Projection-residual Lagrange identity for a single regressor over two levels: the least-squares
residual of `obs = (o0, o1)` against the profiled multiple of `(c0, c1)` equals
`(o1·c0 − o0·c1)² / (c0² + c1²)`. Pure real algebra (`field_simp` + `ring`); the shared core of the
two-line profiled-residual closed form. -/
private lemma residual_two_cross (c0 c1 o0 o1 : ℝ) (hden : c0 ^ 2 + c1 ^ 2 ≠ 0) :
    ((c0 * o0 + c1 * o1) / (c0 ^ 2 + c1 ^ 2) * c0 - o0) ^ 2
      + ((c0 * o0 + c1 * o1) / (c0 ^ 2 + c1 ^ 2) * c1 - o1) ^ 2
      = (o1 * c0 - o0 * c1) ^ 2 / (c0 ^ 2 + c1 ^ 2) := by
  field_simp
  ring

/-- The joint objective at any `(T, N)`, rewritten through linearity in `N`:
`nlObjective … (T, N) = ∑ₖ (N·c_k(T) − obs_k)²`, `c_k(T) = lineIntensity kB T 1 Fcal g E A k`.
Shared expansion behind the two-line closed form and the exact-fit characterization. -/
theorem nlObjective_eq_sq_sum (kB Fcal T N : ℝ) (g E A obs : ι → ℝ) :
    nlObjective kB Fcal g E A obs (T, N)
      = ∑ k, (N * lineIntensity kB T 1 Fcal g E A k - obs k) ^ 2 := by
  change ∑ k, (lineIntensity kB T N Fcal g E A k - obs k) ^ 2 = _
  exact Finset.sum_congr rfl (fun k _ => by rw [lineIntensity_linear_in_N])

/-- **Exact-fit characterization of a zero residual.** The joint objective vanishes at `(T, N)` iff
`N` reproduces every line exactly: `nlObjective … (T, N) = 0 ↔ ∀ k, N·c_k(T) = obs_k`. A sum of
squares is zero iff every summand is (`Finset.sum_eq_zero_iff_of_nonneg`). This is the engine behind
on-manifold `T`- and joint uniqueness: a perfect fit forces the intensity ratios, hence `T`. -/
theorem nlObjective_eq_zero_iff (kB Fcal T N : ℝ) (g E A obs : ι → ℝ) :
    nlObjective kB Fcal g E A obs (T, N) = 0
      ↔ ∀ k, N * lineIntensity kB T 1 Fcal g E A k = obs k := by
  rw [nlObjective_eq_sq_sum, Finset.sum_eq_zero_iff_of_nonneg (fun k _ => sq_nonneg _)]
  refine ⟨fun h k => ?_, fun h k _ => by simp [h k]⟩
  have hk := sq_eq_zero_iff.mp (h k (Finset.mem_univ k))
  linarith

/-- **Profiled density recovers the true density on-manifold.** If `obs` is the exact forward
spectrum of `(T₀, N₀)`, the variable-projection density at the true temperature is exactly `N₀`
(`∑ c_k·obs_k = N₀·∑ c_k²`, then divide by the nondegeneracy). -/
theorem profiledDensity_onManifold {kB Fcal T0 N0 : ℝ} {g E A obs : ι → ℝ}
    (hc : 0 < ∑ k, (lineIntensity kB T0 1 Fcal g E A k) ^ 2)
    (hobs : ∀ k, obs k = lineIntensity kB T0 N0 Fcal g E A k) :
    profiledDensity kB Fcal g E A obs T0 = N0 := by
  have hnum : ∑ k, lineIntensity kB T0 1 Fcal g E A k * obs k
      = N0 * ∑ k, (lineIntensity kB T0 1 Fcal g E A k) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hobs k, lineIntensity_linear_in_N kB T0 N0 Fcal g E A k]
    ring
  unfold profiledDensity
  rw [hnum, mul_div_assoc, div_self hc.ne', mul_one]

/-- **Two-line profiled-residual closed form (PURE-MATH).** For two lines, evaluating the joint
objective at the variable-projection density `N̂(T) = profiledDensity … T` yields the explicit
projection residual
`nlObjective … (T, N̂(T)) = (obs₁·c₀ − obs₀·c₁)² / (c₀² + c₁²)`,
with `c_k = lineIntensity kB T 1 Fcal g E A k`. The calibration, density, and partition function all
cancel out of the Rayleigh-quotient residual — only the two unit-density line intensities `c₀, c₁`
survive. Pure algebra: expand `nlObjective` over `Fin 2`, substitute `profiledDensity`, then apply
the Lagrange identity `residual_two_cross`. Needs only the nondegeneracy `0 < c₀² + c₁²`
(`profiledDensity_denom_pos`). This is the closed form the two-line `T`-uniqueness rests on. -/
theorem profiledResidual_two_closed_form (kB Fcal T : ℝ) (g E A obs : Fin 2 → ℝ)
    (hc : (0 : ℝ) < (lineIntensity kB T 1 Fcal g E A 0) ^ 2
      + (lineIntensity kB T 1 Fcal g E A 1) ^ 2) :
    nlObjective kB Fcal g E A obs (T, profiledDensity kB Fcal g E A obs T)
      = (obs 1 * lineIntensity kB T 1 Fcal g E A 0
          - obs 0 * lineIntensity kB T 1 Fcal g E A 1) ^ 2
        / ((lineIntensity kB T 1 Fcal g E A 0) ^ 2
          + (lineIntensity kB T 1 Fcal g E A 1) ^ 2) := by
  have hN : profiledDensity kB Fcal g E A obs T
      = (lineIntensity kB T 1 Fcal g E A 0 * obs 0 + lineIntensity kB T 1 Fcal g E A 1 * obs 1)
        / ((lineIntensity kB T 1 Fcal g E A 0) ^ 2
          + (lineIntensity kB T 1 Fcal g E A 1) ^ 2) := by
    simp only [profiledDensity, Fin.sum_univ_two]
  rw [nlObjective_eq_sq_sum, Fin.sum_univ_two, hN]
  exact residual_two_cross (lineIntensity kB T 1 Fcal g E A 0) (lineIntensity kB T 1 Fcal g E A 1)
    (obs 0) (obs 1) hc.ne'

/-! ### General on-manifold `T`- and joint uniqueness (`m` lines)

The two-line closed form is `Fin 2`-specific, but the *on-manifold* uniqueness needs no closed form.
`nlObjective … (T, N̂(T)) = 0` is a sum of squares, so it vanishes **iff** the profiled density fits
every line exactly (`nlObjective_eq_zero_iff`). On the distinct-energy pair `(i, j)` an exact fit
forces the intensity ratio `c_j(T)/c_i(T)` to equal the observed ratio, which on-manifold is the
ratio at `T₀`; `temperature_identifiability` (Ciucci 1999, `Real.exp` injectivity) then gives
`T = T₀`. This holds for **any** finite line set with one distinct-energy pair — no Lagrange /
Cauchy–Schwarz `∑_{i<j}` machinery is needed. The `m ≥ 3` *off-manifold* case is the classical
multimodal exponential-fitting problem and is not claimed. -/

/-- **On-manifold `T`-uniqueness for `m` lines (EXACT, Ciucci 1999).** With `obs` the exact forward
spectrum of `(T₀, N₀)` and **one** distinct-energy pair `E i ≠ E j`, the profiled residual
`Φ(T) = nlObjective … (T, N̂(T))` vanishes **iff** `T = T₀`, for any finite line set. So the true
temperature is the unique global minimizer of the density-profiled objective — the general-`m`
strengthening of `nlObjective_onManifold_min` (min *value* `0` → unique *argmin*), and the
least-squares analogue of `temperature_identifiability`. Forward: `Φ(T) = 0` forces an exact fit
(`nlObjective_eq_zero_iff`), so `c_j(T)/c_i(T) = obs_j/obs_i = c_j(T₀)/c_i(T₀)`, and distinct
energies force `T = T₀`. Reverse: at `T₀` the profiled density is exactly `N₀`
(`profiledDensity_onManifold`), a perfect fit. The `m ≥ 3` off-manifold case is genuinely multimodal
and is not addressed. -/
theorem profiledT_onManifold_unique [Nonempty ι] {kB Fcal T0 N0 T : ℝ} {g E A obs : ι → ℝ}
    (hkB : 0 < kB) (hg : ∀ k, 0 < g k) (hFcal : 0 < Fcal) (hA : ∀ k, 0 < A k)
    (hN0 : 0 < N0) (hT0 : 0 < T0) (hT : 0 < T) (i j : ι) (hE : E i ≠ E j)
    (hobs : ∀ k, obs k = lineIntensity kB T0 N0 Fcal g E A k) :
    nlObjective kB Fcal g E A obs (T, profiledDensity kB Fcal g E A obs T) = 0 ↔ T = T0 := by
  have hci : 0 < lineIntensity kB T 1 Fcal g E A i := lineIntensity_pos hg one_pos hFcal hA i
  have hoi : 0 < obs i := by rw [hobs i]; exact lineIntensity_pos hg hN0 hFcal hA i
  have hcT0 : 0 < ∑ k, (lineIntensity kB T0 1 Fcal g E A k) ^ 2 :=
    profiledDensity_denom_pos hg hFcal hA
  rw [nlObjective_eq_zero_iff]
  constructor
  · intro hfit
    refine temperature_identifiability hkB hT hT0 hg one_pos hN0 hFcal hFcal hA i j hE ?_
    rw [← hobs j, ← hobs i, div_eq_div_iff hci.ne' hoi.ne', ← hfit i, ← hfit j]
    ring
  · intro hTeq
    rw [hTeq]
    intro k
    rw [profiledDensity_onManifold hcT0 hobs, hobs k,
      lineIntensity_linear_in_N kB T0 N0 Fcal g E A k]

/-- **Two-line on-manifold `T`-uniqueness (EXACT, Ciucci 1999).** The `Fin 2`, distinct-energy
`E 0 ≠ E 1` instance of `profiledT_onManifold_unique`: on-manifold, `Φ₂(T) = 0 ↔ T = T₀`. The
original two-line milestone, now a corollary of the general-`m` result. -/
theorem profiledT_two_onManifold_unique {kB Fcal T0 N0 T : ℝ} {g E A obs : Fin 2 → ℝ}
    (hkB : 0 < kB) (hg : ∀ k, 0 < g k) (hFcal : 0 < Fcal) (hA : ∀ k, 0 < A k)
    (hN0 : 0 < N0) (hE : E 0 ≠ E 1) (hT0 : 0 < T0) (hT : 0 < T)
    (hobs : ∀ k, obs k = lineIntensity kB T0 N0 Fcal g E A k) :
    nlObjective kB Fcal g E A obs (T, profiledDensity kB Fcal g E A obs T) = 0 ↔ T = T0 :=
  profiledT_onManifold_unique hkB hg hFcal hA hN0 hT0 hT 0 1 hE hobs

/-- **Joint `(T, N)` on-manifold uniqueness (EXACT, Ciucci 1999).** For any parameter pair `p` with
positive temperature `0 < p.1`, the joint objective vanishes **iff** `p` is exactly the true
parameters: `nlObjective … p = 0 ↔ p = (T₀, N₀)`, given one distinct-energy pair. This is the full
argmin uniqueness that the `N`-VARPRO reduction and `profiledT_onManifold_unique` combine to give:
a zero residual forces an exact fit at every line, which pins `T = T₀` (the ratio argument) and then
`N = N₀` (cancel `c_i(T₀) > 0`). Upgrades `nlObjective_onManifold_min` from "value `0` at the true
parameters" to "`(T₀, N₀)` is the *only* zero of the residual among positive temperatures". -/
theorem joint_onManifold_unique [Nonempty ι] {kB Fcal T0 N0 : ℝ} {g E A obs : ι → ℝ}
    (hkB : 0 < kB) (hg : ∀ k, 0 < g k) (hFcal : 0 < Fcal) (hA : ∀ k, 0 < A k)
    (hN0 : 0 < N0) (hT0 : 0 < T0) (i j : ι) (hE : E i ≠ E j)
    (hobs : ∀ k, obs k = lineIntensity kB T0 N0 Fcal g E A k)
    {p : ℝ × ℝ} (hp : 0 < p.1) :
    nlObjective kB Fcal g E A obs p = 0 ↔ p = (T0, N0) := by
  obtain ⟨T, N⟩ := p
  have hpT : 0 < T := hp
  have hci : 0 < lineIntensity kB T 1 Fcal g E A i := lineIntensity_pos hg one_pos hFcal hA i
  have hoi : 0 < obs i := by rw [hobs i]; exact lineIntensity_pos hg hN0 hFcal hA i
  rw [nlObjective_eq_zero_iff, Prod.mk.injEq]
  constructor
  · intro hfit
    have hTeq : T = T0 := by
      refine temperature_identifiability hkB hpT hT0 hg one_pos hN0 hFcal hFcal hA i j hE ?_
      rw [← hobs j, ← hobs i, div_eq_div_iff hci.ne' hoi.ne', ← hfit i, ← hfit j]
      ring
    have hci0 : 0 < lineIntensity kB T0 1 Fcal g E A i := lineIntensity_pos hg one_pos hFcal hA i
    have hi := hfit i
    rw [hTeq, hobs i, lineIntensity_linear_in_N kB T0 N0 Fcal g E A i] at hi
    exact ⟨hTeq, mul_right_cancel₀ hci0.ne' hi⟩
  · rintro ⟨hTeq, hNeq⟩
    intro k
    rw [hNeq, hTeq, hobs k, lineIntensity_linear_in_N kB T0 N0 Fcal g E A k]

/-! ### Non-vacuity witness (two-line `T`-uniqueness) -/

/-- Degeneracies for the two-line `T`-uniqueness witness. -/
private def nvT2G : Fin 2 → ℝ := fun _ => 1

/-- **Distinct** upper-level energies for the witness (`E 0 = 0 ≠ 1 = E 1`). -/
private def nvT2E : Fin 2 → ℝ := ![0, 1]

/-- Einstein coefficients for the two-line `T`-uniqueness witness. -/
private def nvT2A : Fin 2 → ℝ := fun _ => 1

/-- On-manifold observation for the witness: the exact forward spectrum of `(T₀, N₀) = (1, 1)`. -/
private noncomputable def nvT2Obs : Fin 2 → ℝ :=
  fun k => lineIntensity 1 1 1 1 nvT2G nvT2E nvT2A k

/-- **Non-vacuity of the two-line `T`-uniqueness.** With `kB = Fcal = T₀ = N₀ = 1`, distinct
energies `E = ![0, 1]` (so `E 0 ≠ E 1`), and the on-manifold spectrum `nvT2Obs`, all hypotheses of
`profiledT_two_onManifold_unique` are jointly satisfiable — the distinct-energy hypothesis is
genuinely instantiable, so the on-manifold `T`-uniqueness biconditional is not vacuous. -/
example :
    nlObjective 1 1 nvT2G nvT2E nvT2A nvT2Obs
        (1, profiledDensity 1 1 nvT2G nvT2E nvT2A nvT2Obs 1) = 0 ↔ (1 : ℝ) = 1 :=
  profiledT_two_onManifold_unique one_pos (fun _ => by norm_num [nvT2G]) one_pos
    (fun _ => by norm_num [nvT2A]) one_pos
    (by simp only [nvT2E, Matrix.cons_val_zero, Matrix.cons_val_one]; norm_num)
    one_pos one_pos (fun _ => rfl)

/-- **Non-vacuity of the joint `(T, N)` uniqueness.** The same distinct-energy witness instantiates
`joint_onManifold_unique` at the true parameters `p = (1, 1)`, confirming its hypotheses (including
a positive-temperature `p`) are jointly satisfiable. -/
example :
    nlObjective 1 1 nvT2G nvT2E nvT2A nvT2Obs (1, 1) = 0 ↔ ((1 : ℝ), (1 : ℝ)) = (1, 1) :=
  joint_onManifold_unique one_pos (fun _ => by norm_num [nvT2G]) one_pos
    (fun _ => by norm_num [nvT2A]) one_pos one_pos 0 1
    (by simp only [nvT2E, Matrix.cons_val_zero, Matrix.cons_val_one]; norm_num)
    (fun _ => rfl) one_pos

/-! ### OFF-manifold results (Frontier 01, milestones M4–M6)

On-manifold uniqueness (M1–M3) does not transfer to noisy data unchanged. This section collects the
genuinely off-manifold results: two-line off-manifold `T`-uniqueness (M5 — at most one
exactly-fitting temperature, `obs` arbitrary), a near-manifold `L²` stability bound on the profiled
residual (M4 — the value half of the perturbation picture), and the honest `m ≥ 3` non-uniqueness
counterexample (M6 — the residual value is not injective in `T`, fencing off the frontier). -/

/-- **OFF-manifold `T`-uniqueness for `m` lines (EXACT, Ciucci 1999).** The first genuinely
off-manifold identifiability result: `obs : ι → ℝ` is *arbitrary* (no on-manifold /
exact-forward-spectrum hypothesis), only `obs i ≠ 0` on the chosen distinct-energy pair `E i ≠ E j`.
If two positive temperatures `T₁, T₂` both drive the density-profiled residual
`Φ(T) = nlObjective … (T, N̂(T))` to zero, they coincide. So `m` off-manifold lines admit **at most
one** exactly-fitting temperature.

Mechanism (the same exact-fit engine as the on-manifold `profiledT_onManifold_unique`, no closed
form): `Φ(T) = 0 ⟺` an exact fit `∀ k, N̂(T)·c_k(T) = obs_k` (`nlObjective_eq_zero_iff`). On pair
`(i, j)` this forces the cross-ratio `obs_j·c_i(T) = obs_i·c_j(T)` at each temperature; since the
observed ratio `obs_j/obs_i` is `obs`-fixed, the intensity ratio `c_j/c_i` is *forced identical* at
`T₁` and `T₂`, and `temperature_identifiability` (distinct energies, `Real.exp` injectivity) pins
`T₁ = T₂`. Unlike the on-manifold results, `obs` is unconstrained — this is a true off-manifold
uniqueness statement. -/
theorem profiledT_offManifold_unique [Nonempty ι] {kB Fcal T1 T2 : ℝ} {g E A obs : ι → ℝ}
    (hkB : 0 < kB) (hg : ∀ k, 0 < g k) (hFcal : 0 < Fcal) (hA : ∀ k, 0 < A k)
    (hT1 : 0 < T1) (hT2 : 0 < T2) (i j : ι) (hobsi : obs i ≠ 0) (hE : E i ≠ E j)
    (h1 : nlObjective kB Fcal g E A obs (T1, profiledDensity kB Fcal g E A obs T1) = 0)
    (h2 : nlObjective kB Fcal g E A obs (T2, profiledDensity kB Fcal g E A obs T2) = 0) :
    T1 = T2 := by
  rw [nlObjective_eq_zero_iff] at h1 h2
  have hci1 : 0 < lineIntensity kB T1 1 Fcal g E A i := lineIntensity_pos hg one_pos hFcal hA i
  have hci2 : 0 < lineIntensity kB T2 1 Fcal g E A i := lineIntensity_pos hg one_pos hFcal hA i
  -- Cross-ratio `obs_j·c_i(T) = obs_i·c_j(T)` at each temperature, straight from the exact fit.
  have cr1 : obs j * lineIntensity kB T1 1 Fcal g E A i
      = obs i * lineIntensity kB T1 1 Fcal g E A j := by rw [← h1 i, ← h1 j]; ring
  have cr2 : obs j * lineIntensity kB T2 1 Fcal g E A i
      = obs i * lineIntensity kB T2 1 Fcal g E A j := by rw [← h2 i, ← h2 j]; ring
  -- The shared observed ratio forces `c_j(T₁)·c_i(T₂) = c_j(T₂)·c_i(T₁)`.
  have hprod : lineIntensity kB T1 1 Fcal g E A j * lineIntensity kB T2 1 Fcal g E A i
      = lineIntensity kB T2 1 Fcal g E A j * lineIntensity kB T1 1 Fcal g E A i := by
    have G : obs i * (lineIntensity kB T1 1 Fcal g E A j * lineIntensity kB T2 1 Fcal g E A i)
        = obs i * (lineIntensity kB T2 1 Fcal g E A j * lineIntensity kB T1 1 Fcal g E A i) := by
      linear_combination (lineIntensity kB T1 1 Fcal g E A i) * cr2
        - (lineIntensity kB T2 1 Fcal g E A i) * cr1
    exact mul_left_cancel₀ hobsi G
  refine temperature_identifiability hkB hT1 hT2 hg one_pos one_pos hFcal hFcal hA i j hE ?_
  rw [div_eq_div_iff hci1.ne' hci2.ne']
  exact hprod

/-- **Two-line OFF-manifold `T`-uniqueness (EXACT, Ciucci 1999).** The `Fin 2`, distinct-energy
`E 0 ≠ E 1` instance of `profiledT_offManifold_unique` (pair `i, j = 0, 1`, `obs 0 ≠ 0`): two
off-manifold lines admit at most one exactly-fitting temperature. A corollary of the general-`m`
result. -/
theorem profiledT_two_offManifold_unique {kB Fcal T1 T2 : ℝ} {g E A obs : Fin 2 → ℝ}
    (hkB : 0 < kB) (hg : ∀ k, 0 < g k) (hFcal : 0 < Fcal) (hA : ∀ k, 0 < A k)
    (hT1 : 0 < T1) (hT2 : 0 < T2) (hobs0 : obs 0 ≠ 0) (hE : E 0 ≠ E 1)
    (h1 : nlObjective kB Fcal g E A obs (T1, profiledDensity kB Fcal g E A obs T1) = 0)
    (h2 : nlObjective kB Fcal g E A obs (T2, profiledDensity kB Fcal g E A obs T2) = 0) :
    T1 = T2 :=
  profiledT_offManifold_unique hkB hg hFcal hA hT1 hT2 0 1 hobs0 hE h1 h2

/-! ### Non-vacuity witness (two-line OFF-manifold `T`-uniqueness) -/

/-- Degeneracies for the off-manifold witness. -/
private def nvOffG : Fin 2 → ℝ := fun _ => 1

/-- **Distinct** upper-level energies for the off-manifold witness (`E 0 = 0 ≠ 1 = E 1`). -/
private def nvOffE : Fin 2 → ℝ := ![0, 1]

/-- Einstein coefficients for the off-manifold witness. -/
private def nvOffA : Fin 2 → ℝ := fun _ => 1

/-- **Non-vacuity of `profiledT_two_offManifold_unique`.** Every hypothesis is realized at concrete
distinct-energy data `E = ![0,1]` with an *arbitrary* off-manifold observation `obs = ![3, 7]`
(no exact-forward-spectrum constraint), so the theorem is not vacuous: any two zero-residual
temperatures for these two lines are forced equal. -/
example {T1 T2 : ℝ} (hT1 : 0 < T1) (hT2 : 0 < T2)
    (h1 : nlObjective 1 1 nvOffG nvOffE nvOffA ![3, 7]
        (T1, profiledDensity 1 1 nvOffG nvOffE nvOffA ![3, 7] T1) = 0)
    (h2 : nlObjective 1 1 nvOffG nvOffE nvOffA ![3, 7]
        (T2, profiledDensity 1 1 nvOffG nvOffE nvOffA ![3, 7] T2) = 0) :
    T1 = T2 :=
  profiledT_two_offManifold_unique (obs := ![3, 7]) one_pos (fun _ => one_pos) one_pos
    (fun _ => one_pos) hT1 hT2 (by norm_num) (by simp [nvOffE]) h1 h2

/-- Elementary quadratic split `(a - c)² ≤ 2(a-b)² + 2(b-c)²`, the discrete analogue of
`‖x‖² ≤ 2‖x-y‖² + 2‖y‖²`. Certificate: `2(a-b)² + 2(b-c)² − (a-c)² = (a-2b+c)² ≥ 0`. -/
private lemma sq_sub_le_two_split (a b c : ℝ) :
    (a - c) ^ 2 ≤ 2 * (a - b) ^ 2 + 2 * (b - c) ^ 2 := by
  nlinarith [sq_nonneg (a - 2 * b + c)]

/-- **Near-manifold stability of the profiled residual in the observation (REDUCED, Tognoni 2010).**
For a fixed temperature `T` with nondegenerate regressor energy `0 < ∑ₖ c_k²`
(`c_k = lineIntensity kB T 1 Fcal g E A k`), the density-profiled residual
`Φ_obs(T) = nlObjective … obs (T, N̂_obs(T))` is stable under an `L²` perturbation of the data:
`Φ_obs(T) ≤ 2·Φ_obs'(T) + 2·∑ₖ (obs'_k − obs_k)²` for any two observations `obs, obs'`. This is the
honest analytic core a full perturbation/local-uniqueness argument rests on — a global quadratic
*upper* stability estimate controlling how far the profiled residual can rise under an `L²` data
perturbation. It is NOT a continuity statement
(the factor `2` leaves `Φ ≤ 2Φ` slack at `obs = obs'`) and NOT a local-uniqueness theorem; its
force is the near-manifold corollary below.
Proof: variable-projection minimality (`profiledDensity_isMinOn_Nsection`) bounds `Φ_obs(T)` by the
residual of `obs` measured at the *other* profiled density `N̂_obs'(T)`; the elementary split
`(x−obs)² ≤ 2(x−obs')² + 2(obs'−obs)²` summed over lines finishes. No distinct-energy hypothesis is
needed, so the bound holds for every line set. -/
theorem profiledResidual_stability_in_obs [Nonempty ι] {kB Fcal T : ℝ} {g E A obs obs' : ι → ℝ}
    (hc : 0 < ∑ k, (lineIntensity kB T 1 Fcal g E A k) ^ 2) :
    nlObjective kB Fcal g E A obs (T, profiledDensity kB Fcal g E A obs T)
      ≤ 2 * nlObjective kB Fcal g E A obs' (T, profiledDensity kB Fcal g E A obs' T)
        + 2 * ∑ k, (obs' k - obs k) ^ 2 := by
  set Nh' := profiledDensity kB Fcal g E A obs' T
  -- Minimality of the profiled density for `obs`, evaluated against the competitor `Nh'`.
  have hmin : nlObjective kB Fcal g E A obs (T, profiledDensity kB Fcal g E A obs T)
      ≤ nlObjective kB Fcal g E A obs (T, Nh') :=
    profiledDensity_isMinOn_Nsection kB Fcal T g E A obs hc Nh'
  -- Rewrite both competitor residuals as explicit sums of squares.
  have hL : nlObjective kB Fcal g E A obs (T, Nh')
      = ∑ k, (Nh' * lineIntensity kB T 1 Fcal g E A k - obs k) ^ 2 :=
    nlObjective_eq_sq_sum kB Fcal T Nh' g E A obs
  have hR : nlObjective kB Fcal g E A obs' (T, Nh')
      = ∑ k, (Nh' * lineIntensity kB T 1 Fcal g E A k - obs' k) ^ 2 :=
    nlObjective_eq_sq_sum kB Fcal T Nh' g E A obs'
  -- Pointwise quadratic split, summed over lines.
  have hsum : ∑ k, (Nh' * lineIntensity kB T 1 Fcal g E A k - obs k) ^ 2
      ≤ ∑ k, (2 * (Nh' * lineIntensity kB T 1 Fcal g E A k - obs' k) ^ 2
              + 2 * (obs' k - obs k) ^ 2) :=
    Finset.sum_le_sum (fun k _ =>
      sq_sub_le_two_split (Nh' * lineIntensity kB T 1 Fcal g E A k) (obs' k) (obs k))
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
  calc nlObjective kB Fcal g E A obs (T, profiledDensity kB Fcal g E A obs T)
      ≤ nlObjective kB Fcal g E A obs (T, Nh') := hmin
    _ = ∑ k, (Nh' * lineIntensity kB T 1 Fcal g E A k - obs k) ^ 2 := hL
    _ ≤ 2 * ∑ k, (Nh' * lineIntensity kB T 1 Fcal g E A k - obs' k) ^ 2
          + 2 * ∑ k, (obs' k - obs k) ^ 2 := hsum
    _ = 2 * nlObjective kB Fcal g E A obs' (T, Nh')
          + 2 * ∑ k, (obs' k - obs k) ^ 2 := by rw [hR]

/-- **Near-manifold residual bound at the true temperature (REDUCED, Tognoni 2010).** If the data is
the exact forward spectrum of `(T₀, N₀)` corrupted by additive noise `η` (`obs_k = c_k(T₀)·N₀ + η_k`
via `lineIntensity`), the profiled residual at the *true* temperature is controlled by the noise
energy: `Φ_obs(T₀) ≤ 2·∑ₖ η_k²`. Immediate instance of `profiledResidual_stability_in_obs` against
the clean forward spectrum, whose profiled residual at `T₀` is exactly `0`
(`profiledDensity_onManifold` + `nlObjective_eq_zero_iff`). This quantifies
"small `L²` noise ⇒ small residual at the truth" — the *value* half of the near-manifold picture;
the *argmin* half (that `T₀` strictly out-competes far temperatures) is
`profiledResidual_true_strict_lt` below. -/
theorem profiledResidual_nearManifold_bound [Nonempty ι] {kB Fcal T0 N0 : ℝ}
    {g E A obs η : ι → ℝ}
    (hc : 0 < ∑ k, (lineIntensity kB T0 1 Fcal g E A k) ^ 2)
    (hobs : ∀ k, obs k = lineIntensity kB T0 N0 Fcal g E A k + η k) :
    nlObjective kB Fcal g E A obs (T0, profiledDensity kB Fcal g E A obs T0)
      ≤ 2 * ∑ k, (η k) ^ 2 := by
  set f := fun k => lineIntensity kB T0 N0 Fcal g E A k
  -- The clean forward spectrum has zero profiled residual at `T0`.
  have hfN : profiledDensity kB Fcal g E A f T0 = N0 :=
    profiledDensity_onManifold hc (fun k => rfl)
  have hfzero : nlObjective kB Fcal g E A f (T0, profiledDensity kB Fcal g E A f T0) = 0 := by
    rw [hfN, nlObjective_eq_zero_iff]
    exact fun k => (lineIntensity_linear_in_N kB T0 N0 Fcal g E A k).symm
  -- The perturbation of the data away from the clean spectrum is exactly `η`.
  have hsumeq : ∑ k, (f k - obs k) ^ 2 = ∑ k, (η k) ^ 2 := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hobs k]; ring
  have hbound := profiledResidual_stability_in_obs (kB := kB) (Fcal := Fcal) (T := T0)
    (g := g) (E := E) (A := A) (obs := obs) (obs' := f) hc
  rw [hfzero, hsumeq] at hbound
  linarith

/-- Non-vacuity witness: the stability bound holds at concrete distinct-energy two-line data
(`kB = Fcal = 1`, `g = A = ![1,1]`, `E = ![0,1]`), with clean data `![1,1]` vs. perturbed `![0,0]`.
The nondegeneracy hypothesis is discharged by `profiledDensity_denom_pos`, so the statement is
machine-checked to be inhabited (not vacuously true). -/
example :
    nlObjective (ι := Fin 2) 1 1 ![1, 1] ![0, 1] ![1, 1] ![0, 0]
        (1, profiledDensity 1 1 ![1, 1] ![0, 1] ![1, 1] ![0, 0] 1)
      ≤ 2 * nlObjective 1 1 ![1, 1] ![0, 1] ![1, 1] ![1, 1]
          (1, profiledDensity 1 1 ![1, 1] ![0, 1] ![1, 1] ![1, 1] 1)
        + 2 * ∑ k, (![1, 1] k - (![0, 0] : Fin 2 → ℝ) k) ^ 2 :=
  profiledResidual_stability_in_obs
    (profiledDensity_denom_pos (fun k => by fin_cases k <;> norm_num) (by norm_num)
      (fun k => by fin_cases k <;> norm_num))

/-- **Near-manifold strict domination by the true temperature (REDUCED, Tognoni 2010).** The
*argmin* half of the near-manifold picture. For noisy data `obs = forward(T₀,N₀) + η`, the true
`T₀` gives a **strictly** smaller profiled residual than any temperature `T` whose *clean* residual
gap exceeds six times the noise energy: `6·∑ηₖ² < Φ_clean(T) ⟹ Φ_obs(T₀) < Φ_obs(T)`. So every
temperature the noise-free objective separates from `T₀` by more than `O(‖η‖²)` still loses to `T₀`
on the noisy data — a quantitative local-minimizer statement. Honestly **not** a topological
neighborhood-uniqueness theorem: temperatures with clean gap `≤ 6‖η‖²` are uncontrolled (that tail
would need the heavy perturbation machinery). Proof: `profiledResidual_stability_in_obs`
(clean vs noisy) gives `Φ_clean(T) ≤ 2·Φ_obs(T) + 2∑ηₖ²` and `profiledResidual_nearManifold_bound`
gives `Φ_obs(T₀) ≤ 2∑ηₖ²`; the gap hypothesis closes the strict inequality by linear arithmetic. -/
theorem profiledResidual_true_strict_lt [Nonempty ι] {kB Fcal T0 N0 T : ℝ} {g E A obs η : ι → ℝ}
    (hc0 : 0 < ∑ k, (lineIntensity kB T0 1 Fcal g E A k) ^ 2)
    (hcT : 0 < ∑ k, (lineIntensity kB T 1 Fcal g E A k) ^ 2)
    (hobs : ∀ k, obs k = lineIntensity kB T0 N0 Fcal g E A k + η k)
    (hgap : 6 * ∑ k, (η k) ^ 2
      < nlObjective kB Fcal g E A (fun k => lineIntensity kB T0 N0 Fcal g E A k)
          (T, profiledDensity kB Fcal g E A (fun k => lineIntensity kB T0 N0 Fcal g E A k) T)) :
    nlObjective kB Fcal g E A obs (T0, profiledDensity kB Fcal g E A obs T0)
      < nlObjective kB Fcal g E A obs (T, profiledDensity kB Fcal g E A obs T) := by
  have htruth := profiledResidual_nearManifold_bound hc0 hobs
  have hstab := profiledResidual_stability_in_obs (kB := kB) (Fcal := Fcal) (T := T)
    (g := g) (E := E) (A := A) (obs := fun k => lineIntensity kB T0 N0 Fcal g E A k)
    (obs' := obs) hcT
  have hη : ∑ k, (obs k - lineIntensity kB T0 N0 Fcal g E A k) ^ 2 = ∑ k, (η k) ^ 2 := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hobs k]; ring
  rw [hη] at hstab
  linarith [htruth, hstab, hgap]

/-- Non-vacuity witness: `profiledResidual_nearManifold_bound` at concrete two-line data
(`E = ![0,1]`, `T₀ = N₀ = 1`) with noise `η = ![1,1]`; nondegeneracy via
`profiledDensity_denom_pos`. -/
example :
    nlObjective 1 1 ![1, 1] ![0, 1] ![1, 1]
        (fun k => lineIntensity 1 1 1 1 ![1, 1] ![0, 1] ![1, 1] k + (![1, 1] : Fin 2 → ℝ) k)
        (1, profiledDensity 1 1 ![1, 1] ![0, 1] ![1, 1]
          (fun k => lineIntensity 1 1 1 1 ![1, 1] ![0, 1] ![1, 1] k + (![1, 1] : Fin 2 → ℝ) k) 1)
      ≤ 2 * ∑ k, ((![1, 1] : Fin 2 → ℝ) k) ^ 2 :=
  profiledResidual_nearManifold_bound
    (profiledDensity_denom_pos (fun k => by fin_cases k <;> norm_num) (by norm_num)
      (fun k => by fin_cases k <;> norm_num)) (fun _ => rfl)

/-- Non-vacuity witness: strict domination in the noise-free limit `η = 0`, where the gap hypothesis
reduces to `0 < Φ_clean(T)` for `T ≠ T₀` — discharged by `profiledT_onManifold_unique` (residual
strictly positive off the true temperature) at `E = ![0,1]`, `T₀ = 1`, `T = 2`. -/
example :
    nlObjective 1 1 ![1, 1] ![0, 1] ![1, 1]
        (fun k => lineIntensity 1 1 1 1 ![1, 1] ![0, 1] ![1, 1] k + (![0, 0] : Fin 2 → ℝ) k)
        (1, profiledDensity 1 1 ![1, 1] ![0, 1] ![1, 1]
          (fun k => lineIntensity 1 1 1 1 ![1, 1] ![0, 1] ![1, 1] k + (![0, 0] : Fin 2 → ℝ) k) 1)
      < nlObjective 1 1 ![1, 1] ![0, 1] ![1, 1]
        (fun k => lineIntensity 1 1 1 1 ![1, 1] ![0, 1] ![1, 1] k + (![0, 0] : Fin 2 → ℝ) k)
        (2, profiledDensity 1 1 ![1, 1] ![0, 1] ![1, 1]
          (fun k => lineIntensity 1 1 1 1 ![1, 1] ![0, 1] ![1, 1] k + (![0, 0] : Fin 2 → ℝ) k)
          2) := by
  have hg : ∀ k, 0 < (![1, 1] : Fin 2 → ℝ) k := fun k => by fin_cases k <;> norm_num
  have hA : ∀ k, 0 < (![1, 1] : Fin 2 → ℝ) k := fun k => by fin_cases k <;> norm_num
  have hgap : 6 * ∑ k, ((![0, 0] : Fin 2 → ℝ) k) ^ 2
      < nlObjective 1 1 ![1, 1] ![0, 1] ![1, 1]
          (fun k => lineIntensity 1 1 1 1 ![1, 1] ![0, 1] ![1, 1] k)
          (2, profiledDensity 1 1 ![1, 1] ![0, 1] ![1, 1]
            (fun k => lineIntensity 1 1 1 1 ![1, 1] ![0, 1] ![1, 1] k) 2) := by
    have hsum0 : (6 : ℝ) * ∑ k, ((![0, 0] : Fin 2 → ℝ) k) ^ 2 = 0 := by simp [Fin.sum_univ_two]
    rw [hsum0]
    refine lt_of_le_of_ne ?_ ?_
    · rw [nlObjective_eq_sq_sum]; exact Finset.sum_nonneg (fun k _ => sq_nonneg _)
    · intro h
      have h21 : (2 : ℝ) = 1 := (profiledT_onManifold_unique (by norm_num) hg (by norm_num) hA
        (by norm_num) (by norm_num) (by norm_num) 0 1
        (by simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; norm_num)
        (fun _ => rfl)).mp h.symm
      norm_num at h21
  exact profiledResidual_true_strict_lt (profiledDensity_denom_pos hg (by norm_num) hA)
    (profiledDensity_denom_pos hg (by norm_num) hA) (fun _ => rfl) hgap

/-- **Near-manifold minimizer localization / trapping (REDUCED, Tognoni 2010).** The topological
form of the near-manifold picture. For noisy data `obs = forward(T₀,N₀) + η`, any temperature `T`
that fits the noisy data **at least as well as `T₀`** — in particular any minimizer of the profiled
objective over a set containing `T₀` — has a small *clean* residual gap: `Φ_clean(T) ≤ 6·∑ηₖ²`. So
every noisy near-optimizer is trapped in the clean sublevel set `{T : Φ_clean(T) ≤ 6·∑ηₖ²}`. This is
a genuine neighborhood of `T₀` (it contains `T₀`, where `Φ_clean = 0`), and since `Φ_clean` vanishes
**only** at `T₀` (`profiledT_onManifold_unique`), the trapping set collapses to `{T₀}` as the noise
energy `∑ηₖ² → 0`: the solver's answer is provably pinned near the truth, with the closeness
controlled by the noise. This is the argmin-localization face of `profiledResidual_true_strict_lt`
(its contrapositive), from `profiledResidual_nearManifold_bound` +
`profiledResidual_stability_in_obs` via `linarith`.

Honest scope — what this deliberately does **not** claim: (1) `T₀` is *not* asserted to be a strict
local minimizer of the noisy `Φ_obs` — under generic noise the minimizer shifts off `T₀` by
`O(‖η‖)`, so that statement is false; trapping localizes the *shifted* minimizer, which is correct.
(2) The *metric* refinement `|T − T₀| ≤ C·√(∑ηₖ²)` and strict-convexity uniqueness of the minimizer
*within* the neighborhood need the Rayleigh-quotient curvature/Hessian route (heavy, and flagged
as a trap in the frontier dossier); they remain open. -/
theorem profiledResidual_minimizer_trapped [Nonempty ι] {kB Fcal T0 N0 T : ℝ} {g E A obs η : ι → ℝ}
    (hc0 : 0 < ∑ k, (lineIntensity kB T0 1 Fcal g E A k) ^ 2)
    (hcT : 0 < ∑ k, (lineIntensity kB T 1 Fcal g E A k) ^ 2)
    (hobs : ∀ k, obs k = lineIntensity kB T0 N0 Fcal g E A k + η k)
    (hle : nlObjective kB Fcal g E A obs (T, profiledDensity kB Fcal g E A obs T)
         ≤ nlObjective kB Fcal g E A obs (T0, profiledDensity kB Fcal g E A obs T0)) :
    nlObjective kB Fcal g E A (fun k => lineIntensity kB T0 N0 Fcal g E A k)
        (T, profiledDensity kB Fcal g E A (fun k => lineIntensity kB T0 N0 Fcal g E A k) T)
      ≤ 6 * ∑ k, (η k) ^ 2 := by
  have htruth := profiledResidual_nearManifold_bound hc0 hobs
  have hstab := profiledResidual_stability_in_obs (kB := kB) (Fcal := Fcal) (T := T)
    (g := g) (E := E) (A := A) (obs := fun k => lineIntensity kB T0 N0 Fcal g E A k)
    (obs' := obs) hcT
  have hη : ∑ k, (obs k - lineIntensity kB T0 N0 Fcal g E A k) ^ 2 = ∑ k, (η k) ^ 2 := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hobs k]; ring
  rw [hη] at hstab
  linarith [htruth, hstab, hle]

/-- Non-vacuity witness: the trapping bound at `T = T₀` (the `hle` premise is `le_refl`, the clean
gap at `T₀` is `0`, so `0 ≤ 6·∑ηₖ²`) — data `E = ![0,1]`, `T₀ = N₀ = 1`, noise `η = ![1,1]`. -/
example :
    nlObjective 1 1 ![1, 1] ![0, 1] ![1, 1]
        (fun k => lineIntensity 1 1 1 1 ![1, 1] ![0, 1] ![1, 1] k)
        (1, profiledDensity 1 1 ![1, 1] ![0, 1] ![1, 1]
          (fun k => lineIntensity 1 1 1 1 ![1, 1] ![0, 1] ![1, 1] k) 1)
      ≤ 6 * ∑ k, ((![1, 1] : Fin 2 → ℝ) k) ^ 2 := by
  have hg : ∀ k, 0 < (![1, 1] : Fin 2 → ℝ) k := fun k => by fin_cases k <;> norm_num
  have hA : ∀ k, 0 < (![1, 1] : Fin 2 → ℝ) k := fun k => by fin_cases k <;> norm_num
  exact profiledResidual_minimizer_trapped (profiledDensity_denom_pos hg (by norm_num) hA)
    (profiledDensity_denom_pos hg (by norm_num) hA) (fun _ => rfl) (le_refl _)

/-- **Profiled residual at an orthogonal observation (PURE-MATH).** If the observation vector `obs`
is orthogonal to the unit-density line-intensity vector `c(T)`, i.e.
`∑ₖ lineIntensity kB T 1 Fcal g E A k · obs_k = 0`, then the variable-projection density profiles to
zero and the profiled residual equals the full observation energy:
`nlObjective … (T, N̂(T)) = ∑ₖ obs_k²`. The normal-equation numerator vanishes, so
`N̂(T) = 0/‖c(T)‖² = 0`, and the residual is `∑ₖ (0·c_k − obs_k)² = ∑ₖ obs_k²`. Pure algebra — the
worst-case fit at any temperature where `obs` has no component along the line-intensity ray. -/
theorem profiledResidual_of_orthogonal (kB Fcal T : ℝ) (g E A obs : ι → ℝ)
    (horth : ∑ k, lineIntensity kB T 1 Fcal g E A k * obs k = 0) :
    nlObjective kB Fcal g E A obs (T, profiledDensity kB Fcal g E A obs T)
      = ∑ k, (obs k) ^ 2 := by
  have hpd : profiledDensity kB Fcal g E A obs T = 0 := by
    unfold profiledDensity
    rw [horth, zero_div]
  rw [hpd, nlObjective_eq_sq_sum]
  exact Finset.sum_congr rfl (fun k _ => by ring)

/-! ### Explicit `m = 3` counterexample: the profiled residual value is NOT injective in `T`

The general-`m` *on-manifold* `T`-uniqueness (`profiledT_onManifold_unique`) does NOT extend to the
off-manifold case for `m ≥ 3`. We exhibit an explicit three-line configuration and two distinct
positive temperatures `T₁ = 1 ≠ 2 = T₂` at which the density-profiled least-squares residual takes
the *same* positive value. This documents that the residual VALUE does not single out one
temperature once `m ≥ 3` — the classical multimodal exponential-fitting obstruction. It is NOT a
uniqueness theorem and makes no claim that both temperatures are minimizers. -/

/-- Unit degeneracies for the `m = 3` non-injectivity witness. -/
private def ceG : Fin 3 → ℝ := fun _ => 1

/-- Unit Einstein coefficients for the `m = 3` non-injectivity witness. -/
private def ceA : Fin 3 → ℝ := fun _ => 1

/-- Distinct upper-level energies chosen so the Boltzmann factors are rational at `T ∈ {1, 2}`:
`E = (0, −2·log 2, −2·log 3)`. At `T = 1` the factors are `(1, 4, 9)`; at `T = 2` they are
`(1, 2, 3)` (each is the square-root of its `T = 1` value, since `T₂ = 2·T₁`). -/
private noncomputable def ceE : Fin 3 → ℝ
  | 0 => 0
  | 1 => -(2 * Real.log 2)
  | 2 => -(2 * Real.log 3)

/-- Observation vector orthogonal to the line-intensity ray at BOTH `T = 1` and `T = 2`:
`obs = (3, −3, 1)`. Solves `∑ₖ exp(−E_k/1)·obs_k = 3 − 12 + 9 = 0` and
`∑ₖ exp(−E_k/2)·obs_k = 3 − 6 + 3 = 0`. -/
private def ceObs : Fin 3 → ℝ
  | 0 => 3
  | 1 => -3
  | 2 => 1

private lemma hl2 : Real.exp (Real.log 2) = 2 := Real.exp_log (by norm_num)
private lemma hl3 : Real.exp (Real.log 3) = 3 := Real.exp_log (by norm_num)
private lemma e4 : Real.exp (2 * Real.log 2) = 4 := by rw [two_mul, Real.exp_add, hl2]; norm_num
private lemma e9 : Real.exp (2 * Real.log 3) = 9 := by rw [two_mul, Real.exp_add, hl3]; norm_num

/-- Shared reduction for the orthogonality lemmas: at unit degeneracy/Einstein coefficients, the
line-intensity dot product factors as the Boltzmann dot product over the (nonzero) partition
function, so a vanishing Boltzmann dot product gives a vanishing line-intensity dot product. -/
private lemma ce_lineIntensity_sum_of_boltzmann {T : ℝ}
    (hnum : ∑ k, boltzmannFactor 1 T (ceE k) * ceObs k = 0) :
    ∑ k, lineIntensity 1 T 1 1 ceG ceE ceA k * ceObs k = 0 := by
  have hLI : ∀ k, lineIntensity 1 T 1 1 ceG ceE ceA k * ceObs k
      = boltzmannFactor 1 T (ceE k) * ceObs k / partitionFunction 1 T ceG ceE := by
    intro k
    simp only [lineIntensity, population]
    rw [show ceA k = 1 from rfl, show ceG k = 1 from rfl]
    ring
  rw [Finset.sum_congr rfl (fun k _ => hLI k), ← Finset.sum_div, hnum, zero_div]

/-- Orthogonality of `ceObs` to the line-intensity ray at `T = 1` (Boltzmann factors `1, 4, 9`). -/
private lemma ce_orth_one :
    ∑ k, lineIntensity 1 1 1 1 ceG ceE ceA k * ceObs k = 0 := by
  have b0 : boltzmannFactor 1 1 (ceE 0) = 1 := by
    simp only [boltzmannFactor]
    rw [show -(ceE 0) / (1 * 1) = 0 from by simp only [ceE]; ring, Real.exp_zero]
  have b1 : boltzmannFactor 1 1 (ceE 1) = 4 := by
    simp only [boltzmannFactor]
    rw [show -(ceE 1) / (1 * 1) = 2 * Real.log 2 from by simp only [ceE]; ring, e4]
  have b2 : boltzmannFactor 1 1 (ceE 2) = 9 := by
    simp only [boltzmannFactor]
    rw [show -(ceE 2) / (1 * 1) = 2 * Real.log 3 from by simp only [ceE]; ring, e9]
  exact ce_lineIntensity_sum_of_boltzmann
    (by rw [Fin.sum_univ_three, b0, b1, b2]; simp only [ceObs]; norm_num)

/-- Orthogonality of `ceObs` to the line-intensity ray at `T = 2` (Boltzmann factors `1, 2, 3`). -/
private lemma ce_orth_two :
    ∑ k, lineIntensity 1 2 1 1 ceG ceE ceA k * ceObs k = 0 := by
  have b0 : boltzmannFactor 1 2 (ceE 0) = 1 := by
    simp only [boltzmannFactor]
    rw [show -(ceE 0) / (1 * 2) = 0 from by simp only [ceE]; ring, Real.exp_zero]
  have b1 : boltzmannFactor 1 2 (ceE 1) = 2 := by
    simp only [boltzmannFactor]
    rw [show -(ceE 1) / (1 * 2) = Real.log 2 from by simp only [ceE]; ring, hl2]
  have b2 : boltzmannFactor 1 2 (ceE 2) = 3 := by
    simp only [boltzmannFactor]
    rw [show -(ceE 2) / (1 * 2) = Real.log 3 from by simp only [ceE]; ring, hl3]
  exact ce_lineIntensity_sum_of_boltzmann
    (by rw [Fin.sum_univ_three, b0, b1, b2]; simp only [ceObs]; norm_num)

/-- **Off-manifold `T`-non-uniqueness for `m = 3` (EXACT, HONEST NEGATIVE result).** The
density-profiled least-squares residual is NOT injective in the temperature once there are `m ≥ 3`
lines: for the explicit three-line configuration `ceG`, `ceE = (0, −2·log 2, −2·log 3)` (three
*distinct* energies), `ceA`, and off-manifold observation `ceObs = (3, −3, 1)`, the two distinct
positive temperatures `T₁ = 1` and `T₂ = 2` yield the SAME positive profiled residual
`Φ(1) = Φ(2) = 19 > 0`. Both temperatures make `ceObs` orthogonal to the line-intensity ray, so the
profiled density is `0` and the residual is `‖ceObs‖²` at each. This FALSIFIES any general
off-manifold analogue of `profiledT_onManifold_unique`: the residual VALUE does not single out one
temperature. It is a documented obstruction, NOT a uniqueness theorem — it does not assert either
temperature is a minimizer (this is the classical multimodal exponential-fitting problem). -/
theorem profiledResidual_not_injective_m3 :
    (0 : ℝ) < 1 ∧ (0 : ℝ) < 2 ∧ (1 : ℝ) ≠ 2
      ∧ ceE 0 ≠ ceE 1 ∧ ceE 0 ≠ ceE 2 ∧ ceE 1 ≠ ceE 2
      ∧ nlObjective 1 1 ceG ceE ceA ceObs (1, profiledDensity 1 1 ceG ceE ceA ceObs 1)
          = nlObjective 1 1 ceG ceE ceA ceObs (2, profiledDensity 1 1 ceG ceE ceA ceObs 2)
      ∧ 0 < nlObjective 1 1 ceG ceE ceA ceObs (1, profiledDensity 1 1 ceG ceE ceA ceObs 1) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hlog23 : Real.log 2 < Real.log 3 := Real.log_lt_log (by norm_num) (by norm_num)
  have hsum : ∑ k, (ceObs k) ^ 2 = 19 := by
    rw [Fin.sum_univ_three]; simp only [ceObs]; norm_num
  have hphi1 : nlObjective 1 1 ceG ceE ceA ceObs (1, profiledDensity 1 1 ceG ceE ceA ceObs 1)
      = 19 := by
    rw [profiledResidual_of_orthogonal 1 1 1 ceG ceE ceA ceObs ce_orth_one, hsum]
  have hphi2 : nlObjective 1 1 ceG ceE ceA ceObs (2, profiledDensity 1 1 ceG ceE ceA ceObs 2)
      = 19 := by
    rw [profiledResidual_of_orthogonal 1 1 2 ceG ceE ceA ceObs ce_orth_two, hsum]
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [ceE]; intro h; linarith
  · simp only [ceE]; intro h; linarith
  · simp only [ceE]; intro h; linarith
  · rw [hphi1, hphi2]
  · rw [hphi1]; norm_num


/-! ### Two-line metric neighborhood bound (Frontier 01, M4 tail — piece 2)

The trapping bound localizes the noisy minimizer to a `Φ_clean`-sublevel neighborhood of `T₀`; here
that is upgraded to an explicit **metric** neighborhood in the temperature itself. On a box, the
intensity-ratio coordinate is a bi-Lipschitz image of `T` (via `temp_exp_diff_lower`), so the
`Φ_clean` control transfers to a bound `(sensitivity)²·(T−T₀)² ≤ 6·(1+Rmax²)·∑ηₖ²`, i.e.
`|T−T₀| ≤ C·√(∑ηₖ²)` with `C` an explicit box constant. -/

/-- The two-line intensity-ratio difference is a scaled `Real.exp` difference. -/
lemma two_ratio_diff {kB Fcal T T0 : ℝ} {g E A : Fin 2 → ℝ}
    (hg : ∀ k, 0 < g k) (hFcal : 0 < Fcal) (hA : ∀ k, 0 < A k) :
    lineIntensity kB T 1 Fcal g E A 1 / lineIntensity kB T 1 Fcal g E A 0
      - lineIntensity kB T0 1 Fcal g E A 1 / lineIntensity kB T0 1 Fcal g E A 0
    = (g 1 * A 1) / (g 0 * A 0)
        * (Real.exp ((E 0 - E 1) / (kB * T)) - Real.exp ((E 0 - E 1) / (kB * T0))) := by
  rw [lineIntensity_ratio_closed_form (T := T) hg one_pos hFcal hA 0 1,
      lineIntensity_ratio_closed_form (T := T0) hg one_pos hFcal hA 0 1]
  ring

/-- On-manifold, the two-line profiled residual in the intensity-ratio coordinate. -/
lemma clean_residual_ratio {kB Fcal T0 N0 T : ℝ} {g E A obs : Fin 2 → ℝ}
    (hg : ∀ k, 0 < g k) (hFcal : 0 < Fcal) (hA : ∀ k, 0 < A k)
    (hobs : ∀ k, obs k = lineIntensity kB T0 N0 Fcal g E A k) :
    nlObjective kB Fcal g E A obs (T, profiledDensity kB Fcal g E A obs T)
      = N0 ^ 2 * (lineIntensity kB T0 1 Fcal g E A 0) ^ 2
        * (lineIntensity kB T 1 Fcal g E A 1 / lineIntensity kB T 1 Fcal g E A 0
           - lineIntensity kB T0 1 Fcal g E A 1 / lineIntensity kB T0 1 Fcal g E A 0) ^ 2
        / (1 + (lineIntensity kB T 1 Fcal g E A 1 / lineIntensity kB T 1 Fcal g E A 0) ^ 2) := by
  have hc0T : 0 < lineIntensity kB T 1 Fcal g E A 0 := lineIntensity_pos hg one_pos hFcal hA 0
  have hc1T : 0 < lineIntensity kB T 1 Fcal g E A 1 := lineIntensity_pos hg one_pos hFcal hA 1
  have hc0T0 : 0 < lineIntensity kB T0 1 Fcal g E A 0 := lineIntensity_pos hg one_pos hFcal hA 0
  have _hc1T0 : 0 < lineIntensity kB T0 1 Fcal g E A 1 := lineIntensity_pos hg one_pos hFcal hA 1
  have hc : (0 : ℝ) < (lineIntensity kB T 1 Fcal g E A 0) ^ 2
      + (lineIntensity kB T 1 Fcal g E A 1) ^ 2 := add_pos (pow_pos hc0T 2) (pow_pos hc1T 2)
  rw [profiledResidual_two_closed_form kB Fcal T g E A obs hc,
      hobs 0, hobs 1, lineIntensity_linear_in_N kB T0 N0 Fcal g E A 0,
      lineIntensity_linear_in_N kB T0 N0 Fcal g E A 1]
  field_simp
  ring

theorem profiledResidual_metric_bound {kB Fcal Tmin Tmax T0 N0 T : ℝ} {g E A obs η : Fin 2 → ℝ}
    (hg : ∀ k, 0 < g k) (hFcal : 0 < Fcal) (hA : ∀ k, 0 < A k)
    (hN0 : 0 < N0) (hTmin : 0 < Tmin)
    (hT : Tmin ≤ T) (hTM : T ≤ Tmax) (hT0 : Tmin ≤ T0) (hT0M : T0 ≤ Tmax)
    (hobs : ∀ k, obs k = lineIntensity kB T0 N0 Fcal g E A k + η k)
    (hle : nlObjective kB Fcal g E A obs (T, profiledDensity kB Fcal g E A obs T)
         ≤ nlObjective kB Fcal g E A obs (T0, profiledDensity kB Fcal g E A obs T0)) :
    (N0 * lineIntensity kB T0 1 Fcal g E A 0 * ((g 1 * A 1) / (g 0 * A 0))
      * (Real.exp (-(|(E 0 - E 1) / kB| / Tmin)) * (|(E 0 - E 1) / kB| / Tmax ^ 2))) ^ 2
        * (T - T0) ^ 2
      ≤ 6 * (1 + ((g 1 * A 1) / (g 0 * A 0) * Real.exp (|(E 0 - E 1) / kB| / Tmin)) ^ 2)
          * ∑ k, (η k) ^ 2 := by
  set c0T0 := lineIntensity kB T0 1 Fcal g E A 0 with hc0
  set rT := lineIntensity kB T 1 Fcal g E A 1 / lineIntensity kB T 1 Fcal g E A 0 with hrT
  set rT0 := lineIntensity kB T0 1 Fcal g E A 1 / lineIntensity kB T0 1 Fcal g E A 0 with hrT0
  set K := (g 1 * A 1) / (g 0 * A 0) with hK
  set cA := Real.exp (-(|(E 0 - E 1) / kB| / Tmin)) * (|(E 0 - E 1) / kB| / Tmax ^ 2) with hcA
  set Rmax := K * Real.exp (|(E 0 - E 1) / kB| / Tmin) with hRmax
  set n := ∑ k, (η k) ^ 2 with hn
  have hc0pos : 0 < c0T0 := lineIntensity_pos hg one_pos hFcal hA 0
  have hc0T : 0 < lineIntensity kB T 1 Fcal g E A 0 := lineIntensity_pos hg one_pos hFcal hA 0
  have hc1T : 0 < lineIntensity kB T 1 Fcal g E A 1 := lineIntensity_pos hg one_pos hFcal hA 1
  have hKpos : 0 < K := div_pos (mul_pos (hg 1) (hA 1)) (mul_pos (hg 0) (hA 0))
  have hcAnn : 0 ≤ cA := by rw [hcA]; positivity
  have hrTnn : 0 ≤ rT := by rw [hrT]; exact le_of_lt (div_pos hc1T hc0T)
  have hspos : (0:ℝ) < 1 + rT ^ 2 := by positivity
  have hnnn : 0 ≤ n := Finset.sum_nonneg (fun k _ => sq_nonneg _)
  have hcT : 0 < ∑ k, (lineIntensity kB T 1 Fcal g E A k) ^ 2 :=
    profiledDensity_denom_pos hg hFcal hA
  have hc0d : 0 < ∑ k, (lineIntensity kB T0 1 Fcal g E A k) ^ 2 :=
    profiledDensity_denom_pos hg hFcal hA
  have htrap := profiledResidual_minimizer_trapped hc0d hcT hobs hle
  have hform := clean_residual_ratio (kB := kB) (Fcal := Fcal) (T0 := T0) (N0 := N0) (T := T)
    (g := g) (E := E) (A := A) (obs := fun k => lineIntensity kB T0 N0 Fcal g E A k)
    hg hFcal hA (fun _ => rfl)
  rw [hform, div_le_iff₀ hspos] at htrap
  have hrd := two_ratio_diff (kB := kB) (Fcal := Fcal) (T := T) (T0 := T0)
    (g := g) (E := E) (A := A) hg hFcal hA
  have hL1 := temp_exp_diff_lower (D := (E 0 - E 1) / kB) (Tmin := Tmin) (Tmax := Tmax)
    (T := T) (T0 := T0) hTmin hT hTM hT0 hT0M
  simp only [div_div] at hL1
  set eD := Real.exp ((E 0 - E 1) / (kB * T)) - Real.exp ((E 0 - E 1) / (kB * T0)) with heD
  have he2 : cA ^ 2 * (T - T0) ^ 2 ≤ eD ^ 2 := by
    have hnn : 0 ≤ cA * |T - T0| := mul_nonneg hcAnn (abs_nonneg _)
    have hsq := mul_self_le_mul_self hnn hL1
    have e1 : cA * |T - T0| * (cA * |T - T0|) = cA ^ 2 * (T - T0) ^ 2 := by
      rw [← sq_abs (T - T0)]; ring
    have e2 : |eD| * |eD| = eD ^ 2 := by rw [← sq_abs eD]; ring
    rw [e1, e2] at hsq; exact hsq
  have hstep : N0 ^ 2 * c0T0 ^ 2 * K ^ 2 * cA ^ 2 * (T - T0) ^ 2
      ≤ N0 ^ 2 * c0T0 ^ 2 * (rT - rT0) ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_left he2
      (show (0:ℝ) ≤ N0 ^ 2 * c0T0 ^ 2 * K ^ 2 by positivity)
    calc N0 ^ 2 * c0T0 ^ 2 * K ^ 2 * cA ^ 2 * (T - T0) ^ 2
        = N0 ^ 2 * c0T0 ^ 2 * K ^ 2 * (cA ^ 2 * (T - T0) ^ 2) := by ring
      _ ≤ N0 ^ 2 * c0T0 ^ 2 * K ^ 2 * eD ^ 2 := hmul
      _ = N0 ^ 2 * c0T0 ^ 2 * (K * eD) ^ 2 := by ring
      _ = N0 ^ 2 * c0T0 ^ 2 * (rT - rT0) ^ 2 := by rw [← hrd]
  -- r(T) bounded on the box:  rT ≤ Rmax
  have hrbound : rT ≤ Rmax := by
    have hrTeq : rT = K * Real.exp ((E 0 - E 1) / (kB * T)) := by
      rw [hrT, hK, lineIntensity_ratio_closed_form hg one_pos hFcal hA 0 1]
    have harg : (E 0 - E 1) / (kB * T) ≤ |(E 0 - E 1) / kB| / Tmin := by
      rw [← div_div]
      gcongr
      exact le_abs_self _
    rw [hrTeq, hRmax]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr harg) hKpos.le
  have hRmaxnn : 0 ≤ Rmax := by rw [hRmax]; positivity
  have hr2 : rT ^ 2 ≤ Rmax ^ 2 := by
    apply sq_le_sq'
    · linarith [hrTnn]
    · exact hrbound
  calc (N0 * c0T0 * K * cA) ^ 2 * (T - T0) ^ 2
      = N0 ^ 2 * c0T0 ^ 2 * K ^ 2 * cA ^ 2 * (T - T0) ^ 2 := by ring
    _ ≤ N0 ^ 2 * c0T0 ^ 2 * (rT - rT0) ^ 2 := hstep
    _ ≤ 6 * n * (1 + rT ^ 2) := htrap
    _ ≤ 6 * n * (1 + Rmax ^ 2) := by nlinarith [hnnn, hr2]
    _ = 6 * (1 + Rmax ^ 2) * n := by ring

/-- Non-vacuity: every hypothesis of `profiledResidual_metric_bound` is dischargeable at concrete
box data (`Tmin=1, Tmax=2, T0=T=1`, `E=![0,1]`, noise `η=![1,1]`). -/
example : True := by
  have _ := profiledResidual_metric_bound (kB := 1) (Fcal := 1) (Tmin := 1) (Tmax := 2)
    (T0 := 1) (N0 := 1) (T := 1) (g := ![1, 1]) (E := ![0, 1]) (A := ![1, 1]) (η := ![1, 1])
    (obs := fun k => lineIntensity 1 1 1 1 ![1, 1] ![0, 1] ![1, 1] k + (![1, 1] : Fin 2 → ℝ) k)
    (fun k => by fin_cases k <;> norm_num) one_pos (fun k => by fin_cases k <;> norm_num)
    one_pos one_pos le_rfl (by norm_num) le_rfl (by norm_num) (fun _ => rfl) le_rfl
  trivial

end CflibsFormal
