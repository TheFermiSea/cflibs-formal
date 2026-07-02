/-
Copyright (c) 2026 Brian Squires. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Squires
-/
import Mathlib
import CflibsFormal.ForwardMap

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
