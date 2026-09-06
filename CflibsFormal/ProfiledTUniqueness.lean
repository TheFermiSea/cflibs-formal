/-
Copyright (c) 2026 Brian Squires. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Squires
-/
import Mathlib
import CflibsFormal.Boltzmann
import CflibsFormal.ForwardMap
import CflibsFormal.NonlinearLeastSquares
import CflibsFormal.ProfiledUnimodality

/-!
# CF-LIBS formalization — `T`-uniqueness of the profiled fit, and the joint `(T, N)` corollary

`NonlinearLeastSquares.lean` proves existence of a joint `(T, N)` minimizer on a compact box and the
full variable-projection (VARPRO) reduction: the `N`-section is exactly quadratic, and
`profiledDensity` is its UNIQUE minimizer (`Nsection_minimizer_unique`), so the two-dimensional fit
is provably one-dimensional in `T`. `ProfiledUnimodality.lean` then proves, **for two lines**, that
the density-profiled objective is strictly unimodal on a temperature box around an apex `Tstar`, and
that `Tstar` strictly beats every other box temperature
(`profiledResidual_two_strictUnimodalOn`, `profiledResidual_two_Tstar_isStrictMin`).

This module does two things.

1. **States the uniqueness corollary that was implicit but never written down.** Strict unimodality
   on the box already forces a unique profiled-`T` minimizer; combining it with the `N`-section
   strict-convexity fact `nlObjective_Nsection_lt_of_ne` upgrades that to *joint* uniqueness: on
   `Icc Tmin Tmax ×ˢ univ` the pair `(Tstar, N̂(Tstar))` is the **strict** global minimizer of
   `nlObjective`, and any minimizer over that region equals it
   (`joint_two_box_isStrictMin`, `joint_two_box_minimizer_unique`). This is a corollary of landed
   work — bookkeeping over `ProfiledUnimodality` plus VARPRO, **not** new mathematics.

2. **Widens the class of line configurations for which strict unimodality actually holds** —
   from two lines to **arbitrarily many lines whose upper-level energies take exactly two values**
   (`Ea` on a line subset `S`, `Eb` off it; both groups nonempty, `Ea ≠ Eb`). This is the
   multi-line multiplet configuration: several transitions from each of two upper levels. The
   mechanism is a genuine reduction, not a repackaging of the `Fin 2` proof: the unit-density
   intensity vector `c(T)` lies, for every `T`, in the **fixed two-dimensional coordinate plane**
   spanned by the two group-weight vectors, which are orthogonal because their supports are
   disjoint. Profiling `N` out leaves the Rayleigh residual
   `Φ(T) = ‖obs‖² − ⟨c(T), obs⟩²/‖c(T)‖²`, and the exact identity `profiledResidual_twoLevel_eq`
   splits it as
   `Φ(T) = K + (S_B·P·t(T) − S_A·Q)² / (S_A·S_B·(S_A + S_B·t(T)²))`
   with `S_A = ∑_{k∈S} (A_k g_k)²`, `S_B = ∑_{k∉S} (A_k g_k)²`, `P = ∑_{k∈S} A_k g_k obs_k`,
   `Q = ∑_{k∉S} A_k g_k obs_k`, `t(T) = exp((E_a − E_b)/(k_B T))`, and a **`T`-independent** offset
   `K = ‖obs‖² − P²/S_A − Q²/S_B` (the squared norm of the part of `obs` orthogonal to the plane,
   hence nonnegative — a true remark that is **not** formalized here; only `T`-independence is
   proved, and `T`-independence is all the shape argument uses). Since `t` is
   strictly monotone in `T` and the displayed quotient is strictly unimodal in `t`, `Φ` is strictly
   unimodal in `T`. The two-line configuration is the instance `S = {0}` (with the apex condition
   written in group-aggregated form rather than the `c₀`/`c₁` form of `ProfiledUnimodality`; the
   two are equivalent for two lines, but that translation is not itself formalized). Here `m` is
   arbitrary, and the
   orthogonal offset `K` — identically zero for two lines, and in general nonzero once `m ≥ 3` —
   is carried through as a `T`-independent constant. Its VALUE is never computed; what is proved is
   that it cannot affect the shape.

## Literature and scope

Scope tags: **PURE-MATH** for the algebra (`profiledResidual_eq_rayleigh`, `twoLevelResidual_diff`,
`profiledResidual_twoLevel_eq`), **REDUCED** for everything carrying the fit reading. Citation:
Ciucci et al. (1999) for the Boltzmann-ratio temperature engine; Tognoni et al. (2010) for the
CF-LIBS state of the art. Variable projection is due to Golub & Pereyra (1973) — recorded in this
repository's citation whitelist as UNVERIFIED (prose-only), so it is named for orientation, not
relied on. Non-vacuity is witnessed on an explicit **three-line** configuration
`E = (0, 1, 1)` (one line at the lower level, two at the upper), which the two-line theorems of
`ProfiledUnimodality.lean` cannot reach.

## Honest limitations

* The widened class is **two distinct upper-level energies with arbitrarily many lines**, NOT
  arbitrary `m`-line configurations. Three or more *distinct* energies are genuinely outside this
  argument, and `NonlinearLeastSquares.profiledResidual_not_injective_m3` exhibits an explicit
  three-distinct-energy configuration where the profiled residual takes the same value at two
  temperatures. That frontier stays open.
* The apex hypothesis `hstar` **assumes** a temperature `Tstar` inside the box at which the
  group-aggregated observed ratio `(Q/S_B)/(P/S_A)` equals the Boltzmann ratio
  `exp(−E_b/k_BT)/exp(−E_a/k_BT)`. Nothing here proves such a `Tstar` exists for a given noisy
  `obs`; existence is a solvability-of-the-noisy-ratio condition (equivalently, a bound on how far
  noise may move the minimizer), and the theorems are conditional on it. On-manifold the apex is
  the true temperature `T₀` and the hypothesis is discharged
  (`profiledResidual_twoLevel_strictUnimodal_onManifold`).
* `hP : 0 < P` is an explicit hypothesis. It holds whenever the measured spectrum is nonnegative
  and not identically zero on the group-`S` lines; it is not derived here.
* The joint statements minimize over `Icc Tmin Tmax ×ˢ (univ : Set ℝ)` — the temperature is boxed,
  the density is unconstrained. For a bounded density box the same conclusion needs `N̂(Tstar)` to
  lie inside it; that side condition is not formalized.
* The forward map is the **single-species, optically-thin** `lineIntensity`: one number density
  `N`, one partition function `U(T)`, no self-absorption and no ionization balance. The
  `Fcal`/`U(T)` cancellation that makes the profiled residual calibration-free is a consequence of
  *all* lines sharing one such scalar prefactor; it does **not** carry over to a multi-species or
  multi-ionization-stage fit, and nothing here addresses the joint `(T, n_e, composition)` problem
  or optical depth.
* Nothing here is a solver-convergence theorem. "A descent method cannot stall away from `Tstar`"
  is the intended reading of strict unimodality, not a formalized claim; no derivative, gradient,
  or iteration is defined in this module.
-/

namespace CflibsFormal

open Finset Real
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### The density-profiled residual in Rayleigh-quotient form -/

omit [DecidableEq ι] in
/-- **VARPRO residual in Rayleigh form (PURE-MATH).** Evaluating the joint objective at the
variable-projection density `N̂(T)` gives, for *any* finite line set and *any* observation,
`nlObjective … (T, N̂(T)) = ‖obs‖² − ⟨c(T), obs⟩² / ‖c(T)‖²`,
where `c_k(T) = lineIntensity kB T 1 Fcal g E A k` is the unit-density intensity vector. Pure
algebra: expand the `N`-section `∑ₖ (N·c_k − obs_k)²` as `N²‖c‖² − 2N⟨c,obs⟩ + ‖obs‖²` and
substitute `N = ⟨c,obs⟩/‖c‖²`. This is the general-`m` sibling of the `Fin 2`-only
`profiledResidual_two_closed_form`, and the form in which the residual is manifestly **invariant
under rescaling `c`** — which is why the calibration `Fcal` and the whole partition function `U(T)`
drop out downstream. -/
theorem profiledResidual_eq_rayleigh {kB Fcal T : ℝ} {g E A obs : ι → ℝ}
    (hc : 0 < ∑ k, (lineIntensity kB T 1 Fcal g E A k) ^ 2) :
    nlObjective kB Fcal g E A obs (T, profiledDensity kB Fcal g E A obs T)
      = (∑ k, (obs k) ^ 2)
        - (∑ k, lineIntensity kB T 1 Fcal g E A k * obs k) ^ 2
          / ∑ k, (lineIntensity kB T 1 Fcal g E A k) ^ 2 := by
  have hne : (∑ k, (lineIntensity kB T 1 Fcal g E A k) ^ 2) ≠ 0 := hc.ne'
  have key : ∀ M : ℝ, ∑ k, (M * lineIntensity kB T 1 Fcal g E A k - obs k) ^ 2
      = M ^ 2 * (∑ k, (lineIntensity kB T 1 Fcal g E A k) ^ 2)
        - 2 * M * (∑ k, lineIntensity kB T 1 Fcal g E A k * obs k)
        + ∑ k, (obs k) ^ 2 := by
    intro M
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [nlObjective_eq_sq_sum, key]
  simp only [profiledDensity]
  field_simp
  ring

/-! ### Pure algebra of the two-energy-group residual -/

/-- **Two-level profiled residual as a function of the Boltzmann ratio `t`.** With group energies
`S_A = ∑_{k∈S} (A_k g_k)²`, `S_B = ∑_{k∉S} (A_k g_k)²`, group projections `P = ∑_{k∈S} A_k g_k
obs_k`, `Q = ∑_{k∉S} A_k g_k obs_k`, and `t = exp((E_a − E_b)/(k_B T))`, this is the
`T`-dependent part of the density-profiled least-squares residual (`profiledResidual_twoLevel_eq`).
Its apex is `t* = S_A·Q/(S_B·P)`, where the numerator vanishes. -/
noncomputable def twoLevelResidual (SA SB P Q t : ℝ) : ℝ :=
  (SB * P * t - SA * Q) ^ 2 / (SA * SB * (SA + SB * t ^ 2))

/-- **Algebraic two-point difference identity for the two-level residual (PURE-MATH, pure `ring`).**
With `u_i := S_B·P·t_i − S_A·Q` (which vanishes at the apex) and `w_i := P + Q·t_i`,
`Ψ(t₂) − Ψ(t₁) = (t₂ − t₁)·(u₁w₂ + u₂w₁) / ((S_A + S_B t₁²)(S_A + S_B t₂²))`.
The `S_A·S_B` normalization cancels exactly. This is the discrete "derivative" that drives the
whole unimodality argument: the sign of the difference is `sign(t₂−t₁)·sign(u₁w₂+u₂w₁)`, so no
calculus, Hessian, or curvature computation is needed anywhere below. It generalizes
`NonlinearLeastSquares.profiledRatioResidual_diff` (recovered at `S_A = S_B = 1`). -/
theorem twoLevelResidual_diff {SA SB : ℝ} (hSA : 0 < SA) (hSB : 0 < SB) (P Q t1 t2 : ℝ) :
    twoLevelResidual SA SB P Q t2 - twoLevelResidual SA SB P Q t1
      = (t2 - t1)
          * ((SB * P * t1 - SA * Q) * (P + Q * t2) + (SB * P * t2 - SA * Q) * (P + Q * t1))
        / ((SA + SB * t1 ^ 2) * (SA + SB * t2 ^ 2)) := by
  have hd1 : (0 : ℝ) < SA + SB * t1 ^ 2 :=
    add_pos_of_pos_of_nonneg hSA (mul_nonneg hSB.le (sq_nonneg t1))
  have hd2 : (0 : ℝ) < SA + SB * t2 ^ 2 :=
    add_pos_of_pos_of_nonneg hSA (mul_nonneg hSB.le (sq_nonneg t2))
  simp only [twoLevelResidual]
  field_simp
  ring

/-- Below the apex (`u < 0`), with the antipode avoided (`w = P + Q·t > 0`), the two-level residual
strictly decreases as `t` increases. Sign reading of `twoLevelResidual_diff`. -/
private lemma twoLevel_lt_below {SA SB P Q t1 t2 : ℝ} (hSA : 0 < SA) (hSB : 0 < SB)
    (hw1 : 0 < P + Q * t1) (hw2 : 0 < P + Q * t2)
    (hu1 : SB * P * t1 - SA * Q < 0) (hu2 : SB * P * t2 - SA * Q ≤ 0) (hlt : t1 < t2) :
    twoLevelResidual SA SB P Q t2 < twoLevelResidual SA SB P Q t1 := by
  have hd1 : (0 : ℝ) < SA + SB * t1 ^ 2 :=
    add_pos_of_pos_of_nonneg hSA (mul_nonneg hSB.le (sq_nonneg t1))
  have hd2 : (0 : ℝ) < SA + SB * t2 ^ 2 :=
    add_pos_of_pos_of_nonneg hSA (mul_nonneg hSB.le (sq_nonneg t2))
  have hnum : (SB * P * t1 - SA * Q) * (P + Q * t2)
      + (SB * P * t2 - SA * Q) * (P + Q * t1) < 0 := by
    have a1 : (SB * P * t1 - SA * Q) * (P + Q * t2) < 0 := mul_neg_of_neg_of_pos hu1 hw2
    have a2 : (SB * P * t2 - SA * Q) * (P + Q * t1) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hu2 hw1.le
    linarith
  have hdiff : twoLevelResidual SA SB P Q t2 - twoLevelResidual SA SB P Q t1 < 0 := by
    rw [twoLevelResidual_diff hSA hSB]
    exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (sub_pos.mpr hlt) hnum) (mul_pos hd1 hd2)
  linarith

/-- Above the apex (`u > 0`), with the antipode avoided, the two-level residual strictly increases
as `t` increases. Mirror of `twoLevel_lt_below`. -/
private lemma twoLevel_lt_above {SA SB P Q t1 t2 : ℝ} (hSA : 0 < SA) (hSB : 0 < SB)
    (hw1 : 0 < P + Q * t1) (hw2 : 0 < P + Q * t2)
    (hu1 : 0 ≤ SB * P * t1 - SA * Q) (hu2 : 0 < SB * P * t2 - SA * Q) (hlt : t1 < t2) :
    twoLevelResidual SA SB P Q t1 < twoLevelResidual SA SB P Q t2 := by
  have hd1 : (0 : ℝ) < SA + SB * t1 ^ 2 :=
    add_pos_of_pos_of_nonneg hSA (mul_nonneg hSB.le (sq_nonneg t1))
  have hd2 : (0 : ℝ) < SA + SB * t2 ^ 2 :=
    add_pos_of_pos_of_nonneg hSA (mul_nonneg hSB.le (sq_nonneg t2))
  have hnum : 0 < (SB * P * t1 - SA * Q) * (P + Q * t2)
      + (SB * P * t2 - SA * Q) * (P + Q * t1) := by
    have a1 : 0 ≤ (SB * P * t1 - SA * Q) * (P + Q * t2) := mul_nonneg hu1 hw2.le
    have a2 : 0 < (SB * P * t2 - SA * Q) * (P + Q * t1) := mul_pos hu2 hw1
    linarith
  have hdiff : 0 < twoLevelResidual SA SB P Q t2 - twoLevelResidual SA SB P Q t1 := by
    rw [twoLevelResidual_diff hSA hSB]
    exact div_pos (mul_pos (sub_pos.mpr hlt) hnum) (mul_pos hd1 hd2)
  linarith

/-! ### Strict monotonicity of the Boltzmann ratio in the temperature -/

/-- `exp((E_a − E_b)/(k_B T))` is strictly increasing in `T > 0` when `E_a < E_b`. -/
private lemma boltzRatio_lt_of_lt {kB Ea Eb Ta Tb : ℝ} (hkB : 0 < kB)
    (hE : Ea - Eb < 0) (hTa : 0 < Ta) (hab : Ta < Tb) :
    Real.exp ((Ea - Eb) / (kB * Ta)) < Real.exp ((Ea - Eb) / (kB * Tb)) := by
  have hTb : 0 < Tb := hTa.trans hab
  refine Real.exp_lt_exp.mpr ?_
  rw [div_lt_div_iff₀ (mul_pos hkB hTa) (mul_pos hkB hTb)]
  nlinarith [mul_pos (mul_pos hkB (sub_pos.mpr hab)) (neg_pos.mpr hE)]

/-- `exp((E_a − E_b)/(k_B T))` is strictly decreasing in `T > 0` when `E_b < E_a`. -/
private lemma boltzRatio_gt_of_lt {kB Ea Eb Ta Tb : ℝ} (hkB : 0 < kB)
    (hE : 0 < Ea - Eb) (hTa : 0 < Ta) (hab : Ta < Tb) :
    Real.exp ((Ea - Eb) / (kB * Tb)) < Real.exp ((Ea - Eb) / (kB * Ta)) := by
  have hTb : 0 < Tb := hTa.trans hab
  refine Real.exp_lt_exp.mpr ?_
  rw [div_lt_div_iff₀ (mul_pos hkB hTb) (mul_pos hkB hTa)]
  nlinarith [mul_pos (mul_pos hkB (sub_pos.mpr hab)) hE]

/-- `exp(−E_b/(k_BT)) = exp(−E_a/(k_BT))·exp((E_a − E_b)/(k_BT))`: the group-`B` Boltzmann factor
factored through the group-`A` one and the ratio coordinate. -/
private lemma boltzmannFactor_factor (kB T Ea Eb : ℝ) :
    boltzmannFactor kB T Eb
      = boltzmannFactor kB T Ea * Real.exp ((Ea - Eb) / (kB * T)) := by
  simp only [boltzmannFactor, ← Real.exp_add]
  congr 1
  ring

/-! ### The two-energy-group reduction of the profiled residual -/

omit [DecidableEq ι] in
/-- Unit-density intensity of a group-`A` line:
`c_k(T) = (Fcal/U(T))·exp(−E_a/(k_BT))·(A_k g_k)`. -/
private lemma twoLevel_lineIntensity_S {kB T Fcal Ea : ℝ} {g E A : ι → ℝ} {S : Finset ι}
    (hSmem : ∀ k ∈ S, E k = Ea) {k : ι} (hk : k ∈ S) :
    lineIntensity kB T 1 Fcal g E A k
      = Fcal / partitionFunction kB T g E * boltzmannFactor kB T Ea * (A k * g k) := by
  simp only [lineIntensity, population]
  rw [hSmem k hk]
  ring

omit [DecidableEq ι] in
/-- Unit-density intensity of a group-`B` line:
`c_k(T) = (Fcal/U(T))·exp(−E_b/(k_BT))·(A_k g_k)`. -/
private lemma twoLevel_lineIntensity_C {kB T Fcal Eb : ℝ} {g E A : ι → ℝ} {S : Finset ι}
    (hScom : ∀ k ∉ S, E k = Eb) {k : ι} (hk : k ∉ S) :
    lineIntensity kB T 1 Fcal g E A k
      = Fcal / partitionFunction kB T g E * boltzmannFactor kB T Eb * (A k * g k) := by
  simp only [lineIntensity, population]
  rw [hScom k hk]
  ring

omit [Fintype ι] [DecidableEq ι] in
/-- Positivity of a group energy `∑_{k ∈ S} (A_k g_k)²` from one member of the group. -/
private lemma group_energy_pos {S : Finset ι} {g A : ι → ℝ}
    (hg : ∀ k, 0 < g k) (hA : ∀ k, 0 < A k) {i : ι} (hi : i ∈ S) :
    0 < ∑ k ∈ S, (A k * g k) ^ 2 :=
  Finset.sum_pos' (fun _ _ => sq_nonneg _) ⟨i, hi, pow_pos (mul_pos (hA i) (hg i)) 2⟩

/-- **Two-energy-group reduction of the density-profiled residual (PURE-MATH).** Let the upper-level
energies take exactly two values — `E k = E_a` for `k ∈ S` and `E k = E_b` for `k ∉ S`, with both
groups carrying positive energy `S_A, S_B > 0`. Then for **every** temperature and **every**
observation vector,
`nlObjective … (T, N̂(T)) = K + twoLevelResidual S_A S_B P Q (exp((E_a − E_b)/(k_B T)))`,
with the `T`-independent offset `K = ‖obs‖² − P²/S_A − Q²/S_B` (the squared norm of the component of
`obs` orthogonal to the fixed two-dimensional group plane).

Mechanism: `c(T) = (Fcal/U(T))·exp(−E_a/(k_BT))·(v_A + t(T)·v_B)` where `v_A, v_B` are the fixed
group-weight vectors, orthogonal because their supports are disjoint. The Rayleigh residual
(`profiledResidual_eq_rayleigh`) is invariant under rescaling `c`, so calibration and partition
function cancel identically, and the Pythagorean split of `obs` along `v_A`, `v_B`, and their
orthogonal complement produces the displayed identity. No positivity of `obs`, no on-manifold
hypothesis, no bound on `T` is used. -/
theorem profiledResidual_twoLevel_eq [Nonempty ι] {kB Fcal T Ea Eb : ℝ}
    {g E A obs : ι → ℝ} {S : Finset ι}
    (hg : ∀ k, 0 < g k) (hFcal : 0 < Fcal)
    (hSmem : ∀ k ∈ S, E k = Ea) (hScom : ∀ k ∉ S, E k = Eb)
    (hSA : 0 < ∑ k ∈ S, (A k * g k) ^ 2) (hSB : 0 < ∑ k ∈ univ \ S, (A k * g k) ^ 2) :
    nlObjective kB Fcal g E A obs (T, profiledDensity kB Fcal g E A obs T)
      = ((∑ k, (obs k) ^ 2)
          - (∑ k ∈ S, A k * g k * obs k) ^ 2 / (∑ k ∈ S, (A k * g k) ^ 2)
          - (∑ k ∈ univ \ S, A k * g k * obs k) ^ 2 / (∑ k ∈ univ \ S, (A k * g k) ^ 2))
        + twoLevelResidual (∑ k ∈ S, (A k * g k) ^ 2) (∑ k ∈ univ \ S, (A k * g k) ^ 2)
            (∑ k ∈ S, A k * g k * obs k) (∑ k ∈ univ \ S, A k * g k * obs k)
            (Real.exp ((Ea - Eb) / (kB * T))) := by
  have hUpos : (0 : ℝ) < partitionFunction kB T g E := partitionFunction_pos hg
  have hspos : (0 : ℝ) < Fcal / partitionFunction kB T g E * boltzmannFactor kB T Ea :=
    mul_pos (div_pos hFcal hUpos) (boltzmannFactor_pos _ _ _)
  have hptS : ∀ k ∈ S, lineIntensity kB T 1 Fcal g E A k
      = Fcal / partitionFunction kB T g E * boltzmannFactor kB T Ea * (A k * g k) :=
    fun k hk => twoLevel_lineIntensity_S hSmem hk
  have hptC : ∀ k ∈ univ \ S, lineIntensity kB T 1 Fcal g E A k
      = Fcal / partitionFunction kB T g E * boltzmannFactor kB T Ea
        * (Real.exp ((Ea - Eb) / (kB * T)) * (A k * g k)) := by
    intro k hk
    rw [twoLevel_lineIntensity_C hScom (Finset.mem_sdiff.mp hk).2, boltzmannFactor_factor]
    ring
  have hnumS : ∑ k ∈ S, lineIntensity kB T 1 Fcal g E A k * obs k
      = Fcal / partitionFunction kB T g E * boltzmannFactor kB T Ea
        * ∑ k ∈ S, A k * g k * obs k := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k hk => by rw [hptS k hk]; ring
  have hnumC : ∑ k ∈ univ \ S, lineIntensity kB T 1 Fcal g E A k * obs k
      = Fcal / partitionFunction kB T g E * boltzmannFactor kB T Ea
        * Real.exp ((Ea - Eb) / (kB * T)) * ∑ k ∈ univ \ S, A k * g k * obs k := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k hk => by rw [hptC k hk]; ring
  have hdenS : ∑ k ∈ S, (lineIntensity kB T 1 Fcal g E A k) ^ 2
      = (Fcal / partitionFunction kB T g E * boltzmannFactor kB T Ea) ^ 2
        * ∑ k ∈ S, (A k * g k) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k hk => by rw [hptS k hk]; ring
  have hdenC : ∑ k ∈ univ \ S, (lineIntensity kB T 1 Fcal g E A k) ^ 2
      = (Fcal / partitionFunction kB T g E * boltzmannFactor kB T Ea) ^ 2
        * (Real.exp ((Ea - Eb) / (kB * T))) ^ 2 * ∑ k ∈ univ \ S, (A k * g k) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k hk => by rw [hptC k hk]; ring
  set s := Fcal / partitionFunction kB T g E * boltzmannFactor kB T Ea with hsdef
  set t := Real.exp ((Ea - Eb) / (kB * T)) with htdef
  set P := ∑ k ∈ S, A k * g k * obs k with hPdef
  set Q := ∑ k ∈ univ \ S, A k * g k * obs k with hQdef
  set SA := ∑ k ∈ S, (A k * g k) ^ 2 with hSAdef
  set SB := ∑ k ∈ univ \ S, (A k * g k) ^ 2 with hSBdef
  have hnum : ∑ k, lineIntensity kB T 1 Fcal g E A k * obs k = s * (P + t * Q) := by
    rw [← Finset.sum_sdiff (Finset.subset_univ S), hnumC, hnumS]; ring
  have hden : ∑ k, (lineIntensity kB T 1 Fcal g E A k) ^ 2 = s ^ 2 * (SA + SB * t ^ 2) := by
    rw [← Finset.sum_sdiff (Finset.subset_univ S), hdenC, hdenS]; ring
  have hDpos : (0 : ℝ) < SA + SB * t ^ 2 :=
    add_pos_of_pos_of_nonneg hSA (mul_nonneg hSB.le (sq_nonneg t))
  have hcpos : (0 : ℝ) < ∑ k, (lineIntensity kB T 1 Fcal g E A k) ^ 2 := by
    rw [hden]; exact mul_pos (pow_pos hspos 2) hDpos
  rw [profiledResidual_eq_rayleigh hcpos, hnum, hden]
  simp only [twoLevelResidual]
  have h1 : s ≠ 0 := hspos.ne'
  have h2 : SA ≠ 0 := hSA.ne'
  have h3 : SB ≠ 0 := hSB.ne'
  have h4 : SA + SB * t ^ 2 ≠ 0 := hDpos.ne'
  field_simp
  ring

/-! ### Strict unimodality for many lines at two upper-level energies -/

/-- **Strict unimodality of the profiled objective in `T`, `m` lines at two energies (REDUCED,
Ciucci 1999).** Let the upper-level energies take exactly two distinct values, `E k = E_a` on a
line subset `S` and `E k = E_b` off it, with at least one line in each group (`i ∈ S`, `j ∉ S`) and
`E_a ≠ E_b`. Let the group-`S` projection be positive, `P = ∑_{k∈S} A_k g_k obs_k > 0` (automatic
for a nonnegative, not-identically-zero spectrum on those lines). Let `Tstar ∈ [Tmin, Tmax]` with
`Tmin > 0` satisfy the **apex** condition
`S_B·P·exp(−E_b/(k_B Tstar)) = S_A·Q·exp(−E_a/(k_B Tstar))`,
i.e. the group-aggregated observed level ratio `(Q/S_B)/(P/S_A)` equals the Boltzmann ratio at
`Tstar`. Then the density-profiled objective `T ↦ nlObjective … (T, N̂(T))` is **strictly
decreasing** on `[Tmin, Tstar]` and **strictly increasing** on `[Tstar, Tmax]`.

This is a genuine widening of `ProfiledUnimodality.profiledResidual_two_strictUnimodalOn`: the
number of lines `m` is arbitrary, and the component of `obs` orthogonal to the two-dimensional
group plane — which can only exist once `m ≥ 3` — is carried through the argument as a
`T`-independent offset rather than assumed away. It is NOT a general `m`-line result: three or
more *distinct* energies are outside the argument. -/
theorem profiledResidual_twoLevel_strictUnimodalOn [Nonempty ι]
    {kB Fcal Tmin Tmax Tstar Ea Eb : ℝ} {g E A obs : ι → ℝ} {S : Finset ι}
    (hkB : 0 < kB) (hg : ∀ k, 0 < g k) (hFcal : 0 < Fcal) (hA : ∀ k, 0 < A k)
    (hSmem : ∀ k ∈ S, E k = Ea) (hScom : ∀ k ∉ S, E k = Eb) (hEne : Ea ≠ Eb)
    (i : ι) (hi : i ∈ S) (j : ι) (hj : j ∉ S)
    (hP : 0 < ∑ k ∈ S, A k * g k * obs k)
    (hTmin : 0 < Tmin) (hTsL : Tmin ≤ Tstar) (_hTsR : Tstar ≤ Tmax)
    (hstar : (∑ k ∈ univ \ S, (A k * g k) ^ 2) * (∑ k ∈ S, A k * g k * obs k)
          * boltzmannFactor kB Tstar Eb
        = (∑ k ∈ S, (A k * g k) ^ 2) * (∑ k ∈ univ \ S, A k * g k * obs k)
          * boltzmannFactor kB Tstar Ea) :
    StrictAntiOn
        (fun T => nlObjective kB Fcal g E A obs (T, profiledDensity kB Fcal g E A obs T))
        (Set.Icc Tmin Tstar)
      ∧ StrictMonoOn
        (fun T => nlObjective kB Fcal g E A obs (T, profiledDensity kB Fcal g E A obs T))
        (Set.Icc Tstar Tmax) := by
  have hSA : 0 < ∑ k ∈ S, (A k * g k) ^ 2 := group_energy_pos hg hA hi
  have hSB : 0 < ∑ k ∈ univ \ S, (A k * g k) ^ 2 :=
    group_energy_pos hg hA (Finset.mem_sdiff.mpr ⟨Finset.mem_univ j, hj⟩)
  have hTs0 : 0 < Tstar := lt_of_lt_of_le hTmin hTsL
  have hαs : (0 : ℝ) < boltzmannFactor kB Tstar Ea := boltzmannFactor_pos _ _ _
  have hβs : (0 : ℝ) < boltzmannFactor kB Tstar Eb := boltzmannFactor_pos _ _ _
  -- the apex condition forces the group-`B` projection to be positive too
  have hQ : 0 < ∑ k ∈ univ \ S, A k * g k * obs k := by
    have hlhs : 0 < (∑ k ∈ S, (A k * g k) ^ 2) * (∑ k ∈ univ \ S, A k * g k * obs k)
        * boltzmannFactor kB Tstar Ea := by
      rw [← hstar]; exact mul_pos (mul_pos hSB hP) hβs
    by_contra hcon
    rw [not_lt] at hcon
    nlinarith [mul_nonneg (mul_nonneg hSA.le (neg_nonneg.mpr hcon)) hαs.le]
  -- bridge to the two-level residual
  have hbr : ∀ T, nlObjective kB Fcal g E A obs (T, profiledDensity kB Fcal g E A obs T)
      = ((∑ k, (obs k) ^ 2)
          - (∑ k ∈ S, A k * g k * obs k) ^ 2 / (∑ k ∈ S, (A k * g k) ^ 2)
          - (∑ k ∈ univ \ S, A k * g k * obs k) ^ 2 / (∑ k ∈ univ \ S, (A k * g k) ^ 2))
        + twoLevelResidual (∑ k ∈ S, (A k * g k) ^ 2) (∑ k ∈ univ \ S, (A k * g k) ^ 2)
            (∑ k ∈ S, A k * g k * obs k) (∑ k ∈ univ \ S, A k * g k * obs k)
            (Real.exp ((Ea - Eb) / (kB * T))) :=
    fun T => profiledResidual_twoLevel_eq hg hFcal hSmem hScom hSA hSB
  -- the apex, transported into the ratio coordinate
  have hapex : (∑ k ∈ univ \ S, (A k * g k) ^ 2) * (∑ k ∈ S, A k * g k * obs k)
      * Real.exp ((Ea - Eb) / (kB * Tstar))
      = (∑ k ∈ S, (A k * g k) ^ 2) * (∑ k ∈ univ \ S, A k * g k * obs k) := by
    have hfac := boltzmannFactor_factor kB Tstar Ea Eb
    rw [hfac] at hstar
    have := mul_right_cancel₀ hαs.ne' (by linarith [hstar] :
      ((∑ k ∈ univ \ S, (A k * g k) ^ 2) * (∑ k ∈ S, A k * g k * obs k)
          * Real.exp ((Ea - Eb) / (kB * Tstar))) * boltzmannFactor kB Tstar Ea
        = ((∑ k ∈ S, (A k * g k) ^ 2) * (∑ k ∈ univ \ S, A k * g k * obs k))
          * boltzmannFactor kB Tstar Ea)
    exact this
  have husign : ∀ T, (∑ k ∈ univ \ S, (A k * g k) ^ 2) * (∑ k ∈ S, A k * g k * obs k)
      * Real.exp ((Ea - Eb) / (kB * T))
      - (∑ k ∈ S, (A k * g k) ^ 2) * (∑ k ∈ univ \ S, A k * g k * obs k)
      = ((∑ k ∈ univ \ S, (A k * g k) ^ 2) * (∑ k ∈ S, A k * g k * obs k))
        * (Real.exp ((Ea - Eb) / (kB * T)) - Real.exp ((Ea - Eb) / (kB * Tstar))) := by
    intro T; rw [← hapex]; ring
  have hSBP : 0 < (∑ k ∈ univ \ S, (A k * g k) ^ 2) * (∑ k ∈ S, A k * g k * obs k) :=
    mul_pos hSB hP
  have hw : ∀ T, 0 < (∑ k ∈ S, A k * g k * obs k)
      + (∑ k ∈ univ \ S, A k * g k * obs k) * Real.exp ((Ea - Eb) / (kB * T)) :=
    fun T => add_pos hP (mul_pos hQ (Real.exp_pos _))
  rcases lt_or_gt_of_ne (sub_ne_zero.mpr hEne) with hEneg | hEpos
  · -- `E_a < E_b`: the ratio coordinate is strictly increasing in `T`
    have mono : ∀ x y : ℝ, 0 < x → x < y →
        Real.exp ((Ea - Eb) / (kB * x)) < Real.exp ((Ea - Eb) / (kB * y)) :=
      fun x y hx hxy => boltzRatio_lt_of_lt hkB hEneg hx hxy
    have mono_le : ∀ x y : ℝ, 0 < x → x ≤ y →
        Real.exp ((Ea - Eb) / (kB * x)) ≤ Real.exp ((Ea - Eb) / (kB * y)) := by
      intro x y hx hxy
      rcases eq_or_lt_of_le hxy with h | h
      · exact le_of_eq (by rw [h])
      · exact le_of_lt (mono x y hx h)
    refine ⟨?_, ?_⟩
    · intro a ha b hb hab
      simp only [Set.mem_Icc] at ha hb
      have h0a : 0 < a := lt_of_lt_of_le hTmin ha.1
      have haS : a < Tstar := lt_of_lt_of_le hab hb.2
      have hua : (∑ k ∈ univ \ S, (A k * g k) ^ 2) * (∑ k ∈ S, A k * g k * obs k)
          * Real.exp ((Ea - Eb) / (kB * a))
          - (∑ k ∈ S, (A k * g k) ^ 2) * (∑ k ∈ univ \ S, A k * g k * obs k) < 0 := by
        rw [husign a]
        exact mul_neg_of_pos_of_neg hSBP (sub_neg.mpr (mono a Tstar h0a haS))
      have hub : (∑ k ∈ univ \ S, (A k * g k) ^ 2) * (∑ k ∈ S, A k * g k * obs k)
          * Real.exp ((Ea - Eb) / (kB * b))
          - (∑ k ∈ S, (A k * g k) ^ 2) * (∑ k ∈ univ \ S, A k * g k * obs k) ≤ 0 := by
        rw [husign b]
        exact mul_nonpos_of_nonneg_of_nonpos hSBP.le
          (sub_nonpos.mpr (mono_le b Tstar (lt_of_lt_of_le hTmin hb.1) hb.2))
      simp only [hbr]
      have := twoLevel_lt_below hSA hSB (hw a) (hw b) hua hub (mono a b h0a hab)
      linarith
    · intro a ha b hb hab
      simp only [Set.mem_Icc] at ha hb
      have h0a : 0 < a := lt_of_lt_of_le hTs0 ha.1
      have hSb : Tstar < b := lt_of_le_of_lt ha.1 hab
      have hua : 0 ≤ (∑ k ∈ univ \ S, (A k * g k) ^ 2) * (∑ k ∈ S, A k * g k * obs k)
          * Real.exp ((Ea - Eb) / (kB * a))
          - (∑ k ∈ S, (A k * g k) ^ 2) * (∑ k ∈ univ \ S, A k * g k * obs k) := by
        rw [husign a]
        exact mul_nonneg hSBP.le (sub_nonneg.mpr (mono_le Tstar a hTs0 ha.1))
      have hub : 0 < (∑ k ∈ univ \ S, (A k * g k) ^ 2) * (∑ k ∈ S, A k * g k * obs k)
          * Real.exp ((Ea - Eb) / (kB * b))
          - (∑ k ∈ S, (A k * g k) ^ 2) * (∑ k ∈ univ \ S, A k * g k * obs k) := by
        rw [husign b]
        exact mul_pos hSBP (sub_pos.mpr (mono Tstar b hTs0 hSb))
      simp only [hbr]
      have := twoLevel_lt_above hSA hSB (hw a) (hw b) hua hub (mono a b h0a hab)
      linarith
  · -- `E_b < E_a`: the ratio coordinate is strictly decreasing in `T`
    have anti : ∀ x y : ℝ, 0 < x → x < y →
        Real.exp ((Ea - Eb) / (kB * y)) < Real.exp ((Ea - Eb) / (kB * x)) :=
      fun x y hx hxy => boltzRatio_gt_of_lt hkB hEpos hx hxy
    have anti_le : ∀ x y : ℝ, 0 < x → x ≤ y →
        Real.exp ((Ea - Eb) / (kB * y)) ≤ Real.exp ((Ea - Eb) / (kB * x)) := by
      intro x y hx hxy
      rcases eq_or_lt_of_le hxy with h | h
      · exact le_of_eq (by rw [h])
      · exact le_of_lt (anti x y hx h)
    refine ⟨?_, ?_⟩
    · intro a ha b hb hab
      simp only [Set.mem_Icc] at ha hb
      have h0a : 0 < a := lt_of_lt_of_le hTmin ha.1
      have h0b : 0 < b := lt_of_lt_of_le hTmin hb.1
      have haS : a < Tstar := lt_of_lt_of_le hab hb.2
      have hub : 0 ≤ (∑ k ∈ univ \ S, (A k * g k) ^ 2) * (∑ k ∈ S, A k * g k * obs k)
          * Real.exp ((Ea - Eb) / (kB * b))
          - (∑ k ∈ S, (A k * g k) ^ 2) * (∑ k ∈ univ \ S, A k * g k * obs k) := by
        rw [husign b]
        exact mul_nonneg hSBP.le (sub_nonneg.mpr (anti_le b Tstar h0b hb.2))
      have hua : 0 < (∑ k ∈ univ \ S, (A k * g k) ^ 2) * (∑ k ∈ S, A k * g k * obs k)
          * Real.exp ((Ea - Eb) / (kB * a))
          - (∑ k ∈ S, (A k * g k) ^ 2) * (∑ k ∈ univ \ S, A k * g k * obs k) := by
        rw [husign a]
        exact mul_pos hSBP (sub_pos.mpr (anti a Tstar h0a haS))
      simp only [hbr]
      have := twoLevel_lt_above hSA hSB (hw b) (hw a) hub hua (anti a b h0a hab)
      linarith
    · intro a ha b hb hab
      simp only [Set.mem_Icc] at ha hb
      have h0a : 0 < a := lt_of_lt_of_le hTs0 ha.1
      have h0b : 0 < b := lt_of_lt_of_le hTs0 hb.1
      have hSb : Tstar < b := lt_of_le_of_lt ha.1 hab
      have hub : (∑ k ∈ univ \ S, (A k * g k) ^ 2) * (∑ k ∈ S, A k * g k * obs k)
          * Real.exp ((Ea - Eb) / (kB * b))
          - (∑ k ∈ S, (A k * g k) ^ 2) * (∑ k ∈ univ \ S, A k * g k * obs k) < 0 := by
        rw [husign b]
        exact mul_neg_of_pos_of_neg hSBP (sub_neg.mpr (anti Tstar b hTs0 hSb))
      have hua : (∑ k ∈ univ \ S, (A k * g k) ^ 2) * (∑ k ∈ S, A k * g k * obs k)
          * Real.exp ((Ea - Eb) / (kB * a))
          - (∑ k ∈ S, (A k * g k) ^ 2) * (∑ k ∈ univ \ S, A k * g k * obs k) ≤ 0 := by
        rw [husign a]
        exact mul_nonpos_of_nonneg_of_nonpos hSBP.le
          (sub_nonpos.mpr (anti_le Tstar a hTs0 ha.1))
      simp only [hbr]
      have := twoLevel_lt_below hSA hSB (hw b) (hw a) hub hua (anti a b h0a hab)
      linarith

/-- **`Tstar` is the strict profiled-`T` minimizer on the box (`m` lines, two energies; REDUCED,
Ciucci 1999).** Under the hypotheses of `profiledResidual_twoLevel_strictUnimodalOn`, every box
temperature other than the apex gives a strictly larger density-profiled residual. Hence the
profiled `T`-minimizer on `[Tmin, Tmax]` is **unique** and equals `Tstar`; there is no spurious
local minimum in the box. -/
theorem profiledResidual_twoLevel_Tstar_isStrictMin [Nonempty ι]
    {kB Fcal Tmin Tmax Tstar Ea Eb : ℝ} {g E A obs : ι → ℝ} {S : Finset ι}
    (hkB : 0 < kB) (hg : ∀ k, 0 < g k) (hFcal : 0 < Fcal) (hA : ∀ k, 0 < A k)
    (hSmem : ∀ k ∈ S, E k = Ea) (hScom : ∀ k ∉ S, E k = Eb) (hEne : Ea ≠ Eb)
    (i : ι) (hi : i ∈ S) (j : ι) (hj : j ∉ S)
    (hP : 0 < ∑ k ∈ S, A k * g k * obs k)
    (hTmin : 0 < Tmin) (hTsL : Tmin ≤ Tstar) (hTsR : Tstar ≤ Tmax)
    (hstar : (∑ k ∈ univ \ S, (A k * g k) ^ 2) * (∑ k ∈ S, A k * g k * obs k)
          * boltzmannFactor kB Tstar Eb
        = (∑ k ∈ S, (A k * g k) ^ 2) * (∑ k ∈ univ \ S, A k * g k * obs k)
          * boltzmannFactor kB Tstar Ea)
    {T : ℝ} (hT : T ∈ Set.Icc Tmin Tmax) (hne : T ≠ Tstar) :
    nlObjective kB Fcal g E A obs (Tstar, profiledDensity kB Fcal g E A obs Tstar)
      < nlObjective kB Fcal g E A obs (T, profiledDensity kB Fcal g E A obs T) := by
  obtain ⟨hanti, hmono⟩ := profiledResidual_twoLevel_strictUnimodalOn hkB hg hFcal hA hSmem hScom
    hEne i hi j hj hP hTmin hTsL hTsR hstar
  simp only [Set.mem_Icc] at hT
  rcases lt_or_gt_of_ne hne with h | h
  · exact hanti ⟨hT.1, le_of_lt h⟩ ⟨hTsL, le_refl _⟩ h
  · exact hmono ⟨le_refl _, hTsR⟩ ⟨le_of_lt h, hT.2⟩ h

/-! ### From profiled-`T` uniqueness to joint `(T, N)` uniqueness (VARPRO bookkeeping) -/

omit [DecidableEq ι] in
/-- Shared VARPRO step: a strict profiled-`T` minimum at `Tstar` plus strict convexity of the
`N`-section makes `(Tstar, N̂(Tstar))` a strict joint minimum over the temperature box crossed with
all densities. Case `T = Tstar` is `nlObjective_Nsection_lt_of_ne`; case `T ≠ Tstar` chains the
profiled strict inequality with `profiledDensity_isMinOn_Nsection`. -/
private lemma joint_strictMin_of_T_strictMin [Nonempty ι] {kB Fcal Tmin Tmax Tstar : ℝ}
    {g E A obs : ι → ℝ} (hg : ∀ k, 0 < g k) (hFcal : 0 < Fcal) (hA : ∀ k, 0 < A k)
    (hTs : ∀ T ∈ Set.Icc Tmin Tmax, T ≠ Tstar →
      nlObjective kB Fcal g E A obs (Tstar, profiledDensity kB Fcal g E A obs Tstar)
        < nlObjective kB Fcal g E A obs (T, profiledDensity kB Fcal g E A obs T))
    {p : ℝ × ℝ} (hp : p.1 ∈ Set.Icc Tmin Tmax)
    (hne : p ≠ (Tstar, profiledDensity kB Fcal g E A obs Tstar)) :
    nlObjective kB Fcal g E A obs (Tstar, profiledDensity kB Fcal g E A obs Tstar)
      < nlObjective kB Fcal g E A obs p := by
  obtain ⟨T, N⟩ := p
  have hcT : 0 < ∑ k, (lineIntensity kB T 1 Fcal g E A k) ^ 2 :=
    profiledDensity_denom_pos hg hFcal hA
  by_cases hTeq : T = Tstar
  · subst hTeq
    have hN : N ≠ profiledDensity kB Fcal g E A obs T := fun h => hne (by rw [h])
    exact nlObjective_Nsection_lt_of_ne kB Fcal T g E A obs hcT hN
  · have h1 := hTs T hp hTeq
    have h2 := profiledDensity_isMinOn_Nsection kB Fcal T g E A obs hcT N
    linarith

omit [DecidableEq ι] in
/-- Shared final step: a strict joint minimum at `(Tstar, N̂(Tstar))` makes every minimizer over
the region equal to it. -/
private lemma minimizer_eq_of_strictMin {kB Fcal Tmin Tmax Tstar : ℝ} {g E A obs : ι → ℝ}
    (hTsL : Tmin ≤ Tstar) (hTsR : Tstar ≤ Tmax)
    (hstrict : ∀ q : ℝ × ℝ, q.1 ∈ Set.Icc Tmin Tmax →
      q ≠ (Tstar, profiledDensity kB Fcal g E A obs Tstar) →
      nlObjective kB Fcal g E A obs (Tstar, profiledDensity kB Fcal g E A obs Tstar)
        < nlObjective kB Fcal g E A obs q)
    {p : ℝ × ℝ}
    (hmin : IsMinOn (nlObjective kB Fcal g E A obs)
      (Set.Icc Tmin Tmax ×ˢ (Set.univ : Set ℝ)) p)
    (hp : p ∈ Set.Icc Tmin Tmax ×ˢ (Set.univ : Set ℝ)) :
    p = (Tstar, profiledDensity kB Fcal g E A obs Tstar) := by
  by_contra hne
  have hpm : (Tstar, profiledDensity kB Fcal g E A obs Tstar)
      ∈ Set.Icc Tmin Tmax ×ˢ (Set.univ : Set ℝ) := ⟨⟨hTsL, hTsR⟩, Set.mem_univ _⟩
  have hle := isMinOn_iff.mp hmin _ hpm
  have hlt := hstrict p hp.1 hne
  linarith

/-- **Strict joint `(T, N)` minimum (`m` lines, two energies; REDUCED, Tognoni 2010).** Under the
hypotheses of `profiledResidual_twoLevel_strictUnimodalOn`, the pair `(Tstar, N̂(Tstar))` strictly
beats **every** other parameter pair whose temperature lies in the box — the density being
completely unconstrained. Two ingredients: strict unimodality pins the temperature, and the
`N`-section of `nlObjective` is a strictly convex quadratic whose unique minimizer is the profiled
density (`nlObjective_Nsection_lt_of_ne`). -/
theorem joint_twoLevel_box_isStrictMin [Nonempty ι]
    {kB Fcal Tmin Tmax Tstar Ea Eb : ℝ} {g E A obs : ι → ℝ} {S : Finset ι}
    (hkB : 0 < kB) (hg : ∀ k, 0 < g k) (hFcal : 0 < Fcal) (hA : ∀ k, 0 < A k)
    (hSmem : ∀ k ∈ S, E k = Ea) (hScom : ∀ k ∉ S, E k = Eb) (hEne : Ea ≠ Eb)
    (i : ι) (hi : i ∈ S) (j : ι) (hj : j ∉ S)
    (hP : 0 < ∑ k ∈ S, A k * g k * obs k)
    (hTmin : 0 < Tmin) (hTsL : Tmin ≤ Tstar) (hTsR : Tstar ≤ Tmax)
    (hstar : (∑ k ∈ univ \ S, (A k * g k) ^ 2) * (∑ k ∈ S, A k * g k * obs k)
          * boltzmannFactor kB Tstar Eb
        = (∑ k ∈ S, (A k * g k) ^ 2) * (∑ k ∈ univ \ S, A k * g k * obs k)
          * boltzmannFactor kB Tstar Ea)
    {p : ℝ × ℝ} (hp : p.1 ∈ Set.Icc Tmin Tmax)
    (hne : p ≠ (Tstar, profiledDensity kB Fcal g E A obs Tstar)) :
    nlObjective kB Fcal g E A obs (Tstar, profiledDensity kB Fcal g E A obs Tstar)
      < nlObjective kB Fcal g E A obs p :=
  joint_strictMin_of_T_strictMin hg hFcal hA
    (fun _ hT hTne => profiledResidual_twoLevel_Tstar_isStrictMin hkB hg hFcal hA hSmem hScom
      hEne i hi j hj hP hTmin hTsL hTsR hstar hT hTne) hp hne

/-- **Uniqueness of the joint `(T, N)` minimizer (`m` lines, two energies; REDUCED, Tognoni 2010).**
Under the hypotheses of `profiledResidual_twoLevel_strictUnimodalOn`, ANY minimizer of the joint
nonlinear least-squares objective over `[Tmin, Tmax] ×ˢ ℝ` equals `(Tstar, N̂(Tstar))` — the
`T`-direction uniqueness that VARPRO alone could not supply, now for arbitrarily many lines at two
upper-level energies. Scope note: `NonlinearLeastSquares.nlObjective_exists_min` gives existence on
a compact box `[Tmin,Tmax] ×ˢ [Nmin,Nmax]`, a DIFFERENT region; the two do not compose into a
single existence-and-uniqueness statement unless `N̂(Tstar)` lies in that density box, which is not
proved here. -/
theorem joint_twoLevel_box_minimizer_unique [Nonempty ι]
    {kB Fcal Tmin Tmax Tstar Ea Eb : ℝ} {g E A obs : ι → ℝ} {S : Finset ι}
    (hkB : 0 < kB) (hg : ∀ k, 0 < g k) (hFcal : 0 < Fcal) (hA : ∀ k, 0 < A k)
    (hSmem : ∀ k ∈ S, E k = Ea) (hScom : ∀ k ∉ S, E k = Eb) (hEne : Ea ≠ Eb)
    (i : ι) (hi : i ∈ S) (j : ι) (hj : j ∉ S)
    (hP : 0 < ∑ k ∈ S, A k * g k * obs k)
    (hTmin : 0 < Tmin) (hTsL : Tmin ≤ Tstar) (hTsR : Tstar ≤ Tmax)
    (hstar : (∑ k ∈ univ \ S, (A k * g k) ^ 2) * (∑ k ∈ S, A k * g k * obs k)
          * boltzmannFactor kB Tstar Eb
        = (∑ k ∈ S, (A k * g k) ^ 2) * (∑ k ∈ univ \ S, A k * g k * obs k)
          * boltzmannFactor kB Tstar Ea)
    {p : ℝ × ℝ} (hp : p ∈ Set.Icc Tmin Tmax ×ˢ (Set.univ : Set ℝ))
    (hmin : IsMinOn (nlObjective kB Fcal g E A obs)
      (Set.Icc Tmin Tmax ×ˢ (Set.univ : Set ℝ)) p) :
    p = (Tstar, profiledDensity kB Fcal g E A obs Tstar) :=
  minimizer_eq_of_strictMin hTsL hTsR
    (fun _ hq hqne => joint_twoLevel_box_isStrictMin hkB hg hFcal hA hSmem hScom hEne i hi j hj
      hP hTmin hTsL hTsR hstar hq hqne) hmin hp

/-! ### The two-line corollary of already-landed work -/

/-- **Strict joint `(T, N)` minimum, two lines (REDUCED, Tognoni 2010).** The explicit corollary of
`ProfiledUnimodality.profiledResidual_two_Tstar_isStrictMin` that was implicit but never stated:
strict unimodality of the profiled residual on the box, plus the VARPRO fact that the `N`-section
has the profiled density as its unique minimizer, makes `(Tstar, N̂(Tstar))` a strict global
minimizer of the joint objective over `[Tmin, Tmax] ×ˢ ℝ`. This is bookkeeping over landed results,
not new mathematics. -/
theorem joint_two_box_isStrictMin {kB Fcal Tmin Tmax Tstar : ℝ} {g E A obs : Fin 2 → ℝ}
    (hkB : 0 < kB) (hg : ∀ k, 0 < g k) (hFcal : 0 < Fcal) (hA : ∀ k, 0 < A k)
    (ho0 : 0 < obs 0) (ho1 : 0 < obs 1) (hE : E 0 ≠ E 1)
    (hTmin : 0 < Tmin) (hTsL : Tmin ≤ Tstar) (hTsR : Tstar ≤ Tmax)
    (hstar : obs 1 * lineIntensity kB Tstar 1 Fcal g E A 0
           = obs 0 * lineIntensity kB Tstar 1 Fcal g E A 1)
    {p : ℝ × ℝ} (hp : p.1 ∈ Set.Icc Tmin Tmax)
    (hne : p ≠ (Tstar, profiledDensity kB Fcal g E A obs Tstar)) :
    nlObjective kB Fcal g E A obs (Tstar, profiledDensity kB Fcal g E A obs Tstar)
      < nlObjective kB Fcal g E A obs p :=
  joint_strictMin_of_T_strictMin hg hFcal hA
    (fun _ hT hTne => profiledResidual_two_Tstar_isStrictMin hkB hg hFcal hA ho0 ho1 hE hTmin
      hTsL hTsR hstar hT hTne) hp hne

/-- **Uniqueness of the joint `(T, N)` minimizer, two lines (REDUCED, Tognoni 2010).** Any minimizer
of the joint objective over `[Tmin, Tmax] ×ˢ ℝ` equals `(Tstar, N̂(Tstar))`. The statement the
`ProfiledUnimodality` module's `V`-shape always implied; recorded here so that "a joint minimizer
of the two-line CF-LIBS fit over this region, **if one exists**, is unique and equals
`(Tstar, N̂(Tstar))`" is an actual theorem rather than a reading of one. This is a *conditional*
uniqueness statement, not an existence-and-uniqueness statement: the minimizer is supplied by the
hypothesis `hmin`, and existence over this non-compact region is not proved anywhere here. -/
theorem joint_two_box_minimizer_unique {kB Fcal Tmin Tmax Tstar : ℝ} {g E A obs : Fin 2 → ℝ}
    (hkB : 0 < kB) (hg : ∀ k, 0 < g k) (hFcal : 0 < Fcal) (hA : ∀ k, 0 < A k)
    (ho0 : 0 < obs 0) (ho1 : 0 < obs 1) (hE : E 0 ≠ E 1)
    (hTmin : 0 < Tmin) (hTsL : Tmin ≤ Tstar) (hTsR : Tstar ≤ Tmax)
    (hstar : obs 1 * lineIntensity kB Tstar 1 Fcal g E A 0
           = obs 0 * lineIntensity kB Tstar 1 Fcal g E A 1)
    {p : ℝ × ℝ} (hp : p ∈ Set.Icc Tmin Tmax ×ˢ (Set.univ : Set ℝ))
    (hmin : IsMinOn (nlObjective kB Fcal g E A obs)
      (Set.Icc Tmin Tmax ×ˢ (Set.univ : Set ℝ)) p) :
    p = (Tstar, profiledDensity kB Fcal g E A obs Tstar) :=
  minimizer_eq_of_strictMin hTsL hTsR
    (fun _ hq hqne => joint_two_box_isStrictMin hkB hg hFcal hA ho0 ho1 hE hTmin hTsL hTsR
      hstar hq hqne) hmin hp

/-! ### On-manifold specialization: the apex is the true temperature -/

/-- On the noise-free manifold the group projections are `P = N₀·λ(T₀)·α(T₀)·S_A` and
`Q = N₀·λ(T₀)·β(T₀)·S_B`, so the group-`S` projection is positive and the apex condition holds
exactly at `T₀`. -/
private lemma twoLevel_onManifold_apex [Nonempty ι] {kB Fcal T0 N0 Ea Eb : ℝ}
    {g E A obs : ι → ℝ} {S : Finset ι}
    (hg : ∀ k, 0 < g k) (hFcal : 0 < Fcal) (hN0 : 0 < N0)
    (hSmem : ∀ k ∈ S, E k = Ea) (hScom : ∀ k ∉ S, E k = Eb)
    (hSA : 0 < ∑ k ∈ S, (A k * g k) ^ 2)
    (hobs : ∀ k, obs k = lineIntensity kB T0 N0 Fcal g E A k) :
    0 < ∑ k ∈ S, A k * g k * obs k
      ∧ (∑ k ∈ univ \ S, (A k * g k) ^ 2) * (∑ k ∈ S, A k * g k * obs k)
          * boltzmannFactor kB T0 Eb
        = (∑ k ∈ S, (A k * g k) ^ 2) * (∑ k ∈ univ \ S, A k * g k * obs k)
          * boltzmannFactor kB T0 Ea := by
  have hUpos : (0 : ℝ) < partitionFunction kB T0 g E := partitionFunction_pos hg
  have hPeq : ∑ k ∈ S, A k * g k * obs k
      = N0 * (Fcal / partitionFunction kB T0 g E) * boltzmannFactor kB T0 Ea
        * ∑ k ∈ S, (A k * g k) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [hobs k, lineIntensity_linear_in_N kB T0 N0 Fcal g E A k,
      twoLevel_lineIntensity_S hSmem hk]
    ring
  have hQeq : ∑ k ∈ univ \ S, A k * g k * obs k
      = N0 * (Fcal / partitionFunction kB T0 g E) * boltzmannFactor kB T0 Eb
        * ∑ k ∈ univ \ S, (A k * g k) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [hobs k, lineIntensity_linear_in_N kB T0 N0 Fcal g E A k,
      twoLevel_lineIntensity_C hScom (Finset.mem_sdiff.mp hk).2]
    ring
  refine ⟨?_, ?_⟩
  · rw [hPeq]
    exact mul_pos (mul_pos (mul_pos hN0 (div_pos hFcal hUpos)) (boltzmannFactor_pos _ _ _)) hSA
  · rw [hPeq, hQeq]; ring

omit [DecidableEq ι] in
/-- **On-manifold strict unimodality about the true temperature (`m` lines, two energies; REDUCED,
Ciucci 1999).** In the noise-free case `obs = forward(T₀, N₀)` with `N₀ > 0`, the apex is `T₀`
itself, so the density-profiled objective is strictly decreasing on `[Tmin, T₀]` and strictly
increasing on `[T₀, Tmax]` for a line set with arbitrarily many lines at exactly two distinct upper
level energies. This upgrades `NonlinearLeastSquares.profiledT_onManifold_unique` (which shows the
residual VANISHES only at `T₀`) to a local shape statement, and widens
`ProfiledUnimodality.profiledResidual_two_strictUnimodal_onManifold` past two lines. -/
theorem profiledResidual_twoLevel_strictUnimodal_onManifold [Nonempty ι]
    {kB Fcal Tmin Tmax T0 N0 Ea Eb : ℝ} {g E A obs : ι → ℝ} {S : Finset ι}
    (hkB : 0 < kB) (hg : ∀ k, 0 < g k) (hFcal : 0 < Fcal) (hA : ∀ k, 0 < A k) (hN0 : 0 < N0)
    (hSmem : ∀ k ∈ S, E k = Ea) (hScom : ∀ k ∉ S, E k = Eb) (hEne : Ea ≠ Eb)
    (i : ι) (hi : i ∈ S) (j : ι) (hj : j ∉ S)
    (hTmin : 0 < Tmin) (hTL : Tmin ≤ T0) (hTR : T0 ≤ Tmax)
    (hobs : ∀ k, obs k = lineIntensity kB T0 N0 Fcal g E A k) :
    StrictAntiOn
        (fun T => nlObjective kB Fcal g E A obs (T, profiledDensity kB Fcal g E A obs T))
        (Set.Icc Tmin T0)
      ∧ StrictMonoOn
        (fun T => nlObjective kB Fcal g E A obs (T, profiledDensity kB Fcal g E A obs T))
        (Set.Icc T0 Tmax) := by
  classical
  obtain ⟨hP, hstar⟩ :=
    twoLevel_onManifold_apex hg hFcal hN0 hSmem hScom (group_energy_pos hg hA hi) hobs
  exact profiledResidual_twoLevel_strictUnimodalOn hkB hg hFcal hA hSmem hScom hEne i hi j hj
    hP hTmin hTL hTR hstar

/-! ### Non-vacuity witnesses (an explicit THREE-line, two-level configuration) -/

/-- Unit degeneracies for the three-line two-level witness. -/
private def wtG : Fin 3 → ℝ := fun _ => 1

/-- Unit Einstein coefficients for the three-line two-level witness. -/
private def wtA : Fin 3 → ℝ := fun _ => 1

/-- Upper-level energies of the witness: line `0` sits at `E_a = 0`, lines `1` and `2` both sit at
`E_b = 1`. Three lines, exactly two distinct energies — outside the reach of the `Fin 2` theorems
of `ProfiledUnimodality.lean`. -/
private def wtE : Fin 3 → ℝ := fun k => if k = 0 then 0 else 1

/-- On-manifold observation: the exact forward spectrum of `(T₀, N₀) = (1, 1)`. -/
private noncomputable def wtObs : Fin 3 → ℝ := fun k => lineIntensity 1 1 1 1 wtG wtE wtA k

private lemma wtG_pos : ∀ k, 0 < wtG k := fun _ => by norm_num [wtG]
private lemma wtA_pos : ∀ k, 0 < wtA k := fun _ => by norm_num [wtA]

private lemma wtE_S : ∀ k ∈ ({0} : Finset (Fin 3)), wtE k = 0 := by
  intro k hk
  rw [Finset.mem_singleton] at hk
  subst hk
  simp only [wtE]
  norm_num

private lemma wtE_C : ∀ k ∉ ({0} : Finset (Fin 3)), wtE k = 1 := by
  intro k hk
  have hk0 : k ≠ 0 := fun h => hk (Finset.mem_singleton.mpr h)
  simp only [wtE, if_neg hk0]

/-- **Non-vacuity of the widened strict unimodality (three lines, two energies).** With
`kB = Fcal = T₀ = N₀ = 1`, three lines at energies `E = (0, 1, 1)`, and the exact forward spectrum
`wtObs`, the density-profiled objective is strictly decreasing on `[1/2, 1]` and strictly increasing
on `[1, 2]`. This genuinely exercises the general theorem: the line index type is `Fin 3`, the
group-`B` level carries **two** lines, and the observation is a full three-component spectrum — so
the conclusion is not the two-line result in disguise, and it does not collapse to any `0 ≤ 0`
tie. -/
example :
    StrictAntiOn
        (fun T => nlObjective 1 1 wtG wtE wtA wtObs (T, profiledDensity 1 1 wtG wtE wtA wtObs T))
        (Set.Icc (1 / 2 : ℝ) 1)
      ∧ StrictMonoOn
        (fun T => nlObjective 1 1 wtG wtE wtA wtObs (T, profiledDensity 1 1 wtG wtE wtA wtObs T))
        (Set.Icc (1 : ℝ) 2) :=
  profiledResidual_twoLevel_strictUnimodal_onManifold (S := ({0} : Finset (Fin 3)))
    (Ea := 0) (Eb := 1) one_pos wtG_pos one_pos wtA_pos one_pos wtE_S wtE_C (by norm_num)
    0 (Finset.mem_singleton_self 0) 1 (by decide) (by norm_num) (by norm_num) (by norm_num)
    (fun _ => rfl)

/-- **Non-vacuity of the joint `(T, N)` uniqueness (three lines, two energies).** For the same
three-line witness, the joint parameter pair `(3/2, 2)` — a wrong temperature AND a wrong density —
is strictly beaten by `(T₀, N̂(T₀)) = (1, N̂(1))`. Both coordinates are genuinely off, so the strict
inequality is not a tie between equal values. -/
example :
    nlObjective 1 1 wtG wtE wtA wtObs (1, profiledDensity 1 1 wtG wtE wtA wtObs 1)
      < nlObjective 1 1 wtG wtE wtA wtObs (3 / 2, 2) := by
  obtain ⟨hP, hstar⟩ := twoLevel_onManifold_apex (kB := 1) (Fcal := 1) (T0 := 1) (N0 := 1)
    (Ea := 0) (Eb := 1) (S := ({0} : Finset (Fin 3))) (A := wtA) (obs := wtObs)
    wtG_pos one_pos one_pos
    wtE_S wtE_C (group_energy_pos wtG_pos wtA_pos (Finset.mem_singleton_self 0))
    (fun _ => rfl)
  refine joint_twoLevel_box_isStrictMin (Tmin := 1 / 2) (Tmax := 2) (Tstar := 1)
    (S := ({0} : Finset (Fin 3))) (Ea := 0) (Eb := 1) one_pos wtG_pos one_pos wtA_pos
    wtE_S wtE_C (by norm_num) 0 (Finset.mem_singleton_self 0) 1 (by decide) hP
    (by norm_num) (by norm_num) (by norm_num) hstar (by norm_num) ?_
  intro h
  have h1 := congrArg Prod.fst h
  norm_num at h1

/-! ### Non-vacuity witness on genuinely OFF-manifold three-line data -/

/-- A perturbation supported on the two group-`B` lines and summing to zero across them: it is
orthogonal to the two-dimensional group plane, so it changes neither group projection `P`, `Q`.
Its magnitude `1/10` is chosen below the group-`B` line intensity at `T₀ = 1`, so the perturbed
spectrum still has every component strictly positive — a physically admissible noisy measurement,
proved as `wtObsOff_pos` rather than asserted. -/
private noncomputable def wtEta : Fin 3 → ℝ
  | 0 => 0
  | 1 => 1 / 10
  | 2 => -(1 / 10)

/-- Off-manifold observation: the exact forward spectrum of `(1, 1)` plus the plane-orthogonal
perturbation `wtEta`. -/
private noncomputable def wtObsOff : Fin 3 → ℝ := fun k => wtObs k + wtEta k

private lemma wt_pair : (univ \ ({0} : Finset (Fin 3))) = {1, 2} := by decide

/-- Lines `1` and `2` share an upper level, degeneracy, and Einstein coefficient, so the CF-LIBS
forward map assigns them equal intensity at every `(T, N)`. -/
private lemma wtObs_one_eq_two : wtObs 1 = wtObs 2 := by
  simp only [wtObs, lineIntensity, population, wtA, wtG]
  rw [wtE_C 1 (by decide), wtE_C 2 (by decide)]

/-- The group-`B` line intensity of the witness exceeds the perturbation size:
`wtObs 2 = exp(−1)/(1 + 2·exp(−1)) > 1/10`, because `e < 8`. -/
private lemma wtObs_two_gt : (1 : ℝ) / 10 < wtObs 2 := by
  have hE2 : wtE 2 = 1 := wtE_C 2 (by decide)
  have hpos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have h8 : Real.exp 1 < 8 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have hlow : (1 : ℝ) / 8 < Real.exp (-1 : ℝ) := by
    rw [Real.exp_neg, ← one_div]
    exact one_div_lt_one_div_of_lt hpos h8
  have hUpos : (0 : ℝ) < 1 + 2 * Real.exp (-1 : ℝ) := by positivity
  have hU : partitionFunction 1 1 wtG wtE = 1 + 2 * Real.exp (-1 : ℝ) := by
    have hE0 : wtE 0 = 0 := wtE_S 0 (Finset.mem_singleton_self 0)
    have hE1 : wtE 1 = 1 := wtE_C 1 (by decide)
    simp only [partitionFunction, Fin.sum_univ_three, wtG, boltzmannFactor, hE0, hE1, hE2,
      neg_zero, mul_one, div_one, Real.exp_zero, one_mul]
    ring
  have hval : wtObs 2
      = Real.exp (-1 : ℝ) / (1 + 2 * Real.exp (-1 : ℝ)) := by
    have h : wtObs 2 = 1 * wtA 2
        * (1 * wtG 2 * boltzmannFactor 1 1 (wtE 2) / partitionFunction 1 1 wtG wtE) := rfl
    rw [h, hU, hE2]
    simp only [wtA, wtG, boltzmannFactor]
    norm_num
  rw [hval, lt_div_iff₀ hUpos]
  linarith

/-- Every component of the perturbed observation is strictly positive: `wtObsOff` is a physically
admissible (nonnegative-intensity) noisy spectrum, not merely a mathematical perturbation. -/
private lemma wtObsOff_pos : 0 < wtObsOff 0 ∧ 0 < wtObsOff 1 ∧ 0 < wtObsOff 2 := by
  have hb : ∀ j, 0 < wtObs j := fun j =>
    lineIntensity_pos (kB := 1) (T := 1) (E := wtE) wtG_pos one_pos one_pos wtA_pos j
  refine ⟨?_, ?_, ?_⟩
  · simp only [wtObsOff, wtEta]
    linarith [hb 0]
  · simp only [wtObsOff, wtEta]
    linarith [hb 1]
  · simp only [wtObsOff, wtEta]
    linarith [wtObs_two_gt]

private lemma wtOff_P : ∑ k ∈ ({0} : Finset (Fin 3)), wtA k * wtG k * wtObsOff k
    = ∑ k ∈ ({0} : Finset (Fin 3)), wtA k * wtG k * wtObs k := by
  rw [Finset.sum_singleton, Finset.sum_singleton]
  simp only [wtObsOff, wtEta, wtA, wtG]
  ring

private lemma wtOff_Q : ∑ k ∈ (univ \ ({0} : Finset (Fin 3))), wtA k * wtG k * wtObsOff k
    = ∑ k ∈ (univ \ ({0} : Finset (Fin 3))), wtA k * wtG k * wtObs k := by
  rw [wt_pair, Finset.sum_pair (by decide : (1 : Fin 3) ≠ 2),
    Finset.sum_pair (by decide : (1 : Fin 3) ≠ 2)]
  simp only [wtObsOff, wtEta, wtA, wtG]
  ring

/-- **Non-vacuity on genuinely off-manifold three-line data.** The observation `wtObsOff` is NOT any
forward spectrum: lines `1` and `2` share an upper level, degeneracy, and Einstein coefficient, so
every model spectrum gives them equal intensity (`wtObs_one_eq_two`), whereas `wtObsOff 1 ≠
wtObsOff 2`. Yet the density-profiled objective is still strictly decreasing on `[1/2, 1]` and
strictly increasing on `[1, 2]`, with apex at `T = 1`. This is the substantive witness: three
lines, two energy groups, an observation off the model manifold whose orthogonal component is
carried by the `T`-independent offset `K`, and a strict `V`-shape all the same. The statement also
carries `wtObsOff k > 0` for every line, so the witness is a *physically admissible* noisy spectrum
(all intensities positive), not a perturbation that drives a line intensity negative. No hypothesis
collapses and no inequality degenerates to a tie. -/
example :
    (0 < wtObsOff 0 ∧ 0 < wtObsOff 1 ∧ 0 < wtObsOff 2)
      ∧ wtObsOff 1 ≠ wtObsOff 2
      ∧ StrictAntiOn
        (fun T => nlObjective 1 1 wtG wtE wtA wtObsOff
          (T, profiledDensity 1 1 wtG wtE wtA wtObsOff T))
        (Set.Icc (1 / 2 : ℝ) 1)
      ∧ StrictMonoOn
        (fun T => nlObjective 1 1 wtG wtE wtA wtObsOff
          (T, profiledDensity 1 1 wtG wtE wtA wtObsOff T))
        (Set.Icc (1 : ℝ) 2) := by
  obtain ⟨hP, hstar⟩ := twoLevel_onManifold_apex (kB := 1) (Fcal := 1) (T0 := 1) (N0 := 1)
    (Ea := 0) (Eb := 1) (S := ({0} : Finset (Fin 3))) (A := wtA) (obs := wtObs)
    wtG_pos one_pos one_pos
    wtE_S wtE_C (group_energy_pos wtG_pos wtA_pos (Finset.mem_singleton_self 0))
    (fun _ => rfl)
  rw [← wtOff_P] at hP
  rw [← wtOff_P, ← wtOff_Q] at hstar
  refine ⟨wtObsOff_pos, ?_,
    profiledResidual_twoLevel_strictUnimodalOn (Tmin := 1 / 2) (Tmax := 2) (Tstar := 1)
    (S := ({0} : Finset (Fin 3))) (Ea := 0) (Eb := 1) one_pos wtG_pos one_pos wtA_pos
    wtE_S wtE_C (by norm_num) 0 (Finset.mem_singleton_self 0) 1 (by decide) hP
    (by norm_num) (by norm_num) (by norm_num) hstar⟩
  simp only [wtObsOff, wtEta, wtObs_one_eq_two]
  intro h
  linarith

end CflibsFormal
