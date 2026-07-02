/-
Copyright (c) 2026 Brian Squires. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Squires
-/
import Mathlib
import CflibsFormal.Boltzmann
import CflibsFormal.Saha
import CflibsFormal.ForwardMap

/-!
# Saha–Boltzmann formalization — Part 5: identifiability of the inverse problem

This module turns the *forward* CF-LIBS model (`ForwardMap.lineIntensity`, the
`Boltzmann` populations, the `Saha` ionization diagnostic) into rigorous
**identifiability** (injectivity) statements: precisely when, and under which
explicit nondegeneracy hypotheses, the plasma parameters `(T, n_e, N_s)` are
*uniquely* recoverable from line intensities.

We reuse the already-built definitions verbatim — nothing here re-defines the
forward model:

* `lineIntensity` from `ForwardMap.lean` (`I_{ki} = Fcal · A · n_k`,
  `n_k = population kB T N g E k`),
* `population`, `partitionFunction`, `boltzmannFactor` from `Boltzmann.lean`,
* `electronDensityFromRatio`, `sahaFactor`, and the strict-antitone inverse
  `electronDensity_antitone` from `Saha.lean`.

The theorems are:

* `lineIntensity_ratio_closed_form` — the shared engine: the within-set two-line
  ratio is `I_j/I_i = ((g_j·A_j)/(g_i·A_i)) · exp((E_i − E_j)/(k_B T))`.
* `temperature_identifiability` — **Target 1.** Two same-species lines with
  *distinct upper-level energies* fix `T` uniquely: if two parameter sets
  produce the same intensity *ratio* on such a line pair, then `T₁ = T₂`. The
  calibration `Fcal`, density `N`, partition function `U`, degeneracies `g`, and
  Einstein coefficient `A` all cancel; the proof reduces to injectivity of
  `Real.exp` and `E i ≠ E j`.
* `temperature_degeneracy` / `temperature_not_identifiable_of_degenerate` — the
  **degeneracy converse.** With `E i = E j` the ratio collapses to the
  `T`-independent constant `(g_j·A_j)/(g_i·A_i)`, so distinct temperatures
  produce identical ratio observations: the distinct-energy hypothesis of
  Target 1 is *necessary*, and a runtime "small `ΔE` ⇒ refuse" gate is grounded
  in a theorem rather than a heuristic.
* `temperature_ratio_near_degenerate` — **quantitative interpolation.** For small
  `|E_i − E_j|` the two-line ratio is *nearly* `T`-independent: the difference of the
  ratio at two temperatures is bounded LINEARLY in `|E_i − E_j|`, so as `ΔE → 0` the
  observable temperature signal vanishes and inference is ill-conditioned. This is the
  quantitative form of `temperature_degeneracy`, whose `ΔE = 0` collapse it recovers as
  an exact limit (RHS `→ 0`).
* `density_identifiability` — **Target 2.** With `T` and atomic data fixed and
  nondegenerate, the species total number density `N` is recovered from a single
  line intensity (equal intensities ⇒ equal `N`). Since composition `C_s` is `N_s`
  up to the closure normalization `∑ C_s = 1`, this is the per-species core of
  composition identifiability.
* `electron_density_identifiability` — **Target 3.** At fixed `T` (hence fixed
  Saha factor `S = sahaFactor … > 0`) the density diagnostic `R ↦ n_e = S/R` is
  *injective* on positive stage ratios: two ratios giving the same inferred `n_e`
  must coincide, so a measured electron density back-determines `R` uniquely.
  Obtained from the proven strict antitonicity `electronDensity_antitone`; it
  rests only on `S > 0`, the Saha factor's internal structure being certified
  separately by `sahaFactor_pos` / `log_sahaFactor`.

All hypotheses are satisfiable (see the witness discussion in each docstring), so
the theorems are non-vacuous.
-/

namespace CflibsFormal

open Finset Real
open scoped BigOperators

variable {ι : Type*} [Fintype ι]
variable {κ : Type*} [Fintype κ]

/-- **Two-line intensity-ratio closed form.** Within one parameter set, the same-species
two-line ratio is
  `I_j / I_i = ((g_j·A_j)/(g_i·A_i)) · exp((E_i − E_j)/(k_B T))` —
the calibration `Fcal`, density `N`, and partition function `U(T)` all cancel (Ciucci et al.
1999, the two-line Boltzmann ratio). This single identity carries BOTH directions of the
temperature question: with `E i ≠ E j` the exponential factor genuinely varies with `T` and the
temperature is identifiable (`temperature_identifiability`); with `E i = E j` it collapses to
the `T`-independent constant `(g_j·A_j)/(g_i·A_i)` and the temperature is provably lost
(`temperature_degeneracy`). No sign or positivity constraint on `T` is needed — the identity is
total algebra over ℝ (at `T = 0` both sides read the same `exp(·/0) = exp 0` convention). -/
theorem lineIntensity_ratio_closed_form [Nonempty ι] {kB T N Fcal : ℝ} {g E A : ι → ℝ}
    (hg : ∀ k, 0 < g k) (hN : 0 < N) (hFcal : 0 < Fcal) (hA : ∀ k, 0 < A k) (i j : ι) :
    lineIntensity kB T N Fcal g E A j / lineIntensity kB T N Fcal g E A i
      = (g j * A j) / (g i * A i) * Real.exp ((E i - E j) / (kB * T)) := by
  have hU : 0 < partitionFunction kB T g E := partitionFunction_pos hg
  have hgi : g i ≠ 0 := (hg i).ne'
  have hgj : g j ≠ 0 := (hg j).ne'
  have hAi : A i ≠ 0 := (hA i).ne'
  have hAj : A j ≠ 0 := (hA j).ne'
  have hNne : N ≠ 0 := hN.ne'
  have hFne : Fcal ≠ 0 := hFcal.ne'
  have hexp : Real.exp ((E i - E j) / (kB * T))
      = Real.exp (-E j / (kB * T)) / Real.exp (-E i / (kB * T)) := by
    rw [← Real.exp_sub]; ring_nf
  rw [hexp]
  simp only [lineIntensity, population, boltzmannFactor]
  field_simp

/-- **Target 1 — temperature identifiability.**

Two same-species lines with **distinct upper-level energies** `E i ≠ E j` fix the
temperature uniquely. If two parameter sets (possibly differing in calibration
`Fcal`, total density `N`, and temperature `T`) produce the *same intensity ratio*
`I_j / I_i` on this line pair, and both temperatures are positive, then `T₁ = T₂`.

Inside one parameter set the ratio is
`I_j/I_i = ((g_j·A_j)/(g_i·A_i)) · exp((E_i − E_j)/(k_B T))` — the common positive
prefactor `(g_j·A_j)/(g_i·A_i)` (shared across both sides because `g`, `E`, `A`, the
species, are the same) cancels *across* the two sides, after which `Real.exp` injectivity
plus `E i ≠ E j` and `k_B > 0` force `T₁ = T₂`. `Fcal`, `N`, and the partition function
`U` all cancel.

Non-vacuous: e.g. `ι = Fin 2`, `kB = 1`, `g = A = fun _ => 1`, `E = ![0,1]`
(so `E 0 ≠ E 1`), `N = Fcal = 1`, any `T₁, T₂ > 0`. Then the ratio is
`exp((E i − E j)/(kB·T))`, a non-constant function of `T`; equality genuinely
forces `T₁ = T₂` (it depends on `Real.exp` injectivity, not `rfl`). -/
theorem temperature_identifiability [Nonempty ι]
    {kB : ℝ} {T₁ T₂ N₁ N₂ Fcal₁ Fcal₂ : ℝ} {g E A : ι → ℝ}
    (hkB : 0 < kB) (hT₁ : 0 < T₁) (hT₂ : 0 < T₂)
    (hg : ∀ k, 0 < g k) (hN₁ : 0 < N₁) (hN₂ : 0 < N₂)
    (hFcal₁ : 0 < Fcal₁) (hFcal₂ : 0 < Fcal₂) (hA : ∀ k, 0 < A k)
    (i j : ι) (hE : E i ≠ E j)
    (hratio :
      lineIntensity kB T₁ N₁ Fcal₁ g E A j / lineIntensity kB T₁ N₁ Fcal₁ g E A i
        = lineIntensity kB T₂ N₂ Fcal₂ g E A j / lineIntensity kB T₂ N₂ Fcal₂ g E A i) :
    T₁ = T₂ := by
  rw [lineIntensity_ratio_closed_form hg hN₁ hFcal₁ hA i j,
    lineIntensity_ratio_closed_form hg hN₂ hFcal₂ hA i j] at hratio
  -- Cancel the common positive prefactor `(g j · A j) / (g i · A i)`.
  have hc : (0 : ℝ) < (g j * A j) / (g i * A i) :=
    div_pos (mul_pos (hg j) (hA j)) (mul_pos (hg i) (hA i))
  have hexp : Real.exp ((E i - E j) / (kB * T₁)) = Real.exp ((E i - E j) / (kB * T₂)) :=
    mul_left_cancel₀ hc.ne' hratio
  -- `exp` injective ⇒ equal arguments.
  rw [Real.exp_eq_exp] at hexp
  -- `(E i − E j)/(kB·T₁) = (E i − E j)/(kB·T₂)` with `E i − E j ≠ 0`, `kB > 0`.
  have hEij : E i - E j ≠ 0 := sub_ne_zero.mpr hE
  rw [div_eq_div_iff (mul_pos hkB hT₁).ne' (mul_pos hkB hT₂).ne'] at hexp
  -- `(E i − E j)·(kB·T₂) = (E i − E j)·(kB·T₁)`.
  have h2 : kB * T₂ = kB * T₁ := mul_left_cancel₀ hEij hexp
  exact (mul_left_cancel₀ hkB.ne' h2).symm

/-- **Degeneracy converse — equal energies make the ratio `T`-independent.** If the two lines
share the SAME upper-level energy (`E i = E j`), the two-line intensity ratio collapses to the
constant `(g_j·A_j)/(g_i·A_i)` (`lineIntensity_ratio_closed_form` with a zero exponent) — the
same value for EVERY temperature, density, and calibration on both sides. The ratio observation
then carries no information about `T`: the ratio-equality antecedent of
`temperature_identifiability` is satisfied by every pair `(T₁, T₂)` whatsoever, so its
distinct-energy hypothesis `E i ≠ E j` is *necessary*, not merely convenient. Note the
strength: no positivity of `kB`, `T₁`, `T₂` is needed — the collapse is total. -/
theorem temperature_degeneracy [Nonempty ι]
    {kB T₁ T₂ N₁ N₂ Fcal₁ Fcal₂ : ℝ} {g E A : ι → ℝ}
    (hg : ∀ k, 0 < g k) (hN₁ : 0 < N₁) (hN₂ : 0 < N₂)
    (hFcal₁ : 0 < Fcal₁) (hFcal₂ : 0 < Fcal₂) (hA : ∀ k, 0 < A k)
    (i j : ι) (hE : E i = E j) :
    lineIntensity kB T₁ N₁ Fcal₁ g E A j / lineIntensity kB T₁ N₁ Fcal₁ g E A i
      = lineIntensity kB T₂ N₂ Fcal₂ g E A j / lineIntensity kB T₂ N₂ Fcal₂ g E A i := by
  rw [lineIntensity_ratio_closed_form hg hN₁ hFcal₁ hA i j,
    lineIntensity_ratio_closed_form hg hN₂ hFcal₂ hA i j, hE]
  simp

/-- **Degenerate pair ⇒ temperature NOT identifiable.** With a degenerate line pair
(`E i = E j`), two genuinely different positive temperatures (here `T₁ = 1 ≠ 2 = T₂`, same
density and calibration) produce the SAME two-line ratio observation — the formal converse of
`temperature_identifiability`, exhibiting the non-injectivity directly. This grounds the
runtime "small `ΔE` ⇒ refuse" gate of the strict-mode solver: at `ΔE = 0` the refusal is not
heuristic caution but a theorem — NO algorithm can recover `T` from a degenerate pair's ratio,
because the observation itself is constant in `T`. -/
theorem temperature_not_identifiable_of_degenerate [Nonempty ι]
    {kB N Fcal : ℝ} {g E A : ι → ℝ}
    (hg : ∀ k, 0 < g k) (hN : 0 < N) (hFcal : 0 < Fcal) (hA : ∀ k, 0 < A k)
    (i j : ι) (hE : E i = E j) :
    ∃ T₁ T₂ : ℝ, 0 < T₁ ∧ 0 < T₂ ∧ T₁ ≠ T₂ ∧
      lineIntensity kB T₁ N Fcal g E A j / lineIntensity kB T₁ N Fcal g E A i
        = lineIntensity kB T₂ N Fcal g E A j / lineIntensity kB T₂ N Fcal g E A i :=
  ⟨1, 2, one_pos, two_pos, by norm_num,
    temperature_degeneracy hg hN hN hFcal hFcal hA i j hE⟩

private def nvDegg : Fin 2 → ℝ := ![1, 2]
private def nvDegE : Fin 2 → ℝ := ![5, 5]
private def nvDegA : Fin 2 → ℝ := ![1, 3]

/-- **Non-vacuity witness for the degeneracy converse.** A genuine two-line degenerate pair
(`ι = Fin 2`, distinct indices `0 ≠ 1`, equal energies `E = ![5,5]`, non-trivial atomic data
`g = ![1,2]`, `A = ![1,3]`): at BOTH `T = 1` and `T = 2` the ratio equals the same non-trivial
constant `(g₁·A₁)/(g₀·A₀) = 6`. So the aliasing of `temperature_degeneracy` is real content on
distinct lines with a genuinely non-constant forward model — not an artifact of `i = j` or of a
trivial ratio `1`. -/
example :
    lineIntensity 1 1 1 1 nvDegg nvDegE nvDegA 1 / lineIntensity 1 1 1 1 nvDegg nvDegE nvDegA 0
      = 6
    ∧ lineIntensity 1 2 1 1 nvDegg nvDegE nvDegA 1 / lineIntensity 1 2 1 1 nvDegg nvDegE nvDegA 0
      = 6 := by
  have hg : ∀ k, 0 < nvDegg k := fun k => by fin_cases k <;> norm_num [nvDegg]
  have hA : ∀ k, 0 < nvDegA k := fun k => by fin_cases k <;> norm_num [nvDegA]
  constructor <;>
    rw [lineIntensity_ratio_closed_form hg one_pos one_pos hA 0 1] <;>
    norm_num [nvDegg, nvDegE, nvDegA]

/-- **Target 2 — relative-density / composition identifiability.**

With `T` and the atomic data (`Fcal`, `A`, `g`, `E`, `U`) fixed and nondegenerate
(`Fcal > 0`, `A u > 0`, `g k > 0`), the species total number density `N` is uniquely
recovered from a single line intensity: equal intensities ⇒ equal `N`. Since the
composition `C_s` is `N_s` up to the closure normalization `∑ C_s = 1`
(`composition_sum_one` in `Closure.lean`), equal `N` for every species gives equal
composition; this lemma is the per-species core.

The map `N ↦ I` is multiplication by the strictly positive constant
`c = Fcal · A_u · g u · exp(−E_u/(k_B T)) / U(T)`, so it is injective but not
trivially so (the constant is genuine physics, so the proof needs
`mul_left_cancel₀`, not `rfl`).

Non-vacuous: `ι = Fin 1`, `kB = T = Fcal = 1`, `g = A = fun _ => 1`,
`E = fun _ => 0`, `u = 0`; then `I = c · N` with `c > 0`, so `N₁ = 3 ≠ N₂ = 5`
give distinct intensities. `T` may be any real (positivity of `T` is *not* needed:
`exp` and the partition function are positive regardless of `T`'s sign). -/
theorem density_identifiability [Nonempty ι]
    {kB T Fcal : ℝ} {g E A : ι → ℝ} {N₁ N₂ : ℝ}
    (hg : ∀ k, 0 < g k) (hFcal : 0 < Fcal) (u : ι) (hA : 0 < A u)
    (hI : lineIntensity kB T N₁ Fcal g E A u = lineIntensity kB T N₂ Fcal g E A u) :
    N₁ = N₂ := by
  have hU : 0 < partitionFunction kB T g E := partitionFunction_pos hg
  simp only [lineIntensity, population] at hI
  -- Pull out the positive constant `c` multiplying `N`.
  set c : ℝ := Fcal * A u * (g u * boltzmannFactor kB T (E u) / partitionFunction kB T g E)
    with hcdef
  have hc : 0 < c := by
    rw [hcdef]
    exact mul_pos (mul_pos hFcal hA)
      (div_pos (mul_pos (hg u) (boltzmannFactor_pos _ _ _)) hU)
  have hI' : c * N₁ = c * N₂ := by rw [hcdef]; linear_combination hI
  exact mul_left_cancel₀ hc.ne' hI'

/-- **Target 3 — electron-density / stage-ratio identifiability via Saha.**

At fixed temperature `T` (hence fixed Saha factor `S = sahaFactor … > 0`), the Saha
density diagnostic `R ↦ n_e = S/R = electronDensityFromRatio` is **injective** on
positive stage ratios: if two positive ratios `R₁, R₂` yield the same inferred
electron density, then `R₁ = R₂`. Equivalently, the diagnostic is invertible — a
measured `n_e` back-determines the stage ratio `R` uniquely. (The forward reading
`n_e = S/R` from a known `R` is, of course, mere function evaluation; the content
here is the converse: no two distinct ratios alias to the same `n_e`.)

This is exactly the injectivity packaged from the proven strict antitonicity
`electronDensity_antitone` (`R ↦ S/R` strictly decreasing on `(0,∞)`). It rests
*only* on `S > 0`; identifiability does not — and need not — re-derive the Saha
factor's internal structure: the exponent sign `−χ/(k_B T)`, the `(3/2)` thermal
power, the spin weight `2`, and the partition-function ratio are certified
separately by `sahaFactor_pos` and the closed form `log_sahaFactor`. (`S = 0` would
make the map constantly `0`, destroying injectivity, so positivity is load-bearing.)

Non-vacuous: with `S > 0` (guaranteed by `sahaFactor_pos` under positive physical
constants/weights) and `R₁ = R₂ = 2`, both sides equal `S/2`; the antitone map
forces `R₁ = R₂`. -/
theorem electron_density_identifiability [Nonempty ι] [Nonempty κ]
    {kB T me h chi : ℝ} {gZ EZ : ι → ℝ} {gZ1 EZ1 : κ → ℝ} {R₁ R₂ : ℝ}
    (hkB : 0 < kB) (hT : 0 < T) (hme : 0 < me) (hh : 0 < h)
    (hgZ : ∀ k, 0 < gZ k) (hgZ1 : ∀ k, 0 < gZ1 k)
    (hR₁ : 0 < R₁) (hR₂ : 0 < R₂)
    (hne : electronDensityFromRatio kB T me h chi gZ EZ gZ1 EZ1 R₁
        = electronDensityFromRatio kB T me h chi gZ EZ gZ1 EZ1 R₂) :
    R₁ = R₂ := by
  -- The inverse map is strictly antitone on `(0,∞)`, hence injective there.
  have hanti : StrictAntiOn (electronDensityFromRatio kB T me h chi gZ EZ gZ1 EZ1)
      (Set.Ioi 0) := electronDensity_antitone hkB hT hme hh hgZ hgZ1
  exact hanti.injOn (Set.mem_Ioi.mpr hR₁) (Set.mem_Ioi.mpr hR₂) hne

/-! ### Non-vacuity witness for `density_identifiability`

`density_identifiability` is the injectivity statement `obs N₁ = obs N₂ → N₁ = N₂` for the forward
observation `obs N = lineIntensity …`. Its non-vacuity rests on the forward map being a GENUINELY
NON-DEGENERATE function of `N` (not a constant). With `ι = Fin 1`, `kB = T = Fcal = g = A = 1`,
`E = 0`, `u = 0`, the forward observation is exactly `obs N = N`:

* The observation is non-degenerate / non-constant — distinct densities give distinct intensities
  (first `example`), so injectivity has real content.
* The antecedent is achievable and the identified quantity is a SPECIFIC non-trivial value: a
  measured intensity equal to `obs 4` pins the density to exactly `N = 4` (second `example`). -/

private def nvIdg : Fin 1 → ℝ := fun _ => 1
private def nvIdE : Fin 1 → ℝ := fun _ => 0
private def nvIdA : Fin 1 → ℝ := fun _ => 1

/-- The forward observation is non-degenerate: distinct densities `3 ≠ 5` yield distinct
intensities, so `density_identifiability` is NOT about a constant map. -/
example :
    lineIntensity 1 1 3 1 nvIdg nvIdE nvIdA 0 ≠ lineIntensity 1 1 5 1 nvIdg nvIdE nvIdA 0 := by
  norm_num [lineIntensity, population, partitionFunction, boltzmannFactor, nvIdg, nvIdE, nvIdA,
    Fin.sum_univ_one]

/-- The antecedent is achievable and the identified density is a specific non-trivial value:
a measured intensity matching `obs 4` forces `N = 4`. -/
example {N : ℝ}
    (hI : lineIntensity 1 1 N 1 nvIdg nvIdE nvIdA 0 = lineIntensity 1 1 4 1 nvIdg nvIdE nvIdA 0) :
    N = 4 :=
  density_identifiability (kB := 1) (T := 1) (Fcal := 1) (g := nvIdg) (E := nvIdE) (A := nvIdA)
    (fun _ => one_pos) one_pos (0 : Fin 1) one_pos hI

/-! ### Quantitative near-degeneracy — the linear-in-`ΔE` conditioning bound

`temperature_degeneracy` is the *exact* `ΔE = 0` statement: at equal upper-level energies the
two-line ratio is constant in `T`. The runtime solver, however, refuses not only at `ΔE = 0` but
for *small* `|E_i − E_j|`; that gate wants a quantitative interpolation. The next theorem supplies
it: the two-temperature ratio difference is bounded LINEARLY in `|E_i − E_j|`. -/

/-- **Elementary exponential slope bound.** For all reals `a, b`,
`exp a − exp b ≤ exp a · (a − b)`. Proof: `exp a − exp b = exp a·(1 − exp(b−a))` and
`1 − exp(b−a) ≤ a − b` from `Real.add_one_le_exp (b − a) : (b − a) + 1 ≤ exp(b − a)` (valid for
every `a, b`, no ordering needed). Private helper (no scope-tag row); pure real analysis. -/
private lemma exp_sub_le_mul (a b : ℝ) :
    Real.exp a - Real.exp b ≤ Real.exp a * (a - b) := by
  have hstep : b - a + 1 ≤ Real.exp (b - a) := Real.add_one_le_exp (b - a)
  have hle : Real.exp a * (1 - Real.exp (b - a)) ≤ Real.exp a * (a - b) :=
    mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos a).le
  have hrw : Real.exp a * (1 - Real.exp (b - a)) = Real.exp a - Real.exp b := by
    have hab : a + (b - a) = b := by ring
    rw [mul_sub, mul_one, ← Real.exp_add, hab]
  rwa [hrw] at hle

/-- **Two-point Lipschitz-type bound for `exp`.** `|exp a − exp b| ≤ max(exp a, exp b)·|a − b|`.
The slope is controlled by the larger endpoint value (the exponential is convex and increasing).
Symmetrising `exp_sub_le_mul` over `le_total b a`. Private helper (no scope-tag row); pure real
analysis. -/
private lemma abs_exp_sub_le (a b : ℝ) :
    |Real.exp a - Real.exp b| ≤ max (Real.exp a) (Real.exp b) * |a - b| := by
  rcases le_total b a with h | h
  · rw [max_eq_left (Real.exp_le_exp.mpr h),
      abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr h)),
      abs_of_nonneg (sub_nonneg.mpr h)]
    exact exp_sub_le_mul a b
  · rw [max_eq_right (Real.exp_le_exp.mpr h),
      abs_sub_comm (Real.exp a) (Real.exp b), abs_sub_comm a b,
      abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr h)),
      abs_of_nonneg (sub_nonneg.mpr h)]
    exact exp_sub_le_mul b a

/-- **Quantitative near-degeneracy — linear-in-`ΔE` temperature-conditioning bound.**

For positive atomic data (`g k > 0`, `A k > 0`), positive densities/calibrations, and any two
temperatures `T₁, T₂` (via their inverse-temperature slots `1/(k_B·T_m)`), the two-line
intensity ratio differs between the two parameter sets by at most a quantity **linear in**
`|E_i − E_j|`:

`|ratio(T₁) − ratio(T₂)| ≤ ((g_j·A_j)/(g_i·A_i)) · C · |E_i − E_j| · |1/(k_B·T₁) − 1/(k_B·T₂)|`,

with the explicit constant `C = max(exp x₁, exp x₂)`, `x_m = (E_i − E_j)/(k_B·T_m)`.

Derivation (all steps EXACT, no approximation of the forward model): by
`lineIntensity_ratio_closed_form` the difference is `(g_j·A_j)/(g_i·A_i)·(exp x₁ − exp x₂)`;
`abs_exp_sub_le` gives `|exp x₁ − exp x₂| ≤ max(exp x₁, exp x₂)·|x₁ − x₂|`; and
`x₁ − x₂ = (E_i − E_j)·(1/(k_B·T₁) − 1/(k_B·T₂))` factors the energy gap out of the argument
difference. Everything (`Fcal`, `N`, the partition function `U`) cancels, exactly as in the
identifiability theorems.

Physics reading: as `ΔE = E_i − E_j → 0` the right-hand side vanishes *linearly* in `ΔE`, so the
temperature-dependence of the observed ratio — the entire signal a two-line thermometer has to
work with — shrinks to zero at a controlled rate. Any measurement noise `ε` of fixed size then
swamps the `O(ΔE)` signal, so `T` inference is ill-conditioned: this is the quantitative,
finite-`ΔE` form of `temperature_degeneracy` (the `ΔE = 0` collapse), and it grounds the strict
solver's *"small `ΔE` ⇒ refuse"* gate in a bound rather than a heuristic threshold. At `E_i = E_j`
the factor `|E_i − E_j|` is `0`, so the bound forces `ratio(T₁) = ratio(T₂)`, recovering
`temperature_degeneracy` as the exact limit (see the witness below). (Ciucci et al. 1999, the
two-line Boltzmann ratio.) -/
theorem temperature_ratio_near_degenerate [Nonempty ι]
    {kB T₁ T₂ N₁ N₂ Fcal₁ Fcal₂ : ℝ} {g E A : ι → ℝ}
    (hg : ∀ k, 0 < g k) (hN₁ : 0 < N₁) (hN₂ : 0 < N₂)
    (hFcal₁ : 0 < Fcal₁) (hFcal₂ : 0 < Fcal₂) (hA : ∀ k, 0 < A k) (i j : ι) :
    |lineIntensity kB T₁ N₁ Fcal₁ g E A j / lineIntensity kB T₁ N₁ Fcal₁ g E A i
        - lineIntensity kB T₂ N₂ Fcal₂ g E A j / lineIntensity kB T₂ N₂ Fcal₂ g E A i|
      ≤ (g j * A j) / (g i * A i)
        * max (Real.exp ((E i - E j) / (kB * T₁))) (Real.exp ((E i - E j) / (kB * T₂)))
        * |E i - E j| * |1 / (kB * T₁) - 1 / (kB * T₂)| := by
  rw [lineIntensity_ratio_closed_form hg hN₁ hFcal₁ hA i j,
    lineIntensity_ratio_closed_form hg hN₂ hFcal₂ hA i j]
  set K := (g j * A j) / (g i * A i) with hK
  have hKpos : 0 < K := by
    rw [hK]; exact div_pos (mul_pos (hg j) (hA j)) (mul_pos (hg i) (hA i))
  set x₁ := (E i - E j) / (kB * T₁) with hx₁
  set x₂ := (E i - E j) / (kB * T₂) with hx₂
  -- Factor the positive prefactor `K` out of the difference and its absolute value.
  have h1 : |K * Real.exp x₁ - K * Real.exp x₂| = K * |Real.exp x₁ - Real.exp x₂| := by
    rw [← mul_sub, abs_mul, abs_of_pos hKpos]
  rw [h1]
  -- Two-point exponential bound.
  have h2 : |Real.exp x₁ - Real.exp x₂|
      ≤ max (Real.exp x₁) (Real.exp x₂) * |x₁ - x₂| := abs_exp_sub_le x₁ x₂
  -- Factor the energy gap out of the argument difference.
  have h3 : |x₁ - x₂| = |E i - E j| * |1 / (kB * T₁) - 1 / (kB * T₂)| := by
    rw [hx₁, hx₂, ← abs_mul]
    congr 1
    ring
  rw [h3] at h2
  calc K * |Real.exp x₁ - Real.exp x₂|
      ≤ K * (max (Real.exp x₁) (Real.exp x₂)
          * (|E i - E j| * |1 / (kB * T₁) - 1 / (kB * T₂)|)) :=
        mul_le_mul_of_nonneg_left h2 hKpos.le
    _ = K * max (Real.exp x₁) (Real.exp x₂)
          * |E i - E j| * |1 / (kB * T₁) - 1 / (kB * T₂)| := by ring

/-- **`ΔE = 0` limit — the bound recovers `temperature_degeneracy`.** Non-vacuity witness for the
near-degeneracy bound: at equal energies (`E i = E j`) the factor `|E_i − E_j|` is `0`, so the
right-hand side is exactly `0`; the bound then forces the ratio difference to `0`, i.e. the ratio
is `T`-independent. So the linear bound genuinely interpolates through the exact degeneracy at
`ΔE = 0` (it is not a slack over-estimate that stays positive there). -/
example [Nonempty ι] {kB T₁ T₂ N₁ N₂ Fcal₁ Fcal₂ : ℝ} {g E A : ι → ℝ}
    (hg : ∀ k, 0 < g k) (hN₁ : 0 < N₁) (hN₂ : 0 < N₂)
    (hFcal₁ : 0 < Fcal₁) (hFcal₂ : 0 < Fcal₂) (hA : ∀ k, 0 < A k)
    (i j : ι) (hE : E i = E j) :
    lineIntensity kB T₁ N₁ Fcal₁ g E A j / lineIntensity kB T₁ N₁ Fcal₁ g E A i
      = lineIntensity kB T₂ N₂ Fcal₂ g E A j / lineIntensity kB T₂ N₂ Fcal₂ g E A i := by
  have hb := temperature_ratio_near_degenerate (kB := kB) (T₁ := T₁) (T₂ := T₂) (E := E)
    hg hN₁ hN₂ hFcal₁ hFcal₂ hA i j
  rw [hE] at hb
  simp only [sub_self, abs_zero, mul_zero, zero_mul] at hb
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hb (abs_nonneg _)))

private def nvNdgg : Fin 2 → ℝ := ![1, 1]
private def nvNdgE : Fin 2 → ℝ := ![0, 1]
private def nvNdgA : Fin 2 → ℝ := ![1, 1]

/-- **Non-vacuity witness — the bounded signal is genuinely non-zero away from degeneracy.** With
distinct energies (`E = ![0,1]`, so `E 0 ≠ E 1`) the two-line ratio is a *non-constant* function
of `T`: at `T = 1` and `T = 2` the ratios genuinely differ (via `temperature_identifiability`
contrapositively — equal ratios would force `1 = 2`). So the near-degeneracy bound bounds a
signal that is truly positive for `ΔE ≠ 0` and only vanishes in the `ΔE → 0` limit; it is not the
trivial `0 ≤ 0`. -/
example :
    lineIntensity 1 1 1 1 nvNdgg nvNdgE nvNdgA 1 / lineIntensity 1 1 1 1 nvNdgg nvNdgE nvNdgA 0
      ≠ lineIntensity 1 2 1 1 nvNdgg nvNdgE nvNdgA 1
          / lineIntensity 1 2 1 1 nvNdgg nvNdgE nvNdgA 0 := by
  intro h
  have hg : ∀ k, 0 < nvNdgg k := fun k => by fin_cases k <;> norm_num [nvNdgg]
  have hA : ∀ k, 0 < nvNdgA k := fun k => by fin_cases k <;> norm_num [nvNdgA]
  have hE : nvNdgE 0 ≠ nvNdgE 1 := by norm_num [nvNdgE]
  have hT : (1 : ℝ) = 2 :=
    temperature_identifiability one_pos one_pos two_pos hg one_pos one_pos one_pos one_pos hA
      0 1 hE h
  norm_num at hT

end CflibsFormal

