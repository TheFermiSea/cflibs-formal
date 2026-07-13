/-
Copyright (c) 2026 Brian Squires. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Squires
-/
import Mathlib
import CflibsFormal.SahaEquilibrium
import CflibsFormal.MatrixEffects

/-!
# Coupling the ionization-suppression channel with the multi-element fixed point

This module closes the loop between two previously separate legs of the CF-LIBS
formalization:

* the **multi-element coupled charge-neutrality fixed point** — the shared electron density
  `x` solving `x = ∑ s, Ntot s · S s / (x + S s) =: multiElementIonized S Ntot x`, whose
  existence and uniqueness are `SahaEquilibrium.multiElement_exists_pos_fixedPoint` /
  `multiElement_pos_fixedPoint_unique`; and
* the **ionization-suppression channel** — the Saha ion density
  `sahaIonDensity S Ntot n_e = Ntot·S/(S + n_e)` is strictly decreasing in `n_e`
  (`MatrixEffects.sahaIonDensity_antitone`).

The headline is a **comparative-statics** theorem: as a species is made more easily ionized
(a larger Saha coefficient `S s`, e.g. a low-ionization-potential Na/K matrix element) or
more abundant (a larger elemental density `Ntot s`), the shared equilibrium electron density
at the coupled fixed point moves **strictly upward** — more free electrons ⇒ larger `n_e`
(`coupledNe_lt_of_S_lt`, `coupledNe_lt_of_Ntot_lt`; weak `≤` siblings
`coupledNe_le_of_S_le`, `coupledNe_le_of_Ntot_le`; unconditional existential headline
`coupledNe_exists_lt_of_S_lt`).

## Proof architecture

The comparative statics is a monotone-fixed-point argument, deliberately factored so the
physics enters only through pointwise domination of the closure map:

1. **Abstract core** (`coupledFixedPoint_lt_of_map_lt`, `coupledFixedPoint_le_of_map_le`):
   if `f` is antitone on `[0,∞)`, `x = f x`, `y = g y` (both `≥ 0`) and `f y < g y`
   (resp. `≤`), then `x < y` (resp. `≤`). Pure order theory: `y ≤ x` would force
   `x = f x ≤ f y < g y = y`, contradiction. This is the only place the fixed-point
   structure is used, and it needs antitonicity of the *lower* map only.
2. **Pointwise domination** of `multiElementIonized` under a parameter increase
   (`multiElementIonized_le_of_S_le`, `_lt_of_S_lt`, `_le_of_Ntot_le`, `_lt_of_Ntot_lt`):
   each closure term `Ntot s · S s / (z + S s)` is monotone in `S s` and in `Ntot s`, and
   strictly so at a species that strictly increases (with `z > 0` for the `S` channel).
3. **Instantiation** at `f = multiElementIonized S Ntot` (antitone by
   `multiElementIonized_strictAntiOn`) and `g` the raised-parameter map.

## The envelope corollary

`envelope_ionization_matrix_shift` couples all three channels at once. Introducing a more
easily ionized species (a) raises the coupled `n_e` (`x < y`); (b) therefore **suppresses**
a spectator element's ionization — its Saha ion density strictly drops,
`sahaIonDensity Sspec Nspec y < sahaIonDensity Sspec Nspec x`
(`sahaIonDensity_antitone` at the induced shift); yet (c) a **homologous line pair**
(matched upper-level energies `E a = E b`, shared partition-function manifold) has an
intensity ratio that is invariant across the box temperatures `Told, Tnew`
(`MatrixEffects.homologousPair_ratio_temperature_invariant`). In this Boltzmann-only
intensity encoding the homologous ratio depends on neither `T` nor `n_e`, so the induced
`n_e` shift does **not** perturb the reported homologous subcomposition ratio — the matrix
effect on that ratio is not merely bounded but *zero*, a fortiori bounded by the induced
`n_e` shift. The genuine, nonzero matrix effect is the spectator ionization suppression in
clause (b), whose sign and monotone dependence on the `n_e` shift are exactly what the
comparative statics pins down.

## Non-circularity / non-vacuity

There is no approximation being bounded against a same-definition reference: the "moved"
quantity is the exact coupled fixed point, characterized independently of any parameter
change by the previously proven existence/uniqueness. The comparison is between two genuine
fixed points of two different closure maps, so the ordering is a substantive statement, not
an artifact. A fully explicit witness (`Fin 1`, `S = ![1]`, abundances `![2]` vs `![6]`)
exhibits the two coupled fixed points as `1 < 2`; a second witness instantiates the whole
envelope on explicit homologous-pair data.

## Literature and scope

* Core order lemmas and the closure-map domination lemmas are `PURE-MATH` (elementary real
  analysis / monotone comparative statics of fixed points).
* The physical comparative-statics theorems and the envelope are `REDUCED`: fixed
  temperature `T` (hence scalar Saha factors), a two-stage (neutral/singly-ionized) balance
  per element, and exact LTE — the same reductions as `SahaEquilibrium`'s multi-element leg.
  Ionization balance: the Saha–Eggert equation (Griem, *Principles of Plasma Spectroscopy*).
  Electron-density coupling / ionization suppression: Aguilera & Aragón, *Spectrochim. Acta
  B* **62** (2007) 378.
* The reused homologous-pair temperature invariance is `EXACT` (Ciucci et al., *Appl.
  Spectrosc.* **53** (1999) 960; two-line Boltzmann ratio), carried over verbatim from
  `MatrixEffects`.
-/

namespace CflibsFormal

/-! ## Abstract monotone-fixed-point core

The single order-theoretic input: an antitone lower map dominated pointwise by an upper map
forces the corresponding fixed points to be ordered. No calculus, no continuity. -/

/-- **Strict comparative statics of an antitone fixed point** (`PURE-MATH`).  If `f` is
antitone on `[0, ∞)`, `x` is a fixed point of `f` and `y` a fixed point of `g` (both
nonnegative), and `f` lies strictly below `g` at `y`, then `x < y`.  Proof: were `y ≤ x`,
antitonicity gives `f x ≤ f y`, so `x = f x ≤ f y < g y = y ≤ x`, a contradiction. -/
theorem coupledFixedPoint_lt_of_map_lt {f g : ℝ → ℝ}
    (hf : AntitoneOn f (Set.Ici 0)) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hfx : x = f x) (hgy : y = g y) (hlt : f y < g y) : x < y := by
  by_contra hc
  rw [not_lt] at hc
  have hmono : f x ≤ f y := hf (Set.mem_Ici.mpr hy) (Set.mem_Ici.mpr hx) hc
  rw [← hfx] at hmono
  rw [← hgy] at hlt
  linarith

/-- **Weak comparative statics of an antitone fixed point** (`PURE-MATH`).  Same hypotheses
as `coupledFixedPoint_lt_of_map_lt` but with a non-strict domination `f y ≤ g y`, yielding
`x ≤ y`.  The one-directional bound: pointwise domination of the closure map moves the fixed
point in the matching direction. -/
theorem coupledFixedPoint_le_of_map_le {f g : ℝ → ℝ}
    (hf : AntitoneOn f (Set.Ici 0)) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hfx : x = f x) (hgy : y = g y) (hle : f y ≤ g y) : x ≤ y := by
  by_contra hc
  rw [not_le] at hc
  have hmono : f x ≤ f y := hf (Set.mem_Ici.mpr hy) (Set.mem_Ici.mpr hx) hc.le
  rw [← hfx] at hmono
  rw [← hgy] at hle
  linarith

/-! ## Pointwise domination of the closure map under a parameter increase

The physics of "more free electrons": raising any species' abundance `Ntot s`, or its Saha
coefficient `S s`, raises the closure map `multiElementIonized S Ntot` pointwise on `[0,∞)`
(strictly, at a strictly-increased species). -/

section Domination

variable {ι : Type*} [Fintype ι]

/-- **Abundance domination (weak).**  Increasing every elemental density `Ntot s ≤ Ntot' s`
raises the ionized-density closure map pointwise for `z ≥ 0`: each term
`Ntot s · S s / (z + S s)` is increasing in `Ntot s` (positive coefficient
`S s/(z + S s)`).  (`PURE-MATH`.) -/
theorem multiElementIonized_le_of_Ntot_le (S Ntot Ntot' : ι → ℝ) (hS : ∀ s, 0 < S s)
    (hmono : ∀ s, Ntot s ≤ Ntot' s) {z : ℝ} (hz : 0 ≤ z) :
    multiElementIonized S Ntot z ≤ multiElementIonized S Ntot' z := by
  simp only [multiElementIonized]
  refine Finset.sum_le_sum fun s _ => ?_
  have hden : (0 : ℝ) < z + S s := by linarith [hS s]
  have hcoef : (0 : ℝ) ≤ S s / (z + S s) := (div_pos (hS s) hden).le
  rw [mul_div_assoc, mul_div_assoc]
  exact mul_le_mul_of_nonneg_right (hmono s) hcoef

/-- **Abundance domination (strict).**  If moreover some species `s0` is strictly more
abundant (`Ntot s0 < Ntot' s0`), the closure map is raised strictly at every `z ≥ 0`: the
`s0` term strictly increases while the others do not decrease.  (`PURE-MATH`.) -/
theorem multiElementIonized_lt_of_Ntot_lt (S Ntot Ntot' : ι → ℝ) (hS : ∀ s, 0 < S s)
    (hmono : ∀ s, Ntot s ≤ Ntot' s) {s0 : ι} (hs0 : Ntot s0 < Ntot' s0) {z : ℝ}
    (hz : 0 ≤ z) :
    multiElementIonized S Ntot z < multiElementIonized S Ntot' z := by
  simp only [multiElementIonized]
  refine Finset.sum_lt_sum (fun s _ => ?_) ⟨s0, Finset.mem_univ s0, ?_⟩
  · have hden : (0 : ℝ) < z + S s := by linarith [hS s]
    have hcoef : (0 : ℝ) ≤ S s / (z + S s) := (div_pos (hS s) hden).le
    rw [mul_div_assoc, mul_div_assoc]
    exact mul_le_mul_of_nonneg_right (hmono s) hcoef
  · have hden : (0 : ℝ) < z + S s0 := by linarith [hS s0]
    have hcoef : (0 : ℝ) < S s0 / (z + S s0) := div_pos (hS s0) hden
    rw [mul_div_assoc, mul_div_assoc]
    exact mul_lt_mul_of_pos_right hs0 hcoef

/-- **Saha-coefficient domination (weak).**  Increasing every Saha coefficient
`S s ≤ S' s` raises the closure map pointwise for `z ≥ 0`.  Per term it suffices that
`S s/(z + S s) ≤ S' s/(z + S' s)`, which cross-multiplies to `S s · z ≤ S' s · z`
(true since `z ≥ 0`); scale by the nonnegative abundance `Ntot s`.  (`PURE-MATH`.) -/
theorem multiElementIonized_le_of_S_le (S S' Ntot : ι → ℝ) (hS : ∀ s, 0 < S s)
    (hS' : ∀ s, 0 < S' s) (hN : ∀ s, 0 ≤ Ntot s) (hmono : ∀ s, S s ≤ S' s) {z : ℝ}
    (hz : 0 ≤ z) :
    multiElementIonized S Ntot z ≤ multiElementIonized S' Ntot z := by
  simp only [multiElementIonized]
  refine Finset.sum_le_sum fun s _ => ?_
  have hd : (0 : ℝ) < z + S s := by linarith [hS s]
  have hd' : (0 : ℝ) < z + S' s := by linarith [hS' s]
  have hfrac : S s / (z + S s) ≤ S' s / (z + S' s) := by
    rw [div_le_div_iff₀ hd hd']
    nlinarith [mul_nonneg (sub_nonneg.mpr (hmono s)) hz]
  rw [mul_div_assoc, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left hfrac (hN s)

/-- **Saha-coefficient domination (strict).**  If moreover some species `s0` is strictly
more easily ionized (`S s0 < S' s0`) and `z > 0`, the closure map is raised strictly: the
`s0` term strictly increases (the fraction `S s0/(z + S s0)` is strictly increasing in the
Saha coefficient at `z > 0`), scaled by the positive abundance `Ntot s0`.  (`PURE-MATH`.) -/
theorem multiElementIonized_lt_of_S_lt (S S' Ntot : ι → ℝ) (hS : ∀ s, 0 < S s)
    (hS' : ∀ s, 0 < S' s) (hN : ∀ s, 0 < Ntot s) (hmono : ∀ s, S s ≤ S' s) {s0 : ι}
    (hs0 : S s0 < S' s0) {z : ℝ} (hz : 0 < z) :
    multiElementIonized S Ntot z < multiElementIonized S' Ntot z := by
  simp only [multiElementIonized]
  refine Finset.sum_lt_sum (fun s _ => ?_) ⟨s0, Finset.mem_univ s0, ?_⟩
  · have hd : (0 : ℝ) < z + S s := by linarith [hS s]
    have hd' : (0 : ℝ) < z + S' s := by linarith [hS' s]
    have hfrac : S s / (z + S s) ≤ S' s / (z + S' s) := by
      rw [div_le_div_iff₀ hd hd']
      nlinarith [mul_nonneg (sub_nonneg.mpr (hmono s)) hz.le]
    rw [mul_div_assoc, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hfrac (hN s).le
  · have hd : (0 : ℝ) < z + S s0 := by linarith [hS s0]
    have hd' : (0 : ℝ) < z + S' s0 := by linarith [hS' s0]
    have hfrac : S s0 / (z + S s0) < S' s0 / (z + S' s0) := by
      rw [div_lt_div_iff₀ hd hd']
      nlinarith [mul_pos (sub_pos.mpr hs0) hz]
    rw [mul_div_assoc, mul_div_assoc]
    exact mul_lt_mul_of_pos_left hfrac (hN s0)

end Domination

/-! ## Physical comparative statics of the coupled electron density

Combining the abstract core with the closure-map domination: at the coupled charge-neutrality
fixed point, `n_e` is monotone (strictly, at a strictly-increased species) in each species'
Saha coefficient and abundance. -/

section Physical

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- **Ionization comparative statics — the headline (`REDUCED`; Saha–Eggert, Griem).**  Make
one species strictly more easily ionized (`S s0 < S' s0`, all other `S s ≤ S' s`, abundances
`Ntot` fixed and positive).  Then the shared equilibrium electron density at the coupled
charge-neutrality fixed point **strictly increases**: if `x = G_S x` and `y = G_{S'} y` are
the positive coupled fixed points, `x < y`.  More easily ionized matrix ⇒ more free
electrons.  `REDUCED`: fixed `T`, two stages per element, exact LTE. -/
theorem coupledNe_lt_of_S_lt (S S' Ntot : ι → ℝ) (hS : ∀ s, 0 < S s) (hS' : ∀ s, 0 < S' s)
    (hN : ∀ s, 0 < Ntot s) (hmono : ∀ s, S s ≤ S' s) {s0 : ι} (hs0 : S s0 < S' s0)
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hxeq : x = multiElementIonized S Ntot x)
    (hyeq : y = multiElementIonized S' Ntot y) : x < y := by
  have hf : AntitoneOn (multiElementIonized S Ntot) (Set.Ici 0) :=
    (multiElementIonized_strictAntiOn S Ntot hS hN).antitoneOn
  have hlt : multiElementIonized S Ntot y < multiElementIonized S' Ntot y :=
    multiElementIonized_lt_of_S_lt S S' Ntot hS hS' hN hmono hs0 hy
  exact coupledFixedPoint_lt_of_map_lt hf hx.le hy.le hxeq hyeq hlt

/-- **One-directional Saha-coefficient bound (`REDUCED`; Saha–Eggert, Griem).**  Raising all
Saha coefficients weakly (`S s ≤ S' s`) does not decrease the coupled electron density:
`x ≤ y`.  The robust fallback of `coupledNe_lt_of_S_lt` without the strictly-increased
species. -/
theorem coupledNe_le_of_S_le (S S' Ntot : ι → ℝ) (hS : ∀ s, 0 < S s) (hS' : ∀ s, 0 < S' s)
    (hN : ∀ s, 0 < Ntot s) (hmono : ∀ s, S s ≤ S' s)
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hxeq : x = multiElementIonized S Ntot x)
    (hyeq : y = multiElementIonized S' Ntot y) : x ≤ y := by
  have hf : AntitoneOn (multiElementIonized S Ntot) (Set.Ici 0) :=
    (multiElementIonized_strictAntiOn S Ntot hS hN).antitoneOn
  have hle : multiElementIonized S Ntot y ≤ multiElementIonized S' Ntot y :=
    multiElementIonized_le_of_S_le S S' Ntot hS hS' (fun s => (hN s).le) hmono hy.le
  exact coupledFixedPoint_le_of_map_le hf hx.le hy.le hxeq hyeq hle

/-- **Abundance comparative statics (`REDUCED`; Saha–Eggert, Griem).**  Introducing more of
one species (`Ntot s0 < Ntot' s0`, all other `Ntot s ≤ Ntot' s`, Saha coefficients `S`
fixed) **strictly increases** the coupled electron density: `x < y`.  A more abundant
easily-ionized element floods the plasma with electrons. -/
theorem coupledNe_lt_of_Ntot_lt (S Ntot Ntot' : ι → ℝ) (hS : ∀ s, 0 < S s)
    (hN : ∀ s, 0 < Ntot s) (_hN' : ∀ s, 0 < Ntot' s) (hmono : ∀ s, Ntot s ≤ Ntot' s)
    {s0 : ι} (hs0 : Ntot s0 < Ntot' s0) {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hxeq : x = multiElementIonized S Ntot x)
    (hyeq : y = multiElementIonized S Ntot' y) : x < y := by
  have hf : AntitoneOn (multiElementIonized S Ntot) (Set.Ici 0) :=
    (multiElementIonized_strictAntiOn S Ntot hS hN).antitoneOn
  have hlt : multiElementIonized S Ntot y < multiElementIonized S Ntot' y :=
    multiElementIonized_lt_of_Ntot_lt S Ntot Ntot' hS hmono hs0 hy.le
  exact coupledFixedPoint_lt_of_map_lt hf hx.le hy.le hxeq hyeq hlt

/-- **One-directional abundance bound (`REDUCED`; Saha–Eggert, Griem).**  Raising all
abundances weakly (`Ntot s ≤ Ntot' s`) does not decrease the coupled electron density:
`x ≤ y`. -/
theorem coupledNe_le_of_Ntot_le (S Ntot Ntot' : ι → ℝ) (hS : ∀ s, 0 < S s)
    (hN : ∀ s, 0 < Ntot s) (_hN' : ∀ s, 0 < Ntot' s) (hmono : ∀ s, Ntot s ≤ Ntot' s)
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hxeq : x = multiElementIonized S Ntot x)
    (hyeq : y = multiElementIonized S Ntot' y) : x ≤ y := by
  have hf : AntitoneOn (multiElementIonized S Ntot) (Set.Ici 0) :=
    (multiElementIonized_strictAntiOn S Ntot hS hN).antitoneOn
  have hle : multiElementIonized S Ntot y ≤ multiElementIonized S Ntot' y :=
    multiElementIonized_le_of_Ntot_le S Ntot Ntot' hS hmono hy.le
  exact coupledFixedPoint_le_of_map_le hf hx.le hy.le hxeq hyeq hle

/-- **Unconditional existential headline (`REDUCED`; Saha–Eggert, Griem).**  Combining the
comparative statics with existence of the coupled fixed point
(`multiElement_exists_pos_fixedPoint`): making one species strictly more easily ionized
produces two genuine positive coupled fixed points that are strictly ordered.  By uniqueness
(`multiElement_pos_fixedPoint_unique`) these are *the* equilibrium electron densities, so this
is the self-contained statement "the coupled `n_e` strictly increases." -/
theorem coupledNe_exists_lt_of_S_lt (S S' Ntot : ι → ℝ) (hS : ∀ s, 0 < S s)
    (hS' : ∀ s, 0 < S' s) (hN : ∀ s, 0 < Ntot s) (hmono : ∀ s, S s ≤ S' s) {s0 : ι}
    (hs0 : S s0 < S' s0) :
    ∃ x y : ℝ, (0 < x ∧ x = multiElementIonized S Ntot x)
      ∧ (0 < y ∧ y = multiElementIonized S' Ntot y) ∧ x < y := by
  obtain ⟨x, hxpos, hxeq⟩ := multiElement_exists_pos_fixedPoint S Ntot hS hN
  obtain ⟨y, hypos, hyeq⟩ := multiElement_exists_pos_fixedPoint S' Ntot hS' hN
  exact ⟨x, y, ⟨hxpos, hxeq⟩, ⟨hypos, hyeq⟩,
    coupledNe_lt_of_S_lt S S' Ntot hS hS' hN hmono hs0 hxpos hypos hxeq hyeq⟩

end Physical

/-! ## The envelope corollary — coupling all three channels

Introducing a more easily ionized species (i) raises the coupled `n_e`, (ii) therefore
suppresses a spectator element's ionization by the induced shift, while (iii) a homologous
line pair keeps its intensity ratio invariant across the box temperatures. -/

/-- **Ionization-suppression matrix-shift envelope (`REDUCED` comparative statics + `EXACT`
homologous invariance; Saha–Eggert/Griem, Aguilera & Aragón 2007, Ciucci et al. 1999).**
Making one species strictly more easily ionized simultaneously yields:

* `x < y` — the shared coupled electron density strictly increases;
* `sahaIonDensity Sspec Nspec y < sahaIonDensity Sspec Nspec x` — a spectator element's ion
  density strictly **drops**: its ionization is suppressed by exactly the induced `n_e`
  shift (`sahaIonDensity_antitone` at `x < y`); this is the genuine, nonzero matrix effect,
  whose sign is fixed by the comparative statics;
* the **homologous-line-pair** intensity ratio (matched upper-level energies `E a = E b`,
  shared partition-function manifold) is invariant across the box temperatures
  `Told, Tnew` (`homologousPair_ratio_temperature_invariant`).

In this Boltzmann-only intensity encoding the homologous ratio depends on neither `T` nor
`n_e`, so the induced `n_e` shift leaves the reported homologous subcomposition ratio exactly
unchanged (matrix effect zero, a fortiori bounded by the `n_e` shift); the physical residual
lives entirely in the spectator ionization suppression above. -/
theorem envelope_ionization_matrix_shift {ι : Type*} [Fintype ι] [Nonempty ι]
    (S S' Ntot : ι → ℝ) (hS : ∀ s, 0 < S s) (hS' : ∀ s, 0 < S' s) (hN : ∀ s, 0 < Ntot s)
    (hmono : ∀ s, S s ≤ S' s) {s0 : ι} (hs0 : S s0 < S' s0)
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hxeq : x = multiElementIonized S Ntot x)
    (hyeq : y = multiElementIonized S' Ntot y)
    {Sspec Nspec : ℝ} (hSspec : 0 < Sspec) (hNspec : 0 < Nspec)
    {μ : Type*} [Fintype μ] [Nonempty μ]
    {kB Told Tnew Ns Nt Fcal : ℝ} {g E A : μ → ℝ}
    (hg : ∀ k, 0 < g k) (hNt : 0 < Nt) (hFcal : 0 < Fcal) (hA : ∀ k, 0 < A k)
    (a b : μ) (hE : E a = E b) :
    x < y
      ∧ sahaIonDensity Sspec Nspec y < sahaIonDensity Sspec Nspec x
      ∧ lineIntensity kB Told Ns Fcal g E A a / lineIntensity kB Told Nt Fcal g E A b
          = lineIntensity kB Tnew Ns Fcal g E A a / lineIntensity kB Tnew Nt Fcal g E A b := by
  have hxy : x < y :=
    coupledNe_lt_of_S_lt S S' Ntot hS hS' hN hmono hs0 hx hy hxeq hyeq
  refine ⟨hxy, ?_, ?_⟩
  · exact sahaIonDensity_antitone hSspec hNspec (Set.mem_Ioi.mpr hx) (Set.mem_Ioi.mpr hy) hxy
  · exact homologousPair_ratio_temperature_invariant hg hNt hFcal hA a b hE

/-! ## Non-vacuity witnesses

### Explicit coupled fixed points, strictly ordered under an abundance increase

Single species (`ι = Fin 1`), Saha coefficient `S = ![1]`.  With abundance `![2]` the closure
map is `G(x) = 2/(x + 1)`, whose positive fixed point is `1` (`1 = 2/(1 + 1)`); with abundance
`![6]` it is `G(x) = 6/(x + 1)`, positive fixed point `2` (`2 = 6/(2 + 1)`).  So the coupled
electron density moves `1 < 2` as the species is made more abundant — certifying the
comparative-statics theorem is not vacuous, on genuinely distinct explicit fixed points. -/

private def nvS1 : Fin 1 → ℝ := ![1]
private def nvNa : Fin 1 → ℝ := ![2]
private def nvNb : Fin 1 → ℝ := ![6]

private theorem nvfix_a : (1 : ℝ) = multiElementIonized nvS1 nvNa 1 := by
  simp only [multiElementIonized, Fin.sum_univ_one, nvS1, nvNa, Matrix.cons_val_zero]
  norm_num

private theorem nvfix_b : (2 : ℝ) = multiElementIonized nvS1 nvNb 2 := by
  simp only [multiElementIonized, Fin.sum_univ_one, nvS1, nvNb, Matrix.cons_val_zero]
  norm_num

example : ∃ x y : ℝ, (0 < x ∧ x = multiElementIonized nvS1 nvNa x)
    ∧ (0 < y ∧ y = multiElementIonized nvS1 nvNb y) ∧ x < y := by
  refine ⟨1, 2, ⟨one_pos, nvfix_a⟩, ⟨two_pos, nvfix_b⟩, ?_⟩
  refine coupledNe_lt_of_Ntot_lt nvS1 nvNa nvNb
    (fun s => by fin_cases s; norm_num [nvS1])
    (fun s => by fin_cases s; norm_num [nvNa])
    (fun s => by fin_cases s; norm_num [nvNb])
    (fun s => by fin_cases s; norm_num [nvNa, nvNb])
    (show nvNa 0 < nvNb 0 by norm_num [nvNa, nvNb]) one_pos two_pos nvfix_a nvfix_b

/-! ### The full envelope on explicit data

The abundance witness above, promoted to a Saha-coefficient increase (`S = ![1]` raised to
`![2]`, abundance `![2]` fixed) so the strictly-more-ionizable hypothesis applies, together
with a homologous line pair on a shared manifold (`Fin 2`, degeneracies `![2,5]`, MATCHED
energies `![1,1]`, Einstein coefficients `![3,7]`) and a spectator element (`Sspec = Nspec =
1`).  The coupled fixed points come from existence; the envelope then delivers all three
coupled conclusions at once. -/

private def nvES : Fin 1 → ℝ := ![1]
private def nvES' : Fin 1 → ℝ := ![2]
private def nvEN : Fin 1 → ℝ := ![2]
private def nvHg : Fin 2 → ℝ := ![2, 5]
private def nvHE : Fin 2 → ℝ := ![1, 1]
private def nvHA : Fin 2 → ℝ := ![3, 7]

example : ∃ x y : ℝ,
    x < y
      ∧ sahaIonDensity 1 1 y < sahaIonDensity 1 1 x
      ∧ lineIntensity 1 1 4 1 nvHg nvHE nvHA 0 / lineIntensity 1 1 6 1 nvHg nvHE nvHA 1
          = lineIntensity 1 5 4 1 nvHg nvHE nvHA 0 / lineIntensity 1 5 6 1 nvHg nvHE nvHA 1 := by
  have hS : ∀ s, 0 < nvES s := fun s => by fin_cases s; norm_num [nvES]
  have hS' : ∀ s, 0 < nvES' s := fun s => by fin_cases s; norm_num [nvES']
  have hN : ∀ s, 0 < nvEN s := fun s => by fin_cases s; norm_num [nvEN]
  have hmono : ∀ s, nvES s ≤ nvES' s := fun s => by fin_cases s; norm_num [nvES, nvES']
  have hs0 : nvES 0 < nvES' 0 := by norm_num [nvES, nvES']
  have hg : ∀ k, 0 < nvHg k := fun k => by fin_cases k <;> norm_num [nvHg]
  have hA : ∀ k, 0 < nvHA k := fun k => by fin_cases k <;> norm_num [nvHA]
  have hE : nvHE 0 = nvHE 1 := by norm_num [nvHE]
  obtain ⟨x, hxpos, hxeq⟩ := multiElement_exists_pos_fixedPoint nvES nvEN hS hN
  obtain ⟨y, hypos, hyeq⟩ := multiElement_exists_pos_fixedPoint nvES' nvEN hS' hN
  exact ⟨x, y, envelope_ionization_matrix_shift nvES nvES' nvEN hS hS' hN hmono hs0
    hxpos hypos hxeq hyeq one_pos one_pos hg (by norm_num) (by norm_num) hA 0 1 hE⟩

end CflibsFormal

