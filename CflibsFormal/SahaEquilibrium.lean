/-
Copyright (c) 2026 Brian Squires. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Squires
-/
import Mathlib
import CflibsFormal.Saha

/-!
# Coupled Saha–closure–charge self-consistency (reduced core)

The CF-LIBS working loop iterates Saha ionization equilibrium against closure
(mass balance) and charge neutrality to fix the electron density `n_e`.  In the
full pipeline only the *static* facts about each individual equation are proven
(see `Saha.lean`, `Closure.lean`).  This module isolates and closes the
**reduced single-element, two-stage, fixed-temperature core** of that loop and
proves it has a unique self-consistent state.

## The reduced system

Fix the temperature `T`; then the Saha factor `S = sahaFactor … > 0` is a fixed
positive real (positivity: `sahaFactor_pos`).  Fix the total elemental density
`Ntot > 0`.  Split the element into a neutral stage (density `N₀`) and a singly
ionized stage (density `N₁`).  The three loop equations are

* **charge neutrality** `n_e = N₁` (the two-stage form of `chargeNeutrality`,
  neutral charge `0`, singly-ionized charge `1` — see `chargeNeutrality_two_stage`);
* **Saha** `N₁/N₀ = S/n_e`, i.e. the stage ratio `R = N₁/N₀` obeys `R · n_e = S`
  (the structural form of `saha_relation`);
* **closure** `N₀ + N₁ = Ntot`.

Eliminating `N₀ = Ntot − n_e` and `N₁ = n_e` turns the Saha law into the scalar
fixed-point equation

`n_e² = S · (Ntot − n_e)`,

a quadratic with a unique positive root

`n_e = (−S + √(S² + 4·S·Ntot)) / 2`.

We prove existence (`0 < n_e < Ntot`, self-consistency), uniqueness (any positive
solution equals the closed form), and bundle them into the unique existence of the
full self-consistent state `(n_e, N₀, N₁)`.

## Multi-element coupling (appended below)

The multi-element leg (gap #6) couples one two-stage Saha balance per species `s`
through a *shared* electron density `x`.  With Saha factor `S s > 0` and elemental
density `Ntot s > 0`, per-element closure gives the ionized density
`N₁ s = Ntot s · S s / (x + S s)`, and charge neutrality closes the loop as the
scalar fixed-point equation

`x = ∑ s, Ntot s · S s / (x + S s)  =:  multiElementIonized S Ntot x`.

We prove this coupled fixed point **exists** (a positive `x`, via the intermediate
value theorem on `[0, ∑ Ntot]`) and is **unique** (the right-hand side is strictly
antitone in `x`, so `x ↦ x − G(x)` is strictly monotone), and that for a single
species it reproduces `sahaEquilibriumNe`.

## Honest scope

This is the **REDUCED** core, not the full CF-LIBS self-consistency loop.  We fix
`T` (hence a scalar Saha factor `S`), restrict to a *single* element resolved into
*two* stages, and impose exact LTE.  The multi-element section relaxes the
single-element restriction — existence and uniqueness of the coupled fixed point
are proven at fixed `T`.  For the *single*-element scalar core we now also prove
**convergence of the fixed-point iteration** `sahaIter`: it is a geometric
contraction toward `sahaEquilibriumNe` on an explicit invariant interval, so the
iterates converge to the root (see the convergence section below).  What remains
open is the outer temperature iteration and the convergence of the *multi-element*
coupled iteration.

## Literature

The ionization balance is the Saha–Eggert equation (Griem, *Principles of Plasma
Spectroscopy*); the closure + charge-neutrality + Saha coupling used to fix `n_e`
in an LTE LIBS plasma follows the standard treatment (Yalcin 1999).  The scalar
reduction and its quadratic root are elementary algebra (`PURE-MATH`).
-/

namespace CflibsFormal

/-- **Self-consistent electron density** of the reduced single-element, two-stage,
fixed-`T` Saha core: the unique positive root of `n_e² = S · (Ntot − n_e)`,

`n_e = (−S + √(S² + 4·S·Ntot)) / 2`.

Here `S` is the (fixed-temperature) Saha factor `sahaFactor …` and `Ntot` the
total elemental density. -/
noncomputable def sahaEquilibriumNe (S Ntot : ℝ) : ℝ :=
  (-S + Real.sqrt (S ^ 2 + 4 * S * Ntot)) / 2

/-- **Positivity of the self-consistent density.** For a positive Saha factor and
positive total density the equilibrium electron density is strictly positive:
`√(S² + 4·S·Ntot) > √(S²) = S`, so the numerator `−S + √(…)` is positive. -/
theorem sahaEquilibriumNe_pos {S Ntot : ℝ} (hS : 0 < S) (hN : 0 < Ntot) :
    0 < sahaEquilibriumNe S Ntot := by
  have hSD : S < Real.sqrt (S ^ 2 + 4 * S * Ntot) :=
    (Real.lt_sqrt hS.le).mpr (by nlinarith [mul_pos hS hN])
  unfold sahaEquilibriumNe
  linarith

/-- **Self-consistency (fixed-point) equation.** The closed form satisfies the
reduced coupled equation `n_e² = S · (Ntot − n_e)`, obtained by eliminating
`N₀ = Ntot − n_e`, `N₁ = n_e` from Saha × closure × charge neutrality.  The proof
substitutes `(√D)² = D` with `D = S² + 4·S·Ntot`. -/
theorem sahaEquilibriumNe_selfConsistent {S Ntot : ℝ} (hS : 0 < S) (hN : 0 < Ntot) :
    sahaEquilibriumNe S Ntot ^ 2 = S * (Ntot - sahaEquilibriumNe S Ntot) := by
  have hD : (0 : ℝ) ≤ S ^ 2 + 4 * S * Ntot := by positivity
  have hd : Real.sqrt (S ^ 2 + 4 * S * Ntot) ^ 2 = S ^ 2 + 4 * S * Ntot :=
    Real.sq_sqrt hD
  unfold sahaEquilibriumNe
  linear_combination (1 / 4 : ℝ) * hd

/-- **The equilibrium density is below the total density.** Since `n_e > 0` forces
`n_e² > 0`, the self-consistency equation `n_e² = S · (Ntot − n_e)` with `S > 0`
gives `Ntot − n_e > 0`, i.e. the neutral stage `N₀ = Ntot − n_e` is populated. -/
theorem sahaEquilibriumNe_lt_totalDensity {S Ntot : ℝ} (hS : 0 < S) (hN : 0 < Ntot) :
    sahaEquilibriumNe S Ntot < Ntot := by
  have hpos := sahaEquilibriumNe_pos hS hN
  have hsc := sahaEquilibriumNe_selfConsistent hS hN
  have h1 : 0 < S * (Ntot - sahaEquilibriumNe S Ntot) := by
    rw [← hsc]; exact pow_pos hpos 2
  nlinarith [h1, hS]

/-- **Uniqueness of the positive root.** Any strictly positive `x` solving the
reduced self-consistency equation `x² = S · (Ntot − x)` equals the closed form.
Both `x` and `sahaEquilibriumNe S Ntot` are roots of `t² + S·t − S·Ntot = 0`, so
`(x − r)·(x + r + S) = 0`; the second factor is strictly positive, forcing
`x = r`. -/
theorem selfConsistent_unique {S Ntot : ℝ} (hS : 0 < S) (hN : 0 < Ntot)
    {x : ℝ} (hx : 0 < x) (hxeq : x ^ 2 = S * (Ntot - x)) :
    x = sahaEquilibriumNe S Ntot := by
  have hrpos := sahaEquilibriumNe_pos hS hN
  have hreq := sahaEquilibriumNe_selfConsistent hS hN
  have hfac : (x - sahaEquilibriumNe S Ntot) * (x + sahaEquilibriumNe S Ntot + S) = 0 := by
    linear_combination hxeq - hreq
  rcases mul_eq_zero.mp hfac with h | h
  · linarith
  · linarith

/-- **Coupled self-consistency conditions** for a single element split into a
neutral stage (density `N0`) and a singly-ionized stage (density `N1`) at fixed
temperature — hence fixed Saha factor `S > 0` (the scalar produced by `sahaFactor`,
positive by `sahaFactor_pos`) — and fixed total elemental density `Ntot`.  This
bundles the three loop equations of the CF-LIBS Saha–closure–charge cycle:

* `neutrality` — charge neutrality `n_e = N1` in the two-stage form of
  `chargeNeutrality` (neutral charge `0`, singly-ionized charge `1`);
* `closure` — mass closure `N0 + N1 = Ntot`;
* `saha` — the Saha law in the structural form of `saha_relation`: the stage ratio
  `R = N1/N0` obeys `R · n_e = S`. -/
structure SelfConsistentState (S Ntot ne N0 N1 : ℝ) : Prop where
  ne_pos : 0 < ne
  N0_pos : 0 < N0
  N1_pos : 0 < N1
  neutrality : chargeNeutrality (σ := Fin 2) ![0, 1] ![N0, N1] ne
  closure : N0 + N1 = Ntot
  saha : N1 / N0 * ne = S

/-- **Existence of the self-consistent state.** With `n_e = sahaEquilibriumNe S Ntot`,
`N₀ = Ntot − n_e`, `N₁ = n_e`, all three CF-LIBS loop equations (charge neutrality,
closure, Saha) hold with all populations strictly positive.  This is the coupled
system, not bare algebra: neutrality is `chargeNeutrality_two_stage` and the Saha
field is the structural `R · n_e = S`. -/
theorem sahaEquilibrium_selfConsistent {S Ntot : ℝ} (hS : 0 < S) (hN : 0 < Ntot) :
    SelfConsistentState S Ntot (sahaEquilibriumNe S Ntot)
      (Ntot - sahaEquilibriumNe S Ntot) (sahaEquilibriumNe S Ntot) := by
  have hpos := sahaEquilibriumNe_pos hS hN
  have hlt := sahaEquilibriumNe_lt_totalDensity hS hN
  have hsc := sahaEquilibriumNe_selfConsistent hS hN
  have hne : Ntot - sahaEquilibriumNe S Ntot ≠ 0 := by
    have hp : 0 < Ntot - sahaEquilibriumNe S Ntot := by linarith
    exact hp.ne'
  refine ⟨hpos, by linarith, hpos, ?_, by ring, ?_⟩
  · exact chargeNeutrality_two_stage.mpr rfl
  · rw [div_mul_eq_mul_div, div_eq_iff hne]
    linear_combination hsc

/-- **Uniqueness of the self-consistent state.** Any triple `(n_e, N₀, N₁)`
satisfying all three loop equations with positive populations is forced to be
`n_e = sahaEquilibriumNe S Ntot`, `N₀ = Ntot − n_e`, `N₁ = n_e`. -/
theorem selfConsistentState_unique {S Ntot ne N0 N1 : ℝ} (hS : 0 < S) (hN : 0 < Ntot)
    (h : SelfConsistentState S Ntot ne N0 N1) :
    ne = sahaEquilibriumNe S Ntot ∧ N0 = Ntot - sahaEquilibriumNe S Ntot ∧
      N1 = sahaEquilibriumNe S Ntot := by
  obtain ⟨hne_pos, hN0_pos, hN1_pos, hneut, hclose, hsaha⟩ := h
  have hneN1 : ne = N1 := chargeNeutrality_two_stage.mp hneut
  have hN0 : N0 = Ntot - ne := by linarith
  have hne2 : (0 : ℝ) < Ntot - ne := by linarith
  have hself : ne ^ 2 = S * (Ntot - ne) := by
    rw [← hneN1, hN0] at hsaha
    rw [div_mul_eq_mul_div, div_eq_iff hne2.ne'] at hsaha
    linear_combination hsaha
  have hEq : ne = sahaEquilibriumNe S Ntot := selfConsistent_unique hS hN hne_pos hself
  refine ⟨hEq, ?_, ?_⟩
  · rw [hN0, hEq]
  · rw [← hneN1]; exact hEq

/-- **Unique existence of the coupled self-consistent state.** The reduced
single-element, two-stage, fixed-`T` Saha–closure–charge system has exactly one
solution `(n_e, N₀, N₁)`, namely `(sahaEquilibriumNe S Ntot, Ntot − n_e, n_e)`.
This is the headline corollary: the fixed point of the CF-LIBS loop exists and is
unique (its iterative *approximation* is a separate, still-open question). -/
theorem sahaEquilibrium_unique_state {S Ntot : ℝ} (hS : 0 < S) (hN : 0 < Ntot) :
    ∃! t : ℝ × ℝ × ℝ, SelfConsistentState S Ntot t.1 t.2.1 t.2.2 := by
  refine ⟨(sahaEquilibriumNe S Ntot, Ntot - sahaEquilibriumNe S Ntot,
      sahaEquilibriumNe S Ntot), sahaEquilibrium_selfConsistent hS hN, ?_⟩
  rintro ⟨ne, N0, N1⟩ hstate
  obtain ⟨h1, h2, h3⟩ := selfConsistentState_unique hS hN hstate
  simp only [Prod.mk.injEq]
  exact ⟨h1, h2, h3⟩

/-- **Monotonicity in the Saha factor.** At fixed `Ntot > 0` the self-consistent
electron density is strictly increasing in the Saha factor `S`: a hotter plasma
(larger `S`) is more strongly ionized.  Proof by contradiction from the two
self-consistency equations, cancelling the common positive factor `Ntot − n_e`. -/
theorem sahaEquilibriumNe_strictMono_S {Ntot : ℝ} (hN : 0 < Ntot) :
    StrictMonoOn (fun S => sahaEquilibriumNe S Ntot) (Set.Ioi 0) := by
  intro S1 hS1 S2 hS2 hlt
  rw [Set.mem_Ioi] at hS1 hS2
  change sahaEquilibriumNe S1 Ntot < sahaEquilibriumNe S2 Ntot
  by_contra hcon
  rw [not_lt] at hcon
  have h1p := sahaEquilibriumNe_pos hS1 hN
  have h2p := sahaEquilibriumNe_pos hS2 hN
  have h1lt := sahaEquilibriumNe_lt_totalDensity hS1 hN
  have h1sc := sahaEquilibriumNe_selfConsistent hS1 hN
  have h2sc := sahaEquilibriumNe_selfConsistent hS2 hN
  have hsq : sahaEquilibriumNe S2 Ntot ^ 2 ≤ sahaEquilibriumNe S1 Ntot ^ 2 :=
    pow_le_pow_left₀ h2p.le hcon 2
  have hXpos : 0 < Ntot - sahaEquilibriumNe S1 Ntot := by linarith
  have hstep : S2 * (Ntot - sahaEquilibriumNe S1 Ntot)
      ≤ S1 * (Ntot - sahaEquilibriumNe S1 Ntot) :=
    calc S2 * (Ntot - sahaEquilibriumNe S1 Ntot)
        ≤ S2 * (Ntot - sahaEquilibriumNe S2 Ntot) :=
          mul_le_mul_of_nonneg_left (by linarith) hS2.le
      _ = sahaEquilibriumNe S2 Ntot ^ 2 := h2sc.symm
      _ ≤ sahaEquilibriumNe S1 Ntot ^ 2 := hsq
      _ = S1 * (Ntot - sahaEquilibriumNe S1 Ntot) := h1sc
  have hS21 : S2 ≤ S1 := le_of_mul_le_mul_right hstep hXpos
  linarith

/-! ### Non-vacuity witnesses

With `S = 1`, `Ntot = 2` the reduced system has the clean interior solution
`n_e = 1`, `N₀ = 1`, `N₁ = 1` (indeed `1² = 1 · (2 − 1)`), certifying that the
existence and uniqueness theorems are not vacuous. -/

private def nvSeqS : ℝ := 1
private def nvSeqNtot : ℝ := 2

example : sahaEquilibriumNe nvSeqS nvSeqNtot = 1 := by
  have hsqrt : Real.sqrt (nvSeqS ^ 2 + 4 * nvSeqS * nvSeqNtot) = 3 := by
    rw [show nvSeqS ^ 2 + 4 * nvSeqS * nvSeqNtot = (3 : ℝ) ^ 2 by
      norm_num [nvSeqS, nvSeqNtot]]
    exact Real.sqrt_sq (by norm_num)
  unfold sahaEquilibriumNe
  rw [hsqrt]
  norm_num [nvSeqS]

example : SelfConsistentState nvSeqS nvSeqNtot 1 (nvSeqNtot - 1) 1 := by
  have h := sahaEquilibrium_selfConsistent (S := nvSeqS) (Ntot := nvSeqNtot)
    (by norm_num [nvSeqS]) (by norm_num [nvSeqNtot])
  have he : sahaEquilibriumNe nvSeqS nvSeqNtot = 1 := by
    have hsqrt : Real.sqrt (nvSeqS ^ 2 + 4 * nvSeqS * nvSeqNtot) = 3 := by
      rw [show nvSeqS ^ 2 + 4 * nvSeqS * nvSeqNtot = (3 : ℝ) ^ 2 by
        norm_num [nvSeqS, nvSeqNtot]]
      exact Real.sqrt_sq (by norm_num)
    unfold sahaEquilibriumNe
    rw [hsqrt]
    norm_num [nvSeqS]
  rwa [he] at h

/-! ## Multi-element coupled self-consistency

The multi-element leg of gap #6: one two-stage Saha balance per species, coupled
through a shared electron density `x`.  See the module header for the physics and the
reduction taken. -/

/-- **Multi-element ionized-density closure map** `G`.  Summing one two-stage Saha
balance per species, coupled through the shared electron density `x`: species `s`
(Saha factor `S s`, elemental density `Ntot s`) contributes ionized density
`Ntot s · S s / (x + S s)`.  Charge neutrality `x = G(x)` closes the loop.  This is
the multi-element generalization of the single-element core above. -/
noncomputable def multiElementIonized {ι : Type*} [Fintype ι] (S Ntot : ι → ℝ)
    (x : ℝ) : ℝ :=
  ∑ s, Ntot s * S s / (x + S s)

/-- **The ionized-density map is strictly antitone** in the electron density on
`x ≥ 0`.  Each term `Ntot s · S s / (x + S s)` strictly decreases as `x` grows (the
denominator increases, numerator fixed positive); a nonempty finite sum of strictly
decreasing terms is strictly decreasing.  Physically: raising `n_e` shifts every
species toward recombination.  (`PURE-MATH`: bare monotonicity of the closure map.) -/
theorem multiElementIonized_strictAntiOn {ι : Type*} [Fintype ι] [Nonempty ι]
    (S Ntot : ι → ℝ) (hS : ∀ s, 0 < S s) (hN : ∀ s, 0 < Ntot s) :
    StrictAntiOn (multiElementIonized S Ntot) (Set.Ici 0) := by
  intro a ha b hb hab
  rw [Set.mem_Ici] at ha hb
  change (∑ s, Ntot s * S s / (b + S s)) < (∑ s, Ntot s * S s / (a + S s))
  refine Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun s _ => ?_)
  rw [div_lt_div_iff₀ (by linarith [hS s]) (by linarith [hS s])]
  nlinarith [mul_pos (mul_pos (hN s) (hS s)) (sub_pos.mpr hab)]

/-- **Existence of the coupled electron density.**  For a nonempty finite family of
species with positive Saha factors `S s` and positive elemental densities `Ntot s`,
there is a strictly positive electron density `x` solving the coupled
charge-neutrality fixed point `x = ∑ s, Ntot s · S s / (x + S s)`.  Proof: with
`M = ∑ Ntot`, the map `f(x) = x − G(x)` is continuous on `[0, M]`, `f(0) = −M < 0`
and `f(M) = M − G(M) ≥ 0` (each term `Ntot s · S s / (M + S s) ≤ Ntot s`), so the
intermediate value theorem yields a root, positive since `f(0) < 0`.
REDUCED: fixed `T`, two stages per element, exact LTE; the iterative map's
convergence is not addressed. -/
theorem multiElement_exists_pos_fixedPoint {ι : Type*} [Fintype ι] [Nonempty ι]
    (S Ntot : ι → ℝ) (hS : ∀ s, 0 < S s) (hN : ∀ s, 0 < Ntot s) :
    ∃ x, 0 < x ∧ x = multiElementIonized S Ntot x := by
  set M : ℝ := ∑ s, Ntot s with hMdef
  have hMpos : 0 < M := by
    rw [hMdef]; exact Finset.sum_pos (fun i _ => hN i) Finset.univ_nonempty
  have hGcont : ContinuousOn (multiElementIonized S Ntot) (Set.Icc (0 : ℝ) M) := by
    change ContinuousOn (fun x => ∑ s, Ntot s * S s / (x + S s)) (Set.Icc (0 : ℝ) M)
    refine continuousOn_finsetSum Finset.univ (fun s _ => ?_)
    refine ContinuousOn.div continuousOn_const
      ((continuousOn_id' _).add continuousOn_const) ?_
    intro x hx
    have hpos : (0 : ℝ) < x + S s := by have hx0 := hx.1; linarith [hS s]
    exact hpos.ne'
  have hcont : ContinuousOn (fun x => x - multiElementIonized S Ntot x)
      (Set.Icc (0 : ℝ) M) := (continuousOn_id' _).sub hGcont
  have hG0 : multiElementIonized S Ntot 0 = M := by
    change (∑ s, Ntot s * S s / ((0 : ℝ) + S s)) = M
    rw [hMdef]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [zero_add, mul_div_assoc, div_self (hS s).ne', mul_one]
  have hGM : multiElementIonized S Ntot M ≤ M := by
    change (∑ s, Ntot s * S s / (M + S s)) ≤ M
    conv_rhs => rw [hMdef]
    refine Finset.sum_le_sum (fun s _ => ?_)
    rw [div_le_iff₀ (by linarith [hMpos, hS s])]
    nlinarith [mul_pos (hN s) hMpos, hS s]
  have h0 : (fun x => x - multiElementIonized S Ntot x) 0 ≤ 0 := by
    change (0 : ℝ) - multiElementIonized S Ntot 0 ≤ 0
    rw [hG0]; linarith
  have hMle : 0 ≤ (fun x => x - multiElementIonized S Ntot x) M := by
    change (0 : ℝ) ≤ M - multiElementIonized S Ntot M
    linarith [hGM]
  obtain ⟨x, hx, hfx⟩ :=
    intermediate_value_Icc hMpos.le hcont (Set.mem_Icc.mpr ⟨h0, hMle⟩)
  change x - multiElementIonized S Ntot x = 0 at hfx
  have hxeq : x = multiElementIonized S Ntot x := sub_eq_zero.mp hfx
  refine ⟨x, ?_, hxeq⟩
  rcases eq_or_lt_of_le hx.1 with h | h
  · exfalso
    rw [← h, hG0] at hxeq
    linarith [hMpos]
  · exact h

/-- **Uniqueness of the coupled electron density.**  Any two strictly positive
solutions of the coupled fixed point `x = ∑ s, Ntot s · S s / (x + S s)` coincide.
Since `G` is strictly antitone (`multiElementIonized_strictAntiOn`), `x < y` forces
`x = G(x) > G(y) = y`, a contradiction; likewise `y < x`.  REDUCED: same reductions
as the existence theorem. -/
theorem multiElement_pos_fixedPoint_unique {ι : Type*} [Fintype ι] [Nonempty ι]
    (S Ntot : ι → ℝ) (hS : ∀ s, 0 < S s) (hN : ∀ s, 0 < Ntot s)
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hxeq : x = multiElementIonized S Ntot x)
    (hyeq : y = multiElementIonized S Ntot y) : x = y := by
  rcases lt_trichotomy x y with h | h | h
  · exfalso
    have hlt := multiElementIonized_strictAntiOn S Ntot hS hN
      (Set.mem_Ici.mpr hx.le) (Set.mem_Ici.mpr hy.le) h
    rw [← hxeq, ← hyeq] at hlt
    linarith
  · exact h
  · exfalso
    have hlt := multiElementIonized_strictAntiOn S Ntot hS hN
      (Set.mem_Ici.mpr hy.le) (Set.mem_Ici.mpr hx.le) h
    rw [← hxeq, ← hyeq] at hlt
    linarith

/-- **Single-species consistency.**  For one species (`ι = PUnit`) the coupled
multi-element fixed point reduces to the single-element core: any positive solution
of `x = multiElementIonized (fun _ => S₀) (fun _ => Ntot₀) x` equals
`sahaEquilibriumNe S₀ Ntot₀`.  The one-term closure `x = Ntot₀ · S₀ / (x + S₀)`
rearranges to `x² = S₀ · (Ntot₀ − x)`, whose unique positive root is the closed form
(`selfConsistent_unique`).  REDUCED: single element, two stages, fixed `T`. -/
theorem multiElement_single_eq_sahaEquilibriumNe {S0 Ntot0 : ℝ}
    (hS : 0 < S0) (hN : 0 < Ntot0) {x : ℝ} (hx : 0 < x)
    (hxeq : x = multiElementIonized (fun _ : PUnit => S0) (fun _ : PUnit => Ntot0) x) :
    x = sahaEquilibriumNe S0 Ntot0 := by
  have hsum : multiElementIonized (fun _ : PUnit => S0) (fun _ : PUnit => Ntot0) x
      = Ntot0 * S0 / (x + S0) := by
    change (∑ _s : PUnit, Ntot0 * S0 / (x + S0)) = Ntot0 * S0 / (x + S0)
    rw [Finset.univ_unique, Finset.sum_singleton]
  rw [hsum] at hxeq
  have hden : (0 : ℝ) < x + S0 := by linarith
  rw [eq_div_iff hden.ne'] at hxeq
  have hself : x ^ 2 = S0 * (Ntot0 - x) := by linear_combination hxeq
  exact selfConsistent_unique hS hN hx hself

/-! ### Non-vacuity witnesses (multi-element)

Two species with `S = ![1, 1]`, `Ntot = ![1, 1]`: the closure is `G(x) = 2/(x + 1)`,
so `x = G(x)` is `x² + x − 2 = 0`, with positive root `x = 1` (indeed
`1 = 2 · (1 · 1 / (1 + 1)) = 1`).  This certifies that the existence and uniqueness
theorems above are not vacuous. -/

private def nvMseS : Fin 2 → ℝ := ![1, 1]
private def nvMseNtot : Fin 2 → ℝ := ![1, 1]

private theorem nvMseS_pos : ∀ s, 0 < nvMseS s := by
  intro s
  fin_cases s <;> norm_num [nvMseS]

private theorem nvMseNtot_pos : ∀ s, 0 < nvMseNtot s := by
  intro s
  fin_cases s <;> norm_num [nvMseNtot]

example : (1 : ℝ) = multiElementIonized nvMseS nvMseNtot 1 := by
  change (1 : ℝ) = ∑ s, nvMseNtot s * nvMseS s / (1 + nvMseS s)
  simp only [nvMseS, nvMseNtot, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  norm_num

example : ∃ x : ℝ, 0 < x ∧ x = multiElementIonized nvMseS nvMseNtot x :=
  multiElement_exists_pos_fixedPoint nvMseS nvMseNtot nvMseS_pos nvMseNtot_pos

example {x : ℝ} (hx : 0 < x) (hxeq : x = multiElementIonized nvMseS nvMseNtot x) :
    x = 1 := by
  have h1 : (1 : ℝ) = multiElementIonized nvMseS nvMseNtot 1 := by
    change (1 : ℝ) = ∑ s, nvMseNtot s * nvMseS s / (1 + nvMseS s)
    simp only [nvMseS, nvMseNtot, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    norm_num
  exact multiElement_pos_fixedPoint_unique nvMseS nvMseNtot nvMseS_pos nvMseNtot_pos
    hx one_pos hxeq h1

/-! ## Convergence of the scalar fixed-point iteration

The last open leg of gap #6.  The single-element self-consistency equation
`n_e² = S · (Ntot − n_e)` rewrites in fixed-point form `n_e = √(S · (Ntot − n_e))`,
whose natural scalar iteration is `sahaIter`.  We prove this iteration is a geometric
contraction toward the closed-form root `sahaEquilibriumNe S Ntot` on an explicit
invariant interval, hence converges — licensing the solver's convergence flag for the
iteration itself, not merely for the (already established) target fixed point. -/

/-- **Scalar fixed-point iteration map** of the reduced Saha self-consistency equation
`n_e² = S · (Ntot − n_e)`.  Writing it as `n_e = √(S · (Ntot − n_e))`, the natural
iteration is `x ↦ √(S · (Ntot − x))`. -/
noncomputable def sahaIter (S Ntot x : ℝ) : ℝ := Real.sqrt (S * (Ntot - x))

/-- **`sahaEquilibriumNe` is a fixed point of `sahaIter`** (`EXACT`; Saha–Eggert,
Griem).  The closed-form root satisfies `sahaIter S Ntot r = r`: by self-consistency
`S · (Ntot − r) = r²`, and `√(r²) = r` since `r ≥ 0`. -/
theorem sahaIter_fixedPoint {S Ntot : ℝ} (hS : 0 < S) (hN : 0 < Ntot) :
    sahaIter S Ntot (sahaEquilibriumNe S Ntot) = sahaEquilibriumNe S Ntot := by
  have hpos := sahaEquilibriumNe_pos hS hN
  have hsc := sahaEquilibriumNe_selfConsistent hS hN
  unfold sahaIter
  rw [← hsc]
  exact Real.sqrt_sq hpos.le

/-- **Sqrt-difference identity** (`PURE-MATH`).  For `u, v ≥ 0` with `√u + √v > 0`,
`|√u − √v| = |u − v| / (√u + √v)`, from `(√u − √v)(√u + √v) = u − v`. -/
private theorem abs_sqrt_sub_eq {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hpos : 0 < Real.sqrt u + Real.sqrt v) :
    |Real.sqrt u - Real.sqrt v| = |u - v| / (Real.sqrt u + Real.sqrt v) := by
  rw [eq_div_iff hpos.ne', ← abs_of_pos hpos, ← abs_mul]
  congr 1
  have h1 : Real.sqrt u ^ 2 = u := Real.sq_sqrt hu
  have h2 : Real.sqrt v ^ 2 = v := Real.sq_sqrt hv
  linear_combination h1 - h2

/-- **One-step geometric contraction toward the fixed point** (`REDUCED`; Saha–Eggert,
Griem).  Write `r := sahaEquilibriumNe S Ntot`.  On the interval `[0, b]` with
`b < Ntot` and `r ≤ b`, the iteration map contracts distances to `r` by the explicit
factor `q := √S / (2 · √(Ntot − b))`:

`|sahaIter S Ntot x − r| ≤ q · |x − r|`.

Reduction (stated as the sufficient conditions): fixed `T`; single element, two
stages; exact LTE; and the interval hypotheses `b < Ntot`, `r ≤ b`, `x ∈ [0, b]`,
which bound the local slope of `√(S·(Ntot−·))`.  The constant `q` is explicit and
need not be sharp. -/
theorem sahaIter_contraction {S Ntot b x : ℝ} (hS : 0 < S) (hN : 0 < Ntot)
    (hb : b < Ntot) (hrb : sahaEquilibriumNe S Ntot ≤ b) (hxb : x ≤ b) :
    |sahaIter S Ntot x - sahaEquilibriumNe S Ntot|
      ≤ Real.sqrt S / (2 * Real.sqrt (Ntot - b)) * |x - sahaEquilibriumNe S Ntot| := by
  set r := sahaEquilibriumNe S Ntot
  have hrpos : 0 < r := sahaEquilibriumNe_pos hS hN
  have hsc : r ^ 2 = S * (Ntot - r) := sahaEquilibriumNe_selfConsistent hS hN
  have hNb : 0 < Ntot - b := by linarith
  have hSNb : 0 < S * (Ntot - b) := mul_pos hS hNb
  have hden_ne : (2 : ℝ) * Real.sqrt (Ntot - b) ≠ 0 :=
    (mul_pos (by norm_num : (0 : ℝ) < 2) (Real.sqrt_pos.mpr hNb)).ne'
  have hqval : Real.sqrt S / (2 * Real.sqrt (Ntot - b))
      * (2 * Real.sqrt (S * (Ntot - b))) = S := by
    rw [Real.sqrt_mul hS.le]
    rw [show Real.sqrt S / (2 * Real.sqrt (Ntot - b))
          * (2 * (Real.sqrt S * Real.sqrt (Ntot - b)))
        = Real.sqrt S * Real.sqrt S
          * ((2 * Real.sqrt (Ntot - b)) / (2 * Real.sqrt (Ntot - b))) by ring]
    rw [div_self hden_ne, mul_one]
    exact Real.mul_self_sqrt hS.le
  set u := S * (Ntot - x) with hudef
  set v := S * (Ntot - r) with hvdef
  have hu_ge : S * (Ntot - b) ≤ u := by
    rw [hudef]; exact mul_le_mul_of_nonneg_left (by linarith) hS.le
  have hv_ge : S * (Ntot - b) ≤ v := by
    rw [hvdef]; exact mul_le_mul_of_nonneg_left (by linarith) hS.le
  have hu_pos : 0 < u := lt_of_lt_of_le hSNb hu_ge
  have hv_pos : 0 < v := lt_of_lt_of_le hSNb hv_ge
  have hrv : Real.sqrt v = r := by rw [← hsc]; exact Real.sqrt_sq hrpos.le
  have hiter : sahaIter S Ntot x = Real.sqrt u := by unfold sahaIter; rw [hudef]
  have hsqrtSNb_pos : 0 < Real.sqrt (S * (Ntot - b)) := Real.sqrt_pos.mpr hSNb
  have hbound_u : Real.sqrt (S * (Ntot - b)) ≤ Real.sqrt u := Real.sqrt_le_sqrt hu_ge
  have hbound_v : Real.sqrt (S * (Ntot - b)) ≤ Real.sqrt v := Real.sqrt_le_sqrt hv_ge
  have hsum_ge : 2 * Real.sqrt (S * (Ntot - b)) ≤ Real.sqrt u + Real.sqrt v := by linarith
  have hsum_pos : 0 < Real.sqrt u + Real.sqrt v := by linarith
  have habs : |Real.sqrt u - Real.sqrt v| = |u - v| / (Real.sqrt u + Real.sqrt v) :=
    abs_sqrt_sub_eq hu_pos.le hv_pos.le hsum_pos
  have huv : |u - v| = S * |x - r| := by
    rw [hudef, hvdef, show S * (Ntot - x) - S * (Ntot - r) = S * (r - x) by ring,
      abs_mul, abs_of_pos hS, abs_sub_comm r x]
  rw [hiter]
  conv_lhs => rw [← hrv]
  rw [habs, huv, div_le_iff₀ hsum_pos]
  calc S * |x - r|
      = Real.sqrt S / (2 * Real.sqrt (Ntot - b))
          * (2 * Real.sqrt (S * (Ntot - b))) * |x - r| := by rw [hqval]
    _ = Real.sqrt S / (2 * Real.sqrt (Ntot - b)) * |x - r|
          * (2 * Real.sqrt (S * (Ntot - b))) := by ring
    _ ≤ Real.sqrt S / (2 * Real.sqrt (Ntot - b)) * |x - r|
          * (Real.sqrt u + Real.sqrt v) :=
        mul_le_mul_of_nonneg_left hsum_ge (by positivity)

/-- **Interval invariance of the iteration** (`REDUCED`; Saha–Eggert, Griem).  Under
`√(S · Ntot) ≤ b`, the map `sahaIter S Ntot` sends `[0, b]` into `[0, b]`:
`0 ≤ √(S·(Ntot−x))` always, and `√(S·(Ntot−x)) ≤ √(S·Ntot) ≤ b` for `x ≥ 0`.  This is
the invariant interval on which the contraction runs.  Reduction: the sufficient
condition `√(S·Ntot) ≤ b` (with `x ∈ [0, b]`). -/
theorem sahaIter_mapsTo {S Ntot b x : ℝ} (hS : 0 < S)
    (hbN : Real.sqrt (S * Ntot) ≤ b) (hx0 : 0 ≤ x) :
    0 ≤ sahaIter S Ntot x ∧ sahaIter S Ntot x ≤ b := by
  unfold sahaIter
  refine ⟨Real.sqrt_nonneg _, ?_⟩
  calc Real.sqrt (S * (Ntot - x)) ≤ Real.sqrt (S * Ntot) := by
        apply Real.sqrt_le_sqrt; nlinarith [mul_nonneg hS.le hx0]
    _ ≤ b := hbN

/-- **Geometric error decay of the iterates** (`REDUCED`; Saha–Eggert, Griem).  With
`q := √S / (2·√(Ntot − b))`, every iterate started in `[0, b]` obeys
`|(sahaIter S Ntot)^[n] x0 − r| ≤ qⁿ · |x0 − r|`, `r := sahaEquilibriumNe S Ntot`.
Proof: the iterates stay in `[0, b]` (`sahaIter_mapsTo`), so the one-step contraction
`sahaIter_contraction` applies at each step; induct on `n`.  The bound holds for any
`q` (no `q < 1` needed) — it is the explicit per-step decay.  Reduction: the interval
hypotheses `b < Ntot`, `r ≤ b`, `√(S·Ntot) ≤ b`, `x0 ∈ [0, b]`. -/
theorem sahaIter_geometric_error {S Ntot b x0 : ℝ} (hS : 0 < S) (hN : 0 < Ntot)
    (hb : b < Ntot) (hrb : sahaEquilibriumNe S Ntot ≤ b)
    (hbN : Real.sqrt (S * Ntot) ≤ b) (hx0 : 0 ≤ x0) (hx0b : x0 ≤ b) (n : ℕ) :
    |(sahaIter S Ntot)^[n] x0 - sahaEquilibriumNe S Ntot|
      ≤ (Real.sqrt S / (2 * Real.sqrt (Ntot - b))) ^ n
          * |x0 - sahaEquilibriumNe S Ntot| := by
  have hmem : ∀ m, 0 ≤ (sahaIter S Ntot)^[m] x0 ∧ (sahaIter S Ntot)^[m] x0 ≤ b := by
    intro m
    induction m with
    | zero => exact ⟨hx0, hx0b⟩
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact sahaIter_mapsTo hS hbN ih.1
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    calc |sahaIter S Ntot ((sahaIter S Ntot)^[k] x0) - sahaEquilibriumNe S Ntot|
        ≤ Real.sqrt S / (2 * Real.sqrt (Ntot - b))
            * |(sahaIter S Ntot)^[k] x0 - sahaEquilibriumNe S Ntot| :=
          sahaIter_contraction hS hN hb hrb (hmem k).2
      _ ≤ Real.sqrt S / (2 * Real.sqrt (Ntot - b))
            * ((Real.sqrt S / (2 * Real.sqrt (Ntot - b))) ^ k
              * |x0 - sahaEquilibriumNe S Ntot|) :=
          mul_le_mul_of_nonneg_left ih (by positivity)
      _ = (Real.sqrt S / (2 * Real.sqrt (Ntot - b))) ^ (k + 1)
            * |x0 - sahaEquilibriumNe S Ntot| := by ring

/-- **Geometric convergence of the iteration** (`REDUCED`; Saha–Eggert, Griem).  When
the contraction factor `q := √S / (2·√(Ntot − b))` satisfies `q < 1`, the iterates
converge to the closed-form root `r := sahaEquilibriumNe S Ntot` for any start
`x0 ∈ [0, b]`: `(sahaIter S Ntot)^[n] x0 → r`.  Squeeze the error `|·^[n] x0 − r|`
between `0` and `qⁿ · |x0 − r| → 0` (`sahaIter_geometric_error` +
`tendsto_pow_atTop_nhds_zero_of_lt_one`).  Reduction: the same interval hypotheses,
plus `q < 1`. -/
theorem sahaIter_tendsto {S Ntot b x0 : ℝ} (hS : 0 < S) (hN : 0 < Ntot)
    (hb : b < Ntot) (hrb : sahaEquilibriumNe S Ntot ≤ b)
    (hbN : Real.sqrt (S * Ntot) ≤ b)
    (hq : Real.sqrt S / (2 * Real.sqrt (Ntot - b)) < 1)
    (hx0 : 0 ≤ x0) (hx0b : x0 ≤ b) :
    Filter.Tendsto (fun n => (sahaIter S Ntot)^[n] x0) Filter.atTop
      (nhds (sahaEquilibriumNe S Ntot)) := by
  have hq0 : 0 ≤ Real.sqrt S / (2 * Real.sqrt (Ntot - b)) := by positivity
  have hgeom : Filter.Tendsto
      (fun n => (Real.sqrt S / (2 * Real.sqrt (Ntot - b))) ^ n
        * |x0 - sahaEquilibriumNe S Ntot|) Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto
        (fun n : ℕ => (Real.sqrt S / (2 * Real.sqrt (Ntot - b))) ^ n)
        Filter.atTop (nhds 0) := tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq
    simpa using h1.mul_const |x0 - sahaEquilibriumNe S Ntot|
  have habs : Filter.Tendsto
      (fun n => |(sahaIter S Ntot)^[n] x0 - sahaEquilibriumNe S Ntot|)
      Filter.atTop (nhds 0) :=
    squeeze_zero (fun _ => abs_nonneg _)
      (fun n => sahaIter_geometric_error hS hN hb hrb hbN hx0 hx0b n) hgeom
  rw [tendsto_iff_dist_tendsto_zero]
  simpa only [Real.dist_eq] using habs

/-! ### Non-vacuity witness (iteration convergence)

`S = 1`, `Ntot = 2`, `b = 3/2`: all hypotheses of `sahaIter_tendsto` hold at once —
`b < Ntot` (`3/2 < 2`), `r = 1 ≤ 3/2`, `√(S·Ntot) = √2 ≤ 3/2` (as `2 ≤ 9/4`), and
`q = √1 / (2·√(1/2)) = √2/2 < 1` — so the iteration from `x0 = 0 ∈ [0, 3/2]` provably
converges to `sahaEquilibriumNe 1 2 = 1`.  This certifies the convergence theorems are
not vacuous. -/

private def nvSitS : ℝ := 1
private def nvSitNtot : ℝ := 2
private noncomputable def nvSitB : ℝ := 3 / 2

example : Filter.Tendsto (fun n => (sahaIter nvSitS nvSitNtot)^[n] 0) Filter.atTop
    (nhds (sahaEquilibriumNe nvSitS nvSitNtot)) := by
  have hS : (0 : ℝ) < nvSitS := by norm_num [nvSitS]
  have hN : (0 : ℝ) < nvSitNtot := by norm_num [nvSitNtot]
  have hb : nvSitB < nvSitNtot := by norm_num [nvSitB, nvSitNtot]
  have hre : sahaEquilibriumNe nvSitS nvSitNtot = 1 := by
    have hsqrt : Real.sqrt (nvSitS ^ 2 + 4 * nvSitS * nvSitNtot) = 3 := by
      rw [show nvSitS ^ 2 + 4 * nvSitS * nvSitNtot = (3 : ℝ) ^ 2 by
        norm_num [nvSitS, nvSitNtot]]
      exact Real.sqrt_sq (by norm_num)
    unfold sahaEquilibriumNe
    rw [hsqrt]; norm_num [nvSitS]
  have hrb : sahaEquilibriumNe nvSitS nvSitNtot ≤ nvSitB := by rw [hre]; norm_num [nvSitB]
  have hbN : Real.sqrt (nvSitS * nvSitNtot) ≤ nvSitB := by
    rw [show nvSitS * nvSitNtot = (2 : ℝ) by norm_num [nvSitS, nvSitNtot],
      show nvSitB = Real.sqrt ((3 / 2 : ℝ) ^ 2) by
        rw [Real.sqrt_sq (by norm_num)]; norm_num [nvSitB]]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hqlt : Real.sqrt nvSitS / (2 * Real.sqrt (nvSitNtot - nvSitB)) < 1 := by
    rw [show nvSitS = (1 : ℝ) from rfl, Real.sqrt_one,
      show nvSitNtot - nvSitB = (1 / 2 : ℝ) by norm_num [nvSitNtot, nvSitB],
      div_lt_one (by positivity)]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 1 / 2 by norm_num),
      Real.sqrt_nonneg (1 / 2 : ℝ)]
  exact sahaIter_tendsto (b := nvSitB) hS hN hb hrb hbN hqlt (by norm_num)
    (by norm_num [nvSitB])

end CflibsFormal
