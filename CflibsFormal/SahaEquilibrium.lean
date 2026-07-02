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
are proven at fixed `T` — but what remains open is the outer temperature iteration
and — crucially — the *convergence of the fixed-point iteration itself*.  We prove
existence and uniqueness of the fixed point, **not** that the CF-LIBS iterative map
converges to it.

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

end CflibsFormal
