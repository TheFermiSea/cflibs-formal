/-
Copyright (c) 2026 Brian Squires. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Squires
-/
import Mathlib
import CflibsFormal.SahaEquilibrium

/-!
# Damped Saha closure iteration converges to the *unique* equilibrium

`SahaEquilibrium.lean` closes the coupled multi-element electron-density loop in three
separate pieces:

* **existence** of a strictly positive coupled fixed point `r = G r`
  (`multiElement_exists_pos_fixedPoint`, via the intermediate value theorem);
* **uniqueness** of that positive fixed point
  (`multiElement_pos_fixedPoint_unique`, from strict antitonicity);
* **convergence** of the damped Krasnoselskii–Mann iterate
  `H := dampedMultiElementIter S Ntot lam` toward a *given* fixed point `r`, with the
  geometric error bound `|H^[n] x0 − r| ≤ (1 − lam)ⁿ · |x0 − r|`
  (`dampedMultiElementIter_geometric_error`, `dampedMultiElementIter_tendsto`).

Each convergence theorem takes the fixed point `r` as a **free hypothesis** — it proves
"the iteration converges to whatever fixed point you hand it", not "the iteration
converges to *the* equilibrium".  This module supplies the missing capstone: it *pins the
limit to the unique equilibrium electron density*.  For any nonnegative start `x0` the
damped iteration converges to a limit `r` that is simultaneously

* strictly positive, `0 < r`;
* a coupled fixed point, `r = G r`;
* **the unique** such positive fixed point (`∀ y, 0 < y → y = G y → y = r`);
* the geometric-error limit, `|H^[n] x0 − r| ≤ (1 − lam)ⁿ · |x0 − r|`.

Nothing new is assumed: the capstone is a synthesis of the three existing legs into the
single statement "damped iteration → equilibrium n_e".  We then specialize to one species,
where the equilibrium is the closed-form root `sahaEquilibriumNe S₀ Ntot₀`, so the abstract
limit becomes the explicit quadratic-root formula.

## Literature and scope

Scope tag: **REDUCED**.  Reductions inherited verbatim from the underlying legs — fixed
temperature `T` (Saha factors `S s` are then fixed positive reals), two ionization stages
per element, exact local thermodynamic equilibrium, and the *damped* (averaged) scheme with
the canonical relaxation `lam := 1/(1 + ∑ Ntot s / S s)`.  The outer temperature loop is
handled separately (`outerContraction_box`, `jointOuterContraction_box`).

Citation: M. Saha, *Ionization in the solar chromosphere*, Phil. Mag. 40 (1920) 472;
Saha–Eggert equation as presented in H. R. Griem, *Principles of Plasma Spectroscopy*
(Cambridge Univ. Press, 1997), §5.  The Krasnoselskii–Mann averaged-iteration convergence
rate is the standard fixed-point-iteration bound (Banach contraction principle).
-/

namespace CflibsFormal

open scoped BigOperators

section EquilibriumCapstone

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- **Damped closure iteration converges to the unique equilibrium electron density**
(`REDUCED`; Saha–Eggert, Griem) — *the equilibrium capstone*.  Fix a nonempty finite
species family with positive Saha factors `S s` and positive elemental densities `Ntot s`,
and take the canonical relaxation `lam := 1/(1 + ∑ Ntot s / S s)`.  Then from **any**
nonnegative start `x0` there is a limit `r` that is at once
(1) strictly positive, (2) a coupled fixed point `r = G r` with `G := multiElementIonized
S Ntot`, (3) **the unique** positive fixed point, (4) the limit of the damped orbit, and
(5) approached at the geometric rate `(1 − lam)ⁿ`.  Unlike the underlying convergence
lemmas, `r` is *not* a free hypothesis: existence (`multiElement_exists_pos_fixedPoint`)
produces it, uniqueness (`multiElement_pos_fixedPoint_unique`) certifies it is the
equilibrium, and `dampedMultiElementIter_tendsto` / `dampedMultiElementIter_geometric_error`
route the orbit to it.  This is the statement "the CF-LIBS electron-density iteration
converges to the equilibrium n_e".  Reduction: fixed `T`, two stages per element, exact
LTE; the damped (averaged) scheme; outer `T`-loop separate. -/
theorem dampedMultiElementIter_converges_to_equilibrium (S Ntot : ι → ℝ)
    (hS : ∀ s, 0 < S s) (hN : ∀ s, 0 < Ntot s) {lam : ℝ}
    (hlamval : lam = 1 / (1 + ∑ s, Ntot s / S s)) {x0 : ℝ} (hx0 : 0 ≤ x0) :
    ∃ r, 0 < r ∧ r = multiElementIonized S Ntot r
      ∧ (∀ y, 0 < y → y = multiElementIonized S Ntot y → y = r)
      ∧ Filter.Tendsto (fun n => (dampedMultiElementIter S Ntot lam)^[n] x0)
          Filter.atTop (nhds r)
      ∧ (∀ n, |(dampedMultiElementIter S Ntot lam)^[n] x0 - r|
          ≤ (1 - lam) ^ n * |x0 - r|) := by
  obtain ⟨r, hrpos, hrfix⟩ := multiElement_exists_pos_fixedPoint S Ntot hS hN
  refine ⟨r, hrpos, hrfix, ?_, ?_, ?_⟩
  · intro y hy hyeq
    exact multiElement_pos_fixedPoint_unique S Ntot hS hN hy hrpos hyeq hrfix
  · exact dampedMultiElementIter_tendsto S Ntot hS hN hlamval hrpos.le hrfix hx0
  · intro n
    exact dampedMultiElementIter_geometric_error S Ntot hS hN hlamval hrpos.le hrfix hx0 n

end EquilibriumCapstone

/-- **Single-species damped iteration converges to the closed-form root** (`REDUCED`;
Saha–Eggert, Griem).  For one species (`ι = PUnit`) the coupled equilibrium is the explicit
quadratic root `sahaEquilibriumNe S₀ Ntot₀ = (−S₀ + √(S₀² + 4 S₀ Ntot₀))/2`.  With the
canonical relaxation the damped orbit from any nonnegative start converges to *that closed
form*: `(dampedMultiElementIter (fun _ => S₀) (fun _ => Ntot₀) lam)^[n] x0 →
sahaEquilibriumNe S₀ Ntot₀`.  Proof: existence gives a positive fixed point `r`, which by
`multiElement_single_eq_sahaEquilibriumNe` equals the closed form, so the closed form is a
positive fixed point; then `dampedMultiElementIter_tendsto` sends the orbit to it.  This
turns the abstract equilibrium limit into the concrete algebraic formula.  Reduction: one
element, two stages, fixed `T`, exact LTE. -/
theorem dampedIter_single_converges_to_sahaEquilibriumNe {S0 Ntot0 : ℝ}
    (hS : 0 < S0) (hN : 0 < Ntot0) {lam : ℝ}
    (hlamval : lam = 1 / (1 + ∑ _s : PUnit, Ntot0 / S0)) {x0 : ℝ} (hx0 : 0 ≤ x0) :
    Filter.Tendsto
      (fun n => (dampedMultiElementIter (fun _ : PUnit => S0)
        (fun _ : PUnit => Ntot0) lam)^[n] x0)
      Filter.atTop (nhds (sahaEquilibriumNe S0 Ntot0)) := by
  obtain ⟨r, hrpos, hrfix⟩ :=
    multiElement_exists_pos_fixedPoint (fun _ : PUnit => S0) (fun _ : PUnit => Ntot0)
      (fun _ => hS) (fun _ => hN)
  have hreq : r = sahaEquilibriumNe S0 Ntot0 :=
    multiElement_single_eq_sahaEquilibriumNe hS hN hrpos hrfix
  have hne_pos : 0 < sahaEquilibriumNe S0 Ntot0 := hreq ▸ hrpos
  have hne_fix : sahaEquilibriumNe S0 Ntot0
      = multiElementIonized (fun _ : PUnit => S0) (fun _ : PUnit => Ntot0)
          (sahaEquilibriumNe S0 Ntot0) := by
    rw [← hreq]; exact hrfix
  exact dampedMultiElementIter_tendsto (fun _ : PUnit => S0) (fun _ : PUnit => Ntot0)
    (fun _ => hS) (fun _ => hN) hlamval hne_pos.le hne_fix hx0

/-! ### Non-vacuity witness

Two species with `S = ![1, 1]`, `Ntot = ![1, 1]`: the closure is `G(x) = 2/(x + 1)`, whose
unique positive fixed point is `x = 1` (indeed `2 · (1/(1 + 1)) = 1`).  The canonical
relaxation is `lam = 1/(1 + (1/1 + 1/1)) = 1/3`.  We feed this concrete data through the
capstone and additionally pin the equilibrium to the explicit value `1`, so the damped
iteration from `x0 = 0` provably converges to `nhds 1`.  This certifies the capstone is not
vacuous — its hypotheses are simultaneously satisfiable and its conclusion has real
content on explicit numbers. -/

private def nvcS : Fin 2 → ℝ := ![1, 1]
private def nvcN : Fin 2 → ℝ := ![1, 1]
private noncomputable def nvclam : ℝ := 1 / (1 + ∑ s, nvcN s / nvcS s)

private theorem nvcS_pos : ∀ s, 0 < nvcS s := by
  intro s; fin_cases s <;> norm_num [nvcS]

private theorem nvcN_pos : ∀ s, 0 < nvcN s := by
  intro s; fin_cases s <;> norm_num [nvcN]

private theorem nvc_one_fix : (1 : ℝ) = multiElementIonized nvcS nvcN 1 := by
  change (1 : ℝ) = ∑ s, nvcN s * nvcS s / (1 + nvcS s)
  rw [Fin.sum_univ_two]
  norm_num [nvcS, nvcN]

/-- Non-vacuity: for `S = Ntot = ![1, 1]` the damped orbit from `0` converges to the
concrete equilibrium `1`.  Extracted from the capstone, whose uniqueness clause forces the
limit to equal the explicit fixed point `1`. -/
example :
    Filter.Tendsto (fun n => (dampedMultiElementIter nvcS nvcN nvclam)^[n] 0)
      Filter.atTop (nhds 1) := by
  obtain ⟨r, _, _, huniq, htend, _⟩ :=
    dampedMultiElementIter_converges_to_equilibrium nvcS nvcN nvcS_pos nvcN_pos
      (lam := nvclam) rfl (le_refl (0 : ℝ))
  have h1r : (1 : ℝ) = r := huniq 1 one_pos nvc_one_fix
  rwa [← h1r] at htend

end CflibsFormal
