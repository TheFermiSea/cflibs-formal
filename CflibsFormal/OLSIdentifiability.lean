/-
Copyright (c) 2026 Brian Squires. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Squires
-/
import Mathlib
import CflibsFormal.OLS
import CflibsFormal.JointIdentifiability

/-!
# CF-LIBS formalization — n-line Boltzmann-plot identifiability (design-map injectivity)

`OLS.lean` proves the noise-free recovery `ols_recovers_line` (exactly collinear points ⇒ exact
slope and intercept) and the rank gate `designNormalMatrix_det_ne_zero_iff`
(`det (XᵀX) ≠ 0 ↔ 0 < SS_E`). `JointIdentifiability.lean` closes the **two-line** joint
`(T, composition)` identifiability (`joint_identifiability`), whose sole nondegeneracy input is a
*distinct-energy line pair* on some species (`hEdist : p.E (emitA s₀) ≠ p.E (emitB s₀)`).

This module supplies the **n-line linear-algebra bridge** between those two layers: it exhibits
the Boltzmann parameter → observation map as a matrix–vector product and proves it **injective**
exactly when the excitation energies are not all equal.

* `boltzmannDesign` — the two-column design `X : Matrix (Fin n) (Fin 2) ℝ` with row `k` equal to
  `(1, E k)`, so `(X *ᵥ θ) k = θ 0 + E k · θ 1` is the Boltzmann-plot ordinate for
  `θ = (intercept, slope)`.
* `boltzmannDesign_mulVec_injective` — **the target.** If two energies differ
  (`∃ i j, E i ≠ E j`), the linear map `θ ↦ X *ᵥ θ` is injective: `X *ᵥ u = 0` forces
  `u 0 + E k · u 1 = 0` for all `k`, two distinct energies kill `u 1` then `u 0`, so the kernel is
  trivial.
* `boltzmannDesign_mulVec_injective_iff` — the **exact** characterization: injective ⟺ two
  energies differ (the constant-energy design has the nonzero kernel vector `(-E i₀, 1)`).
* `boltzmannDesign_mulVec_injective_iff_pos_var` / `…_iff_det` — the same condition re-expressed
  as **positive energy variance** `0 < SS_E` and as **full column rank** `det (XᵀX) ≠ 0`, tying
  the injectivity to the existing OLS rank gate (`designNormalMatrix_det_ne_zero_iff`).
* `boltzmann_params_unique` — the identifiability payoff: the fitted `(intercept, slope)` is the
  **unique** pair reproducing the Boltzmann-plot ordinates. *Under* the invertible Boltzmann
  reparametrization `slope = −1/(k_B T)`, `intercept = log(F_cal·N/U)` (interpretation only —
  see the scope note; no physics enters the theorem) this reads as a unique `(T, N)`.
* `twoLine_design_injective_of_distinct` / `twoLine_boltzmannDesign_injective_of_hEdist` — the
  **consistency with the two-line layer**: at `n = 2` the injectivity condition `E 0 ≠ E 1` is
  *exactly* the distinct-energy hypothesis `hEdist` that powers `joint_identifiability`, so the
  n-line linear map generalizes the two-line result on precisely the same nondegeneracy.

## Literature and scope

Scope tag: **PURE-MATH** (consistent with the OLS layer it sits in: `ols_recovers_line`,
`designNormalMatrix_det_ne_zero_iff` are PURE-MATH). The injectivity is an exact algebraic
identity — trivial kernel of the two-column design map, proved by a two-point elimination with no
approximation — and the `iff`/variance/determinant restatements are exact equivalences; no physics
enters the theorem statements (the `(T, N)` reading below is interpretation only). The physical
reading (Boltzmann plot: `y_k = log(F_cal N/U) − E_k/(k_B T)`, so the fit recovers `(T, N)`) is the
Boltzmann-plot method; the formal content here is kept as **pure linear algebra** of the
two-column design, so citation "—" (see `OLS.ols_recovers_line` / `designNormalMatrix` for the
Tognoni et al. 2010 / Ciucci et al. 1999 provenance of the estimator this map underlies).

Non-vacuity: an `n = 3`, `E = ![0,1,2]` injective witness, a degenerate `E = ![1,1]`
*non*-injective witness (the condition is necessary, not decorative), and an `n = 2` distinct
witness tying back to the two-line layer.
-/

namespace CflibsFormal

open Finset Real Matrix
open scoped BigOperators

variable {n : ℕ}

/-- **The two-column Boltzmann-plot design matrix.** `X : Matrix (Fin n) (Fin 2) ℝ` with row `k`
equal to `(1, E k)`: the constant regressor in column `0` and the excitation energy `E k` in
column `1`. Then `(X *ᵥ θ) k = θ 0 + E k · θ 1` is the affine Boltzmann-plot ordinate at line `k`
for the parameter vector `θ = (intercept, slope)`. Pure linear algebra of the two-column design
(no physics content in the definition itself). This is the row form of the OLS Boltzmann design;
its Gram matrix `Xᵀ X` agrees with `OLS.designNormalMatrix E` **only up to the column order**
(`OLS.lean` orders the columns `[E | 1]`, this file `[1 | E]`), so the two are *not* the same
matrix but are related by a symmetric row/column permutation (orthogonally similar), so share
determinant, rank and spectrum (hence conditioning); the determinant equality is all the `_iff_det`
bridge below relies on. -/
def boltzmannDesign (E : Fin n → ℝ) : Matrix (Fin n) (Fin 2) ℝ := fun k => ![1, E k]

/-- **The design map is the affine Boltzmann-plot ordinate.**
`(boltzmannDesign E *ᵥ θ) k = θ 0 + E k · θ 1`. Unfolds the `2`-term matrix–vector sum
`∑ⱼ X k j · θ j` over the two columns `(1, E k)`. -/
theorem boltzmannDesign_mulVec_apply (E : Fin n → ℝ) (θ : Fin 2 → ℝ) (k : Fin n) :
    (boltzmannDesign E *ᵥ θ) k = θ 0 + E k * θ 1 := by
  simp only [boltzmannDesign, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- **Trivial kernel from two distinct energies.** If some pair of energies differ
(`∃ i j, E i ≠ E j`) and `boltzmannDesign E *ᵥ u = 0`, then `u = 0`. The kernel equation reads
`u 0 + E k · u 1 = 0` for every line `k`; subtracting it at the two distinct-energy indices gives
`(E i − E j) · u 1 = 0`, so `u 1 = 0`, and then `u 0 = 0`. This is the exact algebraic core of
the design map's injectivity. -/
theorem boltzmannDesign_mulVec_eq_zero {E : Fin n → ℝ} (hdist : ∃ i j, E i ≠ E j)
    {u : Fin 2 → ℝ} (hu : boltzmannDesign E *ᵥ u = 0) : u = 0 := by
  obtain ⟨i, j, hij⟩ := hdist
  have hi : u 0 + E i * u 1 = 0 := by
    have h := congrFun hu i; rw [boltzmannDesign_mulVec_apply] at h; simpa using h
  have hj : u 0 + E j * u 1 = 0 := by
    have h := congrFun hu j; rw [boltzmannDesign_mulVec_apply] at h; simpa using h
  have h1 : (E i - E j) * u 1 = 0 := by linear_combination hi - hj
  have hu1 : u 1 = 0 := by
    rcases mul_eq_zero.1 h1 with h | h
    · exact absurd (sub_eq_zero.1 h) hij
    · exact h
  have hu0 : u 0 = 0 := by rw [hu1, mul_zero, add_zero] at hi; exact hi
  funext k
  fin_cases k
  · simpa using hu0
  · simpa using hu1

/-- **THE TARGET — the Boltzmann parameter → observation map is injective.** When some pair of
excitation energies differ (`∃ i j, E i ≠ E j`, equivalently positive energy variance / full
column rank of `X`), the linear map `θ ↦ boltzmannDesign E *ᵥ θ` sending `(intercept, slope)` to
the vector of Boltzmann-plot ordinates is injective. Proof: `X *ᵥ a = X *ᵥ b` gives
`X *ᵥ (a − b) = 0`, whose kernel is trivial (`boltzmannDesign_mulVec_eq_zero`), so `a = b`. This
is the n-line generalization of the two-line temperature/composition identifiability, at the
linear-algebra (Boltzmann-plot) layer. -/
theorem boltzmannDesign_mulVec_injective {E : Fin n → ℝ} (hdist : ∃ i j, E i ≠ E j) :
    Function.Injective (fun θ : Fin 2 → ℝ => boltzmannDesign E *ᵥ θ) := by
  intro a b hab
  simp only at hab
  have hker : boltzmannDesign E *ᵥ (a - b) = 0 := by
    rw [Matrix.mulVec_sub, hab, sub_self]
  exact sub_eq_zero.1 (boltzmannDesign_mulVec_eq_zero hdist hker)

/-- **Uniqueness of the recovered `(intercept, slope)`.** If two parameter vectors `θ`, `θ'`
reproduce the same Boltzmann-plot ordinates on every line (`θ 0 + E k · θ 1 = θ' 0 + E k · θ' 1`
for all `k`) and some two energies differ, then `θ = θ'`. This is pure-algebra uniqueness of the
affine coefficients `(intercept, slope)`. *Under the standard invertible Boltzmann
reparametrization* `slope = −1/(k_B T)`, `intercept = log(F_cal·N/U)` (Ciucci 1999 — which requires
the physical forward map, positivity/calibration and the partition function, supplied elsewhere in
the spec, not here), it is the linear-algebra *shadow* of unique temperature/column-density
recovery: the coefficient-level payoff of the design map's injectivity, not a standalone proof of
physical `(T, N)` identifiability. -/
theorem boltzmann_params_unique {E : Fin n → ℝ} (hdist : ∃ i j, E i ≠ E j)
    {θ θ' : Fin 2 → ℝ} (h : ∀ k, θ 0 + E k * θ 1 = θ' 0 + E k * θ' 1) : θ = θ' := by
  refine boltzmannDesign_mulVec_injective hdist ?_
  funext k
  change (boltzmannDesign E *ᵥ θ) k = (boltzmannDesign E *ᵥ θ') k
  rw [boltzmannDesign_mulVec_apply, boltzmannDesign_mulVec_apply]
  exact h k

/-- **Necessity of distinct energies (the degenerate direction).** If all energies coincide
(`∀ i j, E i = E j`, e.g. a single line or a constant-energy design) the design map is *not*
injective: for nonempty `Fin n` the vector `(−E i₀, 1)` lies in the kernel
(`−E i₀ + E i₀ · 1 = 0` on every line), and for empty `Fin n` every parameter maps to the empty
observation; either way a nonzero vector collides with `0`. This shows the distinct-energy
hypothesis of `boltzmannDesign_mulVec_injective` is exactly necessary. -/
theorem boltzmannDesign_mulVec_not_injective_of_forall_eq {E : Fin n → ℝ}
    (hconst : ∀ i j, E i = E j) :
    ¬ Function.Injective (fun θ : Fin 2 → ℝ => boltzmannDesign E *ᵥ θ) := by
  intro hinj
  by_cases hne : Nonempty (Fin n)
  · obtain ⟨i0⟩ := hne
    have hk : boltzmannDesign E *ᵥ (![- E i0, 1] : Fin 2 → ℝ)
        = boltzmannDesign E *ᵥ (0 : Fin 2 → ℝ) := by
      funext k
      rw [boltzmannDesign_mulVec_apply, boltzmannDesign_mulVec_apply, hconst k i0]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply]
      ring
    have h0 : (![- E i0, 1] : Fin 2 → ℝ) = 0 := hinj hk
    have h1 := congrFun h0 1
    simp only [Matrix.cons_val_one, Pi.zero_apply] at h1
    exact one_ne_zero h1
  · rw [not_nonempty_iff] at hne
    have hk : boltzmannDesign E *ᵥ (![0, 1] : Fin 2 → ℝ)
        = boltzmannDesign E *ᵥ (0 : Fin 2 → ℝ) := by
      funext k; exact (IsEmpty.false k).elim
    have h0 : (![0, 1] : Fin 2 → ℝ) = 0 := hinj hk
    have h1 := congrFun h0 1
    simp only [Matrix.cons_val_one, Pi.zero_apply] at h1
    exact one_ne_zero h1

/-- **Exact characterization: injective ⟺ two energies differ.** The Boltzmann design map is
injective if and only if the excitation energies are not all equal — combining the sufficiency
(`boltzmannDesign_mulVec_injective`) and the necessity
(`boltzmannDesign_mulVec_not_injective_of_forall_eq`). -/
theorem boltzmannDesign_mulVec_injective_iff {E : Fin n → ℝ} :
    Function.Injective (fun θ : Fin 2 → ℝ => boltzmannDesign E *ᵥ θ) ↔ ∃ i j, E i ≠ E j := by
  constructor
  · intro hinj
    by_contra h
    push Not at h
    exact boltzmannDesign_mulVec_not_injective_of_forall_eq h hinj
  · exact boltzmannDesign_mulVec_injective

/-- **Distinct energies ⟺ positive energy variance.** For a nonempty index set, some two entries
differ iff the sum of squared deviations `SS_E = ∑ₖ (Eₖ − Ē)²` is positive. This is the bridge
between the elementary "two distinct energies" hypothesis of the kernel argument and the
`0 < SS_E` nondegeneracy used throughout the OLS layer. Pure algebra. -/
theorem exists_distinct_iff_pos_var {ι : Type*} [Fintype ι] [Nonempty ι] (E : ι → ℝ) :
    (∃ i j, E i ≠ E j) ↔ 0 < ∑ k, (E k - mean E) ^ 2 := by
  have hcard : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hnn : 0 ≤ ∑ k, (E k - mean E) ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
  constructor
  · rintro ⟨i, j, hij⟩
    rcases lt_or_eq_of_le hnn with h | h
    · exact h
    · exfalso
      have hall : ∀ k ∈ Finset.univ, (E k - mean E) ^ 2 = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg fun k _ => sq_nonneg _).1 h.symm
      have hi : E i = mean E := by
        have h := hall i (Finset.mem_univ i); rw [sq_eq_zero_iff, sub_eq_zero] at h; exact h
      have hj : E j = mean E := by
        have h := hall j (Finset.mem_univ j); rw [sq_eq_zero_iff, sub_eq_zero] at h; exact h
      exact hij (hi.trans hj.symm)
  · intro hpos
    by_contra h
    push Not at h
    obtain ⟨i0⟩ := ‹Nonempty ι›
    have hmean : mean E = E i0 := by
      unfold mean
      rw [Finset.sum_congr rfl (fun k _ => h k i0), Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul]
      field_simp
    have hz : ∑ k, (E k - mean E) ^ 2 = 0 := by
      apply Finset.sum_eq_zero
      intro k _
      rw [hmean, h k i0]; ring
    rw [hz] at hpos
    exact lt_irrefl 0 hpos

/-- **Injective ⟺ positive energy variance.** The design map is injective exactly when
`0 < SS_E = ∑ₖ (Eₖ − Ē)²` — the standing OLS nondegeneracy (`ols_recovers_line`'s `hvar`). Needs
`[NeZero n]` so `Fin n` is nonempty. -/
theorem boltzmannDesign_mulVec_injective_iff_pos_var [NeZero n] (E : Fin n → ℝ) :
    Function.Injective (fun θ : Fin 2 → ℝ => boltzmannDesign E *ᵥ θ)
      ↔ 0 < ∑ k, (E k - mean E) ^ 2 :=
  boltzmannDesign_mulVec_injective_iff.trans (exists_distinct_iff_pos_var E)

/-- **Injective ⟺ full column rank of the design (nonsingular normal matrix).** The design map is
injective exactly when `(designNormalMatrix E).det ≠ 0` (the Gram matrix `XᵀX` here is
`designNormalMatrix E` only *up to column order*, so they are not equal but share this determinant).
This closes the loop with the runtime rank gate
`designNormalMatrix_det_ne_zero_iff` (`OLS.lean`): "the parameter → observation map is injective"
and "the normal equations are invertible" are the *same* condition on the `n`-line design —
positive energy variance / full column rank. -/
theorem boltzmannDesign_mulVec_injective_iff_det [NeZero n] (E : Fin n → ℝ) :
    Function.Injective (fun θ : Fin 2 → ℝ => boltzmannDesign E *ᵥ θ)
      ↔ (designNormalMatrix E).det ≠ 0 :=
  (boltzmannDesign_mulVec_injective_iff_pos_var E).trans
    (designNormalMatrix_det_ne_zero_iff E).symm

/-! ### Consistency with the two-line joint-identifiability layer -/

/-- **Two-line design injectivity from a distinct-energy pair.** At `n = 2` the design map for
energies `(EA, EB)` is injective as soon as `EA ≠ EB`. This is the `n`-line map specialized to two
lines. -/
theorem twoLine_design_injective_of_distinct {EA EB : ℝ} (h : EA ≠ EB) :
    Function.Injective (fun θ : Fin 2 → ℝ => boltzmannDesign ![EA, EB] *ᵥ θ) :=
  boltzmannDesign_mulVec_injective ⟨0, 1, by simpa using h⟩

/-- **The n-line map generalizes the two-line result on the same nondegeneracy.** The
distinct-energy hypothesis `hEdist : p.E (emitA s₀) ≠ p.E (emitB s₀)` that powers
`JointIdentifiability.joint_identifiability` (it is what lets `observe₂` deliver the temperature
ratio at `s₀`) is *exactly* the condition making the two-line Boltzmann design map injective. So
the linear n-line identifiability of this module and the two-line joint identifiability rest on
one and the same nondegeneracy — the n-line design map at `n = 2` is the linear (Boltzmann-plot)
shadow of `observe₂` on the distinct-energy pair. -/
theorem twoLine_boltzmannDesign_injective_of_hEdist
    {species levelIndex : Type*} {emitA emitB : species → levelIndex}
    {p : PlasmaParams species levelIndex} (s₀ : species)
    (hEdist : p.E (emitA s₀) ≠ p.E (emitB s₀)) :
    Function.Injective
      (fun θ : Fin 2 → ℝ => boltzmannDesign ![p.E (emitA s₀), p.E (emitB s₀)] *ᵥ θ) :=
  twoLine_design_injective_of_distinct hEdist

/-! ### Non-vacuity witnesses -/

/-- **Non-vacuity (injective case).** Three lines at distinct energies `E = ![0,1,2]`: the
parameter → observation map is injective, so `(intercept, slope)` is uniquely recovered — hence,
under the Boltzmann reparametrization (interpretation only), so is `(T, N)`. The hypotheses are
jointly satisfiable and the conclusion is non-trivial. -/
example : Function.Injective (fun θ : Fin 2 → ℝ => boltzmannDesign ![0, 1, 2] *ᵥ θ) :=
  boltzmannDesign_mulVec_injective ⟨0, 1, by norm_num⟩

/-- **Non-vacuity (uniqueness on concrete data).** On `E = ![0,1,2]`, any two `(intercept, slope)`
vectors that match the Boltzmann-plot ordinates on all three lines are equal — a concrete instance
of `boltzmann_params_unique`, witnessing it is not vacuous. -/
example {θ θ' : Fin 2 → ℝ}
    (h : ∀ k, θ 0 + (![0, 1, 2] : Fin 3 → ℝ) k * θ 1
      = θ' 0 + (![0, 1, 2] : Fin 3 → ℝ) k * θ' 1) : θ = θ' :=
  boltzmann_params_unique ⟨0, 1, by norm_num⟩ h

/-- **Non-vacuity (degenerate / necessary-condition case).** Two lines at *equal* energies
`E = ![1,1]`: the design map is genuinely NOT injective (kernel vector `(-1, 1)`), so the
distinct-energy hypothesis is necessary, not decorative. Mirrors the singular normal matrix at
`E = ![1,1]` in `OLS.lean`. -/
example : ¬ Function.Injective (fun θ : Fin 2 → ℝ => boltzmannDesign ![1, 1] *ᵥ θ) := by
  apply boltzmannDesign_mulVec_not_injective_of_forall_eq
  intro i j; fin_cases i <;> fin_cases j <;> rfl

/-- **Non-vacuity (two-line consistency).** At `n = 2` with distinct energies `E = ![5,7]` the map
is injective — the `twoLine_design_injective_of_distinct` specialization on which the tie to
`joint_identifiability`'s `hEdist` rests. -/
example : Function.Injective (fun θ : Fin 2 → ℝ => boltzmannDesign ![5, 7] *ᵥ θ) :=
  twoLine_design_injective_of_distinct (by norm_num)

end CflibsFormal

