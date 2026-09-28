# FT19-tiltMean-reweight-le: a reweight antitone in `b` lowers the tilted mean

Planning dossier for the proof queue (2026-09-24 audit, frontier FT-19, weighted Chebyshev
step). Written for a planner who cannot open the repository. Every repo definition and lemma is
quoted, and every Mathlib name was checked with `#check` against the pinned Mathlib (v4.33.1).

## 1. Goal

```lean
import Mathlib
import CflibsFormal.InhomogeneityBias

open CflibsFormal

namespace Plan.FT19

theorem tiltMean_reweight_le {ζ : Type*} [Fintype ζ] [Nonempty ζ] {w b ρ : ζ → ℝ}
    (hw : ∀ z, 0 < w z) (hρ : ∀ z, 0 < ρ z) (hanti : ∀ i j, b i < b j → ρ j ≤ ρ i) (a : ℝ) :
    tiltMean (fun z => w z * ρ z) b a ≤ tiltMean w b a := by
  sorry
```

No new definitions. Keep the signature verbatim; helper lemmas may be added. `hanti` is
`Antivary ρ b` unfolded (Mathlib: `Antivary f g := ∀ ⦃i j⦄, g i < g j → f j ≤ f i`).

## 2. Definitions (namespace `CflibsFormal`, `InhomogeneityBias.lean:147-166`)

```lean
noncomputable def mixture (w b : ζ → ℝ) (E : ℝ) : ℝ :=
  ∑ z, w z * Real.exp (-(E * b z))

noncomputable def tiltWeight (w b : ζ → ℝ) (a : ℝ) (z : ζ) : ℝ :=
  w z * Real.exp (-(a * b z)) / mixture w b a

noncomputable def tiltMean (w b : ζ → ℝ) (a : ℝ) : ℝ :=
  ∑ z, tiltWeight w b a z * b z
```
(`variable {ζ : Type*} [Fintype ζ]` in that file.)

## 3. Repo lemmas (signatures checked)

- `mixture_pos [Nonempty ζ] {w b : ζ → ℝ} (hw : ∀ z, 0 < w z) (E : ℝ) : 0 < mixture w b E`
- `tiltWeight_pos [Nonempty ζ] {w b : ζ → ℝ} (hw : ∀ z, 0 < w z) (a : ℝ) (z : ζ) :
  0 < tiltWeight w b a z`
- `tiltWeight_sum_one [Nonempty ζ] {w b : ζ → ℝ} (hw : ∀ z, 0 < w z) (a : ℝ) :
  ∑ z, tiltWeight w b a z = 1`

## 4. Mathematics

Put `u z := w z * Real.exp (-(a * b z)) > 0`. Unfolding,
`tiltMean w b a = (∑ u b) / (∑ u)` and `tiltMean (w·ρ) b a = (∑ u ρ b) / (∑ u ρ)` (the
`mixture` of `w·ρ` is `∑ u ρ`). By `div_le_div_iff₀` the goal is
`(∑ u ρ b) * (∑ u) ≤ (∑ u b) * (∑ u ρ)`. Chebyshev double sum:
`2 * [(∑ u ρ b)(∑ u) − (∑ u b)(∑ u ρ)] = ∑ i, ∑ j, u i * u j * (ρ i − ρ j) * (b i − b j)`,
and every term is `≤ 0` because `(ρ i − ρ j)(b i − b j) ≤ 0` (case split `lt_trichotomy (b i)
(b j)`: `b i < b j` gives `ρ j ≤ ρ i` by `hanti i j`; `b j < b i` gives `ρ i ≤ ρ j`; equality
gives factor `0`).

## 5. Suggested Lean decomposition

1. `hu : ∀ z, 0 < w z * Real.exp (-(a * b z))`.
2. Closed forms: `tiltMean w b a = (∑ z, w z * exp(-(a*b z)) * b z) / mixture w b a` by
   `simp only [tiltMean, tiltWeight]; rw [Finset.sum_div]; congr; ring` (per term:
   `x / M * y = x * y / M`, `div_mul_eq_mul_div`), and the same for `fun z => w z * ρ z`,
   whose mixture is `∑ z, w z * ρ z * exp(-(a*b z))` (`simp only [mixture]`).
3. `rw [div_le_div_iff₀ (mixture_pos hwρ a) (mixture_pos hw a)]` where
   `hwρ : ∀ z, 0 < w z * ρ z := fun z => mul_pos (hw z) (hρ z)`.
4. Chebyshev: prove `∑ i, ∑ j, u i * u j * ((ρ i - ρ j) * (b i - b j)) ≤ 0` by
   `Finset.sum_nonpos` twice and the sign case split, then identify it with
   `2 * (LHS − RHS)` using `Finset.sum_mul_sum`, `Finset.sum_sub_distrib`, `Finset.sum_comm`,
   `Finset.mul_sum`, `Finset.sum_mul` and `ring`-per-term (`Finset.sum_congr rfl`). Close with
   `linarith`.
   Alternative for the identity: expand the product into four double sums
   `∑∑ u_i u_j ρ_i b_i − ∑∑ u_i u_j ρ_i b_j − ∑∑ u_i u_j ρ_j b_i + ∑∑ u_i u_j ρ_j b_j`; the 1st
   and 4th are equal (swap with `Finset.sum_comm`), as are the 2nd and 3rd.

## 6. Mathlib lemmas (signatures checked)

- `Finset.sum_mul_sum (s t f g) : (∑ i ∈ s, f i) * ∑ j ∈ t, g j = ∑ i ∈ s, ∑ j ∈ t, f i * g j`
- `Finset.sum_comm : ∑ x ∈ s, ∑ y ∈ t, f x y = ∑ y ∈ t, ∑ x ∈ s, f x y`
- `Finset.sum_nonpos : (∀ i ∈ s, f i ≤ 0) → ∑ i ∈ s, f i ≤ 0`; `Finset.sum_pos`
- `Finset.sum_div`, `Finset.mul_sum`, `Finset.sum_mul`, `Finset.sum_sub_distrib`,
  `Finset.sum_congr`
- `div_le_div_iff₀ : 0 < b → 0 < d → (a / b ≤ c / d ↔ a * d ≤ c * b)`
- `mul_nonpos_of_nonneg_of_nonpos : 0 ≤ a → b ≤ 0 → a * b ≤ 0`;
  `mul_nonpos_of_nonpos_of_nonneg : a ≤ 0 → 0 ≤ b → a * b ≤ 0`; `lt_trichotomy`
- Mathlib's Chebyshev (`Mathlib/Algebra/Order/Chebyshev.lean`, e.g.
  `Antivary.card_mul_sum_le_sum_mul_sum`) is UNWEIGHTED only; no weighted version was found in
  `Chebyshev.lean` / `Rearrangement.lean` / `Monovary.lean`. Prove the weighted one by hand.

## 7. Pitfalls

- `tiltMean (fun z => w z * ρ z) b a` needs beta-reduction after unfolding; use `simp only
  [tiltMean, tiltWeight, mixture]` rather than `unfold`.
- `hanti` only gives `ρ j ≤ ρ i` from a STRICT `b i < b j`; the tie `b i = b j` must be handled
  by the zero factor, not by `hanti`.
- Keep `-(a * b z)` in the exponent exactly as in the def; `Real.exp_pos` covers positivity.
- `Nonempty ζ` is needed for `mixture_pos` (sum over `univ`).

## 8. Satisfiability witness (checked)

`ζ = Fin 2`, `w = ![1, 1]`, `b = ![1, 2]`, `ρ = ![2, 1]`, `a = 0`: all hypotheses hold and
`tiltMean (w·ρ) b 0 = 4/3 < 3/2 = tiltMean w b 0` (checked by
`simp [tiltMean, tiltWeight, mixture, Fin.sum_univ_two]; norm_num`), so the inequality is strict
on this data.

## 9. Scope

PURE-MATH (weighted Chebyshev for finite positive mixtures). Its FT-19 application (with
`ρ z = ionReweight … (T z)`, `b z = 1/(k_B T z)`) is REDUCED: uniform `n_e`, per-zone LTE.
