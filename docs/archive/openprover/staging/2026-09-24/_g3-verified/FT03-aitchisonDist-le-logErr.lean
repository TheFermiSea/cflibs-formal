import Mathlib
import CflibsFormal.AitchisonIsometry

/-!
# Queue target FT03-aitchisonDist-le-logErr (deep audit 2026-09-24, FT-03 items 3-5)

Loss certificate for the Aitchison PAS loss: a per-species log-ratio error bound bounds the
Aitchison distance. Statement file for the proof queue: one target theorem, one `sorry`.
-/

open Finset CflibsFormal

namespace Plan.FT03

variable {ι : Type*} [Fintype ι]

theorem aitchisonDist_eq_sqrt [Nonempty ι] (x y : ι → ℝ) :
    aitchisonDist y x = Real.sqrt (∑ s, (clr y s - clr x s) ^ 2) := by
  rw [aitchisonDist, EuclideanSpace.norm_eq]
  congr 1
  refine Finset.sum_congr rfl fun s _ => ?_
  simp [clrE, Real.norm_eq_abs, sq_abs]

theorem clr_sub_eq_centered_log [Nonempty ι] {x y : ι → ℝ} (hx : ∀ k, 0 < x k)
    (hy : ∀ k, 0 < y k) (s : ι) :
    clr y s - clr x s
      = Real.log (y s / x s) - (∑ j, Real.log (y j / x j)) / (Fintype.card ι : ℝ) := by
  simp only [clr, Real.log_div (hy _).ne' (hx _).ne', Finset.sum_sub_distrib]
  ring

theorem sum_sq_centered_le [Nonempty ι] (e : ι → ℝ) (c : ℝ) :
    ∑ s, (e s - (∑ j, e j) / (Fintype.card ι : ℝ)) ^ 2 ≤ ∑ s, (e s - c) ^ 2 := by
  have hD : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  set m := (∑ j, e j) / (Fintype.card ι : ℝ) with hm
  have h0 : ∑ s, (e s - m) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hm]
    field_simp
    ring
  have hsplit : ∑ s, (e s - c) ^ 2
      = ∑ s, (e s - m) ^ 2 + 2 * (m - c) * ∑ s, (e s - m)
        + (Fintype.card ι : ℝ) * (m - c) ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    rw [show (Fintype.card ι : ℝ) * (m - c) ^ 2 = ∑ _s : ι, (m - c) ^ 2 by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun s _ => by ring
  rw [hsplit, h0, mul_zero, add_zero]
  have : 0 ≤ (Fintype.card ι : ℝ) * (m - c) ^ 2 := by positivity
  linarith

/-- **Log-error certificate for the Aitchison distance.** For strictly positive compositions
`x` (truth) and `y` (estimate) and **any** constant `c`,
  `d_A(y, x) ≤ √(∑ s, (log (y s / x s) − c)²)`.
Reason: with `e s = log (y s / x s)`, positivity gives `clr y s − clr x s = e s − ē` (`ē` the
mean of `e`), so `d_A(y, x) = √(∑ s, (e s − ē)²)`, and centring minimises the sum of squares
over constant shifts: `∑ (e − c)² = ∑ (e − ē)² + D·(ē − c)²` with `D = card ι`. The bound is
sharp: `c = ē` gives equality, so it is not vacuous. Use: per-species log-error bounds
`|log (y s / x s) − c| ≤ ε s` certify the loss upper bound `U = √(∑ ε s²)` consumed by the
refuse-to-report policy (`pasPolicy_guarantees`); `c` absorbs any error common to all species
(a total-density or calibration factor), to which `d_A` is blind.

Hypotheses: `hx`, `hy` (strict positivity). `clr` uses `Real.log`, and Lean's `log 0 = 0` would
silently give a zero component a finite clr coordinate; mathematically nonzero entries suffice,
positivity is the compositional meaning, and zero replacement must happen before this applies.
`[Nonempty ι]` is required by `aitchisonDist` (its section variable) and makes `D ≥ 1`.

Scope (two-axis): relation PURE-MATH; definitions used (`clr`, `clrE`, `aitchisonDist`) are
PURE-MATH; published PURE-MATH. Citation: — (clr and `d_A` after Aitchison 1986). -/
theorem aitchisonDist_le_logErr [Nonempty ι] {x y : ι → ℝ} (hx : ∀ k, 0 < x k)
    (hy : ∀ k, 0 < y k) (c : ℝ) :
    aitchisonDist y x ≤ Real.sqrt (∑ s, (Real.log (y s / x s) - c) ^ 2) := by
  rw [aitchisonDist_eq_sqrt]
  apply Real.sqrt_le_sqrt
  rw [Finset.sum_congr rfl fun s _ => by rw [clr_sub_eq_centered_log hx hy s]]
  exact sum_sq_centered_le (fun s => Real.log (y s / x s)) c

end Plan.FT03
