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
  sorry

end Plan.FT03
