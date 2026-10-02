import Mathlib
import CflibsFormal.AitchisonIsometry

open Finset CflibsFormal

namespace Plan.FT03


variable {ι : Type*} [Fintype ι]

theorem aitchisonDist_le_logErr [Nonempty ι] {x y : ι → ℝ} (hx : ∀ k, 0 < x k)
    (hy : ∀ k, 0 < y k) (c : ℝ) :
    aitchisonDist y x ≤ Real.sqrt (∑ s, (Real.log (y s / x s) - c) ^ 2) := by
  sorry

end Plan.FT03
