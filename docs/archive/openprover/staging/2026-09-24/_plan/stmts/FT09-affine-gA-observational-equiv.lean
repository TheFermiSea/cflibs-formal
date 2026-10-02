import Mathlib
import CflibsFormal.ForwardMap

open Finset CflibsFormal

namespace Plan.FT09


variable {ι : Type*} [Fintype ι]

theorem affine_gA_observational_equiv [Nonempty ι]
    {kB T N Fcal α b : ℝ} {g E A A' : ι → ℝ}
    (hkB : 0 < kB) (hT : 0 < T) (hg : ∀ k, 0 < g k) (hA : ∀ k, 0 < A k) (hN : 0 < N)
    (hFcal : 0 < Fcal) (haff : ∀ k, A' k = A k * Real.exp (-(α + b * E k)))
    (hb : b * (kB * T) < 1) :
    ∃ T' N' : ℝ, 0 < T' ∧ 0 < N' ∧ 1 / (kB * T') = 1 / (kB * T) - b ∧
      ∀ k, Real.log (lineIntensity kB T N Fcal g E A k / (g k * A' k))
        = Real.log (lineIntensity kB T' N' Fcal g E A k / (g k * A k)) := by
  sorry

end Plan.FT09
