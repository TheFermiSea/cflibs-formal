import Mathlib

open Filter Topology

namespace Plan.FT01


theorem exists_weights_iff {a b c d : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c) :
    (∃ wT wn : ℝ, 0 < wT ∧ 0 < wn ∧ max (a + b * wn / wT) (c * wT / wn + d) < 1)
      ↔ (a < 1 ∧ d < 1 ∧ b * c < (1 - a) * (1 - d)) := by
  sorry

end Plan.FT01
