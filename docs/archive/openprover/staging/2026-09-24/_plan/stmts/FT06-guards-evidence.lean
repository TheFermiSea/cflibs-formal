import Mathlib
import CflibsFormal.StarkBroadening

open CflibsFormal

namespace Plan.FT06g


/-- Guard check: without `0 < nRef`, `0 ≤ neTrue` the revised statement is false. -/
example : ¬ (∀ w ρw kOpac wTrue nRef neTrue widthMeas : ℝ, 0 < w → 1 ≤ ρw → 0 < kOpac →
    (w / ρw ≤ wTrue ∧ wTrue ≤ w * ρw) → starkFWHM wTrue nRef neTrue ≤ widthMeas →
    widthMeas ≤ kOpac * starkFWHM wTrue nRef neTrue →
    (starkDensity w nRef widthMeas / (kOpac * ρw) ≤ neTrue ∧
      neTrue ≤ starkDensity w nRef widthMeas * ρw)) := by
  intro H
  have := (H 1 1 2 1 (-1) (-1) 2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num [starkFWHM]) (by norm_num [starkFWHM])).1
  norm_num [starkDensity] at this

/-- Guard check: `0 < nRef` alone is not enough; `0 ≤ neTrue` is also load-bearing. -/
example : ¬ (∀ w ρw kOpac wTrue nRef neTrue widthMeas : ℝ, 0 < w → 1 ≤ ρw → 0 < kOpac →
    0 < nRef → (w / ρw ≤ wTrue ∧ wTrue ≤ w * ρw) → starkFWHM wTrue nRef neTrue ≤ widthMeas →
    widthMeas ≤ kOpac * starkFWHM wTrue nRef neTrue →
    (starkDensity w nRef widthMeas / (kOpac * ρw) ≤ neTrue ∧
      neTrue ≤ starkDensity w nRef widthMeas * ρw)) := by
  intro H
  have := (H 1 2 1 1 1 (-1) (-2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num [starkFWHM]) (by norm_num [starkFWHM])).2
  norm_num [starkDensity] at this

end Plan.FT06g
