import Mathlib
import CflibsFormal.StarkBroadening
open CflibsFormal
/-- rho = 0 breaks the upper end (so hρ is load-bearing beyond making hwT nonempty). -/
example : ¬ (∀ w ρw kOpac wTrue nRef neTrue widthMeas : ℝ, 0 < w → 0 < kOpac →
    0 < nRef → 0 ≤ neTrue → (w / ρw ≤ wTrue ∧ wTrue ≤ w * ρw) →
    starkFWHM wTrue nRef neTrue ≤ widthMeas →
    widthMeas ≤ kOpac * starkFWHM wTrue nRef neTrue →
    (starkDensity w nRef widthMeas / (kOpac * ρw) ≤ neTrue ∧
      neTrue ≤ starkDensity w nRef widthMeas * ρw)) := by
  intro H
  have := (H 1 0 1 0 1 1 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num [starkFWHM]) (by norm_num [starkFWHM])).2
  norm_num [starkDensity] at this
