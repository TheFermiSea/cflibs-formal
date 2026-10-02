import Mathlib
import CflibsFormal.StarkBroadening
open CflibsFormal

-- hnRef isolated: with hne present (ne = 1 ≥ 0) and every other hypothesis, nRef = -1 breaks
-- the LOWER end; the docstring's witness (…,-1,-1,…) also violates hne, so it does not isolate.
example : ¬ (∀ w ρw kOpac wTrue nRef neTrue widthMeas : ℝ, 0 < w → 1 ≤ ρw → 0 < kOpac →
    0 ≤ neTrue → (w / ρw ≤ wTrue ∧ wTrue ≤ w * ρw) → starkFWHM wTrue nRef neTrue ≤ widthMeas →
    widthMeas ≤ kOpac * starkFWHM wTrue nRef neTrue →
    (starkDensity w nRef widthMeas / (kOpac * ρw) ≤ neTrue ∧
      neTrue ≤ starkDensity w nRef widthMeas * ρw)) := by
  intro H
  have := (H 1 1 (1/2) 1 (-1) 1 (-2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num [starkFWHM]) (by norm_num [starkFWHM])).1
  norm_num [starkDensity] at this

-- nRef = 0 (junk x/0 = 0 in starkFWHM) breaks the UPPER end.
example : ¬ (∀ w ρw kOpac wTrue nRef neTrue widthMeas : ℝ, 0 < w → 1 ≤ ρw → 0 < kOpac →
    0 ≤ neTrue → (w / ρw ≤ wTrue ∧ wTrue ≤ w * ρw) → starkFWHM wTrue nRef neTrue ≤ widthMeas →
    widthMeas ≤ kOpac * starkFWHM wTrue nRef neTrue →
    (starkDensity w nRef widthMeas / (kOpac * ρw) ≤ neTrue ∧
      neTrue ≤ starkDensity w nRef widthMeas * ρw)) := by
  intro H
  have := (H 1 1 1 1 0 1 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num [starkFWHM]) (by norm_num [starkFWHM])).2
  norm_num [starkDensity] at this

-- P2: non-degenerate witness (ρw = 2, kOpac = 3/2): bracket [1/2, 3] around ne = 1.
example : starkDensity 1 1 3 / ((3/2) * 2) = 1/2 ∧ starkDensity 1 1 3 * 2 = 3 ∧
    starkFWHM 1 1 1 ≤ 3 ∧ (3:ℝ) ≤ 3/2 * starkFWHM 1 1 1 ∧ (1:ℝ)/2 ≤ 1 ∧ (1:ℝ) ≤ 1 * 2 := by
  norm_num [starkDensity, starkFWHM]

-- at ρw = 1 the prior art covers ne < 0; the staged statement (hne) does not: prior-art
-- hypotheses and conclusion both hold at (w,nRef,k,ne,W) = (1,1,1,-1,-2).
example : starkFWHM 1 1 (-1) ≤ -2 ∧ (-2:ℝ) ≤ 1 * starkFWHM 1 1 (-1) ∧
    starkDensity 1 1 (-2) / 1 ≤ -1 ∧ (-1:ℝ) ≤ starkDensity 1 1 (-2) := by
  norm_num [starkDensity, starkFWHM]
