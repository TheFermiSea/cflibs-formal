import Mathlib
import CflibsFormal.StarkBroadening

open CflibsFormal

namespace Plan.FT06


theorem stark_bracket_rho {w ρw kOpac wTrue nRef neTrue widthMeas : ℝ} (hw : 0 < w)
    (hρ : 1 ≤ ρw) (hk : 0 < kOpac) (hnRef : 0 < nRef) (hne : 0 ≤ neTrue)
    (hwT : w / ρw ≤ wTrue ∧ wTrue ≤ w * ρw)
    (hopac : starkFWHM wTrue nRef neTrue ≤ widthMeas)
    (hbudget : widthMeas ≤ kOpac * starkFWHM wTrue nRef neTrue) :
    starkDensity w nRef widthMeas / (kOpac * ρw) ≤ neTrue ∧
      neTrue ≤ starkDensity w nRef widthMeas * ρw := by
  sorry


end Plan.FT06
