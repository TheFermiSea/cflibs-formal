import Mathlib
import CflibsFormal.OLS

open Finset CflibsFormal

namespace Plan.FT10


theorem interceptDiff_noiseGain {ιa ιb : Type*} [Fintype ιa] [Fintype ιb] [Nonempty ιa]
    [Nonempty ιb] (Ea : ιa → ℝ) (Eb : ιb → ℝ)
    (hSS : 0 < ∑ k, (Ea k - mean Ea) ^ 2 + ∑ k, (Eb k - mean Eb) ^ 2) :
    let SS := ∑ k, (Ea k - mean Ea) ^ 2 + ∑ k, (Eb k - mean Eb) ^ 2
    let wa : ιa → ℝ := fun k =>
      (1 : ℝ) / (Fintype.card ιa : ℝ) - (mean Ea - mean Eb) * (Ea k - mean Ea) / SS
    let wb : ιb → ℝ := fun k =>
      -((1 : ℝ) / (Fintype.card ιb : ℝ)) - (mean Ea - mean Eb) * (Eb k - mean Eb) / SS
    ∑ k, wa k ^ 2 + ∑ k, wb k ^ 2
      = (1 : ℝ) / (Fintype.card ιa : ℝ) + (1 : ℝ) / (Fintype.card ιb : ℝ)
          + (mean Ea - mean Eb) ^ 2 / SS := by
  sorry

end Plan.FT10
