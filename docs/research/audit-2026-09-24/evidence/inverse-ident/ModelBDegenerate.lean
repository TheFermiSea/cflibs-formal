import Mathlib
import CflibsFormal.OuterLoopModelB

/-! Audit scratch (inverse-ident). If the Saha offset `offConst` of the Model-B temperature leg is
evaluated at the CURRENT temperature (`offConst = log S(T)`, the physically consistent choice the
`combinedSahaBoltzmannSlope` docstring describes "at fixed T"), then composing with the Model-B
density leg `n_e(T) = S(T)/R` makes the temperature update independent of `T`: the outer loop is
degenerate (constant map), exactly the "Model A" degeneracy `OuterLoopModelB` says it avoids. -/

namespace CflibsFormal

theorem modelB_consistent_offset_degenerate
    {ιe κe ιl : Type*} [Fintype ιe] [Nonempty ιe] [Fintype κe] [Nonempty κe] [Fintype ιl]
    {kB me h chi R : ℝ} {gZ EZ : ιe → ℝ} {gZ1 EZ1 : κe → ℝ} {E y s : ιl → ℝ}
    (hkB : 0 < kB) (hme : 0 < me) (hh : 0 < h)
    (hgZ : ∀ k, 0 < gZ k) (hgZ1 : ∀ k, 0 < gZ1 k) (hR : 0 < R) (T : ℝ) (hT : 0 < T) :
    combinedSlopeTempUpdate kB E y s (Real.log (sahaFactor kB T me h chi gZ EZ gZ1 EZ1))
        (electronDensityFromRatio kB T me h chi gZ EZ gZ1 EZ1 R)
      = combinedSlopeTempUpdate kB E y s (Real.log R) 1 := by
  have hS : 0 < sahaFactor kB T me h chi gZ EZ gZ1 EZ1 := sahaFactor_pos hkB hT hme hh hgZ hgZ1
  have hoff : Real.log (sahaFactor kB T me h chi gZ EZ gZ1 EZ1)
      - Real.log (electronDensityFromRatio kB T me h chi gZ EZ gZ1 EZ1 R)
      = Real.log R - Real.log 1 := by
    unfold electronDensityFromRatio
    rw [Real.log_div hS.ne' hR.ne', Real.log_one]; ring
  unfold combinedSlopeTempUpdate combinedSahaBoltzmannSlope
  rw [hoff]

#print axioms modelB_consistent_offset_degenerate
end CflibsFormal
