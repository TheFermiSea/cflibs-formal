import Mathlib

open Finset

namespace Plan.FT04

variable {ι κ : Type*} [Fintype ι] [DecidableEq κ]

/-- Weighted group mean of `f` over the lines of group `e` (empty group: `0/0 = 0`). -/
noncomputable def gMean (grp : ι → κ) (w f : ι → ℝ) (e : κ) : ℝ :=
  (∑ k ∈ univ.filter (fun k => grp k = e), w k * f k) /
    ∑ k ∈ univ.filter (fun k => grp k = e), w k

/-- Weighted within-group cross product. -/
noncomputable def withinCross (grp : ι → κ) (w x y : ι → ℝ) : ℝ :=
  ∑ k, w k * (x k - gMean grp w x (grp k)) * (y k - gMean grp w y (grp k))

/-- Weighted within-group sum of squares `SS_W`. -/
noncomputable def withinSS (grp : ι → κ) (w x : ι → ℝ) : ℝ := withinCross grp w x x

/-- Fixed-effects (within-element) slope. -/
noncomputable def feSlope (grp : ι → κ) (w x y : ι → ℝ) : ℝ :=
  withinCross grp w x y / withinSS grp w x

theorem feSlope_isMin (grp : ι → κ) (w x y : ι → ℝ) (hw : ∀ k, 0 < w k)
    (hSS : 0 < withinSS grp w x) (a : κ → ℝ) (β : ℝ) :
    ∑ k, w k * (y k - (gMean grp w y (grp k) - feSlope grp w x y * gMean grp w x (grp k))
        - feSlope grp w x y * x k) ^ 2
      ≤ ∑ k, w k * (y k - a (grp k) - β * x k) ^ 2 := by
  sorry

end Plan.FT04
