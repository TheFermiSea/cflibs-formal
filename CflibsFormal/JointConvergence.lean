/-
Copyright (c) 2026 Brian Squires. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Squires
-/
import Mathlib
import CflibsFormal.OuterLoopModelB
import CflibsFormal.SahaRangeEnclosure

/-!
# CF-LIBS formalization — the joint `(T, n_e)` outer-loop contraction (Frontier)

This leaf lands the **physics-level joint `(T, n_e)` convergence theorem** for the CF-LIBS
outer loop, instantiating the abstract 2-D box Banach spine `jointOuterContraction_box`
(`SahaEquilibrium`) at the concrete legs: the temperature update
`fT (T,n_e) = combinedSlopeTempUpdate … n_e` (`ErrorBudget`, depends **only on `n_e`**) and
the density reader `fNe (T,n_e) = electronDensityFromRatio … T … R` (`Saha`, `n_e(T)=S(T)/R`,
depends **only on `T`**). Each leg ignores its own output coordinate, so the joint row-sum
matrix is **anti-diagonal** — `a=0`, `b=L₂`, `c=L₁`, `d=0` — with density `T`-constant
`L₁ = sahaFactorLipConst … / R₀` (`electronDensityFromRatio_lipschitz_temp`) and temperature
`n_e`-constant `L₂ = (|∑ₖ (Eₖ − Ē)·sₖ| / SS_E)/(k_B·smin²·nemin)`
(`combinedSlopeTempUpdate_lipschitz`). The gate `max (a+b) (c+d) < 1` collapses to
`max L₂ L₁ < 1`.

## Literature and scope

`REDUCED` (Aguilera & Aragón 2007, Model B; Saha–Eggert (Griem)). Genuine 2-D upgrade of
`outerLoop_contracts`: the joint state iterates in the product (max) metric on `ℝ × ℝ` and the
fixed point is self-consistent in **both** coordinates at once.

*Discharged.* The two anti-diagonal Lipschitz bounds (from the two published sensitivity
lemmas), the four coefficient signs, and the density interval-invariance `hmapsNe` — proven
a-priori from the endpoint containments `hnelo`/`hnehi` via `electronDensityFromRatio_mem_Icc`
∘ `Set.Icc_subset_Icc`, as in `outerLoop_contracts_apriori`.

*Carried (genuine runtime side conditions).* The temperature interval-invariance `hmapsT`
(no monotonicity for the slope-inversion leg), the slope floor `hslopeFloor`, the box
order/positivity data, and the **convergence certificate** `hgate : max L₂ L₁ < 1` — the
runtime-checkable gate (sufficient, not necessary), mirroring `outerLoop_contracts`'s `hgate`.
-/

namespace CflibsFormal

open Finset Real
open scoped BigOperators NNReal

/-- **The CF-LIBS joint `(T, n_e)` outer loop contracts** (`REDUCED`; Aguilera & Aragón 2007,
Model B; Saha–Eggert (Griem)). Instantiating the abstract 2-D box Banach theorem
`jointOuterContraction_box` at the anti-diagonal CF-LIBS legs `fT (T,n_e) =
combinedSlopeTempUpdate … n_e` and `fNe (T,n_e) = electronDensityFromRatio … T … R`: the joint
sweep `Φ (T,n_e) = (fT T n_e, fNe T n_e)` on the box `[Tmin,Tmax] ×ˢ [nemin,nemax]` has a
**unique** self-consistent fixed point `pstar`, and the iterates `Φ^[n] p0` converge to `pstar`
jointly in both coordinates (product metric) from every start in the box. The density
interval-invariance is discharged a-priori from the endpoint containments `hnelo`/`hnehi`; the
gate `max L₂ L₁ < 1` is the carried convergence certificate. -/
theorem jointConvergence
    {ιe : Type*} [Fintype ιe] [Nonempty ιe]
    {κe : Type*} [Fintype κe] [Nonempty κe]
    {ιl : Type*} [Fintype ιl] [Nonempty ιl]
    {kB me h chi R0 R : ℝ} {gZ EZ : ιe → ℝ} {gZ1 EZ1 : κe → ℝ}
    {E yb svec : ιl → ℝ} {offConst Tmin Tmax nemin nemax smin : ℝ}
    (hTle : Tmin ≤ Tmax) (hnele : nemin ≤ nemax)
    (hkB : 0 < kB) (hme : 0 < me) (hh : 0 < h) (hchi : 0 ≤ chi) (hTmin : 0 < Tmin)
    (hgZ : ∀ k, 0 < gZ k) (hEZ : ∀ k, 0 ≤ EZ k) (hgZ1 : ∀ k, 0 < gZ1 k) (hEZ1 : ∀ k, 0 ≤ EZ1 k)
    (hEχ : ∀ k, EZ k ≤ chi) (hR0 : 0 < R0) (hR : R0 ≤ R)
    (hvar : 0 < ∑ k, (E k - mean E) ^ 2) (hnemin : 0 < nemin) (hsmin : 0 < smin)
    (hnelo : nemin ≤ electronDensityFromRatio kB Tmin me h chi gZ EZ gZ1 EZ1 R)
    (hnehi : electronDensityFromRatio kB Tmax me h chi gZ EZ gZ1 EZ1 R ≤ nemax)
    (hmapsT : ∀ ne ∈ Set.Icc nemin nemax,
        combinedSlopeTempUpdate kB E yb svec offConst ne ∈ Set.Icc Tmin Tmax)
    (hslopeFloor : ∀ ne ∈ Set.Icc nemin nemax,
        smin ≤ combinedSahaBoltzmannSlope E yb svec offConst ne)
    (hL1nn : 0 ≤ sahaFactorLipConst kB Tmin Tmax me h chi gZ EZ gZ1 EZ1 / R0)
    (hgate : max
        ((|∑ k, (E k - mean E) * svec k| / (∑ k, (E k - mean E) ^ 2)) / (kB * smin ^ 2 * nemin))
        (sahaFactorLipConst kB Tmin Tmax me h chi gZ EZ gZ1 EZ1 / R0) < 1) :
    ∃ pstar ∈ Set.Icc Tmin Tmax ×ˢ Set.Icc nemin nemax,
      jointOuterMap (fun _ ne => combinedSlopeTempUpdate kB E yb svec offConst ne)
          (fun T _ => electronDensityFromRatio kB T me h chi gZ EZ gZ1 EZ1 R) pstar = pstar ∧
      (∀ p ∈ Set.Icc Tmin Tmax ×ˢ Set.Icc nemin nemax,
          jointOuterMap (fun _ ne => combinedSlopeTempUpdate kB E yb svec offConst ne)
            (fun T _ => electronDensityFromRatio kB T me h chi gZ EZ gZ1 EZ1 R) p = p → p = pstar) ∧
      ∀ p0 ∈ Set.Icc Tmin Tmax ×ˢ Set.Icc nemin nemax,
        Filter.Tendsto (fun n => (jointOuterMap
            (fun _ ne => combinedSlopeTempUpdate kB E yb svec offConst ne)
            (fun T _ => electronDensityFromRatio kB T me h chi gZ EZ gZ1 EZ1 R))^[n] p0)
          Filter.atTop (nhds pstar) := by
  have hRpos : 0 < R := lt_of_lt_of_le hR0 hR
  refine jointOuterContraction_box (a := 0)
      (b := (|∑ k, (E k - mean E) * svec k| / (∑ k, (E k - mean E) ^ 2)) / (kB * smin ^ 2 * nemin))
      (c := sahaFactorLipConst kB Tmin Tmax me h chi gZ EZ gZ1 EZ1 / R0) (d := 0)
      hTle hnele ?_ ?_ ?_ ?_ (le_refl 0) (by positivity) hL1nn (le_refl 0) ?_
  · intro T _ n hn; exact hmapsT n hn
  · intro T hT n _
    exact Set.Icc_subset_Icc hnelo hnehi
      (electronDensityFromRatio_mem_Icc hkB hme hh hchi hgZ hEZ hgZ1 hEZ1 hEχ hTmin hRpos hT)
  · intro T _ n hn T' _ n' hn'
    rw [zero_mul, zero_add]
    exact combinedSlopeTempUpdate_lipschitz kB E yb svec hvar hkB hnemin hsmin hn.1 hn'.1
      (hslopeFloor n hn) (hslopeFloor n' hn')
  · intro T hT n _ T' hT' n' _
    rw [zero_mul, add_zero]
    exact electronDensityFromRatio_lipschitz_temp hkB hme hh hchi hTmin hT.1 hT'.1 hT.2 hT'.2
      hgZ hEZ hgZ1 hEZ1 hR0 hR
  · rw [zero_add, add_zero]; exact hgate

end CflibsFormal
