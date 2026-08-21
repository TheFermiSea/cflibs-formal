/-
Copyright (c) 2026 Brian Squires. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Squires
-/
import Mathlib
import CflibsFormal.OuterLoopModelB

/-!
# CF-LIBS formalization — an a-priori Saha `S(T)`-range enclosure (Frontier 04)

This leaf module upgrades the flagship outer-loop contraction theorem `outerLoop_contracts`
(`OuterLoopModelB`) by turning its carried interval-invariance side condition `hmapsNe` — the
hypothesis that the Saha density reader `n_e(T) = S(T)/R` maps the temperature box `[Tmin,Tmax]`
into the density box `[nemin,nemax]` — from an **assumed** premise into a **proven** consequence
of the monotonicity of the Saha factor.

The chain is:

* `sahaFactor_mem_Icc` — because `S(·)` is monotone on `(0,∞)`
  (`sahaFactor_strictMonoOn_temp`, M4), for any `T ∈ [Tmin,Tmax]` with `0 < Tmin` the value
  `S(T)` is trapped between the two endpoint values `S(Tmin)` and `S(Tmax)`.
* `electronDensityFromRatio_mem_Icc` — dividing the endpoint enclosure by a fixed `R > 0`
  (order-preserving) traps the density reader `n_e(T) = S(T)/R` between its endpoints.
* `outerLoop_contracts_apriori` — the payoff. With the two endpoint containments
  `nemin ≤ n_e(Tmin)` and `n_e(Tmax) ≤ nemax` as the only new density-side hypotheses, the
  full box-invariance `hmapsNe` is discharged internally (endpoint enclosure composed with
  `Set.Icc_subset_Icc`) and forwarded to `outerLoop_contracts`. The interval invariance is now
  *derived from the box endpoints*, not assumed.

## Literature and scope

Scope tag: **`sahaFactor_mem_Icc`, `electronDensityFromRatio_mem_Icc` = EXACT; **
`outerLoop_contracts_apriori` = **REDUCED**. Citation: Saha–Eggert equilibrium, as presented by
H. R. Griem, *Principles of Plasma Spectroscopy* (Cambridge, 1997), and used throughout the
CF-LIBS thermometry of Aguilera & Aragón 2007. The two enclosure lemmas are exact-over-`ℝ`
monotonicity facts about the Saha factor `S(T)` and the density reader `S(T)/R`; they carry no
approximation. `outerLoop_contracts_apriori` is `REDUCED` for the *same* reason its parent
`outerLoop_contracts` is: the product gate `L₁·L₂ < 1` is a sufficient (non-sharp) convergence
certificate. The genuine rigor upgrade over the parent is that the density interval-invariance is
now a *theorem* about the endpoints rather than a carried assumption — one fewer trusted side
condition on the flagship result. The temperature-side invariance `hmapsT` and the slope floor
`hslopeFloor` remain carried side conditions (out of scope here; they concern the combined
Saha–Boltzmann slope leg, not the Saha density leg).
-/

namespace CflibsFormal

open Finset Real
open scoped NNReal BigOperators

/-- **Saha-factor range enclosure (EXACT, Saha–Eggert (Griem)).** On a positive temperature box
`[Tmin,Tmax]` (with `0 < Tmin`), the Saha factor `S(T)` at any interior/boundary temperature is
trapped between its two endpoint values. Immediate from the strict monotonicity of `S(·)` on
`(0,∞)` (`sahaFactor_strictMonoOn_temp`, M4) demoted to `MonotoneOn`: all three of `Tmin`, `T`,
`Tmax` lie in `Set.Ioi 0` (from `0 < Tmin ≤ T ≤ Tmax`), so `S Tmin ≤ S T ≤ S Tmax`. -/
theorem sahaFactor_mem_Icc {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty ι] [Nonempty κ]
    {kB me h chi Tmin Tmax T : ℝ} {gZ EZ : ι → ℝ} {gZ1 EZ1 : κ → ℝ}
    (hkB : 0 < kB) (hme : 0 < me) (hh : 0 < h) (hchi : 0 ≤ chi)
    (hgZ : ∀ k, 0 < gZ k) (hEZ : ∀ k, 0 ≤ EZ k)
    (hgZ1 : ∀ k, 0 < gZ1 k) (hEZ1 : ∀ k, 0 ≤ EZ1 k)
    (hEχ : ∀ k, EZ k ≤ chi) (hTmin : 0 < Tmin) (hT : T ∈ Set.Icc Tmin Tmax) :
    sahaFactor kB T me h chi gZ EZ gZ1 EZ1 ∈
      Set.Icc (sahaFactor kB Tmin me h chi gZ EZ gZ1 EZ1)
        (sahaFactor kB Tmax me h chi gZ EZ gZ1 EZ1) := by
  have hmono :=
    (sahaFactor_strictMonoOn_temp hkB hme hh hchi hgZ hEZ hgZ1 hEZ1 hEχ).monotoneOn
  obtain ⟨hTl, hTu⟩ := hT
  have hTminI : Tmin ∈ Set.Ioi (0 : ℝ) := Set.mem_Ioi.mpr hTmin
  have hTI : T ∈ Set.Ioi (0 : ℝ) := Set.mem_Ioi.mpr (lt_of_lt_of_le hTmin hTl)
  have hTmaxI : Tmax ∈ Set.Ioi (0 : ℝ) := Set.mem_Ioi.mpr (lt_of_lt_of_le hTmin (hTl.trans hTu))
  exact Set.mem_Icc.mpr ⟨hmono hTminI hTI hTl, hmono hTI hTmaxI hTu⟩

/-- **Density-reader range enclosure (EXACT, Saha–Eggert (Griem)).** The Saha density diagnostic
`n_e(T) = S(T)/R` inherits the endpoint enclosure of `S`: for a fixed measured stage ratio
`R > 0`, dividing the `sahaFactor_mem_Icc` bracket by `R` (order-preserving on `ℝ` since
`0 ≤ R`) traps `n_e(T)` between `n_e(Tmin)` and `n_e(Tmax)`. Uses that
`electronDensityFromRatio … R` is *defeq* to `sahaFactor … / R`. -/
theorem electronDensityFromRatio_mem_Icc {ι κ : Type*} [Fintype ι] [Fintype κ]
    [Nonempty ι] [Nonempty κ]
    {kB me h chi Tmin Tmax T R : ℝ} {gZ EZ : ι → ℝ} {gZ1 EZ1 : κ → ℝ}
    (hkB : 0 < kB) (hme : 0 < me) (hh : 0 < h) (hchi : 0 ≤ chi)
    (hgZ : ∀ k, 0 < gZ k) (hEZ : ∀ k, 0 ≤ EZ k)
    (hgZ1 : ∀ k, 0 < gZ1 k) (hEZ1 : ∀ k, 0 ≤ EZ1 k)
    (hEχ : ∀ k, EZ k ≤ chi) (hTmin : 0 < Tmin) (hR : 0 < R)
    (hT : T ∈ Set.Icc Tmin Tmax) :
    electronDensityFromRatio kB T me h chi gZ EZ gZ1 EZ1 R ∈
      Set.Icc (electronDensityFromRatio kB Tmin me h chi gZ EZ gZ1 EZ1 R)
        (electronDensityFromRatio kB Tmax me h chi gZ EZ gZ1 EZ1 R) := by
  obtain ⟨hlo, hhi⟩ :=
    Set.mem_Icc.mp (sahaFactor_mem_Icc hkB hme hh hchi hgZ hEZ hgZ1 hEZ1 hEχ hTmin hT)
  exact Set.mem_Icc.mpr
    ⟨div_le_div_of_nonneg_right hlo hR.le, div_le_div_of_nonneg_right hhi hR.le⟩

/-- **The CF-LIBS outer temperature loop contracts — a-priori density invariance** (`REDUCED`;
Aguilera & Aragón 2007, Model B; Saha–Eggert (Griem)). Identical conclusion to
`outerLoop_contracts`, but the carried interval-invariance side condition `hmapsNe` is **dropped**
and replaced by the two endpoint containments `hnelo : nemin ≤ n_e(Tmin)` and
`hnehi : n_e(Tmax) ≤ nemax` (plus `[Nonempty ιe] [Nonempty κe]` and the level-ceiling monotonicity
premise `hEχ : ∀ k, EZ k ≤ chi`). The full box invariance is then *proven* inside the theorem:
`electronDensityFromRatio_mem_Icc` traps each `n_e(T)` in `[n_e(Tmin), n_e(Tmax)]`, and
`Set.Icc_subset_Icc hnelo hnehi` sends that sub-box into `[nemin,nemax]`. This is a genuine
a-priori discharge — the density interval invariance is no longer assumed but derived from the
box endpoints — after which the parent `outerLoop_contracts` is forwarded verbatim. -/
theorem outerLoop_contracts_apriori
    {ιe : Type*} [Fintype ιe] [Nonempty ιe]
    {κe : Type*} [Fintype κe] [Nonempty κe]
    {ιl : Type*} [Fintype ιl] [Nonempty ιl]
    {kB me h chi R0 R : ℝ} {gZ EZ : ιe → ℝ} {gZ1 EZ1 : κe → ℝ}
    {E yb svec : ιl → ℝ} {offConst Tmin Tmax nemin nemax smin : ℝ}
    (hTle : Tmin ≤ Tmax)
    (hkB : 0 < kB) (hme : 0 < me) (hh : 0 < h) (hchi : 0 ≤ chi) (hTmin : 0 < Tmin)
    (hgZ : ∀ k, 0 < gZ k) (hEZ : ∀ k, 0 ≤ EZ k) (hgZ1 : ∀ k, 0 < gZ1 k) (hEZ1 : ∀ k, 0 ≤ EZ1 k)
    (hEχ : ∀ k, EZ k ≤ chi)
    (hR0 : 0 < R0) (hR : R0 ≤ R)
    (hvar : 0 < ∑ k, (E k - mean E) ^ 2) (hnemin : 0 < nemin) (hsmin : 0 < smin)
    (hnelo : nemin ≤ electronDensityFromRatio kB Tmin me h chi gZ EZ gZ1 EZ1 R)
    (hnehi : electronDensityFromRatio kB Tmax me h chi gZ EZ gZ1 EZ1 R ≤ nemax)
    (hmapsT : ∀ ne ∈ Set.Icc nemin nemax,
        combinedSlopeTempUpdate kB E yb svec offConst ne ∈ Set.Icc Tmin Tmax)
    (hslopeFloor : ∀ ne ∈ Set.Icc nemin nemax,
        smin ≤ combinedSahaBoltzmannSlope E yb svec offConst ne)
    (hL1nn : 0 ≤ sahaFactorLipConst kB Tmin Tmax me h chi gZ EZ gZ1 EZ1 / R0)
    (hgate : (sahaFactorLipConst kB Tmin Tmax me h chi gZ EZ gZ1 EZ1 / R0)
              * ((|∑ k, (E k - mean E) * svec k| / (∑ k, (E k - mean E) ^ 2))
                  / (kB * smin ^ 2 * nemin)) < 1) :
    ∃ Tstar ∈ Set.Icc Tmin Tmax,
      outerMap (fun T => electronDensityFromRatio kB T me h chi gZ EZ gZ1 EZ1 R)
          (fun ne => combinedSlopeTempUpdate kB E yb svec offConst ne) Tstar = Tstar ∧
      (∀ T ∈ Set.Icc Tmin Tmax,
          outerMap (fun T => electronDensityFromRatio kB T me h chi gZ EZ gZ1 EZ1 R)
            (fun ne => combinedSlopeTempUpdate kB E yb svec offConst ne) T = T → T = Tstar) ∧
      ∀ T0 ∈ Set.Icc Tmin Tmax,
        Filter.Tendsto (fun n => (outerMap
            (fun T => electronDensityFromRatio kB T me h chi gZ EZ gZ1 EZ1 R)
            (fun ne => combinedSlopeTempUpdate kB E yb svec offConst ne))^[n] T0)
          Filter.atTop (nhds Tstar) := by
  have hRpos : 0 < R := lt_of_lt_of_le hR0 hR
  have hmapsNe : ∀ T ∈ Set.Icc Tmin Tmax,
      electronDensityFromRatio kB T me h chi gZ EZ gZ1 EZ1 R ∈ Set.Icc nemin nemax := by
    intro T hT
    exact Set.Icc_subset_Icc hnelo hnehi
      (electronDensityFromRatio_mem_Icc hkB hme hh hchi hgZ hEZ hgZ1 hEZ1 hEχ hTmin hRpos hT)
  exact outerLoop_contracts hTle hkB hme hh hchi hTmin hgZ hEZ hgZ1 hEZ1 hR0 hR hvar hnemin hsmin
    hmapsNe hmapsT hslopeFloor hL1nn hgate

/-! ### Non-vacuity witnesses

Concrete `Fin 1` toy plasma (`k_B = m_e = h = 1`, `g = 1`, `E = 0 ≤ chi = 1`, `R = 1`) on the box
`[1,2]` certifying that the enclosure lemmas fire on genuine data, and that the a-priori `hmapsNe`
discharge is satisfiable (taking `nemin, nemax` to be the two `n_e` endpoints). -/

private def toyG : Fin 1 → ℝ := fun _ => 1
private def toyE : Fin 1 → ℝ := fun _ => 0

/-- Non-vacuity for `sahaFactor_mem_Icc`: every `S(T)`, `T ∈ [1,2]`, lands between `S(1)` and
`S(2)` on the toy data (`E = 0 = ` a valid level below the ceiling `chi = 1`). -/
example (T : ℝ) (hT : T ∈ Set.Icc (1 : ℝ) 2) :
    sahaFactor 1 T 1 1 1 toyG toyE toyG toyE ∈
      Set.Icc (sahaFactor 1 1 1 1 1 toyG toyE toyG toyE)
        (sahaFactor 1 2 1 1 1 toyG toyE toyG toyE) :=
  sahaFactor_mem_Icc (ι := Fin 1) (κ := Fin 1) one_pos one_pos one_pos zero_le_one
    (fun _ => by norm_num [toyG]) (fun _ => by norm_num [toyE])
    (fun _ => by norm_num [toyG]) (fun _ => by norm_num [toyE])
    (fun _ => by norm_num [toyE]) one_pos hT

/-- Non-vacuity for the a-priori `hmapsNe` discharge: picking `nemin = n_e(1)` and
`nemax = n_e(2)` (the density endpoints), *every* `T ∈ [1,2]` satisfies
`n_e(T) ∈ [nemin, nemax]` — exactly the box invariance `outerLoop_contracts_apriori` proves from
its two endpoint containments (here both are `le_refl`), witnessed on concrete data. -/
example : ∀ T ∈ Set.Icc (1 : ℝ) 2,
    electronDensityFromRatio 1 T 1 1 1 toyG toyE toyG toyE 1 ∈
      Set.Icc (electronDensityFromRatio 1 1 1 1 1 toyG toyE toyG toyE 1)
        (electronDensityFromRatio 1 2 1 1 1 toyG toyE toyG toyE 1) := by
  intro T hT
  exact electronDensityFromRatio_mem_Icc (ι := Fin 1) (κ := Fin 1)
    one_pos one_pos one_pos zero_le_one
    (fun _ => by norm_num [toyG]) (fun _ => by norm_num [toyE])
    (fun _ => by norm_num [toyG]) (fun _ => by norm_num [toyE])
    (fun _ => by norm_num [toyE]) one_pos one_pos hT

end CflibsFormal

