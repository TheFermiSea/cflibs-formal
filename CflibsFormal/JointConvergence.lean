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

This leaf states the **joint `(T, n_e)` convergence theorem** for the frozen-offset Model-B
outer loop of `OuterLoopModelB`, instantiating the abstract 2-D box Banach spine
`jointOuterContraction_box` (`SahaEquilibrium`) at the two legs: the temperature update
`fT (T,n_e) = combinedSlopeTempUpdate … n_e` (`ErrorBudget`, depends **only on `n_e`**) and
the density reader `fNe (T,n_e) = electronDensityFromRatio … T … R` (`Saha`, `n_e(T)=S(T)/R`,
depends **only on `T`**). Each leg ignores its own output coordinate, so the joint row-sum
matrix is **anti-diagonal** — `a=0`, `b=L₂`, `c=L₁`, `d=0` — with density `T`-constant
`L₁ = sahaFactorLipConst … / R₀` (`electronDensityFromRatio_lipschitz_temp`) and temperature
`n_e`-constant `L₂ = (|∑ₖ (Eₖ − Ē)·sₖ| / SS_E)/(k_B·smin²·nemin)`
(`combinedSlopeTempUpdate_lipschitz`). The gate `max (a+b) (c+d) < 1` collapses to
`max L₂ L₁ < 1`.

## Literature and scope

`REDUCED` (Aguilera & Aragón 2007, Model B; Saha–Eggert (Griem)). The reduction is the one
named in `OuterLoopModelB`: the Saha offset `offConst` is frozen at a reference `T`, the density
leg reads a fixed measured stage ratio `R`, and the slope is the single-element,
unshifted-abscissa `combinedSahaBoltzmannSlope`. With the offset evaluated at the current `T` the
Saha coupling cancels. The theorem does not model the companion's `iterative.py` loop.

**Not a genuinely 2-D result.** Both legs ignore their own coordinate (`a = d = 0`), so the
joint iteration is the 1-D composite `Φ = legT ∘ legNe` of `outerLoop_contracts` unrolled: from
`(T₀, n₀)` the `T`-coordinate is `Φ^[k] T₀` at step `2k` and `Φ^[k] (legT n₀)` at step `2k+1`.
Mathematically the conclusion therefore follows from `outerLoop_contracts_apriori` plus the
Lipschitz continuity of `legNe` (it is proved here directly through the 2-D spine instead). The
joint state iterates in the product (max) metric on `ℝ × ℝ`, and the fixed point is
`pstar = (T⋆, n_e(T⋆))` with `T⋆` the fixed point of `Φ`, self-consistent in both coordinates.
The gate `max L₂ L₁ < 1` implies the product gate `L₁·L₂ < 1` and is strictly stronger:
`L₁ = 2`, `L₂ = 0.1` passes the product gate and fails this one. A genuinely 2-D case
(`a, d ≠ 0`) needs legs that depend on their own coordinate, e.g. an offset evaluated at the
current `T`.

*Discharged.* The two anti-diagonal Lipschitz bounds (from the two published sensitivity
lemmas), the four coefficient signs, and the density interval-invariance `hmapsNe` — proven
a-priori from the endpoint containments `hnelo`/`hnehi` via `electronDensityFromRatio_mem_Icc`
∘ `Set.Icc_subset_Icc`, as in `outerLoop_contracts_apriori`.

*Carried (side conditions).* The temperature interval-invariance `hmapsT`
(no monotonicity for the slope-inversion leg), the slope floor `hslopeFloor`, the box
order/positivity data, the level-truncation obligation `hEχ` (the lower-stage level list is
truncated at or below `chi`; see `sahaFactor_strictMonoOn_temp`), and the **convergence gate**
`hgate : max L₂ L₁ < 1` (sufficient, not necessary). The gate is arithmetic on known
quantities, but `L₁` inherits the 10⁶–10⁸ looseness of `sahaFactorLipConst`, so on real data it
fails by orders of magnitude (see `OuterLoopModelB`).

## Damped-loop and weighted-gate building blocks (frontier FT-01, `PURE-MATH`)

The last section adds three `PURE-MATH` results toward the stop certificate for the loop the
companion pipeline runs (certificate ID C11 under owner decision D16): `dampedMap_contracts`
(a derivative-window certificate for a damped iteration on an invariant box),
`tDamped_mobius_converges` (the `T`-damped iteration of a Möbius temperature map converges for
gains in `(0, 1)`) and `exists_weights_iff` (a unit-invariant test for the weighted row-sum gate
of `jointOuterContraction_box`). They carry no physical claim; binding them to the pipeline's
temperature map is a separate REDUCED step.
-/

namespace CflibsFormal

open Finset Real
open scoped BigOperators NNReal

/-- **The frozen-offset Model-B joint `(T, n_e)` outer loop contracts** (`REDUCED`; Aguilera &
Aragón 2007, Model B; Saha–Eggert (Griem)). Instantiating the abstract 2-D box Banach theorem
`jointOuterContraction_box` at the anti-diagonal CF-LIBS legs `fT (T,n_e) =
combinedSlopeTempUpdate … n_e` and `fNe (T,n_e) = electronDensityFromRatio … T … R`: the joint
sweep `Φ (T,n_e) = (fT T n_e, fNe T n_e)` on the box `[Tmin,Tmax] ×ˢ [nemin,nemax]` has a
**unique** self-consistent fixed point `pstar`, and the iterates `Φ^[n] p0` converge to `pstar`
jointly in both coordinates (product metric) from every start in the box. The density
interval-invariance is discharged a-priori from the endpoint containments `hnelo`/`hnehi`
(using the level-truncation obligation `hEχ`); the gate `max L₂ L₁ < 1` is the carried
convergence condition, strictly stronger than the product gate of `outerLoop_contracts`.
Because `a = d = 0` this is the 1-D composite unrolled (module docstring), and the reduction
(frozen Saha offset, fixed stage ratio `R`) is that of `OuterLoopModelB`. -/
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

section DampedLoopCertificate

/-! ### Building blocks for the `(T, n_e)` loop stop certificate (frontier FT-01)

Owner decision D16 assigns certificate ID C11 to a stop certificate for the `(T, n_e)` loop the
companion's `iterative.py` actually runs: a temperature update damped with `λ = 1/2`. The
results below are its `PURE-MATH` building blocks, not the certificate itself:

* `dampedMap_contracts`: a derivative-window certificate for a damped fixed-point iteration on
  an invariant box, replacing the product gate `L₁·L₂ < 1` of `outerContraction_box`;
* `tDamped_mobius_converges`: the `T`-damped iteration of a Möbius temperature map (the reduced
  outer map, affine in `1/T`) converges from every positive start for gains in `(0, 1)`;
* `exists_weights_iff`: a unit-invariant test for when some rescaling of `T` and `n_e` makes
  the row-sum gate of `jointOuterContraction_box` hold.

Whether the pipeline's temperature map satisfies these hypotheses on a given window is a
REDUCED binding that is not stated here. -/

open Filter Topology

/-- Krasnoselskii–Mann damped map `u ↦ (1−λ)u + λ g(u)` (the pipeline uses `λ = 1/2`).
One relaxation step of the fixed-point iteration for `g` with damping `lam` (`lam = 1` is plain
substitution). The CF-LIBS pipeline relaxes its outer temperature update with `lam = 1/2`,
`T_K = 0.5 * T_prev + 0.5 * T_new` (CF-LIBS-improved `cflibs/inversion/solve/iterative.py`,
lines 908 and 2454), so there the damped coordinate `u` is the temperature `T` itself. -/
def dampedMap (lam : ℝ) (g : ℝ → ℝ) (u : ℝ) : ℝ := (1 - lam) * u + lam * g u

/-- **Derivative-window Lipschitz bound for the damped map.** If `g' T ∈ [m, M]` is the
derivative of `g` at every point of `[a, b]`, `lam > 0`, `1 - 2/lam < m` and `M < 1`, then
`dampedMap lam g` is `q`-Lipschitz on `[a, b]` for some `0 ≤ q < 1`, namely
`q = max |1 - lam + lam * m| |1 - lam + lam * M|` (mean value theorem). `PURE-MATH`. -/
theorem dampedMap_lipschitz {g g' : ℝ → ℝ} {a b m M lam : ℝ} (hlam0 : 0 < lam) (hab : a ≤ b)
    (hd : ∀ T ∈ Set.Icc a b, HasDerivAt g (g' T) T)
    (hmM : ∀ T ∈ Set.Icc a b, m ≤ g' T ∧ g' T ≤ M) (hlo : 1 - 2 / lam < m) (hhi : M < 1) :
    ∃ q : ℝ, 0 ≤ q ∧ q < 1 ∧ ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b,
      |dampedMap lam g y - dampedMap lam g x| ≤ q * |y - x| := by
  set mH : ℝ := 1 - lam + lam * m with hmHdef
  set MH : ℝ := 1 - lam + lam * M with hMHdef
  set q : ℝ := max |mH| |MH| with hqdef
  have hderiv : ∀ T ∈ Set.Icc a b, HasDerivAt (dampedMap lam g) (1 - lam + lam * g' T) T := by
    intro T hT
    have h1 : HasDerivAt (fun u => (1 - lam) * u) (1 - lam) T := by
      simpa using (hasDerivAt_id T).const_mul (1 - lam)
    have h2 : HasDerivAt (fun u => lam * g u) (lam * g' T) T := by
      simpa using (hd T hT).const_mul lam
    have hsum : HasDerivAt (fun u => (1 - lam) * u + lam * g u) (1 - lam + lam * g' T) T :=
      h1.add h2
    have heq : dampedMap lam g = fun u => (1 - lam) * u + lam * g u := by
      funext u
      simp [dampedMap]
    rw [heq]
    exact hsum
  have hwindow : ∀ T ∈ Set.Icc a b,
      mH ≤ 1 - lam + lam * g' T ∧ 1 - lam + lam * g' T ≤ MH := by
    intro T hT
    have hmh := hmM T hT
    constructor
    · have hlm : lam * m ≤ lam * g' T := mul_le_mul_of_nonneg_left hmh.1 hlam0.le
      simpa [mH] using add_le_add (le_rfl : (1 - lam) ≤ (1 - lam)) hlm
    · have hlm : lam * g' T ≤ lam * M := mul_le_mul_of_nonneg_left hmh.2 hlam0.le
      simpa [MH] using add_le_add (le_rfl : (1 - lam) ≤ (1 - lam)) hlm
  have hbound : ∀ T ∈ Set.Icc a b, |1 - lam + lam * g' T| ≤ q := by
    intro T hT
    simpa [q, mH, MH] using abs_le_max_abs_abs (hwindow T hT).1 (hwindow T hT).2
  have hMHlt : MH < 1 := by
    have hpos : 0 < 1 - M := sub_pos.mpr hhi
    have hprod : 0 < lam * (1 - M) := mul_pos hlam0 hpos
    have hrew : MH = 1 - lam * (1 - M) := by
      dsimp [MH]
      ring_nf
    rw [hrew]
    exact sub_lt_self 1 hprod
  have hmHgt : -1 < mH := by
    have hmul : lam * (1 - 2 / lam) < lam * m := mul_lt_mul_of_pos_left hlo hlam0
    have hleft : lam * (1 - 2 / lam) = lam - 2 := by
      field_simp [hlam0.ne']
    have h1 : lam - 2 < lam * m := by
      simpa [hleft] using hmul
    have h2 : -1 < 1 - lam + lam * m := by
      linarith
    simpa [mH] using h2
  have hmmM : m ≤ M := (hmM a ⟨le_rfl, hab⟩).1.trans ((hmM a ⟨le_rfl, hab⟩).2)
  have hmHleMH : mH ≤ MH := by
    simpa [mH, MH] using
      add_le_add (le_rfl : (1 - lam) ≤ (1 - lam)) (mul_le_mul_of_nonneg_left hmmM hlam0.le)
  have habsMH : |MH| < 1 := abs_lt.2 ⟨lt_of_lt_of_le hmHgt hmHleMH, hMHlt⟩
  have habsmH : |mH| < 1 := abs_lt.2 ⟨hmHgt, lt_of_le_of_lt hmHleMH hMHlt⟩
  have hq : q < 1 := max_lt habsmH habsMH
  have hq0 : 0 ≤ q := le_trans (abs_nonneg mH) (le_max_left _ _)
  set H : ℝ → ℝ := dampedMap lam g with hHdef
  have hLip : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, |H y - H x| ≤ q * |y - x| := by
    intro x hx y hy
    have hconv : Convex ℝ (Set.Icc a b) := convex_Icc a b
    have hwithin : ∀ T ∈ Set.Icc a b,
        HasDerivWithinAt H (1 - lam + lam * g' T) (Set.Icc a b) T :=
      fun T hT => (hderiv T hT).hasDerivWithinAt
    have hnormbound : ∀ T ∈ Set.Icc a b, ‖1 - lam + lam * g' T‖ ≤ q :=
      fun T hT => by simpa using hbound T hT
    have hmain : ‖H y - H x‖ ≤ q * ‖y - x‖ :=
      Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hwithin hnormbound hconv hx hy
    simpa [H] using hmain
  exact ⟨q, hq0, hq, by simpa [H] using hLip⟩

/-- **Derivative-window certificate for a damped fixed-point iteration on an invariant box.**
Let `g` have derivative `g' T ∈ [m, M]` at every point of the box `[a, b]` (`a ≤ b`), and let the
damped map `H := dampedMap lam g`, `T ↦ (1 - lam) * T + lam * g T`, map `[a, b]` into itself. If
`1 - 2/lam < m` and `M < 1`, then `H` has a fixed point `Tstar ∈ [a, b]` (equivalently, since
`lam > 0`, `g Tstar = Tstar`) and the `H`-iterates converge to `Tstar` from every start in
`[a, b]`.

Why: `H' = 1 - lam + lam * g' ∈ [1 - lam + lam * m, 1 - lam + lam * M] ⊂ (-1, 1)`, so by the mean
value theorem `H` is a `q`-contraction on `[a, b]` with
`q = max |1 - lam + lam * m| |1 - lam + lam * M| < 1` (`dampedMap_lipschitz`), and Banach's
theorem applies on the complete nonempty interval.

Use: for the T-damped outer loop this replaces the product-of-Lipschitz gate `L1 * L2 < 1` of
`outerContraction_box` (`SahaEquilibrium.lean`), which the audit found 10^3 to 10^5 too loose. It
is to be bound with `g'` the derivative of the undamped T-map, not a constant gain. `hmaps` can
be checked a posteriori from the temperature window.

Hypotheses. `hlam0`: any positive damping (no upper bound is needed). `hab`: the box is nonempty.
`hd`: two-sided differentiability at every box point, endpoints included. `hmM`, `hlo`, `hhi`: the
derivative window; it cannot be widened, since `g' < 1 - 2/lam` gives `H' < -1` and a fixed point
with `g' > 1` repels for every `lam > 0`. `hmaps`: box invariance, which is not automatic.

Scope (two-axis): PURE-MATH on both axes (no model definitions); published tag PURE-MATH.
Whether the pipeline's T-map satisfies `hd`, `hmM` and `hmaps` on a given window is the REDUCED
binding, not claimed here. -/
theorem dampedMap_contracts {g g' : ℝ → ℝ} {a b m M lam : ℝ} (hlam0 : 0 < lam) (hab : a ≤ b)
    (hd : ∀ T ∈ Set.Icc a b, HasDerivAt g (g' T) T)
    (hmM : ∀ T ∈ Set.Icc a b, m ≤ g' T ∧ g' T ≤ M) (hlo : 1 - 2 / lam < m) (hhi : M < 1)
    (hmaps : Set.MapsTo (dampedMap lam g) (Set.Icc a b) (Set.Icc a b)) :
    ∃ Tstar ∈ Set.Icc a b, dampedMap lam g Tstar = Tstar ∧
      ∀ T0 ∈ Set.Icc a b, Tendsto (fun n => (dampedMap lam g)^[n] T0) atTop (𝓝 Tstar) := by
  obtain ⟨q, hq0, hq, hLip⟩ := dampedMap_lipschitz hlam0 hab hd hmM hlo hhi
  have hcomplete : IsComplete (Set.Icc a b) := isClosed_Icc.isComplete
  set K : NNReal := ⟨q, hq0⟩ with hKdef
  have hKcoe : (K : ℝ) = q := rfl
  have hK : K < 1 := by rw [← NNReal.coe_lt_one, hKcoe]; exact hq
  have hlip : LipschitzWith K
      (hmaps.restrict (dampedMap lam g) (Set.Icc a b) (Set.Icc a b)) := by
    refine lipschitzWith_iff_dist_le_mul.mpr ?_
    rintro ⟨x, hx⟩ ⟨y, hy⟩
    rw [Subtype.dist_eq, Subtype.dist_eq, Set.MapsTo.val_restrict_apply,
        Set.MapsTo.val_restrict_apply, Real.dist_eq, Real.dist_eq, hKcoe]
    exact hLip y hy x hx
  have hcontract : ContractingWith K
      (hmaps.restrict (dampedMap lam g) (Set.Icc a b) (Set.Icc a b)) :=
    ⟨hK, hlip⟩
  have hxs : a ∈ Set.Icc a b := Set.left_mem_Icc.mpr hab
  have hxne : edist a (dampedMap lam g a) ≠ ⊤ := edist_ne_top _ _
  obtain ⟨Tstar, hTstarmem, hfixpt, htend, _herr⟩ :=
    hcontract.exists_fixedPoint' hcomplete hmaps hxs hxne
  have hfixeq : dampedMap lam g Tstar = Tstar := hfixpt
  refine ⟨Tstar, hTstarmem, hfixeq, ?_⟩
  intro T0 hT0
  have hT0ne : edist T0 (dampedMap lam g T0) ≠ ⊤ := edist_ne_top _ _
  obtain ⟨y0, hy0mem, hy0fix, hy0tend, _⟩ :=
    hcontract.exists_fixedPoint' hcomplete hmaps hT0 hT0ne
  have hy0fixeq : dampedMap lam g y0 = y0 := hy0fix
  have hsame : y0 = Tstar := by
    have h1 : |dampedMap lam g Tstar - dampedMap lam g y0| ≤ q * |Tstar - y0| :=
      hLip y0 hy0mem Tstar hTstarmem
    have h2 : |Tstar - y0| ≤ q * |Tstar - y0| := by
      simpa [hfixeq, hy0fixeq] using h1
    have h3 : |Tstar - y0| = 0 := by
      have hq0' : 0 ≤ q := hq0
      have hq1 : q < 1 := hq
      have habs : 0 ≤ |Tstar - y0| := abs_nonneg _
      nlinarith
    have h4 : Tstar - y0 = 0 := abs_eq_zero.mp h3
    linarith
  simpa [hsame] using hy0tend

/-- Monotone-orbit convergence: `H` monotone on `(0, ∞)` with unique positive fixed point `Ts`,
pushing points up below `Ts` and down above it, and continuous on `(0, ∞)`; then every positive
orbit converges to `Ts`. -/
private lemma orbit_tendsto_of_monotone {H : ℝ → ℝ} {Ts T0 : ℝ} (hTs : 0 < Ts) (hT0 : 0 < T0)
    (hmono : ∀ S T, 0 < S → S ≤ T → H S ≤ H T) (hfix : H Ts = Ts)
    (hup : ∀ T, 0 < T → T ≤ Ts → T ≤ H T) (hdown : ∀ T, Ts ≤ T → H T ≤ T)
    (hcont : ∀ T, 0 < T → ContinuousAt H T)
    (huniq : ∀ L, 0 < L → H L = L → L = Ts) :
    Tendsto (fun n => H^[n] T0) atTop (𝓝 Ts) := by
  cases le_total T0 Ts with
  | inl hle =>
    have hbounds : ∀ n, T0 ≤ H^[n] T0 ∧ H^[n] T0 ≤ Ts := by
      intro n
      induction n with
      | zero => exact ⟨le_rfl, hle⟩
      | succ n ih =>
        have h1 : T0 ≤ H^[n] T0 := ih.1
        have h2 : H^[n] T0 ≤ Ts := ih.2
        have hposn : 0 < H^[n] T0 := lt_of_lt_of_le hT0 h1
        rw [Function.iterate_succ_apply' H n T0]
        exact ⟨le_trans h1 (hup (H^[n] T0) hposn h2),
          le_trans (hmono (H^[n] T0) Ts hposn h2) (le_of_eq hfix)⟩
    have hmono_seq : Monotone (fun n : ℕ => H^[n] T0) :=
      monotone_nat_of_le_succ fun n => by
        rw [Function.iterate_succ_apply' H n T0]
        exact hup (H^[n] T0) (lt_of_lt_of_le hT0 (hbounds n).1) (hbounds n).2
    have hbdd : BddAbove (Set.range (fun n : ℕ => H^[n] T0)) :=
      ⟨Ts, fun x hx => by
        obtain ⟨k, rfl⟩ := hx
        exact (hbounds k).2⟩
    set L := ⨆ i : ℕ, H^[i] T0
    have htend : Tendsto (fun n : ℕ => H^[n] T0) atTop (𝓝 L) :=
      tendsto_atTop_ciSup hmono_seq hbdd
    have hLpos : 0 < L := lt_of_lt_of_le hT0 (ge_of_tendsto' htend (fun n => (hbounds n).1))
    have hcontL : ContinuousAt H L := hcont L hLpos
    have hfixL : H L = L := isFixedPt_of_tendsto_iterate htend hcontL
    rw [huniq L hLpos hfixL] at htend
    exact htend
  | inr hle =>
    have hbounds : ∀ n, Ts ≤ H^[n] T0 ∧ H^[n] T0 ≤ T0 := by
      intro n
      induction n with
      | zero => exact ⟨hle, le_rfl⟩
      | succ n ih =>
        have h1 : Ts ≤ H^[n] T0 := ih.1
        have h2 : H^[n] T0 ≤ T0 := ih.2
        rw [Function.iterate_succ_apply' H n T0]
        exact ⟨(le_of_eq hfix.symm).trans (hmono Ts (H^[n] T0) hTs h1),
          le_trans (hdown (H^[n] T0) h1) h2⟩
    have hanti : Antitone (fun n : ℕ => H^[n] T0) :=
      antitone_nat_of_succ_le fun n => by
        rw [Function.iterate_succ_apply' H n T0]
        exact hdown (H^[n] T0) (hbounds n).1
    have hbdd : BddBelow (Set.range (fun n : ℕ => H^[n] T0)) :=
      ⟨Ts, fun x hx => by
        obtain ⟨k, rfl⟩ := hx
        exact (hbounds k).1⟩
    set L := ⨅ i : ℕ, H^[i] T0
    have htend : Tendsto (fun n : ℕ => H^[n] T0) atTop (𝓝 L) :=
      tendsto_atTop_ciInf hanti hbdd
    have hLpos : 0 < L := lt_of_lt_of_le hTs (ge_of_tendsto' htend (fun n => (hbounds n).1))
    have hcontL : ContinuousAt H L := hcont L hLpos
    have hfixL : H L = L := isFixedPt_of_tendsto_iterate htend hcontL
    rw [huniq L hLpos hfixL] at htend
    exact htend

/-- `Ts = (1-g)/c` is positive since `g < 1` and `c > 0`. -/
private lemma tDampedMobius_Ts_pos {g c : ℝ} (hg1 : g < 1) (hc : 0 < c) : 0 < (1 - g) / c := by
  positivity

/-- `Ts = (1-g)/c` is a fixed point of the damped Möbius map, since `g + c*Ts = 1`. -/
private lemma tDampedMobius_fix {g c lam : ℝ} (_hg0 : 0 < g) (_hg1 : g < 1) (hc : 0 < c) :
    dampedMap lam (fun T => T / (g + c * T)) ((1 - g) / c) = (1 - g) / c := by
  simp only [dampedMap]
  have hden : g + c * ((1 - g) / c) = 1 := by
    field_simp [hc.ne']
    ring
  rw [hden]
  field_simp
  ring

/-- Below `Ts` the damped Möbius map pushes points up. -/
private lemma tDampedMobius_up {g c lam : ℝ} (hg0 : 0 < g) (hg1 : g < 1) (hc : 0 < c)
    (hl0 : 0 < lam) :
    ∀ T : ℝ, 0 < T → T ≤ (1 - g) / c → T ≤ dampedMap lam (fun T => T / (g + c * T)) T := by
  intro T hT0 hTle
  simp only [dampedMap]
  have hpos : 0 < g + c * T := by nlinarith
  have hTc : T * c ≤ 1 - g := (le_div_iff₀ hc).mp hTle
  have hphi : T ≤ T / (g + c * T) := by
    rw [le_div_iff₀ hpos]
    nlinarith [hTc]
  nlinarith [hphi, hg0, hg1, hc, hl0, hT0]

/-- Above `Ts` the damped Möbius map pushes points down. -/
private lemma tDampedMobius_down {g c lam : ℝ} (hg0 : 0 < g) (hg1 : g < 1) (hc : 0 < c)
    (hl0 : 0 < lam) :
    ∀ T : ℝ, (1 - g) / c ≤ T → dampedMap lam (fun T => T / (g + c * T)) T ≤ T := by
  intro T hTle
  simp only [dampedMap]
  have hT0 : 0 < T := lt_of_lt_of_le (div_pos (sub_pos.mpr hg1) hc) hTle
  have hpos : 0 < g + c * T := by nlinarith
  have hTc : 1 - g ≤ T * c := (div_le_iff₀ hc).mp hTle
  have hphi : T / (g + c * T) ≤ T := by
    rw [div_le_iff₀ hpos]
    nlinarith [hTc]
  nlinarith [hphi, hg0, hg1, hc, hl0, hT0]

/-- `Ts` is the only positive fixed point of the damped Möbius map. -/
private lemma tDampedMobius_uniq {g c lam : ℝ} (hg0 : 0 < g) (hc : 0 < c) (hl0 : 0 < lam) :
    ∀ L : ℝ, 0 < L → dampedMap lam (fun T => T / (g + c * T)) L = L → L = (1 - g) / c := by
  intro L hL0 heq
  simp only [dampedMap] at heq
  have hpos : 0 < g + c * L := by nlinarith
  have h1 : lam * (L / (g + c * L)) = lam * L := by nlinarith
  have h2 : L / (g + c * L) = L := by
    apply mul_left_cancel₀ (ne_of_gt hl0)
    exact h1
  have h3 : L = L * (g + c * L) := by
    rw [div_eq_iff (ne_of_gt hpos)] at h2
    exact h2
  have h4 : 1 = g + c * L := by
    rw [← mul_left_inj' (ne_of_gt hL0)]
    nlinarith [h3]
  have h5 : c * L = 1 - g := by nlinarith [h4]
  rw [eq_comm, div_eq_iff hc.ne']
  nlinarith [h5]

/-- For `0 < lam ≤ 1` the damped Möbius map is monotone on `(0, ∞)`. -/
private lemma tDampedMobius_mono {g c lam : ℝ} (hg0 : 0 < g) (hc : 0 < c) (hl0 : 0 < lam)
    (hl1 : lam ≤ 1) :
    ∀ S T : ℝ, 0 < S → S ≤ T →
      dampedMap lam (fun T => T / (g + c * T)) S
        ≤ dampedMap lam (fun T => T / (g + c * T)) T := by
  intro S T hS hST
  have hSg : 0 < g + c * S := by nlinarith
  have hSTg : 0 < g + c * T := by nlinarith
  have hphi : S / (g + c * S) ≤ T / (g + c * T) := by
    rw [div_le_div_iff₀ hSg hSTg]
    nlinarith
  have h1 : (1 - lam) * S ≤ (1 - lam) * T := by
    exact mul_le_mul_of_nonneg_left hST (by linarith : 0 ≤ 1 - lam)
  have h2 : lam * (S / (g + c * S)) ≤ lam * (T / (g + c * T)) := by
    exact mul_le_mul_of_nonneg_left hphi hl0.le
  simp only [dampedMap]
  nlinarith

/-- The damped Möbius map is continuous at every positive temperature. -/
private lemma tDampedMobius_cont {g c lam : ℝ} (hg0 : 0 < g) (hc : 0 < c) :
    ∀ T : ℝ, 0 < T → ContinuousAt (dampedMap lam (fun T => T / (g + c * T))) T := by
  intro T hT
  unfold dampedMap
  have hden : g + c * T ≠ 0 := by
    have : 0 < g + c * T := by nlinarith
    exact ne_of_gt this
  apply ContinuousAt.add
  · exact continuousAt_const.mul continuousAt_id
  · apply ContinuousAt.mul continuousAt_const
    apply ContinuousAt.div continuousAt_id
      (continuousAt_const.add (continuousAt_const.mul continuousAt_id))
      hden

/-- **The T-damped Möbius iteration converges from every positive start when `0 < g < 1`.**
Model: suppose the undamped outer update is affine in inverse temperature, `u ↦ g * u + c` with
`u = 1/T` (`k_B` absorbed; everything dimensionless). In temperature this is the Möbius map
`φ T = T / (g + c * T)`, whose positive fixed point is `T* = (1 - g) / c`. The pipeline damps `T`:
it iterates `H := dampedMap lam φ`, `T ↦ (1 - lam) * T + lam * φ T`. For gain `0 < g < 1`,
`c > 0` and damping `0 < lam ≤ 1`, the `H`-iterates converge to `T*` from every `T0 > 0`.

This replaces the u-damped idealization for the pipeline: there `u ↦ (1 - lam) * u +
lam * (g * u + c)` is affine with rate `1 - lam + lam * g` and converges from every start iff
`1 - 2/lam < g < 1`, but that window is false for T-damping (the audit's verifier found that at
`g = -1` the T-iterates go negative), so this statement keeps `g > 0`.

Proof idea (the statement asserts convergence only): `H T - T = lam * T * (1 - g - c * T) /
(g + c * T)`, and `H` is increasing on `T > 0` with `H T* = T*` (this uses `lam ≤ 1`), so the orbit
is monotone (upward from below `T*`, downward from above) and bounded; its limit
`L ≥ min T0 T* > 0` is a fixed point of `H`, hence of `φ`, hence `L = T*`.

Hypotheses. `hg0` keeps `g + c * T > 0` for all `T > 0` (for `g < 0` the Möbius map has a pole at
`T = -g/c > 0`; the boundary case `g = 0`, a constant map, is excluded for simplicity). `hg1` is
needed: for `g ≥ 1` there is no positive fixed point (`(1 - g) / c ≤ 0`). `hc` makes `T*`
positive. `hl0`, `hl1` put the damping in `(0, 1]`; `lam ≤ 1` keeps `H` order-preserving (no
overshoot). `hT0` is a positive starting temperature.

Scope (two-axis): PURE-MATH on both axes (no model definitions); published tag PURE-MATH. The
binding "the reduced outer map of `iterative.py` is `u ↦ g * u + c` on one median piece, IPD
off" is REDUCED and is NOT proved here. The Saha–Boltzmann outer loop that the binding models is
described in Aguilera & Aragón 2007 and Yalcin 1999; this statement itself is pure
mathematics. -/
theorem tDamped_mobius_converges {g c lam : ℝ} (hg0 : 0 < g) (hg1 : g < 1) (hc : 0 < c)
    (hl0 : 0 < lam) (hl1 : lam ≤ 1) (T0 : ℝ) (hT0 : 0 < T0) :
    Tendsto (fun n => (dampedMap lam (fun T => T / (g + c * T)))^[n] T0) atTop
      (𝓝 ((1 - g) / c)) := by
  exact orbit_tendsto_of_monotone (H := dampedMap lam (fun T => T / (g + c * T)))
    (Ts := (1 - g) / c)
    (tDampedMobius_Ts_pos hg1 hc) hT0
    (tDampedMobius_mono hg0 hc hl0 hl1)
    (tDampedMobius_fix hg0 hg1 hc)
    (tDampedMobius_up hg0 hg1 hc hl0)
    (tDampedMobius_down hg0 hg1 hc hl0)
    (tDampedMobius_cont hg0 hc)
    (tDampedMobius_uniq hg0 hc hl0)

/-- Constructive direction of `exists_weights_iff`: a single scale ratio `r > 0` making both
weighted rows sub-unit exists under the unit-invariant condition. -/
private theorem weights_of_gate {a b c d : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h1 : a < 1) (h2 : d < 1) (h3 : b * c < (1 - a) * (1 - d)) :
    ∃ r : ℝ, 0 < r ∧ a + b * r < 1 ∧ c / r + d < 1 := by
  have hd1 : 0 < 1 - d := by linarith
  have ha1 : 0 < 1 - a := by linarith
  rcases hb.eq_or_lt with hb0 | hbpos
  · subst hb0
    refine ⟨c / (1 - d) + 1, by positivity, by linarith, ?_⟩
    have hr : 0 < c / (1 - d) + 1 := by positivity
    rw [div_add' _ _ _ hr.ne', div_lt_one hr]
    have : c = c / (1 - d) * (1 - d) := by field_simp
    nlinarith
  · set r := (c / (1 - d) + (1 - a) / b) / 2
    have hlo : c / (1 - d) < (1 - a) / b := by
      rw [div_lt_div_iff₀ hd1 hbpos]; nlinarith
    have hr : 0 < r := by
      have : 0 ≤ c / (1 - d) := by positivity
      have : 0 < (1 - a) / b := by positivity
      simp only [r]; linarith
    refine ⟨r, hr, ?_, ?_⟩
    · have : r < (1 - a) / b := by simp only [r]; linarith
      have := (lt_div_iff₀ hbpos).mp this
      linarith
    · have : c / (1 - d) < r := by simp only [r]; linarith
      have h' : c < r * (1 - d) := by rwa [div_lt_iff₀ hd1] at this
      have : c / r < 1 - d := by rw [div_lt_iff₀ hr]; linarith
      linarith

/-- **When a weighted row-sum gate exists for a 2×2 Lipschitz coupling (FT-01(d)).**
Let `a, b, c, d` be the two-variable Lipschitz coefficients of a joint update
`(T, n) ↦ (fT T n, fNe T n)`: `|ΔfT| ≤ a|ΔT| + b|Δn|` and `|ΔfNe| ≤ c|ΔT| + d|Δn|`.
Measuring `T` in units of `wT` and `n` in units of `wn` (positive scale factors) turns these
into `|ΔfT| ≤ a|ΔT| + b(wn/wT)|Δn|` and `|ΔfNe| ≤ c(wT/wn)|ΔT| + d|Δn|`. The theorem says that
some choice of positive scales makes the weighted row-sum gate
`max (a + b * wn / wT) (c * wT / wn + d) < 1` hold iff `a < 1`, `d < 1` and
`b * c < (1 - a) * (1 - d)`.

Why it matters: the spine `jointOuterContraction_box` (`SahaEquilibrium.lean`) is gated by the
unweighted row sums `max (a + b) (c + d) < 1`. That gate depends on the units: with `T` in eV
and `n_e` in cm⁻³ the off-diagonal coefficients differ by many orders of magnitude, and the
audit found (PS-10) that the gate always fails in those units. Rescaling `n_e` by `s` sends
`b ↦ b / s` and `c ↦ s * c`, so `a`, `d` and `b * c` are unit-invariant, and so is the
right-hand side here. A contraction certificate can therefore test the right-hand side and then
apply `jointOuterContraction_box` in the rescaled coordinates. Example: `a = d = 1/2`, `b = 100`,
`c = 1/1000` fails the unweighted gate (`a + b > 1`) but satisfies `b * c = 1/10 < 1/4`.

Hypotheses. `hb : 0 ≤ b` and `hc : 0 ≤ c` are needed for (⇒): with `b < 0` the weighted row
`a + b * wn / wT` can be below `1` although `a ≥ 1` (e.g. `a = 5`, `b = -10`, `c = d = 0`,
`wT = wn = 1`). Lipschitz coefficients are nonnegative, so these hypotheses are free in use.
No sign condition on `a` or `d` is needed.

Scope (two-axis): relation PURE-MATH; no definitions are used; published tag PURE-MATH. Whether
the real CF-LIBS legs satisfy the Lipschitz bounds, and with which coefficients, is not claimed
here. The joint `(T, n_e)` iteration it serves is the multi-element Saha–Boltzmann loop of
Aguilera & Aragón 2007. -/
theorem exists_weights_iff {a b c d : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c) :
    (∃ wT wn : ℝ, 0 < wT ∧ 0 < wn ∧ max (a + b * wn / wT) (c * wT / wn + d) < 1)
      ↔ (a < 1 ∧ d < 1 ∧ b * c < (1 - a) * (1 - d)) := by
  constructor
  · rintro ⟨wT, wn, hT, hn, h⟩
    rw [max_lt_iff] at h
    obtain ⟨h1, h2⟩ := h
    set u := b * wn / wT with hu_def
    set v := c * wT / wn with hv_def
    have hu : 0 ≤ u := div_nonneg (mul_nonneg hb hn.le) hT.le
    have hv : 0 ≤ v := div_nonneg (mul_nonneg hc hT.le) hn.le
    have huv : u * v = b * c := by
      rw [hu_def, hv_def]; field_simp
    have ha1 : a < 1 := by linarith
    have hd1 : d < 1 := by linarith
    refine ⟨ha1, hd1, ?_⟩
    rw [← huv]
    nlinarith [mul_pos (sub_pos.2 h1) (sub_pos.2 hd1), mul_nonneg hu (sub_pos.2 h2).le]
  · rintro ⟨h1, h2, h3⟩
    obtain ⟨r, hr, har, hcr⟩ := weights_of_gate hb hc h1 h2 h3
    refine ⟨1, r, one_pos, hr, ?_⟩
    rw [max_lt_iff]
    constructor
    · simpa using har
    · simpa using hcr

end DampedLoopCertificate

end CflibsFormal
