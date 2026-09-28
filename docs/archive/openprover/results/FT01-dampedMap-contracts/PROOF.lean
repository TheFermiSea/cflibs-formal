-- Summary: Complete verified proof of dampedMap_contracts (Banach fixed point via Lipschitz helper), fix applied.
import Mathlib

open Filter Topology
open scoped NNReal

namespace Plan.FT01

def dampedMap (lam : ℝ) (g : ℝ → ℝ) (u : ℝ) : ℝ := (1 - lam) * u + lam * g u

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
  have hwindow : ∀ T ∈ Set.Icc a b, mH ≤ 1 - lam + lam * g' T ∧ 1 - lam + lam * g' T ≤ MH := by
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
    simpa [mH, MH] using add_le_add (le_rfl : (1 - lam) ≤ (1 - lam)) (mul_le_mul_of_nonneg_left hmmM hlam0.le)
  have habsMH : |MH| < 1 := abs_lt.2 ⟨lt_of_lt_of_le hmHgt hmHleMH, hMHlt⟩
  have habsmH : |mH| < 1 := abs_lt.2 ⟨hmHgt, lt_of_le_of_lt hmHleMH hMHlt⟩
  have hq : q < 1 := max_lt habsmH habsMH
  have hq0 : 0 ≤ q := le_trans (abs_nonneg mH) (le_max_left _ _)
  set H : ℝ → ℝ := dampedMap lam g with hHdef
  have hLip : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, |H y - H x| ≤ q * |y - x| := by
    intro x hx y hy
    have hconv : Convex ℝ (Set.Icc a b) := convex_Icc a b
    have hwithin : ∀ T ∈ Set.Icc a b, HasDerivWithinAt H (1 - lam + lam * g' T) (Set.Icc a b) T :=
      fun T hT => (hderiv T hT).hasDerivWithinAt
    have hnormbound : ∀ T ∈ Set.Icc a b, ‖1 - lam + lam * g' T‖ ≤ q :=
      fun T hT => by simpa using hbound T hT
    have hmain : ‖H y - H x‖ ≤ q * ‖y - x‖ :=
      Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hwithin hnormbound hconv hx hy
    simpa [H] using hmain
  exact ⟨q, hq0, hq, by simpa [H] using hLip⟩

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
  have hlip : LipschitzWith K (hmaps.restrict (dampedMap lam g) (Set.Icc a b) (Set.Icc a b)) := by
    refine lipschitzWith_iff_dist_le_mul.mpr ?_
    rintro ⟨x, hx⟩ ⟨y, hy⟩
    rw [Subtype.dist_eq, Subtype.dist_eq, Set.MapsTo.val_restrict_apply,
        Set.MapsTo.val_restrict_apply, Real.dist_eq, Real.dist_eq, hKcoe]
    exact hLip y hy x hx
  have hcontract : ContractingWith K (hmaps.restrict (dampedMap lam g) (Set.Icc a b) (Set.Icc a b)) :=
    ⟨hK, hlip⟩
  have hxs : a ∈ Set.Icc a b := Set.left_mem_Icc.mpr hab
  have hxne : edist a (dampedMap lam g a) ≠ ⊤ := edist_ne_top _ _
  obtain ⟨Tstar, hTstarmem, hfixpt, htend, _herr⟩ :=
    hcontract.exists_fixedPoint' hcomplete hmaps hxs hxne
  have hfixeq : dampedMap lam g Tstar = Tstar := hfixpt
  refine ⟨Tstar, hTstarmem, hfixeq, ?_⟩
  intro T0 hT0
  have hT0ne : edist T0 (dampedMap lam g T0) ≠ ⊤ := edist_ne_top _ _
  obtain ⟨y0, hy0mem, hy0fix, hy0tend, _⟩ := hcontract.exists_fixedPoint' hcomplete hmaps hT0 hT0ne
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

end Plan.FT01
