-- Summary: Complete verified Lean proof of neutralityNewton_enclosure (FT17): one Newton step brackets the charge-neutrality root.
import Mathlib
import CflibsFormal.SahaEquilibrium

open Finset CflibsFormal

namespace Plan.FT17

variable {ι : Type*} [Fintype ι]

noncomputable def neutralityNewton (S Ntot : ι → ℝ) (x : ℝ) : ℝ :=
  x - (x - multiElementIonized S Ntot x) / (1 + ∑ s, Ntot s * S s / (x + S s) ^ 2)

theorem neutralityNewton_error_eq (S Ntot : ι → ℝ) (hS : ∀ s, 0 < S s) (hN : ∀ s, 0 ≤ Ntot s)
    {x r : ℝ} (hx : 0 ≤ x) (hr : 0 ≤ r) (hfix : r = multiElementIonized S Ntot r) :
    neutralityNewton S Ntot x - r
      = -((x - r) ^ 2 * ∑ s, Ntot s * S s / ((x + S s) ^ 2 * (r + S s)))
          / (1 + ∑ s, Ntot s * S s / (x + S s) ^ 2) := by
  have hD : 0 < 1 + ∑ s, Ntot s * S s / (x + S s) ^ 2 := by
    have : 0 ≤ ∑ s, Ntot s * S s / (x + S s) ^ 2 :=
      Finset.sum_nonneg (fun s _ => div_nonneg (mul_nonneg (hN s) (hS s).le) (sq_nonneg _))
    linarith
  have htp := multiElementIonized_two_point S Ntot hS x r hx hr
  have hf : x - multiElementIonized S Ntot x
      = (x - r) * (1 + ∑ s, Ntot s * S s / ((x + S s) * (r + S s))) := by
    have : multiElementIonized S Ntot x = r + (r - x) *
        ∑ s, Ntot s * S s / ((x + S s) * (r + S s)) := by
      linarith [htp, hfix]
    rw [this]; ring
  have hterm : (∑ s, Ntot s * S s / (x + S s) ^ 2)
      - (∑ s, Ntot s * S s / ((x + S s) * (r + S s)))
      = (r - x) * ∑ s, Ntot s * S s / ((x + S s) ^ 2 * (r + S s)) := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    have h1 : 0 < x + S s := by linarith [hS s]
    have h2 : 0 < r + S s := by linarith [hS s]
    field_simp
    ring
  unfold neutralityNewton
  rw [hf, eq_div_iff hD.ne']
  have hD' := hD.ne'
  field_simp
  nlinarith [hterm]

theorem neutralityNewton_le_root (S Ntot : ι → ℝ) (hS : ∀ s, 0 < S s) (hN : ∀ s, 0 ≤ Ntot s)
    {x r : ℝ} (hx : 0 ≤ x) (hr : 0 ≤ r) (hfix : r = multiElementIonized S Ntot r) :
    neutralityNewton S Ntot x ≤ r := by
  have hid := neutralityNewton_error_eq S Ntot hS hN hx hr hfix
  have hD : 0 < 1 + ∑ s, Ntot s * S s / (x + S s) ^ 2 := by
    have : 0 ≤ ∑ s, Ntot s * S s / (x + S s) ^ 2 :=
      Finset.sum_nonneg (fun s _ => div_nonneg (mul_nonneg (hN s) (hS s).le) (sq_nonneg _))
    linarith
  have hnum : 0 ≤ (x - r) ^ 2 * ∑ s, Ntot s * S s / ((x + S s) ^ 2 * (r + S s)) := by
    refine mul_nonneg (sq_nonneg _) (Finset.sum_nonneg (fun s _ => ?_))
    have h1 : 0 < x + S s := by linarith [hS s]
    have h2 : 0 < r + S s := by linarith [hS s]
    exact div_nonneg (mul_nonneg (hN s) (hS s).le) (by positivity)
  have : neutralityNewton S Ntot x - r ≤ 0 := by
    rw [hid]; exact div_nonpos_of_nonpos_of_nonneg (by linarith) hD.le
  linarith

theorem G_nonneg (S Ntot : ι → ℝ) (hS : ∀ s, 0 < S s) (hN : ∀ s, 0 ≤ Ntot s)
    {x : ℝ} (hx : 0 ≤ x) : 0 ≤ multiElementIonized S Ntot x := by
  unfold multiElementIonized
  exact Finset.sum_nonneg (fun s _ => div_nonneg (mul_nonneg (hN s) (hS s).le) (by linarith [hS s]))

theorem neutralityNewton_nonneg (S Ntot : ι → ℝ) (hS : ∀ s, 0 < S s) (hN : ∀ s, 0 ≤ Ntot s)
    {x : ℝ} (hx : 0 ≤ x) : 0 ≤ neutralityNewton S Ntot x := by
  have hD : 0 < 1 + ∑ s, Ntot s * S s / (x + S s) ^ 2 := by
    have : 0 ≤ ∑ s, Ntot s * S s / (x + S s) ^ 2 :=
      Finset.sum_nonneg (fun s _ => div_nonneg (mul_nonneg (hN s) (hS s).le) (sq_nonneg _))
    linarith
  have hform : neutralityNewton S Ntot x =
      (x * (∑ s, Ntot s * S s / (x + S s) ^ 2) + multiElementIonized S Ntot x) /
        (1 + ∑ s, Ntot s * S s / (x + S s) ^ 2) := by
    unfold neutralityNewton
    field_simp
    ring
  rw [hform]
  apply div_nonneg
  · refine add_nonneg ?_ ?_
    · exact mul_nonneg hx (Finset.sum_nonneg (fun s _ => div_nonneg (mul_nonneg (hN s) (hS s).le) (sq_nonneg _)))
    · exact G_nonneg S Ntot hS hN hx
  · exact hD.le

theorem G_antitone (S Ntot : ι → ℝ) (hS : ∀ s, 0 < S s) (hN : ∀ s, 0 ≤ Ntot s)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a ≤ b) :
    multiElementIonized S Ntot b ≤ multiElementIonized S Ntot a := by
  have htp := multiElementIonized_two_point S Ntot hS a b ha hb
  have hsum : 0 ≤ ∑ s, Ntot s * S s / ((a + S s) * (b + S s)) :=
    Finset.sum_nonneg (fun s _ =>
      div_nonneg (mul_nonneg (hN s) (hS s).le)
        (mul_pos (by linarith [hS s]) (by linarith [hS s])).le)
  have : multiElementIonized S Ntot a - multiElementIonized S Ntot b ≥ 0 := by
    rw [htp]
    exact mul_nonneg (sub_nonneg_of_le hab) hsum
  linarith

theorem neutralityNewton_enclosure {S Ntot : ι → ℝ} {x r : ℝ} (hS : ∀ s, 0 < S s)
    (hN : ∀ s, 0 ≤ Ntot s) (hx : 0 ≤ x) (hr : 0 ≤ r)
    (hfix : r = multiElementIonized S Ntot r) :
    neutralityNewton S Ntot x ≤ r ∧
      r ≤ multiElementIonized S Ntot (neutralityNewton S Ntot x) := by
  have hle := neutralityNewton_le_root S Ntot hS hN hx hr hfix
  have hNx_nonneg := neutralityNewton_nonneg S Ntot hS hN hx
  have hanti := G_antitone S Ntot hS hN hNx_nonneg hr hle
  rw [← hfix] at hanti
  exact ⟨hle, hanti⟩

end Plan.FT17
