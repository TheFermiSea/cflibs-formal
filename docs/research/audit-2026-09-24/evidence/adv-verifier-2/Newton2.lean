import Mathlib
import CflibsFormal.SahaEquilibrium

namespace AdvNewton
open CflibsFormal Finset

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
  -- x - G x = (x - r) * (1 + Σ a/((x+S)(r+S)))
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



/-- FT-17 step 3: one Newton step from any `x ≥ 0` lands at or below the root. -/
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

/-- FT-17 step 5: the quadratic bound. -/
theorem neutralityNewton_quadratic (S Ntot : ι → ℝ) (hS : ∀ s, 0 < S s) (hN : ∀ s, 0 ≤ Ntot s)
    {x r : ℝ} (hx : 0 ≤ x) (hr : 0 ≤ r) (hfix : r = multiElementIonized S Ntot r) :
    |neutralityNewton S Ntot x - r| ≤ (∑ s, Ntot s / S s ^ 2) * (x - r) ^ 2 := by
  have hid := neutralityNewton_error_eq S Ntot hS hN hx hr hfix
  have hsum0 : 0 ≤ ∑ s, Ntot s * S s / (x + S s) ^ 2 :=
    Finset.sum_nonneg (fun s _ => div_nonneg (mul_nonneg (hN s) (hS s).le) (sq_nonneg _))
  have hD : 1 ≤ 1 + ∑ s, Ntot s * S s / (x + S s) ^ 2 := by linarith
  have hterm : ∀ s ∈ (Finset.univ : Finset ι),
      Ntot s * S s / ((x + S s) ^ 2 * (r + S s)) ≤ Ntot s / S s ^ 2 := by
    intro s _
    have hSs := hS s
    have h1 : S s ≤ x + S s := by linarith
    have h2 : S s ≤ r + S s := by linarith
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h3 : S s ^ 3 ≤ (x + S s) ^ 2 * (r + S s) := by
      have := mul_le_mul (pow_le_pow_left₀ hSs.le h1 2) h2 hSs.le (by positivity)
      nlinarith [this]
    have := mul_le_mul_of_nonneg_left h3 (hN s)
    nlinarith [this]
  have hB : 0 ≤ ∑ s, Ntot s * S s / ((x + S s) ^ 2 * (r + S s)) := by
    refine Finset.sum_nonneg (fun s _ => ?_)
    have h1 : 0 < x + S s := by linarith [hS s]
    have h2 : 0 < r + S s := by linarith [hS s]
    exact div_nonneg (mul_nonneg (hN s) (hS s).le) (by positivity)
  rw [hid, abs_div, abs_neg, abs_of_nonneg (mul_nonneg (sq_nonneg _) hB),
    abs_of_pos (by linarith)]
  calc ((x - r) ^ 2 * ∑ s, Ntot s * S s / ((x + S s) ^ 2 * (r + S s)))
        / (1 + ∑ s, Ntot s * S s / (x + S s) ^ 2)
      ≤ (x - r) ^ 2 * ∑ s, Ntot s * S s / ((x + S s) ^ 2 * (r + S s)) :=
        div_le_self (mul_nonneg (sq_nonneg _) hB) hD
    _ ≤ (x - r) ^ 2 * ∑ s, Ntot s / S s ^ 2 :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) (sq_nonneg _)
    _ = (∑ s, Ntot s / S s ^ 2) * (x - r) ^ 2 := by ring

end AdvNewton
#print axioms AdvNewton.neutralityNewton_le_root
#print axioms AdvNewton.neutralityNewton_quadratic
