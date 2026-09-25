import Mathlib
import CflibsFormal.SahaEquilibrium

namespace AuditNewton
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

end AuditNewton

#print axioms AuditNewton.neutralityNewton_error_eq
