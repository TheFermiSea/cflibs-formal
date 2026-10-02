-- Summary: equivWidth ψ is strictly increasing on [0,∞) for ψ ≥ 0 integrable with positive integral.
import Mathlib
import CflibsFormal.EquivalentWidth

open CflibsFormal MeasureTheory
namespace Plan.FT14
theorem equivWidth_strictMonoOn {ψ : ℝ → ℝ} (hψ0 : 0 ≤ ψ) (hint : Integrable ψ)
    (hpos : 0 < ∫ x, ψ x) : StrictMonoOn (equivWidth ψ) (Set.Ici 0) := by
  intro a ha b hb hab
  set d : ℝ → ℝ := fun x => Real.exp (-(a * ψ x)) - Real.exp (-(b * ψ x)) with hd
  have hfa : Integrable (fun x => 1 - Real.exp (-(a * ψ x))) :=
    equivWidth_integrand_integrable ha hψ0 hint
  have hfb : Integrable (fun x => 1 - Real.exp (-(b * ψ x))) :=
    equivWidth_integrand_integrable hb hψ0 hint
  have hpoint : (fun x => (1 - Real.exp (-(b * ψ x))) - (1 - Real.exp (-(a * ψ x)))) = d := by
    funext x
    simp [hd]
  have hdiff : equivWidth ψ b - equivWidth ψ a = ∫ x, d x := by
    rw [equivWidth, equivWidth, (integral_sub hfb hfa).symm, hpoint]
  have hdn : 0 ≤ d := by
    intro x
    have hψx : 0 ≤ ψ x := hψ0 x
    have hmul : a * ψ x ≤ b * ψ x := mul_le_mul_of_nonneg_right hab.le hψx
    have hneg : -(b * ψ x) ≤ -(a * ψ x) := by linarith
    have hexp : Real.exp (-(b * ψ x)) ≤ Real.exp (-(a * ψ x)) := Real.exp_le_exp.mpr hneg
    simp only [hd]
    exact sub_nonneg.mpr hexp
  have hdi : Integrable d := by
    have hd_eq : d = (fun x => (1 - Real.exp (-(b * ψ x))) - (1 - Real.exp (-(a * ψ x)))) := by
      funext x
      ring
    exact hd_eq.symm ▸ Integrable.sub hfb hfa
  have hsupp : Function.support d = Function.support ψ := by
    ext x
    simp only [Function.mem_support, Function.mem_support]
    constructor
    · intro hd0 hψ0
      have hdx : d x = 0 := by simp [hd, hψ0]
      exact hd0 hdx
    · intro hψ
      have hψpos : 0 < ψ x := lt_of_le_of_ne (hψ0 x) (Ne.symm hψ)
      have hmul : a * ψ x < b * ψ x := mul_lt_mul_of_pos_right hab hψpos
      have hexp : Real.exp (-(b * ψ x)) < Real.exp (-(a * ψ x)) :=
        Real.exp_strictMono (by linarith)
      simp only [hd]
      exact ne_of_gt (sub_pos.mpr hexp)
  have hψpos_support : 0 < volume (Function.support ψ) :=
    (integral_pos_iff_support_of_nonneg hψ0 hint).mp hpos
  have hdpos_support : 0 < volume (Function.support d) := by
    rw [hsupp]
    exact hψpos_support
  have hdiffpos : 0 < ∫ x, d x :=
    (integral_pos_iff_support_of_nonneg hdn hdi).mpr hdpos_support
  have hgoal : 0 < equivWidth ψ b - equivWidth ψ a := by
    rw [hdiff]
    exact hdiffpos
  exact sub_pos.mp hgoal
end Plan.FT14
