import Mathlib
import CflibsFormal.EquivalentWidth

open CflibsFormal
open MeasureTheory

namespace Plan.FT20

noncomputable def stepProfile (η M : ℝ) : ℝ → ℝ := fun x =>
  Set.indicator (Set.Icc 0 1) (fun _ => 1) x + η * Set.indicator (Set.Icc 0 M) (fun _ => 1) x

theorem equivWidth_stepProfile {η M τ : ℝ} (hM : 1 ≤ M) :
    equivWidth (stepProfile η M) τ
      = (1 - Real.exp (-(τ * (1 + η)))) + (M - 1) * (1 - Real.exp (-(τ * η))) := by
  have hrw : (fun x => 1 - Real.exp (-(τ * stepProfile η M x)))
      = fun x => Set.indicator (Set.Icc 0 1) (fun _ => 1 - Real.exp (-(τ * (1 + η)))) x
          + Set.indicator (Set.Ioc 1 M) (fun _ => 1 - Real.exp (-(τ * η))) x := by
    funext x
    unfold stepProfile
    by_cases h1 : x ∈ Set.Icc (0:ℝ) 1
    · have hM' : x ∈ Set.Icc (0:ℝ) M := ⟨h1.1, by linarith [h1.2]⟩
      have h2 : x ∉ Set.Ioc (1:ℝ) M := fun h => by linarith [h.1, h1.2]
      simp only [Set.indicator_of_mem h1, Set.indicator_of_mem hM', Set.indicator_of_notMem h2]
      ring_nf
    · by_cases h2 : x ∈ Set.Ioc (1:ℝ) M
      · have hM' : x ∈ Set.Icc (0:ℝ) M := ⟨by linarith [h2.1], h2.2⟩
        simp only [Set.indicator_of_notMem h1, Set.indicator_of_mem hM', Set.indicator_of_mem h2]
        ring_nf
      · have hM' : x ∉ Set.Icc (0:ℝ) M := by
          intro h
          by_cases hx1 : x ≤ (1:ℝ)
          · exact h1 ⟨h.1, hx1⟩
          · exact h2 ⟨not_le.mp hx1, h.2⟩
        simp only [Set.indicator_of_notMem h1, Set.indicator_of_notMem hM',
          Set.indicator_of_notMem h2]
        simp
  have hi1 : Integrable (Set.indicator (Set.Icc (0:ℝ) 1)
      (fun _ => 1 - Real.exp (-(τ * (1 + η))))) :=
    (integrable_indicator_iff measurableSet_Icc).2 (integrableOn_const measure_Icc_lt_top.ne)
  have hi2 : Integrable (Set.indicator (Set.Ioc (1:ℝ) M)
      (fun _ => 1 - Real.exp (-(τ * η)))) :=
    (integrable_indicator_iff measurableSet_Ioc).2 (integrableOn_const measure_Ioc_lt_top.ne)
  rw [equivWidth, hrw, integral_add hi1 hi2, integral_indicator_const _ measurableSet_Icc,
    integral_indicator_const _ measurableSet_Ioc, measureReal_def, measureReal_def,
    Real.volume_Icc, Real.volume_Ioc, ENNReal.toReal_ofReal (by norm_num),
    ENNReal.toReal_ofReal (by linarith)]
  simp

end Plan.FT20
