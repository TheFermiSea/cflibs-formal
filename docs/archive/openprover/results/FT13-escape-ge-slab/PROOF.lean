-- Summary: Formal proof that the profile escape factor is at least the flat-slab factor (FT13-escape-ge-slab).
import Mathlib
import CflibsFormal.SelfAbsorption
import CflibsFormal.EquivalentWidth

open CflibsFormal MeasureTheory

namespace Plan.FT13

-- Chord inequality: convexity of exp gives (1 - e^{-τ}) * t ≤ 1 - e^{-τ t} for t ∈ [0,1].
theorem slab_chord_le {τ t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 - Real.exp (-τ)) * t ≤ 1 - Real.exp (-(τ * t)) := by
  have hc := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (-τ))
    (by linarith : (0 : ℝ) ≤ 1 - t) ht0 (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at hc
  have : t * -τ = -(τ * t) := by ring
  rw [this] at hc
  nlinarith [hc]

-- Main theorem: selfAbsorptionFactor τ0 * (τ0 * ∫ψ) ≤ equivWidth ψ τ0, via the chord inequality
-- applied pointwise (t = ψ x) and integral_mono.
theorem escape_ge_slab {ψ : ℝ → ℝ} {τ0 : ℝ} (hψ0 : 0 ≤ ψ) (hψ1 : ∀ x, ψ x ≤ 1)
    (hint : Integrable ψ) (hτ : 0 < τ0) :
    selfAbsorptionFactor τ0 * (τ0 * ∫ x, ψ x) ≤ equivWidth ψ τ0 := by
  have hL : selfAbsorptionFactor τ0 * (τ0 * ∫ x, ψ x) = ∫ x, (1 - Real.exp (-τ0)) * ψ x := by
    rw [selfAbsorptionFactor, if_neg hτ.ne']
    field_simp [hτ.ne']
    rw [integral_const_mul]
  rw [hL, equivWidth]
  exact integral_mono (hint.const_mul (1 - Real.exp (-τ0)))
    (equivWidth_integrand_integrable hτ.le hψ0 hint)
    (fun x => slab_chord_le (hψ0 x) (hψ1 x))

end Plan.FT13
