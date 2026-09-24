import Mathlib

namespace AuditGLaw
open MeasureTheory ProbabilityTheory
open scoped NNReal
variable {ι : Type*} [Fintype ι] {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- G2: independent Gaussian line noises form a jointly Gaussian vector. -/
theorem noiseVector_hasGaussianLaw (ε : ι → Ω → ℝ) (σ : ℝ≥0)
    (hlaw : ∀ k, HasLaw (ε k) (gaussianReal 0 (σ ^ 2)) μ) (hind : iIndepFun ε μ) :
    HasGaussianLaw (fun ω ↦ (ε · ω)) μ :=
  iIndepFun.hasGaussianLaw (fun k => (hlaw k).hasGaussianLaw) hind

/-- G3 (core): any fixed weighted sum of the noise is Gaussian, with law identified by its
mean and variance. -/
theorem weightedNoise_map_eq (ε : ι → Ω → ℝ) (σ : ℝ≥0) (w : ι → ℝ)
    (hlaw : ∀ k, HasLaw (ε k) (gaussianReal 0 (σ ^ 2)) μ) (hind : iIndepFun ε μ) :
    μ.map (fun ω => ∑ k, w k * ε k ω)
      = gaussianReal (μ[fun ω => ∑ k, w k * ε k ω])
          (Var[fun ω => ∑ k, w k * ε k ω; μ]).toNNReal := by
  have hG := noiseVector_hasGaussianLaw ε σ hlaw hind
  let L : (ι → ℝ) →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap (∑ k, w k • (LinearMap.proj k : (ι → ℝ) →ₗ[ℝ] ℝ))
  have hL : ∀ v : ι → ℝ, L v = ∑ k, w k * v k := by
    intro v; simp [L, LinearMap.sum_apply]
  have hLG : HasGaussianLaw (L ∘ fun ω ↦ (ε · ω)) μ :=
    hG.map_of_measurable L L.continuous.measurable
  have hfun : (L ∘ fun ω ↦ (ε · ω)) = fun ω => ∑ k, w k * ε k ω := by
    funext ω; simp [hL]
  rw [hfun] at hLG
  exact hLG.map_eq_gaussianReal

end AuditGLaw
#print axioms AuditGLaw.weightedNoise_map_eq
