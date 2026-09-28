import Mathlib
import CflibsFormal.OLSIdentifiability
open MeasureTheory
namespace RedTeam
variable {P L : Type*} [Fintype P] [Fintype L] [DecidableEq L]
/-- Instrument kernel entry: the profile `φ` integrated against the pixel response `R`. -/
noncomputable def pixelKernel (R φ : ℝ → ℝ) : ℝ := ∫ x, φ x * R x
/-- The pixel × line kernel matrix. -/
noncomputable def kernelMatrix (R : P → ℝ → ℝ) (φ : L → ℝ → ℝ) : Matrix P L ℝ :=
  fun p l => pixelKernel (R p) (φ l)
/-- Pixel sums produced by line intensities `I`. -/
noncomputable def pixelSignal (R : P → ℝ → ℝ) (φ : L → ℝ → ℝ) (I : L → ℝ) : P → ℝ :=
  (kernelMatrix R φ).mulVec I
/-- **Pixel-signal identifiability (K2).** The linear map from line intensities `I : L → ℝ` to pixel
sums `y = K ⬝ I` is injective *if and only if* the kernel matrix `K = kernelMatrix R φ` has trivial
kernel, i.e. line intensities are recoverable from pixel data exactly when `K` has full column rank. -/
theorem pixelSignal_injective_iff (R : P → ℝ → ℝ) (φ : L → ℝ → ℝ) :
    Function.Injective (pixelSignal R φ) ↔ LinearMap.ker (kernelMatrix R φ).mulVecLin = ⊥ := by
  sorry
end RedTeam
