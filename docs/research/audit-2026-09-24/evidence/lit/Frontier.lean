import CflibsFormal.CompositionRobustness
import CflibsFormal.SelfAbsorption
import CflibsFormal.OLS
import CflibsFormal.InhomogeneityBias
import CflibsFormal.Saha

open Finset
namespace CflibsFormal

variable {κ : Type*} [Fintype κ] {ι : Type*} [Fintype ι] {ζ : Type*} [Fintype ζ]

-- F3: multiplicative per-species density error => abundance-independent relative composition error
theorem composition_rel_error_mul {N Nhat : κ → ℝ} {η : ℝ}
    (hN : ∀ s, 0 < N s) (hη0 : 0 ≤ η) (hη1 : η < 1)
    (hmul : ∀ s, |Nhat s - N s| ≤ η * N s) (s : κ) :
    |composition Nhat s - composition N s| ≤ (2 * η / (1 - η)) * composition N s := by
  sorry

-- F2: self-absorption with optical depth antitone in upper-level energy flattens the OLS slope
theorem olsSlope_selfAbsorbed_ge [Nonempty ι] {E y τ : ι → ℝ}
    (hτ : ∀ k, 0 < τ k) (hanti : ∀ i j, E i ≤ E j → τ j ≤ τ i) :
    olsSlope E y ≤ olsSlope E (fun k => y k + Real.log (selfAbsorptionFactor (τ k))) := by
  sorry

-- F1: at a common anchor, a reweighting antitone in b lowers the tilted mean inverse temperature
theorem tiltMean_reweight_le [Nonempty ζ] {w b ρ : ζ → ℝ}
    (hw : ∀ z, 0 < w z) (hρ : ∀ z, 0 < ρ z) (hanti : ∀ i j, b i ≤ b j → ρ j ≤ ρ i) (a : ℝ) :
    tiltMean (fun z => w z * ρ z) b a ≤ tiltMean w b a := by
  sorry

end CflibsFormal
