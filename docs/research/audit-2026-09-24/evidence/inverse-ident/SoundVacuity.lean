import Mathlib
import CflibsFormal.Inverse
import CflibsFormal.JointIdentifiability

/-! Audit scratch (inverse-ident). Two probes of the `Inverse` framework. -/

namespace CflibsFormal

open Finset

/-- Probe 1: `Sound` is UNSATISFIABLE as soon as two species emit on different levels.
Species `Fin 2`, levels `Fin 2`, `emit = id`. Two admissible parameter sets that differ only in
`A 1` (by a factor 2) and `N 1` (by a factor 1/2) give identical observations but different
true compositions, so no function of the observation vector can be `Sound`. -/
theorem no_sound_estimator_of_distinct_emit :
    ¬ ∃ est : CompositionEstimator (Fin 2),
        Sound (levelIndex := Fin 2) 1 1 (fun s => s) est := by
  rintro ⟨est, hsound⟩
  let p₁ : PlasmaParams (Fin 2) (Fin 2) :=
    { T := 1, N := ![1, 1], g := fun _ => 1, E := fun _ => 0, A := ![1, 1] }
  let p₂ : PlasmaParams (Fin 2) (Fin 2) :=
    { T := 1, N := ![1, 2], g := fun _ => 1, E := fun _ => 0, A := ![1, 1/2] }
  have ha₁ : p₁.Admissible := by
    refine ⟨by norm_num [p₁], ?_, ?_, ?_⟩ <;> intro k <;> fin_cases k <;> norm_num [p₁]
  have ha₂ : p₂.Admissible := by
    refine ⟨by norm_num [p₂], ?_, ?_, ?_⟩ <;> intro k <;> fin_cases k <;> norm_num [p₂]
  have hobs : observe (levelIndex := Fin 2) 1 1 (fun s => s) p₁
      = observe (levelIndex := Fin 2) 1 1 (fun s => s) p₂ := by
    funext s
    fin_cases s <;>
      simp [observe, lineIntensity, population, partitionFunction, boltzmannFactor, p₁, p₂]
  have h1 := hsound p₁ ha₁
  have h2 := hsound p₂ ha₂
  rw [hobs, h2] at h1
  have := congrFun h1 0
  simp [trueComposition, composition, totalDensity, p₁, p₂, Fin.sum_univ_two] at this

/-- Probe 2: calibration-FREE joint identifiability. Drop `hFeq` from `joint_identifiability`:
with unknown, possibly different calibrations `Fcal₁ ≠ Fcal₂`, equal two-line observations still
force equal temperature AND equal closure composition (only the absolute densities are scaled). -/
theorem joint_identifiability_calibrationFree
    {species levelIndex : Type*} [Fintype species] [Fintype levelIndex] [Nonempty levelIndex]
    {kB Fcal₁ Fcal₂ : ℝ} {emitA emitB : species → levelIndex}
    {p₁ p₂ : PlasmaParams species levelIndex}
    (s₀ : species)
    (hkB : 0 < kB) (hFcal₁ : 0 < Fcal₁) (hFcal₂ : 0 < Fcal₂)
    (ha₁ : p₁.Admissible) (ha₂ : p₂.Admissible)
    (hEdist : p₁.E (emitA s₀) ≠ p₁.E (emitB s₀))
    (hEeq : p₁.E = p₂.E) (hgeq : p₁.g = p₂.g) (hAeq : p₁.A = p₂.A)
    (hObs : observe₂ kB Fcal₁ emitA emitB p₁ = observe₂ kB Fcal₂ emitA emitB p₂) :
    p₁.T = p₂.T ∧ (∀ s, trueComposition p₁ s = trueComposition p₂ s) := by
  obtain ⟨hT₁, hN₁, hg₁, hA₁⟩ := ha₁
  obtain ⟨hT₂, hN₂, _, _⟩ := ha₂
  have h₀ := congrFun hObs s₀
  simp only [observe₂, observe, Prod.mk.injEq] at h₀
  obtain ⟨hA0, hB0⟩ := h₀
  have hratio :
      lineIntensity kB p₁.T (p₁.N s₀) Fcal₁ p₁.g p₁.E p₁.A (emitB s₀)
          / lineIntensity kB p₁.T (p₁.N s₀) Fcal₁ p₁.g p₁.E p₁.A (emitA s₀)
        = lineIntensity kB p₂.T (p₂.N s₀) Fcal₂ p₂.g p₂.E p₂.A (emitB s₀)
          / lineIntensity kB p₂.T (p₂.N s₀) Fcal₂ p₂.g p₂.E p₂.A (emitA s₀) := by
    rw [hA0, hB0]
  rw [← hgeq, ← hEeq, ← hAeq] at hratio
  have hT : p₁.T = p₂.T :=
    temperature_identifiability hkB hT₁ hT₂ hg₁ (hN₁ s₀) (hN₂ s₀)
      hFcal₁ hFcal₂ hA₁ (emitA s₀) (emitB s₀) hEdist hratio
  refine ⟨hT, ?_⟩
  -- per species: Fcal₁ * N₁ s = Fcal₂ * N₂ s (common positive unit-intensity factor cancels)
  have hscale : ∀ s, p₁.N s = (Fcal₂ / Fcal₁) * p₂.N s := by
    intro s
    have hs := congrFun hObs s
    simp only [observe₂, observe, Prod.mk.injEq] at hs
    obtain ⟨hAs, _⟩ := hs
    rw [← hT, ← hgeq, ← hEeq, ← hAeq] at hAs
    have hU : 0 < partitionFunction kB p₁.T p₁.g p₁.E := partitionFunction_pos hg₁
    have hc : 0 < p₁.A (emitA s) * p₁.g (emitA s) * boltzmannFactor kB p₁.T (p₁.E (emitA s)) :=
      mul_pos (mul_pos (hA₁ _) (hg₁ _)) (boltzmannFactor_pos _ _ _)
    simp only [lineIntensity, population] at hAs
    field_simp at hAs
    have key : (p₁.A (emitA s) * p₁.g (emitA s) * boltzmannFactor kB p₁.T (p₁.E (emitA s)))
        * (Fcal₁ * p₁.N s)
        = (p₁.A (emitA s) * p₁.g (emitA s) * boltzmannFactor kB p₁.T (p₁.E (emitA s)))
        * (Fcal₂ * p₂.N s) := by linarith [hAs]
    have key2 := mul_left_cancel₀ hc.ne' key
    field_simp
    linarith [key2]
  have hc0 : Fcal₂ / Fcal₁ ≠ 0 := (div_pos hFcal₂ hFcal₁).ne'
  have hNfun : p₁.N = fun s => (Fcal₂ / Fcal₁) * p₂.N s := funext hscale
  intro s
  simp only [trueComposition, hNfun]
  exact composition_smul_invariant hc0 s

#print axioms CflibsFormal.no_sound_estimator_of_distinct_emit
#print axioms CflibsFormal.joint_identifiability_calibrationFree
end CflibsFormal
