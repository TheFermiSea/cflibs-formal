import Mathlib
import CflibsFormal.AtomicDataPerturbation
open Finset CflibsFormal

-- P2 for FT07: ι = Fin 1, κ = Fin 2, kB = T = Fcal = 1, g = g' = 1, E = E' = 0, A = 1,
-- A'₀ = 1, A'₁ = 21/20 (hpert tight at δ = 1/20), N = (1, 1). Recovered C₀ = 21/41 ≠ 1/2.
example :
    composition (recoveredDensity (ι := Fin 1) 1 1 1 (fun _ _ => 1) (fun _ _ => 0) (fun _ _ => 1)
      (fun _ _ => 1) (fun _ _ => 0) (fun s _ => ![1, 21/20] s) (fun _ => 0) (fun _ : Fin 2 => 1))
      0 = 21/41 ∧ composition (fun _ : Fin 2 => (1:ℝ)) 0 = 1/2 := by
  constructor
  · simp [composition, totalDensity, recoveredDensity, Classic.classicDensity, lineIntensity,
      population, partitionFunction, boltzmannFactor, Fin.sum_univ_two]
    norm_num
  · simp [composition, totalDensity, Fin.sum_univ_two]

-- hpert check for the same witness, at δ = 1/20: for the target species (s = 1, analyst
-- A'₁ = 21/20) the bound holds with equality; for the other species (s = 0, A'₀ = 1 = A₀) it
-- holds trivially. Together these are `hpert` for both elements of κ = Fin 2.
example :
    |responseFactor (ι := Fin 1) (1:ℝ) 1 (fun _ => (1:ℝ)) (fun _ => (0:ℝ))
        (fun _ => (1:ℝ)) 0
      - responseFactor (ι := Fin 1) (1:ℝ) 1 (fun _ => (1:ℝ)) (fun _ => (0:ℝ))
          (fun _ => (1:ℝ)) 0|
    ≤ (1/20 : ℝ) * responseFactor (ι := Fin 1) (1:ℝ) 1 (fun _ => (1:ℝ)) (fun _ => (0:ℝ))
        (fun _ => (1:ℝ)) 0 := by
  simp [responseFactor, boltzmannFactor, partitionFunction]

example :
    |responseFactor (ι := Fin 1) (1:ℝ) 1 (fun _ => (1:ℝ)) (fun _ => (0:ℝ))
        (fun _ => (21/20:ℝ)) 0
      - responseFactor (ι := Fin 1) (1:ℝ) 1 (fun _ => (1:ℝ)) (fun _ => (0:ℝ))
          (fun _ => (1:ℝ)) 0|
    ≤ (1/20 : ℝ) * responseFactor (ι := Fin 1) (1:ℝ) 1 (fun _ => (1:ℝ)) (fun _ => (0:ℝ))
        (fun _ => (1:ℝ)) 0 := by
  simp [responseFactor, boltzmannFactor, partitionFunction]
  norm_num
