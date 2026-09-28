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
