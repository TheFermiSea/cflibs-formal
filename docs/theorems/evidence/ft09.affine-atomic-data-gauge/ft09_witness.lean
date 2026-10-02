import Mathlib
import CflibsFormal.HeteroAtomicData

open CflibsFormal

-- Nontrivial witness for `affine_gA_observational_equiv`: two lines with distinct energies
-- (E = ![0, 1]), so the affine slope `b = 1/2` genuinely shifts a two-point Boltzmann-plot
-- fit (unlike the landed docstring's own `b = 0`, single-line witness). H20 is
-- `b * (kB * T) = 1/2 < 1`; the temperature equation forces `T' = 2`.
noncomputable example :
    ∃ T' N' : ℝ, 0 < T' ∧ 0 < N' ∧ 1 / ((1:ℝ) * T') = 1 / ((1:ℝ) * (1:ℝ)) - (1/2 : ℝ) ∧
      ∀ k : Fin 2,
        Real.log (lineIntensity 1 1 1 1 (fun _ : Fin 2 => (1:ℝ)) ![(0:ℝ), 1]
            (fun _ : Fin 2 => (1:ℝ)) k
          / ((fun _ : Fin 2 => (1:ℝ)) k
              * (fun k : Fin 2 => (1:ℝ) * Real.exp (-((0:ℝ) + (1/2:ℝ) * (![(0:ℝ), 1] : Fin 2 → ℝ) k))) k))
        = Real.log (lineIntensity 1 T' N' 1 (fun _ : Fin 2 => (1:ℝ)) ![(0:ℝ), 1]
            (fun _ : Fin 2 => (1:ℝ)) k
          / ((fun _ : Fin 2 => (1:ℝ)) k * (fun _ : Fin 2 => (1:ℝ)) k)) :=
  affine_gA_observational_equiv (kB := 1) (T := 1) (N := 1) (Fcal := 1) (α := 0) (b := 1/2)
    (g := fun _ => 1) (E := ![(0:ℝ), 1]) (A := fun _ => 1)
    (A' := fun k => (1:ℝ) * Real.exp (-((0:ℝ) + (1/2:ℝ) * (![(0:ℝ), 1] : Fin 2 → ℝ) k)))
    (by norm_num) (by norm_num) (fun _ => by norm_num) (fun _ => by norm_num) (by norm_num)
    (fun _ => rfl) (by norm_num)

-- The witness pins T' = 2: 1/(kB*T') = 1/(kB*T) - b = 1 - 1/2 = 1/2.
example : (1:ℝ) / ((1:ℝ) * 2) = 1 / ((1:ℝ) * (1:ℝ)) - (1/2 : ℝ) := by norm_num
