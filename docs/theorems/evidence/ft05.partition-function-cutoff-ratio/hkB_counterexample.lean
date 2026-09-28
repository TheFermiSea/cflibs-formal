import CflibsFormal

open CflibsFormal

/- FT-05 hypothesis-sharpness check: `hkB : 0 < kB` is load-bearing.

At `kB = 0`, Lean's real division convention `x / 0 = 0` makes every Boltzmann
factor `boltzmannFactor 0 T E = Real.exp (-E / (0 * T)) = Real.exp 0 = 1`,
independent of `T` and `E`. So on the card's own witness
(`ι := Fin 2`, `g = ![1, 1]`, `E = ![0, 1]`, `cut = 1/2`), `U(T) = 2` and
`U_cut(T) = 1` for every `T`, and the ratio is constantly `2`: not
`StrictMonoOn`. This shows the theorem's conclusion genuinely needs `hkB`,
not merely that the proof happens to use it. -/
example :
    ¬ StrictMonoOn
        (fun T : ℝ => partitionFunction (ι := Fin 2) 0 T ![1, 1] ![0, 1] /
                        partitionFunctionCut (ι := Fin 2) 0 T (1 / 2) ![1, 1] ![0, 1])
        (Set.Ioi (0 : ℝ)) := by
  intro h
  have h1 : (1 : ℝ) ∈ Set.Ioi (0 : ℝ) := by norm_num
  have h2 : (2 : ℝ) ∈ Set.Ioi (0 : ℝ) := by norm_num
  have hlt : (1 : ℝ) < 2 := by norm_num
  have hcontra := h h1 h2 hlt
  simp [partitionFunction, partitionFunctionCut, boltzmannFactor, Fin.sum_univ_two] at hcontra
