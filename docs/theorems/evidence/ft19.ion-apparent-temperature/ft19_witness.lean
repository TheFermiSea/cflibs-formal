import CflibsFormal
open CflibsFormal
/-- Non-vacuity of the landed FT-19 statement: the dossier's two-zone witness instantiates
every hypothesis (zones genuinely inhomogeneous, T = ![1, 2]). -/
example :
    let T : Fin 2 → ℝ := ![1, 2]
    let NI : Fin 2 → ℝ := fun _ => 1
    let g : Fin 2 → ℝ := fun _ => 1
    let EZ : Fin 2 → ℝ := ![0, 1]
    let EZ1 : Fin 2 → ℝ := ![1, 2]
    let NII : Fin 2 → ℝ := fun z => NI z * sahaFactor 1 (T z) 1 1 1 g EZ g EZ1 / 1
    apparentBeta (EZ1 0) (Real.log (mixedLineIntensity 1 T NII 1 g EZ1 g 0 / (g 0 * g 0)))
        (EZ1 1) (Real.log (mixedLineIntensity 1 T NII 1 g EZ1 g 1 / (g 1 * g 1)))
      ≤ apparentBeta (EZ 0) (Real.log (mixedLineIntensity 1 T NI 1 g EZ g 0 / (g 0 * g 0)))
        (EZ 1) (Real.log (mixedLineIntensity 1 T NI 1 g EZ g 1 / (g 1 * g 1))) := by
  intro T NI g EZ EZ1 NII
  refine mixed_ion_apparentBeta_le_neutral (ζ := Fin 2) one_pos one_pos one_pos zero_le_one
    one_pos one_pos ?_ (fun _ => one_pos) (fun _ => one_pos) (fun _ => one_pos)
    (fun _ => one_pos) (fun _ => one_pos) (fun _ => rfl) 0 1 ?_ 0 1 ?_ ?_
  · intro z; fin_cases z <;> simp [T]
  · simp [EZ]
  · simp [EZ1]
  · simp [EZ, EZ1]
