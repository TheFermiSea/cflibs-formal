import CflibsFormal

open CflibsFormal Finset Matrix

-- FT-16 non-vacuity / sharpness witness (ft16.kernel-extraction-varah-bound, §3).
-- Singleton pixel/line type, `K = 1`, `K_t = 2`, `I = 1`, `Î = 2`, `η = 0`, `δ = 1`: H1–H3 hold and
-- the bound is attained with equality, `|Î - I| = 1 = RHS`, so the `1/δ` factor cannot be improved
-- in general. Scratch Lean, not landed in `CflibsFormal/`.

abbrev K1 : Matrix (Fin 1) (Fin 1) ℝ := !![(1 : ℝ)]
abbrev Kt1 : Matrix (Fin 1) (Fin 1) ℝ := !![(2 : ℝ)]

theorem ft16_witness_hdom :
    ∀ k : Fin 1, (1 : ℝ) + ∑ j ∈ (Finset.univ : Finset (Fin 1)).erase k,
        |(K1.transpose * K1) k j| ≤ |(K1.transpose * K1) k k| := by
  intro k
  fin_cases k
  simp [Matrix.mul_apply]

theorem ft16_witness_hnormal :
    (K1.transpose * K1).mulVec (fun _ => (2 : ℝ)) =
      K1.transpose.mulVec (Kt1.mulVec (fun _ => (1 : ℝ)) + fun _ => (0 : ℝ)) := by
  ext k
  fin_cases k
  simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]

/-- The bound from the headline theorem, instantiated at the witness. -/
theorem ft16_witness_bound :
    |(2 : ℝ) - (1 : ℝ)| ≤
      (Finset.univ.sup' univ_nonempty
          fun k : Fin 1 => |(K1.transpose.mulVec
            ((Kt1 - K1).mulVec (fun _ => (1 : ℝ)) + fun _ => (0 : ℝ))) k|) / (1 : ℝ) :=
  kernelLS_error_linfty K1 Kt1 (fun _ => (1 : ℝ)) (fun _ => (2 : ℝ)) (fun _ => (0 : ℝ))
    one_pos ft16_witness_hdom ft16_witness_hnormal 0

/-- The bound is attained with equality: both sides equal `1`. -/
theorem ft16_witness_attained :
    |(2 : ℝ) - (1 : ℝ)| =
      (Finset.univ.sup' univ_nonempty
          fun k : Fin 1 => |(K1.transpose.mulVec
            ((Kt1 - K1).mulVec (fun _ => (1 : ℝ)) + fun _ => (0 : ℝ))) k|) / (1 : ℝ) := by
  norm_num [K1, Kt1, Matrix.mulVec, dotProduct, Matrix.transpose,
    Finset.sup'_eq_csSup_image]
