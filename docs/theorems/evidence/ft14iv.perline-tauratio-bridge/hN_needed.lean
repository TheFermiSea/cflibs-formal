import CflibsFormal
open CflibsFormal

/-- Necessity of `hN` in `perLine_tauRatio`: dropping `N ≠ 0` breaks the conclusion. At `N = 0`
(with identical data fed to both "lines") the left side is Lean's junk `0 / 0 = 0`, while the
right side is a ratio of two equal nonzero quantities, hence `1`. Scratch check only; not part
of the landed corpus (review finding, ft14iv.perline-tauratio-bridge). -/
example :
    ¬ (opticalDepth (ι := Unit) 1 1 0 (1 * (1 - Real.exp (-1))) 1 (fun _ => (1:ℝ)) (fun _ => 0) ()
        / opticalDepth (ι := Unit) 1 1 0 (1 * (1 - Real.exp (-1))) 1 (fun _ => (1:ℝ)) (fun _ => 0) ()
      = 1 * (1 - Real.exp (-1)) * 1 * boltzmannFactor 1 1 0
        / (1 * (1 - Real.exp (-1)) * 1 * boltzmannFactor 1 1 0)) := by
  have hlt : Real.exp (-1) < Real.exp 0 := Real.exp_lt_exp.mpr (by norm_num)
  rw [Real.exp_zero] at hlt
  have h : (1:ℝ) - Real.exp (-1) ≠ 0 := by linarith
  have hb : boltzmannFactor (1:ℝ) 1 0 ≠ 0 := (boltzmannFactor_pos 1 1 0).ne'
  simp [opticalDepth, population, h, hb]
