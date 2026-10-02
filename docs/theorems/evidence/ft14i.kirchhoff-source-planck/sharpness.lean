import CflibsFormal

/-!
Card evidence for `ft14i.kirchhoff-source-planck` (`CflibsFormal.source_eq_planck`). Not library
code; not imported by anything under `CflibsFormal/`.

(a) `hκ` is load-bearing: a counterexample at `κ0 = 0` that satisfies `hpop` and `hein`.
(b) `hx` and `hnl` are not logically needed: the statement without them is still a theorem, and
    the `n_l = 0` case is degenerate for a different reason than the source docstring gives (see
    the card, section 3).
(c) Non-vacuity: every hypothesis holds at a nondegenerate point and the conclusion is nonzero.
-/

open CflibsFormal

namespace ScratchFT14I

/-- (a) Without `hκ` the identity fails: `κ0 = 0`, `g_u = 0`, `n_u = 0`, `B0 = 1`, `x = 1`. -/
example : ¬ (lineEmissivity 1 0 / lineOpacity 0 1 1 = 1 / (Real.exp 1 - 1)) := by
  have h1 : 0 < Real.exp 1 - 1 := by
    have := Real.add_one_lt_exp (x := (1 : ℝ)) one_ne_zero; linarith
  simp only [lineEmissivity, lineOpacity, mul_zero, zero_mul, zero_div]
  exact (ne_of_lt (by positivity : (0 : ℝ) < 1 / (Real.exp 1 - 1)))

-- The counterexample point satisfies `hpop` (`0/1 = 0/1 * e^{-1}`) and `hein` (`1*0/1 = 0*1`):
example : (0 : ℝ) / 1 = 0 / 1 * Real.exp (-1) ∧ (1 : ℝ) * 0 / 1 = 0 * 1 := by
  constructor <;> simp

/-- (b) The statement without `hx` and `hnl` is still a theorem. -/
theorem source_eq_planck_noGuards {κ0 ε0 B0 nl nu x gu gl : ℝ} (hκ : 0 < κ0)
    (hpop : nu / nl = gu / gl * Real.exp (-x)) (hein : ε0 * gu / gl = κ0 * B0) :
    lineEmissivity ε0 nu / lineOpacity κ0 nl x = B0 / (Real.exp x - 1) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [lineEmissivity, lineOpacity]
  rcases eq_or_ne nl 0 with rfl | hnl
  · -- `nl = 0` forces `gu / gl = 0` through `hpop`, hence `B0 = 0` through `hein`.
    have hq : gu / gl = 0 := by
      have h0 : gu / gl * Real.exp (-x) = 0 := by rw [← hpop]; simp
      rcases mul_eq_zero.mp h0 with h | h
      · exact h
      · exact absurd h (Real.exp_pos _).ne'
    have hB : B0 = 0 := by
      have : ε0 * gu / gl = 0 := by rw [mul_div_assoc, hq, mul_zero]
      rw [this] at hein
      rcases mul_eq_zero.mp hein.symm with h | h
      · exact absurd h hκ.ne'
      · exact h
    simp [lineEmissivity, lineOpacity, hB]
  · have hnu : nu = gu / gl * Real.exp (-x) * nl := (div_eq_iff hnl).mp hpop
    have hnum : ε0 * nu = κ0 * B0 * nl * Real.exp (-x) := by
      rw [hnu]; linear_combination (nl * Real.exp (-x)) * hein
    have h1 : Real.exp x - 1 ≠ 0 := by
      intro h
      have : Real.exp x = Real.exp 0 := by rw [Real.exp_zero]; linarith
      exact hx (Real.exp_injective this)
    have h2 : 1 - Real.exp (-x) ≠ 0 := by
      intro h
      have : Real.exp (-x) = Real.exp 0 := by rw [Real.exp_zero]; linarith
      exact hx (by linarith [Real.exp_injective this])
    have hκ' : κ0 ≠ 0 := hκ.ne'
    unfold lineEmissivity lineOpacity
    rw [hnum, Real.exp_neg]
    rw [Real.exp_neg] at h2
    field_simp

/-- (c) Non-vacuity: `x = κ0 = n_l = g_u = g_l = ε0 = B0 = 1`, `n_u = e^{-1}`. -/
example : lineEmissivity 1 (Real.exp (-1)) / lineOpacity 1 1 1 = 1 / (Real.exp 1 - 1) :=
  source_eq_planck (gu := 1) (gl := 1) (ε0 := 1) (B0 := 1) one_pos one_pos one_pos
    (by simp) (by simp)

end ScratchFT14I

#print axioms ScratchFT14I.source_eq_planck_noGuards
