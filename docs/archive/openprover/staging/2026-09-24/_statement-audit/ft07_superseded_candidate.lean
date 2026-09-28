import Mathlib
import CflibsFormal.AtomicDataPerturbation

/-!
# SUPERSEDED (statement audit 2026-09-24): the pre-audit FT07 statement and its verified candidate

Restored record of `_g3-verified/FT07-classicComposition-atomicData-error-rel.lean` as it stood
before the statement audit replaced the target with the sharp form (`hδ1 : δ < 1`, constant
`2δ/(1 − δ)`). This form (`hδ : δ < 1/2`, constant `2δ/(1 − 2δ)`) is strictly dominated by the new
target. Kept only as provenance; not a queue target. Docstring trimmed; proofs verbatim.
-/

open Finset CflibsFormal

namespace Plan.FT07.Superseded

variable {ι : Type*} [Fintype ι] {κ : Type*} [Fintype κ]

/-- Additive-to-relative closure: `|N̂ − N| ≤ η·N` gives `2η/(1 − η)` (pre-audit route). -/
theorem composition_rel_error_mul {N Nhat : κ → ℝ} {η : ℝ}
    (hN : ∀ s, 0 < N s) (hη0 : 0 ≤ η) (hη1 : η < 1) (hmul : ∀ s, |Nhat s - N s| ≤ η * N s)
    (s : κ) :
    |composition Nhat s - composition N s| ≤ (2 * η / (1 - η)) * composition N s := by
  have hS : 0 < ∑ t, N t := Finset.sum_pos (fun t _ => hN t) ⟨s, Finset.mem_univ s⟩
  have hlo : ∀ t, (1 - η) * N t ≤ Nhat t := fun t => by
    have := (abs_le.mp (hmul t)).1; linarith
  have hhi : ∀ t, Nhat t ≤ (1 + η) * N t := fun t => by
    have := (abs_le.mp (hmul t)).2; linarith
  have hSh_lo : (1 - η) * ∑ t, N t ≤ ∑ t, Nhat t := by
    rw [Finset.mul_sum]; exact Finset.sum_le_sum fun t _ => hlo t
  have hSh_hi : ∑ t, Nhat t ≤ (1 + η) * ∑ t, N t := by
    rw [Finset.mul_sum]; exact Finset.sum_le_sum fun t _ => hhi t
  have h1η : 0 < 1 - η := by linarith
  have hSh : 0 < ∑ t, Nhat t := lt_of_lt_of_le (mul_pos h1η hS) hSh_lo
  unfold composition totalDensity
  set S := ∑ t, N t
  set Sh := ∑ t, Nhat t
  have key : Nhat s / Sh - N s / S = (Nhat s * S - N s * Sh) / (Sh * S) := by
    field_simp
  rw [key, abs_div, abs_of_pos (mul_pos hSh hS)]
  rw [div_le_iff₀ (mul_pos hSh hS)]
  have hnum : |Nhat s * S - N s * Sh| ≤ 2 * η * N s * S := by
    rw [abs_le]; constructor
    · nlinarith [hlo s, hSh_hi, hN s, hS]
    · nlinarith [hhi s, hSh_lo, hN s, hS]
  have hfac : 2 * η * N s * S ≤ 2 * η / (1 - η) * (N s / S) * (Sh * S) := by
    rw [show 2 * η / (1 - η) * (N s / S) * (Sh * S) = 2 * η * N s * (Sh / (1 - η)) by
      field_simp]
    have : S ≤ Sh / (1 - η) := by rw [le_div_iff₀ h1η]; linarith
    have hc : 0 ≤ 2 * η * N s := by have := hN s; positivity
    exact mul_le_mul_of_nonneg_left this hc
  linarith

/-- `η = δ/(1 − δ)` turns `2η/(1 − η)` into `2δ/(1 − 2δ)`. -/
theorem eta_identity {δ : ℝ} (hδ : δ < 1 / 2) :
    2 * (δ / (1 - δ)) / (1 - δ / (1 - δ)) = 2 * δ / (1 - 2 * δ) := by
  have h1 : (1 : ℝ) - δ ≠ 0 := by intro h; linarith
  have h2 : (1 : ℝ) - 2 * δ ≠ 0 := by intro h; linarith
  have h3 : (1 : ℝ) - δ / (1 - δ) = (1 - 2 * δ) / (1 - δ) := by field_simp; ring
  rw [h3]; field_simp

/-- SUPERSEDED pre-audit form (dominated by the sharp `2δ/(1 − δ)`, `δ < 1` target). -/
theorem classicComposition_atomicData_error_rel [Nonempty ι] [Nonempty κ]
    {kB T Fcal δ : ℝ} {N : κ → ℝ} {g E A g' E' A' : κ → ι → ℝ} {u : κ → ι}
    (hg : ∀ s k, 0 < g s k) (hg' : ∀ s k, 0 < g' s k) (hFcal : 0 < Fcal)
    (hA : ∀ s, 0 < A s (u s)) (hA' : ∀ s, 0 < A' s (u s))
    (hN : ∀ s, 0 < N s) (hδ0 : 0 ≤ δ) (hδ : δ < 1 / 2)
    (hpert : ∀ s, |responseFactor kB T (g' s) (E' s) (A' s) (u s)
                    - responseFactor kB T (g s) (E s) (A s) (u s)|
                  ≤ δ * responseFactor kB T (g s) (E s) (A s) (u s))
    (s : κ) :
    |composition (recoveredDensity kB T Fcal g E A g' E' A' u N) s - composition N s|
      ≤ (2 * δ / (1 - 2 * δ)) * composition N s := by
  have h1δ : 0 < 1 - δ := by linarith
  have hη0 : 0 ≤ δ / (1 - δ) := div_nonneg hδ0 h1δ.le
  have hη1 : δ / (1 - δ) < 1 := by rw [div_lt_one h1δ]; linarith
  have hmul : ∀ t, |recoveredDensity kB T Fcal g E A g' E' A' u N t - N t|
      ≤ δ / (1 - δ) * N t := by
    intro t
    rw [mul_comm]
    unfold recoveredDensity
    exact classicDensity_aliasing_error (hg t) (hg' t) hFcal (u t) (hA t) (hA' t)
      (hN t) hδ0 (by linarith) (hpert t)
  have h := composition_rel_error_mul hN hη0 hη1 hmul s
  rwa [eta_identity hδ] at h

end Plan.FT07.Superseded
