import Mathlib
import CflibsFormal.AtomicDataPerturbation

open Finset CflibsFormal

namespace AuditFT07

variable {ι : Type*} [Fintype ι] {κ : Type*} [Fintype κ]

/-- generic multiplicative closure lemma: two-sided ratio bounds `(1-δ)·N̂ ≤ N ≤ (1+δ)·N̂`. -/
theorem comp_rel_ratio {N Nhat : κ → ℝ} {δ : ℝ} (hN : ∀ s, 0 < N s) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hlo : ∀ t, N t ≤ (1 + δ) * Nhat t) (hhi : ∀ t, (1 - δ) * Nhat t ≤ N t) (s : κ) :
    |composition Nhat s - composition N s| ≤ (2 * δ / (1 - δ)) * composition N s := by
  have hNh : ∀ t, 0 < Nhat t := fun t => by
    have := hlo t; have := hN t; nlinarith
  have hS : 0 < ∑ t, N t := Finset.sum_pos (fun t _ => hN t) ⟨s, Finset.mem_univ s⟩
  have hSh : 0 < ∑ t, Nhat t := Finset.sum_pos (fun t _ => hNh t) ⟨s, Finset.mem_univ s⟩
  have hSlo : ∑ t, N t ≤ (1 + δ) * ∑ t, Nhat t := by
    rw [Finset.mul_sum]; exact Finset.sum_le_sum fun t _ => hlo t
  have hShi : (1 - δ) * ∑ t, Nhat t ≤ ∑ t, N t := by
    rw [Finset.mul_sum]; exact Finset.sum_le_sum fun t _ => hhi t
  have h1δ : 0 < 1 - δ := by linarith
  unfold composition totalDensity
  set S := ∑ t, N t
  set Sh := ∑ t, Nhat t
  have key : Nhat s / Sh - N s / S = (Nhat s * S - N s * Sh) / (Sh * S) := by
    field_simp
  rw [key, abs_div, abs_of_pos (mul_pos hSh hS), div_le_iff₀ (mul_pos hSh hS)]
  have hrhs : 2 * δ / (1 - δ) * (N s / S) * (Sh * S) = 2 * δ * N s * Sh / (1 - δ) := by
    field_simp
  rw [hrhs, le_div_iff₀ h1δ]
  have hNs := hN s
  have hNhs := hNh s
  have p1 : (1 - δ) * Nhat s * S ≤ N s * S := mul_le_mul_of_nonneg_right (hhi s) hS.le
  have p2 : N s * S ≤ N s * ((1 + δ) * Sh) := mul_le_mul_of_nonneg_left hSlo hNs.le
  have p3 : N s * S ≤ (1 + δ) * Nhat s * S := mul_le_mul_of_nonneg_right (hlo s) hS.le
  have p4 : N s * ((1 - δ) * Sh) ≤ N s * S := mul_le_mul_of_nonneg_left hShi hNs.le
  have q : (1 - δ) * (N s * ((1 - δ) * Sh)) ≤ (1 - δ) * ((1 + δ) * Nhat s * S) :=
    mul_le_mul_of_nonneg_left (p4.trans p3) h1δ.le
  have hX : 0 ≤ δ ^ 2 * (N s * Sh) := by positivity
  rcases abs_cases (Nhat s * S - N s * Sh) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h]
  · nlinarith
  · nlinarith

end AuditFT07

namespace AuditFT07
variable {ι : Type*} [Fintype ι] {κ : Type*} [Fintype κ]

/-- the sharp relative statement: domain `δ < 1` (same as the absolute twin), constant `2δ/(1-δ)`. -/
theorem classicComposition_atomicData_error_rel_sharp [Nonempty ι] [Nonempty κ]
    {kB T Fcal δ : ℝ} {N : κ → ℝ} {g E A g' E' A' : κ → ι → ℝ} {u : κ → ι}
    (hg : ∀ s k, 0 < g s k) (hg' : ∀ s k, 0 < g' s k) (hFcal : 0 < Fcal)
    (hA : ∀ s, 0 < A s (u s)) (hA' : ∀ s, 0 < A' s (u s))
    (hN : ∀ s, 0 < N s) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hpert : ∀ s, |responseFactor kB T (g' s) (E' s) (A' s) (u s)
                    - responseFactor kB T (g s) (E s) (A s) (u s)|
                  ≤ δ * responseFactor kB T (g s) (E s) (A s) (u s))
    (s : κ) :
    |composition (recoveredDensity kB T Fcal g E A g' E' A' u N) s - composition N s|
      ≤ (2 * δ / (1 - δ)) * composition N s := by
  have hρ : ∀ t, 0 < responseFactor kB T (g t) (E t) (A t) (u t) := fun t => by
    unfold responseFactor
    exact div_pos (mul_pos (mul_pos (hg t (u t)) (hA t)) (boltzmannFactor_pos _ _ _))
      (partitionFunction_pos (hg t))
  have hρ' : ∀ t, 0 < responseFactor kB T (g' t) (E' t) (A' t) (u t) := fun t => by
    unfold responseFactor
    exact div_pos (mul_pos (mul_pos (hg' t (u t)) (hA' t)) (boltzmannFactor_pos _ _ _))
      (partitionFunction_pos (hg' t))
  have hrec : ∀ t, recoveredDensity kB T Fcal g E A g' E' A' u N t
      = N t * responseFactor kB T (g t) (E t) (A t) (u t)
          / responseFactor kB T (g' t) (E' t) (A' t) (u t) := fun t => by
    unfold recoveredDensity
    exact classicDensity_aliasing (hg t) (hg' t) hFcal (u t) (hA' t)
  refine comp_rel_ratio hN hδ0 hδ1 (fun t => ?_) (fun t => ?_) s
  · rw [hrec t, mul_div_assoc', le_div_iff₀ (hρ' t)]
    have := (abs_le.mp (hpert t)).2
    have := hN t
    nlinarith
  · rw [hrec t, mul_div_assoc', div_le_iff₀ (hρ' t)]
    have := (abs_le.mp (hpert t)).1
    have := hN t
    nlinarith

end AuditFT07

#print axioms AuditFT07.classicComposition_atomicData_error_rel_sharp
