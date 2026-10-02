import Mathlib
import CflibsFormal.AtomicDataPerturbation

/-!
# Queue target FT07-classicComposition-atomicData-error-rel (deep audit 2026-09-24, FT-07 item 5)

Abundance-scaled (relative) closure bound for the classic CF-LIBS reader under per-species
relative atomic-data (response-factor) error. Statement file for the proof queue: one target
theorem, one `sorry`.
-/

open Finset CflibsFormal

namespace Plan.FT07

variable {ι : Type*} [Fintype ι] {κ : Type*} [Fintype κ]

/-- Closure under two-sided ratio bounds `(1 - δ)·N̂ ≤ N ≤ (1 + δ)·N̂`. -/
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

/-- **Relative closure bound for the classic reader under atomic-data error.** Each species `s`
is emitted with the TRUE atomic data `(g s, E s, A s)` at density `N s` (common calibration
`Fcal`, temperature `T` known to the reader) and read off its chosen line `u s` with the WRONG
data `(g' s, E' s, A' s)` (`recoveredDensity`). If every species' response factor
`ρ = g_u·A_u·exp(−E_u/(kB T))/U(T)` is off by at most a relative `δ`, `0 ≤ δ < 1` (`hpert`),
then every recovered number fraction obeys
  `|Ĉ_s − C_s| ≤ (2δ/(1 − δ)) · C_s`,
an error that scales with the true fraction `C_s`. The absolute twin
`classicComposition_atomicData_error` bounds the same error by `compositionErrorBound` with a
density cap `Nmax`, a bound whose leading term `Nmax·δ/((1 − δ)·Ŝ)` does not shrink with `C_s`,
so it is uninformative for minor elements. Example: `δ = 0.05` gives `2δ/(1 − δ) = 2/19 ≈ 0.105`,
so a species with `C_s = 0.005` is recovered within `≈ 5.26·10⁻⁴`.

Route: the EXACT aliasing identity `classicDensity_aliasing` gives `N̂_t = N_t·ρ_t/ρ'_t`, and
`hpert` gives `(1 − δ)·ρ_t ≤ ρ'_t ≤ (1 + δ)·ρ_t`, so `(1 − δ)·N̂_t ≤ N_t ≤ (1 + δ)·N̂_t` for every
species; closure then puts `Ĉ_s/C_s` in `[(1 − δ)/(1 + δ), (1 + δ)/(1 − δ)]`, whose larger
deviation from `1` is `2δ/(1 − δ)`. The constant is approached (numerical check, not
Lean-checked) when species `s` is read high by `1/(1 − δ)`, every other species low by
`1/(1 + δ)`, and the others' share tends to `1`. Routing instead through the additive envelope
`|N̂_t − N_t| ≤ N_t·δ/(1 − δ)` (`classicDensity_aliasing_error`) discards the multiplicative
structure and gives only `2δ/(1 − 2δ)` on `δ < 1/2`, which this statement dominates.

Hypotheses: `hg`, `hg'` (positive degeneracies: both partition functions are positive and
cancel); `hFcal` (the calibration cancels); `hA'` (positive analyst's chosen-line Einstein
coefficient; `A'` divides in the reader); `hA` (positive true chosen-line coefficient; implied by
`hg`, `hg'`, `hA'`, `hδ0` and `hpert`, Lean-checked in the statement-audit scratch, and kept as
the physical guard, as in the absolute twin); `hN` (positive true densities: the bound is
relative to them and the totals must be positive); `hδ0`; `hδ1 : δ < 1` (the absolute twin's
domain; necessary, by hand and not Lean-checked: at `δ ≥ 1` the analyst's response factor can
approach `0` and `Ĉ_s/C_s` is unbounded); `hpert` (the lumped per-species relative response
error: the per-symbol errors in `g`, `A`, `E`, `U` are collapsed into one scalar `δ`, an assumed
input).

Scope (two-axis): relation REDUCED (lumped uniform relative response error `δ`, classic reader at
known `T`; the algebra itself is exact); definitions used: `lineIntensity` REDUCED (optically thin
LTE forward map), `Classic.classicDensity` / `recoveredDensity` (estimator packaging),
`composition` PURE-MATH; published REDUCED. Citation: Tognoni 2010 (as for the absolute twin). -/
theorem classicComposition_atomicData_error_rel [Nonempty ι] [Nonempty κ]
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

end Plan.FT07
