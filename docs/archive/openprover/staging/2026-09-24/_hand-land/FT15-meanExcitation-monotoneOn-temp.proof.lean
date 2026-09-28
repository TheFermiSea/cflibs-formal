import Mathlib
import CflibsFormal.Boltzmann
import CflibsFormal.InhomogeneityBias

/-!
# FT-15: the mean excitation energy is nondecreasing in temperature

Staged target, 2026-09-24 deep audit, frontier FT-15 first batch (verdict KEEP, grade B). Needed
to turn the `max T1 T2` log-Lipschitz bound into a box form and for the `log S` Lipschitz bound.
HAND-LAND, do not queue: the 2026-09-24 statement audit found it a short corollary of results on
main. The mean excitation energy exists on main in inverse-temperature form as `tiltMean`
(`InhomogeneityBias`, levels in the role of zones). Through the bridge
`meanExcitation_eq_tiltMean` below, this statement says that `tiltMean` is antitone in its
anchor, which the pair-slope sandwich `tiltMean_le_pairSlope`/`pairSlope_le_tiltMean` there
gives directly. Neither imported repo module contains this theorem.
-/

open Finset CflibsFormal

namespace Plan.FT15

variable {ι : Type*} [Fintype ι]

/-- **Boltzmann-weighted mean excitation energy**
`⟨E⟩_T = (∑ₖ gₖ·Eₖ·exp(−Eₖ/(k_B T))) / U(T)`: the mean level energy under the LTE level
populations of `population` (same `boltzmannFactor`, same `partitionFunction`), over the
supplied finite, possibly truncated, level list. Equivalently `⟨E⟩_T = −d log U/dβ` at
`β = 1/(k_B T)`; that identity is neither used nor proved here. Division is totalized: the value
is `0` if `U = 0`, which positive weights on a nonempty level set exclude. Mathematically
`meanExcitation kB T g E = tiltMean g E (1/(k_B T))` (`InhomogeneityBias`), with levels in the
role of zones; see `meanExcitation_eq_tiltMean`. -/
noncomputable def meanExcitation (kB T : ℝ) (g E : ι → ℝ) : ℝ :=
  (∑ k, g k * E k * boltzmannFactor kB T (E k)) / partitionFunction kB T g E

/-- **Bridge to `InhomogeneityBias`: the partition function is a `mixture`.** With the weights
`g` as masses and the level energies `E` as abscissae, `U(T) = mixture g E (1/(k_B T))`, the
discrete Laplace transform evaluated at the inverse temperature. -/
lemma partitionFunction_eq_mixture (kB T : ℝ) (g E : ι → ℝ) :
    partitionFunction kB T g E = mixture g E (1 / (kB * T)) := by
  unfold partitionFunction mixture boltzmannFactor
  refine Finset.sum_congr rfl (fun k _ => ?_)
  congr 2; ring

/-- **Bridge to `InhomogeneityBias`: the mean excitation energy is a `tiltMean`.**
`⟨E⟩_T = tiltMean g E (1/(k_B T))`: the level energies averaged under the tilted weights at
anchor `β = 1/(k_B T)`, which are the LTE level fractions. -/
lemma meanExcitation_eq_tiltMean (kB T : ℝ) (g E : ι → ℝ) :
    meanExcitation kB T g E = tiltMean g E (1 / (kB * T)) := by
  unfold meanExcitation tiltMean tiltWeight
  rw [partitionFunction_eq_mixture, Finset.sum_div]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  unfold boltzmannFactor
  have : -E k / (kB * T) = -(1 / (kB * T) * E k) := by ring
  rw [this]; ring

/-- **The mean excitation energy is nondecreasing in temperature (FT-15).**

For `k_B > 0` and positive weights, `T ↦ ⟨E⟩_T` is monotone on `(0, ∞)`. Its derivative is
`Var_T(E)/(k_B T²) ≥ 0`, but no derivative is needed. Through `meanExcitation_eq_tiltMean`, for
`T1 < T2` (so `β₂ < β₁`) the pair-slope sandwich of `InhomogeneityBias`
(`tiltMean_le_pairSlope`, `pairSlope_le_tiltMean`) gives `⟨E⟩_{T1} ≤ β_app ≤ ⟨E⟩_{T2}`, with
`β_app` the negated chord slope of `β ↦ log U` between `β₂` and `β₁`. Equivalently, for `T1 ≤ T2`,
cross-multiplying by `U(T1)·U(T2) > 0` turns the claim into a double sum that symmetrizes to
`½ ∑ⱼ ∑ₖ gⱼ gₖ (Eⱼ − Eₖ)(exp(−β₂Eⱼ − β₁Eₖ) − exp(−β₁Eⱼ − β₂Eₖ)) ≥ 0`, where each term is
nonnegative because the exponent gap is `(β₁ − β₂)(Eⱼ − Eₖ)` with `β₁ ≥ β₂`. No sign condition on
the energies is needed. The monotonicity is not strict in general: equal energies give a constant.

Hypotheses and why each is present:
* `hkB : 0 < kB`: raising `T` then lowers `β = 1/(k_B T)`.
* `hg` and `[Nonempty ι]`: `U > 0` (cross-multiplication is legitimate) and the weights `gⱼ gₖ`
  are positive.

Scope (two-axis): own relation PURE-MATH (finite sums, no physical claim); definitions used:
`partitionFunction` and `meanExcitation` (new); predicted published tag PURE-MATH. It becomes
REDUCED when bound to data over a truncated level list (FT-05). -/
theorem meanExcitation_monotoneOn_temp [Nonempty ι] {kB : ℝ} {g E : ι → ℝ} (hkB : 0 < kB)
    (hg : ∀ k, 0 < g k) :
    MonotoneOn (fun T => meanExcitation kB T g E) (Set.Ioi 0) := by
  intro T1 hT1 T2 hT2 hle
  simp only [Set.mem_Ioi] at hT1 hT2
  show meanExcitation kB T1 g E ≤ meanExcitation kB T2 g E
  rw [meanExcitation_eq_tiltMean, meanExcitation_eq_tiltMean]
  rcases hle.lt_or_eq with hlt | heq
  · have hβ : 1 / (kB * T2) < 1 / (kB * T1) :=
      one_div_lt_one_div_of_lt (mul_pos hkB hT1) (mul_lt_mul_of_pos_left hlt hkB)
    exact le_trans (tiltMean_le_pairSlope hg hβ) (pairSlope_le_tiltMean hg hβ)
  · rw [heq]

/-- Non-vacuity witness: `Fin 2`, `E = ![0, 1]`, `g ≡ 1`, `kB = 1`, `T = 1 ≤ 2` (values about
`0.269` and `0.378`). -/
example : meanExcitation 1 1 (fun _ : Fin 2 => (1:ℝ)) ![0, 1]
    ≤ meanExcitation 1 2 (fun _ : Fin 2 => (1:ℝ)) ![0, 1] :=
  meanExcitation_monotoneOn_temp (ι := Fin 2) one_pos (fun _ => one_pos)
    (Set.mem_Ioi.mpr one_pos) (Set.mem_Ioi.mpr two_pos) one_le_two

/-- Non-vacuity witness with a negative energy (no sign hypothesis): `E = ![-1, 1]`. -/
example : meanExcitation 1 1 (fun _ : Fin 2 => (1:ℝ)) ![-1, 1]
    ≤ meanExcitation 1 3 (fun _ : Fin 2 => (1:ℝ)) ![-1, 1] :=
  meanExcitation_monotoneOn_temp (ι := Fin 2) one_pos (fun _ => one_pos)
    (Set.mem_Ioi.mpr one_pos) (Set.mem_Ioi.mpr (by norm_num)) (by norm_num)

end Plan.FT15
