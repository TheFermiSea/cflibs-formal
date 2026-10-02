import Mathlib
import CflibsFormal.Boltzmann
import CflibsFormal.InhomogeneityBias
import CflibsFormal.SahaStability

/-!
# FT-15: log-Lipschitz bound for the partition function via the mean excitation energy

Staged target, 2026-09-24 deep audit, frontier FT-15 (verdict KEEP, grade B), in the verifier's
form with `⟨E⟩` evaluated at `max T1 T2`, which needs no monotonicity lemma. HAND-LAND, do not
queue: the 2026-09-24 statement audit found it a short corollary of results on main. The mean
excitation energy exists on main in inverse-temperature form as `tiltMean` (`InhomogeneityBias`,
levels in the role of zones); the two bridge lemmas below identify `partitionFunction` and
`meanExcitation` with `mixture` and `tiltMean`, and the tangent inequality this bound rests on is
`logMixture_tangent_le` there. No module on main states this bound for `partitionFunction`; the
existing constants (`partitionFunction_lipschitz_temp`, `sahaFactorLipConst`) are built from
`∑ g·E`. None of the imported modules contains this theorem.
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

/-- **Log-Lipschitz bound for the partition function in inverse temperature (FT-15).**

For positive weights, nonnegative level energies and `T1, T2 > 0`,
`|log U(T1) − log U(T2)| ≤ ⟨E⟩_{max T1 T2} · |1/(k_B T1) − 1/(k_B T2)|`.
This is the two-point form of `d log U/dβ = −⟨E⟩_β` together with `⟨E⟩` increasing in `T`, but
it needs no derivatives: `log U` is convex in `β = 1/(k_B T)` (finite Jensen for `exp`;
`logMixture_tangent_le` through the bridges above), so its tangent at the smaller `β` (the
larger `T`) bounds the chord. The constant is the mean excitation energy at the hotter
temperature, in the audit's measurements (PS-03, a narrow [0.8, 1.2] eV box) far tighter than
the `∑ g·E` constants on main, which bound `U` in `T` rather than `log U` in `β`.

Hypotheses and why each is present:
* `hkB`, `hT1`, `hT2`: both inverse temperatures are positive, ordered opposite to `T`.
* `hg` and `[Nonempty ι]`: `U > 0`, so `log U` is genuine, and the Jensen weights are positive.
* `hE : ∀ k, 0 ≤ E k` (energies measured from the ground state) is load-bearing: it makes
  `log U` nondecreasing in `T`, which fixes the sign inside `|·|`. Without it the statement is
  false: one level with `E < 0` makes the right side negative.

Scope (two-axis): own relation PURE-MATH (finite sums, no physical claim); definitions used:
`partitionFunction` (the Boltzmann sum over the supplied list) and `meanExcitation` (new);
predicted published tag PURE-MATH. It becomes REDUCED when bound to data, because a physical
`U` is a sum over a truncated level list (FT-05). -/
theorem log_partitionFunction_lipschitz_max [Nonempty ι] {kB T1 T2 : ℝ} {g E : ι → ℝ}
    (hkB : 0 < kB) (hT1 : 0 < T1) (hT2 : 0 < T2) (hg : ∀ k, 0 < g k) (hE : ∀ k, 0 ≤ E k) :
    |Real.log (partitionFunction kB T1 g E) - Real.log (partitionFunction kB T2 g E)|
      ≤ meanExcitation kB (max T1 T2) g E * |1 / (kB * T1) - 1 / (kB * T2)| := by
  sorry

end Plan.FT15
