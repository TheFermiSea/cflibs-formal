import Mathlib
import CflibsFormal.ForwardMap

/-!
# Queue target FT09-affine-gA-observational-equiv (deep audit 2026-09-24, FT-09 step 2)

Energy-affine atomic-data gauge: an energy-affine error in the transition probabilities is
observationally equivalent, on the single-stage Boltzmann-plot ordinates, to a temperature shift
plus a density rescale. Statement file for the proof queue: one target theorem, one `sorry`.
-/

open Finset CflibsFormal

namespace Plan.FT09

variable {ι : Type*} [Fintype ι]

theorem exp_shift {kB T T' b e : ℝ} (hT' : 1 / (kB * T') = 1 / (kB * T) - b) :
    -e / (kB * T') = -e / (kB * T) + b * e := by
  rw [div_eq_mul_one_div, hT', div_eq_mul_one_div (-e) (kB * T)]
  ring

theorem ordinate_arg_eq [Nonempty ι] {kB T T' N Fcal α b : ℝ} {g E A A' : ι → ℝ}
    (hg : ∀ k, 0 < g k) (hA : ∀ k, 0 < A k)
    (haff : ∀ k, A' k = A k * Real.exp (-(α + b * E k)))
    (hT' : 1 / (kB * T') = 1 / (kB * T) - b) (k : ι) :
    lineIntensity kB T N Fcal g E A k / (g k * A' k)
      = lineIntensity kB T' (N * Real.exp α * partitionFunction kB T' g E
          / partitionFunction kB T g E) Fcal g E A k / (g k * A k) := by
  have hU : 0 < partitionFunction kB T g E := partitionFunction_pos hg
  have hU' : 0 < partitionFunction kB T' g E := partitionFunction_pos hg
  have hgk := (hg k).ne'
  have hAk := (hA k).ne'
  rw [haff k]
  unfold lineIntensity population boltzmannFactor
  rw [exp_shift hT', Real.exp_add, Real.exp_neg, Real.exp_add]
  field_simp

/-- **Energy-affine gA gauge: observational equivalence.** Let the analyst's transition
probabilities `A'` differ from the true `A` by an energy-affine log factor,
`log (A k / A' k) = α + b·E k` (`haff`). Then the Boltzmann-plot ordinates
`y k = log (I k/(g k·A' k))` of a plasma at `(T, N)`, computed with the wrong `A'`, coincide
**exactly, line by line** with the correct-data ordinates `log (I' k/(g k·A k))` of another plasma
`(T', N')` with
  `1/(kB T') = 1/(kB T) − b`  and (the witness)  `N' = N·e^α·U(T')/U(T)`.
So no function of these ordinates distinguishes `(A', T, N)` from `(A, T', N')`: an energy-affine
gA error is a temperature shift plus a density rescale, and identifying `b` needs information the
ordinates do not carry (an independent `n_e`, or a known composition). The slope identity
(`HeteroAtomicData.olsSlope_aliasing_A` plus an affine fit) is the weaker, already-known shadow of
this statement. Single stage only; the grouped two-stage version (inter-stage offset, `ln n_e`
shift) is deferred to its own pre-registered statement.

The identity holds already for the arguments of the logarithms, so no positivity of the
intensities is used. Hypotheses: `hkB`, `hT`, `hb` give a positive `T'`: `hb : b·(kB·T) < 1` is
exactly the condition for a positive `T'` to satisfy `1/(kB T') = 1/(kB T) − b` (the gauge orbit
stays physical); `hg` (positive degeneracies: `U(T), U(T') > 0`, so `N' > 0`); `hN` (so
`N' > 0`); `haff` (the gauge); `hA` (physical `A > 0`; the proof uses `A k ≠ 0` to cancel the
common factor `A k`). No hypothesis on the calibration `Fcal` is needed: it cancels identically
(the audit sketch's `hFcal` is dropped as unused). `T'` is pinned by its equation, and for
`Fcal > 0` the ordinates also pin `N'` (log is injective on positives), so the existential is not
vacuous. Across several training spectra the same `b` must satisfy `b < min_i 1/(kB·T_i)`
(landing docstring).

Scope (two-axis): relation EXACT (an identity of the ordinates within the stated model);
definitions used: `lineIntensity` REDUCED (optically thin LTE single-stage forward map), with
`population`/`partitionFunction` the Boltzmann populations; published REDUCED (the weaker axis).
Citation: Tognoni 2010; Ciucci 1999 (the Boltzmann-plot ordinate). -/
theorem affine_gA_observational_equiv [Nonempty ι]
    {kB T N Fcal α b : ℝ} {g E A A' : ι → ℝ}
    (hkB : 0 < kB) (hT : 0 < T) (hg : ∀ k, 0 < g k) (hA : ∀ k, 0 < A k) (hN : 0 < N)
    (haff : ∀ k, A' k = A k * Real.exp (-(α + b * E k)))
    (hb : b * (kB * T) < 1) :
    ∃ T' N' : ℝ, 0 < T' ∧ 0 < N' ∧ 1 / (kB * T') = 1 / (kB * T) - b ∧
      ∀ k, Real.log (lineIntensity kB T N Fcal g E A k / (g k * A' k))
        = Real.log (lineIntensity kB T' N' Fcal g E A k / (g k * A k)) := by
  have hkT : 0 < kB * T := mul_pos hkB hT
  have hβ : 0 < 1 / (kB * T) - b := by
    rw [sub_pos, lt_div_iff₀ hkT]; linarith
  refine ⟨1 / (kB * (1 / (kB * T) - b)),
    N * Real.exp α * partitionFunction kB (1 / (kB * (1 / (kB * T) - b))) g E
      / partitionFunction kB T g E, by positivity, ?_, ?_, fun k => ?_⟩
  · have h1 := partitionFunction_pos (kB := kB) (T := 1 / (kB * (1 / (kB * T) - b))) (E := E) hg
    have h2 := partitionFunction_pos (kB := kB) (T := T) (E := E) hg
    positivity
  · field_simp
  · have hT'eq : 1 / (kB * (1 / (kB * (1 / (kB * T) - b)))) = 1 / (kB * T) - b := by
      field_simp
    rw [ordinate_arg_eq hg hA haff hT'eq k]

end Plan.FT09
