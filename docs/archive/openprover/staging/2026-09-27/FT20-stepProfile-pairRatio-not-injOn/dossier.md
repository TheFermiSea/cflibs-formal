# FT20-stepProfile-pairRatio-not-injOn: pair-ratio injectivity fails beyond the flat kernel

Planning dossier for the proof queue (frontier FT-20 (b), the headline counterexample; audit
verdict REVISE, revision applied). Written for a planner who cannot open the repository. Every
Mathlib name was checked with `#check` (Mathlib v4.33.1, `lean-main`); the bridge in §4
compiled in a scratch file on 2026-09-27 with the two sibling results as hypotheses.

## 1. Goal

```lean
import Mathlib
import CflibsFormal.EquivalentWidth

open CflibsFormal

namespace Plan.FT20

noncomputable def stepProfile (η M : ℝ) : ℝ → ℝ := fun x =>
  Set.indicator (Set.Icc 0 1) (fun _ => 1) x + η * Set.indicator (Set.Icc 0 M) (fun _ => 1) x

theorem stepProfile_pairRatio_not_injOn :
    ¬ Set.InjOn (fun n : ℝ => equivWidth (stepProfile (1 / 100) 20) (2 * n)
        / equivWidth (stepProfile (1 / 100) 20) n) (Set.Ioi 0) := by
  sorry
```

Keep `stepProfile` and the signature verbatim. Helper lemmas are fine; avoid adding new defs.
Imports: only `Mathlib` and `CflibsFormal.EquivalentWidth`.

## 2. Repo definition (namespace `CflibsFormal`, `EquivalentWidth.lean:75`)

```lean
noncomputable def equivWidth (φ : ℝ → ℝ) (τ : ℝ) : ℝ :=
  ∫ x, (1 - Real.exp (-(τ * φ x)))
```
(Bochner integral over all of `ℝ`, `volume`.)

## 3. Dependency: two sibling targets (not on main)

- Part 1, `FT20-equivWidth-stepProfile`:
  `theorem equivWidth_stepProfile {η M τ : ℝ} (hM : 1 ≤ M) : equivWidth (stepProfile η M) τ
     = (1 - Real.exp (-(τ * (1 + η)))) + (M - 1) * (1 - Real.exp (-(τ * η)))`.
  Its dossier has a fully compiled ~35-line proof (pointwise split into
  `1_[0,1]·(1 - e^{-τ(1+η)}) + 1_(1,M]·(1 - e^{-τη})`, `integral_add`,
  `integral_indicator_const`, `Real.volume_Icc/Ioc`; pass `measure_Icc_lt_top.ne` to
  `integrableOn_const`).
- Part 2a, `FT20-stepW-pairRatio-not-injOn`: `¬ Set.InjOn (fun n => stepW (1/100) 20 (2*n) /
  stepW (1/100) 20 n) (Set.Ioi 0)` with `stepW η M τ := (1 - exp (-(τ (1+η)))) + (M-1)(1 -
  exp (-(τ η)))`. Route: enclosures `exp(-1/100) ∈ [0.99, 0.9901]` (`Real.add_one_le_exp`),
  `exp(-101/100) ∈ [0.3642, 0.3643]` (`Real.exp_one_gt_d9/lt_d9`), `Real.exp_nat_mul` to write
  the 12 exps as powers, `f 1 > 29/20 > f 3 < 29/20 < f 10` by `nlinarith` after generalizing
  powers, continuity on `[1,10]`, then two IVTs (`intermediate_value_Icc'`,
  `intermediate_value_Icc`) give two distinct preimages of `29/20`.

Queue this target after both land and paste their proofs as helper lemmas (state the 2a helper
with the closed form written out, so no `stepW` def is needed). Standalone, it needs both
proofs inline (~35 + ~120 lines).

## 4. Bridge (compiled with h1, h2 as hypotheses)

```lean
  -- h1 : ∀ {η M τ : ℝ}, 1 ≤ M → equivWidth (stepProfile η M) τ = <closed form>
  -- h2 : ¬ Set.InjOn (fun n : ℝ => stepW (1/100) 20 (2*n) / stepW (1/100) 20 n) (Set.Ioi 0)
  simpa only [h1 (by norm_num : (1:ℝ) ≤ 20), stepW] using h2
```
If h2 is stated with the closed form written out, drop `stepW` from the simp set.

## 5. Mathlib lemmas (checked)

Part 1: `MeasureTheory.integral_add`, `MeasureTheory.integral_indicator_const`,
`MeasureTheory.integrable_indicator_iff`, `MeasureTheory.integrableOn_const`,
`measure_Icc_lt_top`, `measure_Ioc_lt_top`, `MeasureTheory.measureReal_def`, `Real.volume_Icc`,
`Real.volume_Ioc`, `ENNReal.toReal_ofReal`, `Set.indicator_of_mem`, `Set.indicator_of_notMem`.
Part 2a: `Real.add_one_le_exp`, `Real.exp_one_gt_d9`, `Real.exp_one_lt_d9`, `Real.exp_nat_mul`,
`Real.exp_sub`, `Real.exp_neg`, `Real.exp_lt_one_iff`, `pow_le_pow_left₀`, `div_lt_iff₀`,
`lt_div_iff₀`, `inv_le_comm₀`, `intermediate_value_Icc`, `intermediate_value_Icc'`,
`ContinuousOn.strictMonoOn_of_injOn_Icc'` (alternative), `ContinuousOn.div`, `ContinuousOn.mono`.

## 6. Pitfalls

- The `simpa only [h1 ...]` rewrite needs `h1` specialised with `M = 20` proof `1 ≤ 20`; the
  literals must stay `1 / 100` and `20` (do not `norm_num` the goal first).
- See the sibling dossiers for the literal-normalization trap (`1/100` becomes `100⁻¹`) and the
  missing names `Real.exp_lt_one`, `Real.exp_lt_one_of_neg`.

## 7. Scope reading

PURE-MATH counterexample: the surrogate kernel `1_[0,1] + (1/100)·1_[0,20]` is not a physical
line shape. Consequence (a docs action, not part of this target): the flat-kernel results
`CurveOfGrowth.cogRatio_injOn` and `Certificates.saDistinct_certificate_sound` (C13), tagged
EXACT, certify uniqueness only for the flat kernel (`W = 1 - exp (-τ)`, where the `r = 2` pair
ratio is `cogRatio 2 1`) and should be retagged REDUCED with a pointer here. The Voigt behaviour
stays numerics only: at `γ/σ = 0.01` the minimum lies outside the W3-B gate range; at 0.1 and
0.93 it lies inside, with a second-branch band under 1%. Curve of growth: Gornushkin et al.,
Spectrochim. Acta B 54 (1999) 491-503.
