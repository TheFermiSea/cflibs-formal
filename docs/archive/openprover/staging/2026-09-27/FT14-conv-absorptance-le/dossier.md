# FT14-conv-absorptance-le: pointwise Jensen step of "transfer before instrument"

Planning dossier (2026-09-24 audit, frontier FT-14 (v), decomposition item 7 only). The verdict
requires (v) to be split because its measure-theory plumbing matches the F07 queue-failure
profile; the integrated form `equivWidth φ τ ≤ equivWidth (R ⋆ φ) τ` (item 8, Fubini) is a
separate, later target. Mathlib names checked with `#check` (v4.33.1). No repo definitions.

## 1. Goal (only `import Mathlib`)

```lean
open MeasureTheory

namespace Plan.FT14

theorem conv_absorptance_le {R φ : ℝ → ℝ} {τ x : ℝ} (hR : ∀ y, 0 ≤ R y) (hR1 : ∫ y, R y = 1)
    (hφ : 0 ≤ φ) (hτ : 0 ≤ τ) (hRφ : Integrable (fun y => R (x - y) * φ y)) :
    ∫ y, R (x - y) * (1 - Real.exp (-(τ * φ y)))
      ≤ 1 - Real.exp (-(τ * ∫ y, R (x - y) * φ y)) := by
  sorry
```

## 2. Mathlib lemmas (checked)

- `Real.add_one_le_exp : ∀ x, x + 1 ≤ Real.exp x`
- `MeasureTheory.integral_mono_of_nonneg :
  0 ≤ᵐ[μ] f → Integrable g μ → f ≤ᵐ[μ] g → ∫ f ≤ ∫ g`  (no integrability of `f` needed)
- `MeasureTheory.Integrable.of_integral_ne_zero : ∫ f ≠ 0 → Integrable f`  (R from `hR1`)
- `MeasureTheory.Integrable.comp_sub_left : Integrable f μ → ∀ g, Integrable (fun t => f (g - t))`
- `MeasureTheory.integral_sub_left_eq_self (f) (μ) (x') : ∫ x, f (x' - x) ∂μ = ∫ x, f x ∂μ`
- `integral_add`, `integral_sub`, `integral_const_mul`, `integral_mul_const`, `integral_nonneg`
- (heavier alternative) `ConcaveOn.le_map_integral` with `[IsProbabilityMeasure μ]`

## 3. Route (tangent line; avoids `withDensity` plumbing)

Let `m := ∫ y, R (x - y) * φ y` and `c := Real.exp (-(τ * m)) > 0`.
1. Tangent bound, all real `t`: `1 - Real.exp (-(τ * t)) ≤ (1 - c) + τ * c * (t - m)`.
   Proof: `Real.exp (-(τ * t)) = c * Real.exp (-(τ * (t - m)))` (`← Real.exp_add`, ring in the
   exponent) and `Real.exp (-(τ * (t - m))) ≥ 1 - τ * (t - m)` (`Real.add_one_le_exp`); `c > 0`.
2. Multiply by `R (x - y) ≥ 0`: `R (x-y) * (1 - exp …) ≤ (1 - c) * R (x-y)
   + τ * c * (R (x-y) * φ y - m * R (x-y))`.
3. `integral_mono_of_nonneg`: the left integrand is `≥ 0` (`R ≥ 0`, `τ * φ y ≥ 0`, so
   `exp (-(τ φ y)) ≤ 1`); the right integrand is integrable from `hRφ` and
   `(Integrable.of_integral_ne_zero (by rw [hR1]; norm_num)).comp_sub_left x`.
4. Evaluate the right integral: `∫ R (x - y) = 1` (`integral_sub_left_eq_self R volume x`, `hR1`),
   so it equals `(1 - c) * 1 + τ * c * (m - m * 1) = 1 - c`.
Pitfall: do not try to prove integrability of the left integrand (φ need not be measurable off the
support of `R (x - ·)`); `integral_mono_of_nonneg` makes it unnecessary.

## 4. Scope and hypotheses

PURE-MATH (Jensen for the concave `t ↦ 1 - e^{-τt}`); physics reading REDUCED (homogeneous slab,
common source function `S`, linear shift-invariant instrument `R`). Reading: folding the
instrument into the opacity (right side) overstates the emergent intensity `S · (…)` at every
pixel, i.e. understates self-absorption. Necessity: `hRφ` (else the right side is the junk value
`1 - exp 0 = 0` while the left can be positive); `hφ` (with `φ = 2 log |y|` on `[-1, 0]`, box `R`,
`τ = 1`, the left integrand is non-integrable, so the left side is `0` > right side `1 - e²`);
`hτ` (for `τ < 0` the map is convex); `hR`, `hR1` (probability kernel). `Integrable R` is not
assumed: it follows from `hR1`. Witness: `R = (Set.Icc 0 1).indicator 1`, `φ = 1`, `τ = 1`,
`x = 0` (checked in Lean). Literature: Griem 1974 (instrument convolution), Gornushkin 1999.
