# FT13-escape-ge-slab: profile escape factor ≥ flat-slab factor at the line-centre depth

Planning dossier for the proof queue (2026-09-24 audit, frontier FT-13 (a), queue item 2).
Written for a planner who cannot open the repository. Every repo definition and lemma is quoted,
and every Mathlib name was checked with `#check` against the pinned Mathlib (v4.33.1).

This target has exactly ONE measure-theory step (`integral_mono`), following a pattern already
used on main (`equivWidth_le_thin`, `equivWidth_mono`). It deliberately avoids the profile of
the failed F07 target (improper integrals, dominated convergence).

## 1. Goal

```lean
import Mathlib
import CflibsFormal.SelfAbsorption
import CflibsFormal.EquivalentWidth

open CflibsFormal MeasureTheory

namespace Plan.FT13

theorem escape_ge_slab {ψ : ℝ → ℝ} {τ0 : ℝ} (hψ0 : 0 ≤ ψ) (hψ1 : ∀ x, ψ x ≤ 1)
    (hint : Integrable ψ) (hτ : 0 < τ0) :
    selfAbsorptionFactor τ0 * (τ0 * ∫ x, ψ x) ≤ equivWidth ψ τ0 := by
  sorry
```

No new definitions. The audited file is `statement.lean` here; keep the signature verbatim,
add helper lemmas above the theorem if useful, add no imports. `Integrable ψ` means
`MeasureTheory.Integrable ψ volume`; `∫ x, ψ x` is the Bochner integral over `ℝ` (Lebesgue).

## 2. Definitions (namespace `CflibsFormal`)

`CflibsFormal/SelfAbsorption.lean:63`:

```lean
noncomputable def selfAbsorptionFactor (tau : ℝ) : ℝ :=
  if tau = 0 then 1 else (1 - Real.exp (-tau)) / tau
```

`CflibsFormal/EquivalentWidth.lean:75`:

```lean
noncomputable def equivWidth (φ : ℝ → ℝ) (τ : ℝ) : ℝ :=
  ∫ x, (1 - Real.exp (-(τ * φ x)))
```

## 3. Mathematical proof

Since `τ0 ≠ 0`, `selfAbsorptionFactor τ0 * τ0 = 1 - e^(-τ0)`, so the left side is
`(1 - e^(-τ0)) * ∫ ψ = ∫ x, (1 - e^(-τ0)) * ψ x`.

Pointwise chord: for `t ∈ [0, 1]`, convexity of `exp` between `0` and `-τ0` gives
`e^(-τ0 t) = e^((1 - t)·0 + t·(-τ0)) ≤ (1 - t)·1 + t·e^(-τ0)`, i.e.
`(1 - e^(-τ0)) * t ≤ 1 - e^(-(τ0 * t))`. Apply with `t = ψ x` (`0 ≤ ψ x ≤ 1`).

Integrate: both integrands are integrable (`hint.const_mul _` and
`equivWidth_integrand_integrable`), so `integral_mono` gives the claim.

## 4. Suggested Lean proof skeleton

```lean
theorem slab_chord_le {τ t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 - Real.exp (-τ)) * t ≤ 1 - Real.exp (-(τ * t)) := by
  -- PROVED, paste from §5
  ...

theorem escape_ge_slab ... := by
  have hLHS : selfAbsorptionFactor τ0 * (τ0 * ∫ x, ψ x)
      = ∫ x, (1 - Real.exp (-τ0)) * ψ x := by
    rw [integral_const_mul, selfAbsorptionFactor, if_neg hτ.ne']
    field_simp
  rw [hLHS, equivWidth]
  refine integral_mono (hint.const_mul _) (equivWidth_integrand_integrable hτ.le hψ0 hint) ?_
  intro x
  exact slab_chord_le (hψ0 x) (hψ1 x)
```

This skeleton was NOT compiled; expect small repairs (the `field_simp` step may need
`mul_comm`/`div_mul_cancel₀`; the pointwise goal after `refine` may be displayed as
`(fun x => …) x ≤ (fun x => …) x`, so `intro x; simp only []` or `show` may be needed).
Everything it names exists with the signatures below.

## 5. Pasteable proved helper (evidence/adv-verifier-2/Refute.lean:117)

Checked 2026-09-24: compiles verbatim when placed above the theorem in this `statement.lean`.
It needs no sign hypothesis on `τ` (convexity of `exp` on all of `ℝ`).

```lean
theorem slab_chord_le {τ t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 - Real.exp (-τ)) * t ≤ 1 - Real.exp (-(τ * t)) := by
  have hc := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (-τ))
    (by linarith : (0 : ℝ) ≤ 1 - t) ht0 (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at hc
  have : t * -τ = -(τ * t) := by ring
  rw [this] at hc
  nlinarith [hc]
```

## 6. Repo lemmas in scope (namespace `CflibsFormal`)

- `equivWidth_integrand_integrable {φ : ℝ → ℝ} {τ : ℝ} (hτ : 0 ≤ τ) (hφnn : 0 ≤ φ)
  (hφ : Integrable φ) : Integrable (fun x => 1 - Real.exp (-(τ * φ x)))`
  (`EquivalentWidth.lean:80`). This is the integrability of the right-hand integrand.
- Template, the same `integral_mono` pattern (`EquivalentWidth.lean:107`):

```lean
theorem equivWidth_le_thin {φ : ℝ → ℝ} {τ : ℝ} (hτ : 0 ≤ τ) (hφnn : 0 ≤ φ) (hφ : Integrable φ) :
    equivWidth φ τ ≤ τ * ∫ x, φ x := by
  rw [equivWidth, ← integral_const_mul]
  refine integral_mono (equivWidth_integrand_integrable hτ hφnn hφ) (hφ.const_mul τ) (fun x => ?_)
  linarith [Real.one_sub_le_exp_neg (τ * φ x)]
```

  (This target is the matching LOWER bound, with the chord in place of `1 - e^(-y) ≤ y`.)
- `equivWidth_rectangular (τ : ℝ) : equivWidth (Set.indicator (Set.Icc 0 1) (fun _ => 1)) τ =
  1 - Real.exp (-τ)` shows the inequality is sharp (not needed for the proof).
- `selfAbsorptionFactor_pos`, `selfAbsorptionFactor_le_one` exist but are not needed.

## 7. Mathlib lemmas (signatures checked)

- `MeasureTheory.integral_mono {f g : α → E} (hf : Integrable f μ) (hg : Integrable g μ)
  (h : f ≤ g) : ∫ x, f x ∂μ ≤ ∫ x, g x ∂μ` (`Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`;
  note `h : f ≤ g` is a pointwise `Pi.le`, i.e. `∀ x, f x ≤ g x`).
- `MeasureTheory.integral_const_mul (r : L) (f : α → L) : ∫ a, r * f a ∂μ = r * ∫ a, f a ∂μ`.
- `MeasureTheory.Integrable.const_mul : Integrable f μ → ∀ c, Integrable (fun x => c * f x) μ`.
- `convexOn_exp : ConvexOn ℝ Set.univ Real.exp`.
- `Real.exp_zero`, `if_neg`, `ne_of_gt`, `field_simp`.

## 8. Pitfalls

- `hψ0 : 0 ≤ ψ` is a function inequality; the pointwise fact is `hψ0 x : 0 ≤ ψ x`
  (it unfolds through `Pi.le_def`; `hψ0 x` works directly).
- Unfold `selfAbsorptionFactor` with `rw [selfAbsorptionFactor, if_neg hτ.ne']`; `simp` with the
  definition can instead produce an `if` it cannot close.
- Do not rewrite `∫` of a product with the constant on the right (`integral_mul_const`) by
  mistake: `integral_const_mul` expects `r * f a`.
- `equivWidth_integrand_integrable` needs `0 ≤ τ0`: pass `hτ.le`.
- No dominated convergence, no improper integrals, no change of variables are needed. If the
  plan starts to involve them, it has gone off route.
