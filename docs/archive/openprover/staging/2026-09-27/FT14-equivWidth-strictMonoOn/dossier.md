# FT14-equivWidth-strictMonoOn: the curve of growth is strictly increasing in τ

Planning dossier (2026-09-24 audit, frontier FT-14 (ii), decomposition item 3; verdict REVISE,
(ii) kept). Written for a planner who cannot open the repository. Repo text quoted verbatim from
`lean-main` (origin/main); Mathlib names checked with `#check` (v4.33.1).

## 1. Goal

```lean
import Mathlib
import CflibsFormal.EquivalentWidth

open CflibsFormal MeasureTheory

namespace Plan.FT14

theorem equivWidth_strictMonoOn {ψ : ℝ → ℝ} (hψ0 : 0 ≤ ψ) (hint : Integrable ψ)
    (hpos : 0 < ∫ x, ψ x) : StrictMonoOn (equivWidth ψ) (Set.Ici 0) := by
  sorry
```

## 2. Repo definitions and lemmas (`EquivalentWidth.lean`, namespace `CflibsFormal`)

```lean
noncomputable def equivWidth (φ : ℝ → ℝ) (τ : ℝ) : ℝ :=
  ∫ x, (1 - Real.exp (-(τ * φ x)))

theorem equivWidth_integrand_integrable {φ : ℝ → ℝ} {τ : ℝ} (hτ : 0 ≤ τ)
    (hφnn : 0 ≤ φ) (hφ : Integrable φ) :
    Integrable (fun x => 1 - Real.exp (-(τ * φ x)))

theorem equivWidth_mono {φ : ℝ → ℝ} {τ₁ τ₂ : ℝ} (hτ₁ : 0 ≤ τ₁) (hτ : τ₁ ≤ τ₂)
    (hφnn : 0 ≤ φ) (hφ : Integrable φ) :
    equivWidth φ τ₁ ≤ equivWidth φ τ₂          -- non-strict; the strict form is new
```

## 3. Mathlib lemmas (checked)

- `MeasureTheory.integral_pos_iff_support_of_nonneg :
  0 ≤ f → Integrable f μ → (0 < ∫ x, f x ∂μ ↔ 0 < μ (Function.support f))`
- `MeasureTheory.integral_sub : Integrable f μ → Integrable g μ → ∫ f - g = ∫ f - ∫ g`
- `Real.exp_lt_exp : Real.exp x < Real.exp y ↔ x < y`; `Integrable.sub`, `sub_pos`

## 4. Route

Fix `0 ≤ a < b` (`intro a ha b hb hab`; `Set.mem_Ici`). Let
`d x := Real.exp (-(a * ψ x)) - Real.exp (-(b * ψ x))`.
1. `equivWidth ψ b - equivWidth ψ a = ∫ x, d x`: unfold, `← integral_sub` with the two
   `equivWidth_integrand_integrable` facts, then `congr 1; funext x; ring`.
2. `0 ≤ d` pointwise: `a * ψ x ≤ b * ψ x` (`mul_le_mul_of_nonneg_right`), then `Real.exp_le_exp`.
3. `Function.support d = Function.support ψ`: if `ψ x = 0` then `d x = 0`; if `ψ x ≠ 0` then
   `ψ x > 0`, so `a * ψ x < b * ψ x` and `d x > 0` by `Real.exp_lt_exp`.
4. `(integral_pos_iff_support_of_nonneg hψ0 hint).mp hpos : 0 < volume (support ψ)`; rewrite
   with step 3 and apply `(integral_pos_iff_support_of_nonneg hd0 hdint).mpr`.
5. Conclude with `sub_pos.mp`.
Pitfalls: the integrand is `-(τ * ψ x)`, not `-τ * ψ x`; `d` integrable as a difference of the two
integrable integrands (rewrite `d = (1 - e_b) - (1 - e_a)` pointwise first). `hψ0 : 0 ≤ ψ` is a
Pi-order fact: use `hψ0 x`.

## 5. Scope and hypotheses

PURE-MATH (strict monotonicity of a parametric integral); physics reading REDUCED (homogeneous
slab, one common profile). With a Kirchhoff source `S > 0` and `τ = κ L`, the slab-integrated
emergent intensity `S * equivWidth ψ (κ * L)` is strictly increasing in `L > 0` (and in density
at fixed `L`); that composition is a 3-line corollary (`mul_lt_mul_of_pos_left`) and is not staged.
Necessity: `hpos` (if `ψ = 0` a.e. then `W ≡ 0`); `hψ0` (sign changes break monotonicity).
`hint` is implied by `hpos` (`Integrable.of_integral_ne_zero`), kept to match `equivWidth_mono`.
Witness: `ψ x = Real.exp (-x ^ 2)` (integrable, `∫ = √π > 0`; checked in Lean).
Literature: Gornushkin 1999 (curve of growth).
