# FT14-perLine-tauRatio: two-line τ ratio with per-line σ0 and the stimulated-emission factor

Planning dossier (2026-09-24 audit, frontier FT-14 (iv), restated per the binding revision).
Written for a planner who cannot open the repository. Repo definitions are quoted verbatim from
`lean-main` (origin/main); Mathlib names checked with `#check` (v4.33.1). The statement was
closed in scratch by the 6-line route of §4 (hand-land candidate).

## 1. Goal

```lean
import Mathlib
import CflibsFormal.OpticalDepth

open CflibsFormal

namespace Plan.FT14

theorem perLine_tauRatio {ι : Type*} [Fintype ι] [Nonempty ι] {kB T N ell κ01 κ02 x1 x2 : ℝ}
    {g E : ι → ℝ} {l1 l2 : ι} (hN : N ≠ 0) (hell : ell ≠ 0) (hg : ∀ k, 0 < g k)
    (hσ2 : κ02 * (1 - Real.exp (-x2)) ≠ 0) :
    opticalDepth kB T N (κ01 * (1 - Real.exp (-x1))) ell g E l1
        / opticalDepth kB T N (κ02 * (1 - Real.exp (-x2))) ell g E l2
      = κ01 * (1 - Real.exp (-x1)) * g l1 * boltzmannFactor kB T (E l1)
        / (κ02 * (1 - Real.exp (-x2)) * g l2 * boltzmannFactor kB T (E l2)) := by
  sorry
```

## 2. Repo definitions (namespace `CflibsFormal`, `variable {ι : Type*} [Fintype ι]`)

```lean
-- Boltzmann.lean
noncomputable def boltzmannFactor (kB T E : ℝ) : ℝ := Real.exp (-E / (kB * T))
lemma boltzmannFactor_pos (kB T E : ℝ) : 0 < boltzmannFactor kB T E
noncomputable def partitionFunction (kB T : ℝ) (g E : ι → ℝ) : ℝ :=
  ∑ k, g k * boltzmannFactor kB T (E k)
lemma partitionFunction_pos [Nonempty ι] {kB T : ℝ} {g E : ι → ℝ}
    (hg : ∀ k, 0 < g k) : 0 < partitionFunction kB T g E
noncomputable def population (kB T N : ℝ) (g E : ι → ℝ) (k : ι) : ℝ :=
  N * g k * boltzmannFactor kB T (E k) / partitionFunction kB T g E
-- OpticalDepth.lean:118 (argument order: kB T N sigma0 ell g E l)
noncomputable def opticalDepth (kB T N sigma0 ell : ℝ) (g E : ι → ℝ) (l : ι) : ℝ :=
  sigma0 * ell * population kB T N g E l
```

## 3. Lemmas (checked)

`CflibsFormal.partitionFunction_pos`, `CflibsFormal.boltzmannFactor_pos`, `mul_ne_zero_iff`,
`mul_div_mul_right : c ≠ 0 → a * c / (b * c) = a / b`, tactic `field_simp`.

## 4. Route

`have hU := (partitionFunction_pos hg).ne'` (at the goal's `kB T g E`);
`hg2 := (hg l2).ne'`; `hb2 := (boltzmannFactor_pos _ _ _).ne'`;
`obtain ⟨hk2, hs2⟩ := mul_ne_zero_iff.mp hσ2`; `unfold opticalDepth population`; `field_simp`.
(Alternative without `field_simp`: both sides share the factor `ell * N / U`; rearrange and use
`mul_div_mul_right` with that factor `≠ 0`.)
Pitfall: `field_simp` needs `1 - Real.exp (-x2) ≠ 0` and `κ02 ≠ 0` as separate facts.

## 5. Scope and hypotheses

REDUCED: homogeneous single-temperature LTE slab, flat line-centre cross-section. The per-line
`σ0ᵢ = κ0ᵢ (1 - e^{-xᵢ})`, `xᵢ = hνᵢ/(k_B T)`, carries the stimulated-emission factor the
original sketch dropped (verdict: about 0.92 per visible line); `κ0ᵢ` stays abstract (D19), so the
model-level identity for `σ01/σ02` in terms of `λ, g_u, A, φ(0)` is NOT part of this target. The
statement is ratio-of-products algebra; its value is that `N`, `ℓ`, `U(T)` cancel while the
`σ0` ratio (with the stimulated factor) survives, which the shared-`σ0` bridge lemmas hide.
`hN`, `hell`, `hg` are necessary (the verdict's refutation: `N = 0` makes the left side `0/0 = 0`).
`hσ2` and `[Nonempty ι]` are the verdict's guards; they are logically redundant (both sides are
`0` when `σ02 = 0`; `l1 : ι` gives `Nonempty ι`) but the `field_simp` proof consumes them.
Witness: `ι = Unit`, `kB = T = N = ell = κ01 = κ02 = x1 = x2 = 1`, `g = 1`, `E = 0`
(`hσ2`: `1 - e^{-1} ≠ 0`, checked in Lean). Literature: Griem 1997.
