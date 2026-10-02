# FT08-neutrality-closure-same-ratio: closure and neutrality readers agree on ratios (per-U)

Planning dossier (2026-09-24 audit, frontier FT-08 (a), decomposition step 2), in the form the
audit revision requires: per-species partition functions via `MultiSpecies.lineIntensityPerU`.
Every name below was `#check`ed against lean-main (Mathlib v4.33.1). **Already proved in
scratch** (~11 lines, axiom-clean): `_hand-land/FT08-neutrality-closure-same-ratio.proof.lean`.

## 1. Goal

```lean
import Mathlib
import CflibsFormal.MultiSpecies
import CflibsFormal.Alt.NeutralityScale
open CflibsFormal CflibsFormal.Alt
namespace Plan.FT08
variable {ι κ : Type*} [Fintype κ]
theorem neutrality_closure_same_ratio {kB T Fcal : ℝ} {g E A : ι → ℝ} {N U : κ → ℝ}
    {emit : κ → ι} {I unitI : κ → ℝ} (hFcal : 0 < Fcal) (hN : ∀ s, 0 < N s)
    (hI : ∀ s, I s = lineIntensityPerU kB T (N s) Fcal (U s) g E A (emit s))
    (hu : ∀ s, unitI s = lineIntensityPerU kB T 1 1 (U s) g E A (emit s))
    (hunit : ∀ s, 0 < unitI s) (a b : κ) :
    closureEstimate I unitI a / closureEstimate I unitI b = N a / N b ∧
      ∀ (R : κ → ℝ) (ne : ℝ), neutralityScale I unitI R ne ≠ 0 →
        ((I a / unitI a) / neutralityScale I unitI R ne)
            / ((I b / unitI b) / neutralityScale I unitI R ne) = N a / N b := by
  sorry
```

## 2. Repo definitions (verbatim)

```lean
-- Boltzmann.lean (namespace CflibsFormal)
noncomputable def boltzmannFactor (kB T E : ℝ) : ℝ := Real.exp (-E / (kB * T))
-- MultiSpecies.lean:171 (namespace CflibsFormal)
noncomputable def lineIntensityPerU (kB T N Fcal Us : ℝ) (g E A : ι → ℝ) (s : ι) : ℝ :=
  Fcal * A s * (N * g s * boltzmannFactor kB T (E s) / Us)
-- Alt/NeutralityScale.lean:96, :158 (namespace CflibsFormal.Alt)
noncomputable def neutralityScale (I unitI R : κ → ℝ) (ne : ℝ) : ℝ :=
  (∑ s, I s * R s / unitI s) / ne
noncomputable def closureEstimate (I unitI : κ → ℝ) (s : κ) : ℝ :=
  (I s / unitI s) / ∑ t, I t / unitI t
```

Related (not needed): `density_ratio_from_intensities_perU` (known-`U` de-normalization reader).

## 3. Proof route

1. `key : ∀ s, I s / unitI s = Fcal * N s`: rewrite `hu`, `hI`, `div_eq_iff (hunit s).ne'`
   (after rewriting `hu` into it), `unfold lineIntensityPerU; ring`. `U s` cancels here.
2. `hS : 0 < ∑ t, N t := Finset.sum_pos (fun t _ => hN t) ⟨a, Finset.mem_univ a⟩`.
3. Closure: `unfold closureEstimate; simp only [key, ← Finset.mul_sum];
   field_simp [hFcal.ne', hS.ne']`.
4. Neutrality: `rw [div_div_div_cancel_right₀ hne, key, key]; field_simp [hFcal.ne']`.

Pitfall: `field_simp` cannot split `1 * A * (1 * g * bf / U) ≠ 0` into factors; use
`div_eq_iff` with the whole unit intensity instead.

## 4. Witness

`ι = κ = Fin 2`, `emit = id`, `g = A = U = 1`, `E = 0`, `kB = T = Fcal = 1`, `N = ![1, 2]`,
`I s = N s`, `unitI s = 1` (checked: `0 < lineIntensityPerU 1 1 1 1 1 1 0 1 i` by
`norm_num [lineIntensityPerU, boltzmannFactor]`). Second conjunct is non-vacuous: `R = 1`,
`ne = 1` give `neutralityScale = 3 ≠ 0`. Necessity: `Fcal = 0` makes every closure estimate `0`.

## 5. Scope

Prediction REDUCED (LTE, optically thin, single `T`, one designated line per species). Note for
the auditor: the relation is exact algebra and `lineIntensityPerU`'s own docstring tags it EXACT
with `U_s` a free input, so EXACT is arguable. Does not claim absolute accuracy of `Fcal`/`N`.
Literature: Tognoni et al. 2010 (closure over observed species). NeutralityScale's Abbass
citation is off-whitelist and is not cited as prior art.
