# FT08-ratio-mode-normalization-invariant: ratio mode ignores a common-mode normalization

Planning dossier (2026-09-24 audit, frontier FT-08 (a), decomposition step 1). Written for a
planner who cannot open the repository; every name below was `#check`ed against lean-main
(Mathlib v4.33.1). **Already proved in scratch** (2 lines, axioms = propext, Classical.choice,
Quot.sound): `_hand-land/FT08-ratio-mode-normalization-invariant.proof.lean`. Hand-land it;
queueing is optional.

## 1. Goal

```lean
import Mathlib
import CflibsFormal.Closure
open CflibsFormal
namespace Plan.FT08
variable {κ : Type*} [Fintype κ]
theorem ratio_mode_normalization_invariant {N : κ → ℝ} {c : ℝ} (hc : c ≠ 0)
    (hsum : ∑ t, N t ≠ 0) (a b : κ) :
    composition (fun t => c * N t) a / composition (fun t => c * N t) b = N a / N b := by
  sorry
```

## 2. Repo definitions and lemmas (namespace `CflibsFormal`, `Closure.lean`)

```lean
noncomputable def totalDensity (n : κ → ℝ) : ℝ :=
  ∑ s, n s
noncomputable def composition (n : κ → ℝ) (s : κ) : ℝ :=
  n s / totalDensity n
theorem composition_smul_invariant {n : κ → ℝ} {c : ℝ}
    (hc : c ≠ 0) (s : κ) :
    composition (fun t => c * n t) s = composition n s
```

Mathlib: `div_div_div_cancel_right₀ : c ≠ 0 → ∀ (a b : G₀), a / c / (b / c) = a / b`.

## 3. Proof route

`rw [composition_smul_invariant hc, composition_smul_invariant hc]`, then
`exact div_div_div_cancel_right₀ hsum (N a) (N b)` (`composition N a` unfolds definitionally to
`N a / ∑ t, N t`). Pitfall: none; do not `unfold` before rewriting with the smul lemma.

## 4. Witness and necessity

Witness: `κ = Fin 2`, `N = ![1, 2]`, `c = 3`: both sides `1/2`. `hc` is needed (at `c = 0` the
left side is `0/0 = 0`); `hsum` is needed (`N = ![1, -1]`: left side `0`, right side `-1`).

## 5. Scope

PURE-MATH (binding audit revision: algebra on an arbitrary vector). No physics claim; it only
says a common-mode normalization cannot change a ratio.
