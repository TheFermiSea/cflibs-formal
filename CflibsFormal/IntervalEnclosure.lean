/-
Copyright (c) 2026 Brian Squires. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Squires
-/
import Mathlib
import CflibsFormal.OLS

/-!
# CF-LIBS formalization — a verified ε-ball enclosure for the OLS forward map

This module supplies the **bounded-error verification link** the numerical oracle currently
lacks: an *explicit Lipschitz bound* for the Boltzmann-plot forward/design map on a bounded
input box. Concretely, for the two-column normal matrix `designNormalMatrix E =
![![∑ Eₖ², ∑ Eₖ], ![∑ Eₖ, n]]` (OLS.lean:185) viewed as an entrywise map
`normalMap : (ι → ℝ) → (Fin 2 → Fin 2 → ℝ)`, we prove

  `dist (normalMap E) (normalMap Ê) ≤ (2·B + 1)·n · dist E Ê`

for all energy vectors `E, Ê` inside the box `energyBox B = { E | ∀ k, |Eₖ| ≤ B }`, where the
metrics are the ambient sup-metrics of the `Pi` types and `n = card ι`. The Lipschitz constant
`L(B, n) = (2·B + 1)·n` is **explicit** in the box radius `B` and the line count `n`. Packaged
as `LipschitzOnWith` in `normalMap_lipschitzOnWith`.

**Interpretation (the ε-ball link).** If a floating-point execution perturbs the exact real
energies by at most `ε` in the sup-metric — `dist E Ê ≤ ε` — then the computed normal matrix
stays within an `L·ε` ball of the exact real result: `dist (normalMap E) (normalMap Ê) ≤ L·ε`
(`normalMap_epsilon_ball`). This turns the regression oracle into a *bounded-error* verification
link: a perturbation of the inputs propagates to a controlled perturbation of the design normal
matrix, with a constant one can evaluate from the energy bound alone.

## Literature and scope

Scope tag: **PURE-MATH**. Citation: —. Every result here is an exact-over-`ℝ` Lipschitz fact about
the design normal-matrix map; the ε-ball / IEEE reading in the *Interpretation* paragraph above is
motivation, not part of any statement (hence PURE-MATH, matching `docs/scope-tags.tsv`).

Two honest caveats on that interpretation, both stated so nothing is over-claimed:

* **IEEE-754 rounding is modelled abstractly, not derived.** Lean's `Float` carries no verified
  IEEE-754 semantics, so a literal `Float ↔ ℝ` rounding theorem is *not* formalizable and is
  **not** claimed here. We model the effect of finite-precision execution as a *bounded input
  perturbation* `ε` (`dist E Ê ≤ ε`) — an abstraction, not a theorem about `Float`. The result
  below is a statement over the exact reals `ℝ` only.
* **Bounded box, not global.** The `∑ Eₖ²` entry makes the map only *locally* Lipschitz; the
  constant `(2·B + 1)·n` is finite only on the box `|Eₖ| ≤ B`. We prove `LipschitzOnWith` on
  that box (`LipschitzOnWith`, not `LipschitzWith`), which is the honest global truth.

There is **no circularity**: the map `normalMap` and the two exact real inputs `E, Ê` it is
compared at are wholly independent of one another; the bound relates two genuine evaluations of
the same map, and the witnesses below exhibit a case where the output genuinely moves, so the
Lipschitz inequality is a real constraint, not a vacuous `0 ≤ 0`.

Builds on `CflibsFormal.OLS` (`designNormalMatrix`, OLS.lean:185; `det_designNormalMatrix`,
OLS.lean:194). The two-column least-squares design of the Boltzmann plot is standard:
G. Cristoforetti et al., *Spectrochim. Acta B* **65** (2010) 86 (calibration-free LIBS); the
Lipschitz/perturbation content is pure real analysis (no physics in the statement).
-/

namespace CflibsFormal

open Finset Real
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- The **energy box** of sup-radius `B`: all energy vectors with `|Eₖ| ≤ B` for every line `k`.
The bounded input region on which the forward map is Lipschitz. -/
def energyBox (B : ℝ) : Set (ι → ℝ) := {E | ∀ k, |E k| ≤ B}

/-- The **Boltzmann-plot forward/design map**, `E ↦ designNormalMatrix E`, presented as an
entrywise function `Fin 2 → Fin 2 → ℝ` so that both source and target carry the ambient
sup-metric of their `Pi` types (`Matrix (Fin 2) (Fin 2) ℝ` carries no `Dist` instance). The
four entries are `∑ Eₖ²`, `∑ Eₖ` (twice) and the constant `n = card ι`. -/
noncomputable def normalMap (E : ι → ℝ) : Fin 2 → Fin 2 → ℝ :=
  fun i j => designNormalMatrix E i j

@[simp] theorem normalMap_zero_zero (E : ι → ℝ) : normalMap E 0 0 = ∑ k, E k ^ 2 := by
  simp [normalMap, designNormalMatrix]

@[simp] theorem normalMap_zero_one (E : ι → ℝ) : normalMap E 0 1 = ∑ k, E k := by
  simp [normalMap, designNormalMatrix]

@[simp] theorem normalMap_one_zero (E : ι → ℝ) : normalMap E 1 0 = ∑ k, E k := by
  simp [normalMap, designNormalMatrix]

@[simp] theorem normalMap_one_one (E : ι → ℝ) : normalMap E 1 1 = (Fintype.card ι : ℝ) := by
  simp [normalMap, designNormalMatrix]

/-- **The explicit Lipschitz bound (real form).** On the energy box of radius `B`, the entrywise
design map is Lipschitz with the explicit constant `(2·B + 1)·n`, `n = card ι`:
`dist (normalMap E) (normalMap Ê) ≤ (2·B + 1)·n · dist E Ê`, both distances being the ambient
sup-metrics. The `∑ Eₖ²` entry contributes the `2·B` factor (each summand's slope is bounded by
`|Eₖ + Êₖ| ≤ 2·B`); the linear `∑ Eₖ` entries contribute the `+1`; the constant entry `n` is
Lipschitz-`0`. Summing `n` per-line contributions gives the overall factor `n`. -/
theorem normalMap_dist_le {B : ℝ} (hB : 0 ≤ B) {E Ehat : ι → ℝ}
    (hE : ∀ k, |E k| ≤ B) (hEhat : ∀ k, |Ehat k| ≤ B) :
    dist (normalMap E) (normalMap Ehat)
      ≤ (2 * B + 1) * (Fintype.card ι : ℝ) * dist E Ehat := by
  set d : ℝ := dist E Ehat with hd
  have hd0 : (0 : ℝ) ≤ d := dist_nonneg
  have hn0 : (0 : ℝ) ≤ (Fintype.card ι : ℝ) := by positivity
  have hr0 : (0 : ℝ) ≤ (2 * B + 1) * (Fintype.card ι : ℝ) * d := by positivity
  -- per-line perturbation bound from the sup-metric
  have hpt : ∀ k, |E k - Ehat k| ≤ d := by
    intro k
    have h := dist_le_pi_dist E Ehat k
    rwa [Real.dist_eq] at h
  -- the linear entry `∑ Eₖ`
  have hlin : |(∑ k, E k) - ∑ k, Ehat k| ≤ (Fintype.card ι : ℝ) * d := by
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum (fun k _ => hpt k)).trans ?_
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  -- the quadratic entry `∑ Eₖ²`
  have hquad : |(∑ k, E k ^ 2) - ∑ k, Ehat k ^ 2| ≤ 2 * B * (Fintype.card ι : ℝ) * d := by
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ k, |E k ^ 2 - Ehat k ^ 2| ≤ 2 * B * d := by
      intro k
      have hfac : E k ^ 2 - Ehat k ^ 2 = (E k - Ehat k) * (E k + Ehat k) := by ring
      rw [hfac, abs_mul]
      have hsum : |E k + Ehat k| ≤ 2 * B := by
        calc |E k + Ehat k| ≤ |E k| + |Ehat k| := abs_add_le _ _
          _ ≤ B + B := add_le_add (hE k) (hEhat k)
          _ = 2 * B := by ring
      calc |E k - Ehat k| * |E k + Ehat k|
          ≤ d * (2 * B) :=
            mul_le_mul (hpt k) hsum (abs_nonneg _) hd0
        _ = 2 * B * d := by ring
    refine (Finset.sum_le_sum (fun k _ => hterm k)).trans ?_
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring_nf
    rfl
  -- assemble: sup over the four entries
  rw [dist_pi_le_iff hr0, Fin.forall_fin_two]
  refine ⟨?_, ?_⟩ <;>
    · rw [dist_pi_le_iff hr0, Fin.forall_fin_two]
      refine ⟨?_, ?_⟩ <;> rw [Real.dist_eq] <;> simp only [normalMap_zero_zero,
        normalMap_zero_one, normalMap_one_zero, normalMap_one_one]
      all_goals first
        | (exact le_trans hquad (by nlinarith [hd0, hn0, hB]))
        | (exact le_trans hlin (by nlinarith [hd0, hn0, hB]))
        | (simp only [sub_self, abs_zero]; exact hr0)

/-- **The Lipschitz bound, packaged.** `normalMap` is `LipschitzOnWith` with the explicit
constant `L(B, n) = (2·B + 1)·n` on the energy box `energyBox B`. This is `LipschitzOnWith`
(local, on the box) rather than the global `LipschitzWith`, matching the honest scope: the
`∑ Eₖ²` entry has no finite global Lipschitz constant. -/
theorem normalMap_lipschitzOnWith {B : ℝ} (hB : 0 ≤ B) :
    LipschitzOnWith (Real.toNNReal ((2 * B + 1) * (Fintype.card ι : ℝ)))
      (normalMap (ι := ι)) (energyBox B) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro E hE Ehat hEhat
  rw [Real.coe_toNNReal _ (by positivity)]
  exact normalMap_dist_le hB hE hEhat

/-- **The ε-ball enclosure (the verification link).** If the exact real energies are perturbed
by at most `ε` in the sup-metric (the abstract rounding model — see the scope block), the design
normal matrix stays inside the `L·ε` ball of the exact result, `L = (2·B + 1)·n`. Immediate from
`normalMap_dist_le` by monotonicity. -/
theorem normalMap_epsilon_ball {B ε : ℝ} (hB : 0 ≤ B) {E Ehat : ι → ℝ}
    (hE : ∀ k, |E k| ≤ B) (hEhat : ∀ k, |Ehat k| ≤ B) (hε : dist E Ehat ≤ ε) :
    dist (normalMap E) (normalMap Ehat) ≤ (2 * B + 1) * (Fintype.card ι : ℝ) * ε := by
  refine (normalMap_dist_le hB hE hEhat).trans ?_
  have hn0 : (0 : ℝ) ≤ (Fintype.card ι : ℝ) := by positivity
  have hL0 : (0 : ℝ) ≤ (2 * B + 1) * (Fintype.card ι : ℝ) := by positivity
  exact mul_le_mul_of_nonneg_left hε hL0

/-! ### Non-vacuity witnesses (explicit data)

The map genuinely computes and is *non-constant*, so the Lipschitz inequality above constrains a
distance that can be strictly positive — it is not a vacuous `0 ≤ 0`. -/

/-- The forward map computes: on two lines with energies `1, 1` the `(0,0)` entry is `∑ Eₖ² = 2`.
-/
example : normalMap (ι := Fin 2) ![1, 1] 0 0 = 2 := by
  simp [Fin.sum_univ_two]; norm_num

/-- The `(1,1)` entry is the line count `n = 2`, independent of the energies. -/
example : normalMap (ι := Fin 2) ![1, 1] 1 1 = 2 := by simp

/-- **Non-constancy witness.** The energy vectors `![1,1]` and `![0,0]` (both in `energyBox 1`)
map to *different* normal matrices — their `(0,0)` entries are `2` and `0` — so the output of the
forward map genuinely moves. Hence the Lipschitz bound is a real constraint on a positive
distance, not a vacuous one. -/
example : normalMap (ι := Fin 2) ![1, 1] ≠ normalMap (ι := Fin 2) ![0, 0] := by
  intro h
  have h00 := congrFun (congrFun h 0) 0
  rw [normalMap_zero_zero, normalMap_zero_zero] at h00
  simp [Fin.sum_univ_two] at h00

/-- The Lipschitz theorem instantiates on genuine data: `![1,1]` and `![0,0]` both lie in the
box `energyBox 1`, so `normalMap_dist_le` yields a concrete finite bound with `L = 3·2 = 6`. -/
example :
    dist (normalMap (ι := Fin 2) ![1, 1]) (normalMap (ι := Fin 2) ![0, 0])
      ≤ (2 * (1 : ℝ) + 1) * (Fintype.card (Fin 2) : ℝ) * dist (![1, 1] : Fin 2 → ℝ) ![0, 0] :=
  normalMap_dist_le (by norm_num)
    (fun k => by fin_cases k <;> norm_num) (fun k => by fin_cases k <;> norm_num)

end CflibsFormal
