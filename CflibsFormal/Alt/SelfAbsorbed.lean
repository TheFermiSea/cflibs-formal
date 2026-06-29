/-
Copyright (c) 2026 Brian Squires. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Squires
-/
import Mathlib
import CflibsFormal.SelfAbsorption
import CflibsFormal.ForwardMap
import CflibsFormal.Classic
import CflibsFormal.Closure
import CflibsFormal.Inverse

/-!
# CF-LIBS formalization — the self-absorption-corrected composition estimator (alternative)

This module supplies the SECOND alternative CF-LIBS composition estimator
(namespace `CflibsFormal.Alt`), aimed at concentrated alloy / high-entropy-alloy lines
that are optically THICK. Where the classic and C-sigma estimators assume optically-thin
lines, this estimator consumes the optically-THICK measured intensities `Imeas : κ → ℝ`
together with the KNOWN per-species optical depths `tau : κ → ℝ`, applies the exact
curve-of-growth correction `I_thin = Imeas / SA(τ)` (the proven left-inverse
`SelfAbsorption.lineIntensity_eq_selfAbsorbedIntensity_div`), and then runs the classic
algebraic inversion `Classic.classicDensity` / `Closure.composition` verbatim.

We prove:

* `classicDensity_smul_intensity` — linearity of the algebraic inverse `Classic.classicDensity`
  in its intensity argument (the load-bearing scalar-commutation lemma).
* `selfAbsorbed_sound` — **soundness EVEN WHEN LINES ARE OPTICALLY THICK**: on genuine
  thick forward-model data (`Imeas t = selfAbsorbedIntensity … (tau t)` at true densities
  `N t`, `tau t ≥ 0`), `selfAbsorbedComposition` returns the TRUE composition `composition N`.
* `selfAbsorbed_corrects_bias` — the contrast / bias-direction value theorem: the NAIVE
  classic inversion (NO division by `SA`) on a genuinely-thick line (`τ > 0`) returns a
  density STRICTLY BELOW the true `N`, quantifying why the correction is necessary.
* `selfAbsorbed_eq_classic_corrected` — the honest **structural identity**: the corrected
  estimator IS `Classic.classicComposition` applied to the curve-of-growth-corrected
  intensities `Imeas / SA(τ)` (holds for any data, `classic ∘ correction`).
* `selfAbsorbed_eq_classic_thin` — **reduction to classic in the thin limit**: at `τ ≡ 0`
  (`SA = 1`) the estimator coincides with classic on the SAME observations, so it agrees
  with classic exactly where classic is valid and departs only by correcting thick-line
  bias.

Two index types appear: `κ` (species/stages, from `Closure.lean`) and `ι` (energy levels,
from `Boltzmann.lean` / `ForwardMap.lean`). The estimator is a pure function of the
observations `(Imeas, tau)` and NEVER takes the true density `N` (or composition) as input.
-/

namespace CflibsFormal.Alt

open CflibsFormal
open Finset Real
open scoped BigOperators

variable {ι : Type*} [Fintype ι]
variable {κ : Type*} [Fintype κ]

/-- **Self-absorption-corrected (curve-of-growth) composition estimator.** A PURE function
of the OBSERVATIONS (`Imeas : κ → ℝ`, the measured optically-THICK intensities, one chosen
line `u s` per species) and the KNOWN per-species optical depths `tau : κ → ℝ`. It NEVER
takes the true density `N` (or composition) as input. Per species it forms the exact
curve-of-growth correction `I_thin = Imeas t / SA(tau t)` (the proven left-inverse
`SelfAbsorption.lineIntensity_eq_selfAbsorbedIntensity_div`), reuses
`Classic.classicDensity` VERBATIM to read back the density from that corrected thin
intensity, and applies `Closure.composition` (divides by total recovered density). The
signature mirrors `Classic.classicComposition` / `Alt.csigmaComposition` with the added
`tau` argument, so it slots into the same observation interface. -/
noncomputable def selfAbsorbedComposition (kB T Fcal : ℝ) (g E A : κ → ι → ℝ)
    (u : κ → ι) (tau : κ → ℝ) (Imeas : κ → ℝ) (s : κ) : ℝ :=
  composition (fun t => Classic.classicDensity kB T Fcal (g t) (E t) (A t) (u t)
    (Imeas t / selfAbsorptionFactor (tau t))) s

/-- **Linearity of the algebraic inverse in the intensity.** `Classic.classicDensity` is
linear in its intensity argument: scaling the intensity by `c` scales the recovered density
by `c`. This is the load-bearing algebraic step making the curve-of-growth division
equivalent to a density rescale; it reuses `Classic.classicDensity` rather than reproving
any inversion. -/
theorem classicDensity_smul_intensity {kB T Fcal : ℝ} {g E A : ι → ℝ} (u : ι) (c I : ℝ) :
    Classic.classicDensity kB T Fcal g E A u (c * I)
      = c * Classic.classicDensity kB T Fcal g E A u I := by
  unfold Classic.classicDensity
  ring

/-- **Soundness even when lines are optically thick.** On genuine thick forward-model data
(`Imeas t = selfAbsorbedIntensity … (tau t)` at true densities `N t`, with `tau t ≥ 0`),
`selfAbsorbedComposition` returns the TRUE composition `composition N`. The estimator is a
function only of `(Imeas, tau)`, never of `N`, yet it recovers the true composition exactly
— the central physics content, false for the naive classic estimator on the same thick
data. Reuses `SelfAbsorption.lineIntensity_eq_selfAbsorbedIntensity_div` (the exact
correction) and `Classic.classicDensity_recovers` (the inversion) verbatim. -/
theorem selfAbsorbed_sound [Nonempty ι] [Nonempty κ] {kB T Fcal : ℝ}
    {N : κ → ℝ} {g E A : κ → ι → ℝ} {u : κ → ι} {tau : κ → ℝ}
    (hg : ∀ s k, 0 < g s k) (hFcal : 0 < Fcal) (hA : ∀ s, 0 < A s (u s))
    (htau : ∀ s, 0 ≤ tau s) (s : κ) :
    selfAbsorbedComposition kB T Fcal g E A u tau
        (fun t => selfAbsorbedIntensity kB T (N t) Fcal (g t) (E t) (A t) (u t) (tau t)) s
      = composition N s := by
  unfold selfAbsorbedComposition
  have hrec : (fun t => Classic.classicDensity kB T Fcal (g t) (E t) (A t) (u t)
      (selfAbsorbedIntensity kB T (N t) Fcal (g t) (E t) (A t) (u t) (tau t)
        / selfAbsorptionFactor (tau t))) = N := by
    funext t
    rw [← lineIntensity_eq_selfAbsorbedIntensity_div (u t) (htau t)]
    exact Classic.classicDensity_recovers (hg t) hFcal (u t) (hA t)
  rw [hrec]

/-- **Bias-direction value theorem for the NAIVE classic estimator.** Feeding the
optically-thick measured intensity `selfAbsorbedIntensity … tau` into the UNCORRECTED
`Classic.classicDensity` (i.e. WITHOUT dividing by `SA`) yields a recovered density STRICTLY
BELOW the true `N`: the uncorrected method underestimates density on thick lines (`τ > 0`).
This quantitatively justifies the correction performed by `selfAbsorbedComposition`,
contrasting with `selfAbsorbed_sound`'s exactness. -/
theorem selfAbsorbed_corrects_bias [Nonempty ι] {kB T N Fcal : ℝ} {g E A : ι → ℝ}
    (hg : ∀ k, 0 < g k) (hN : 0 < N) (hFcal : 0 < Fcal) (hA : ∀ k, 0 < A k)
    (u : ι) {tau : ℝ} (htau : 0 < tau) :
    Classic.classicDensity kB T Fcal g E A u
        (selfAbsorbedIntensity kB T N Fcal g E A u tau) < N := by
  unfold selfAbsorbedIntensity
  rw [mul_comm, classicDensity_smul_intensity,
    Classic.classicDensity_recovers hg hFcal u (hA u)]
  have hSA : selfAbsorptionFactor tau < 1 := by
    unfold selfAbsorptionFactor
    rw [if_neg htau.ne', div_lt_one htau]
    have := Real.one_sub_lt_exp_neg htau.ne'
    linarith
  exact mul_lt_of_lt_one_left hN hSA

/-- **Relationship to classic — structural identity.** The self-absorption-corrected
estimator IS the classic estimator applied to the curve-of-growth-corrected intensities:
for ANY observations `(Imeas, tau)`,
`selfAbsorbedComposition … tau Imeas = Classic.classicComposition …` fed
`fun t => Imeas t / SA(tau t)`. This holds for all data (no soundness assumed): the new
method is exactly `classic ∘ correction`, which is the honest characterization of how it
relates to the classic algorithm — not a deep peer-method agreement, but a precise
reduction. -/
theorem selfAbsorbed_eq_classic_corrected (kB T Fcal : ℝ) (g E A : κ → ι → ℝ) (u : κ → ι)
    (tau Imeas : κ → ℝ) (s : κ) :
    selfAbsorbedComposition kB T Fcal g E A u tau Imeas s
      = Classic.classicComposition kB T Fcal g E A u
          (fun t => Imeas t / selfAbsorptionFactor (tau t)) s :=
  rfl

/-- **Reduction to classic in the optically-thin limit.** When every line is optically thin
(`tau ≡ 0`, so `SA = 1` and the correction is the identity), the self-absorption-corrected
estimator coincides with the classic estimator on the SAME observations, for ANY `Imeas`:
`selfAbsorbedComposition … (fun _ => 0) Imeas = Classic.classicComposition … Imeas`. So the
new method genuinely agrees with classic exactly where classic is valid (no self-
absorption), and departs from it only by correcting the thick-line bias
(`selfAbsorbed_corrects_bias`). This is a same-observation identity that does not route
through soundness. -/
theorem selfAbsorbed_eq_classic_thin (kB T Fcal : ℝ) (g E A : κ → ι → ℝ) (u : κ → ι)
    (Imeas : κ → ℝ) (s : κ) :
    selfAbsorbedComposition kB T Fcal g E A u (fun _ => 0) Imeas s
      = Classic.classicComposition kB T Fcal g E A u Imeas s := by
  unfold selfAbsorbedComposition Classic.classicComposition
  have h0 : selfAbsorptionFactor (0 : ℝ) = 1 := if_pos rfl
  simp only [h0, div_one]

/-! ### Non-vacuity witness for `selfAbsorbed_sound`

Two species with DISTINCT densities `N = (1, 3)`, one line each, genuinely OPTICALLY-THICK
(`tau = 1 > 0`), with `kB = T = Fcal = g = A = 1`, `E = 0`: the self-absorption-corrected estimator,
run on the genuine thick forward-model spectrum (`Imeas = selfAbsorbedIntensity … (tau)`, not `N`),
recovers the non-trivial composition `C₀ = 1/4` — not the degenerate `= 1` — through the
curve-of-growth correction. So `selfAbsorbed_sound`'s hypotheses (including a strictly positive
optical depth) are jointly satisfiable and its conclusion is non-vacuous. -/

private def nvsaN : Fin 2 → ℝ := ![1, 3]
private def nvsag : Fin 2 → Fin 1 → ℝ := fun _ _ => 1
private def nvsaE : Fin 2 → Fin 1 → ℝ := fun _ _ => 0
private def nvsaA : Fin 2 → Fin 1 → ℝ := fun _ _ => 1
private def nvsau : Fin 2 → Fin 1 := fun _ => 0
private def nvsaTau : Fin 2 → ℝ := fun _ => 1

example :
    selfAbsorbedComposition 1 1 1 nvsag nvsaE nvsaA nvsau nvsaTau
        (fun t => selfAbsorbedIntensity 1 1 (nvsaN t) 1 (nvsag t) (nvsaE t) (nvsaA t)
          (nvsau t) (nvsaTau t)) 0
      = 1 / 4 := by
  have h := selfAbsorbed_sound (kB := 1) (T := 1) (Fcal := 1)
    (N := nvsaN) (g := nvsag) (E := nvsaE) (A := nvsaA) (u := nvsau) (tau := nvsaTau)
    (fun _ _ => one_pos) one_pos (fun _ => one_pos)
    (fun _ => zero_le_one) (0 : Fin 2)
  rw [h]
  norm_num [composition, totalDensity, nvsaN, Fin.sum_univ_two]

end CflibsFormal.Alt
