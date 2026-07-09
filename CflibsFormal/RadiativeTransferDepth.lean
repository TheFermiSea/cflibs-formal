/-
Copyright (c) 2026 Brian Squires. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Squires
-/
import Mathlib
import CflibsFormal.SelfAbsorption
import CflibsFormal.SelfReversal

/-!
# CF-LIBS formalization — depth-structured radiative transfer (the N-zone stack)

The repo has exactly two radiative-transfer kernels, both hard-coded special cases of the
depth-integrated formal solution `I(τ) = ∫₀^τ S(t)·e^{−(τ−t)} dt`:

* `slabIntensity S τ = S·(1 − e^{−τ})` (`SelfAbsorption.lean`) — one homogeneous LTE layer;
* `emergentIntensity Score Sshell τc τs` (`SelfReversal.lean`) — the Cowan–Dieke two-layer
  core+shell model.

This module folds an **arbitrary** stack of `N` homogeneous zones and proves the two hand-coded
kernels are its `N = 1` and `N = 2` base cases, then bounds the emergent intensity of *any*
depth-structured LTE column between the uniform slabs at its coldest and hottest source values.

Order the zones **deepest-first**: zone `0` is farthest from the observer, the last list element
is at the surface. Photons entering a zone are attenuated by `e^{−τ}` and the zone adds its own
emission `S·(1 − e^{−τ})`:

`rtStep I (S,τ) = I·e^{−τ} + S·(1 − e^{−τ})`,   `rtEmergent zs = zs.foldl rtStep 0`.

* `rtEmergent_single` — **exact** `N = 1` identity: `rtEmergent [(S,τ)] = slabIntensity S τ`.
* `rtEmergent_two` — **exact** `N = 2` identity to `emergentIntensity` verbatim (the
  convention-pinning guard: `[core, shell]`, core first). The two kernels are base cases of one
  recursive object.
* `rtEmergent_sandwich` — **the headline**: if every zone source lies in `[Smin, Smax]` and every
  `τₖ ≥ 0`, then `Smin·(1 − e^{−T}) ≤ rtEmergent zs ≤ Smax·(1 − e^{−T})` with `T = Σ τₖ` the total
  optical depth. Depth structure can only move `I` *within* the band the two uniform slabs bracket;
  it cannot brighten past `Smax·(1 − e^{−T})` nor darken below `Smin·(1 − e^{−T})`. The rigorous
  confinement of the spatial-non-uniformity temperature bias — derivative-free, a telescoping
  `(1 − e^{−T₀})·e^{−τ} + (1 − e^{−τ}) = 1 − e^{−(T₀+τ)}` induction.
* `rtEmergent_uniform` — **exact**: an isothermal stack (all sources equal `S`) collapses to a
  single slab of combined depth, `slabIntensity S T`. Generalizes `selfReversal_uniformSource` to
  `N` zones: depth structure carries no information iff the column is isothermal.

The continuous companion layer:

* `rtFormal` — the interval-integral formal solution `∫₀^τ S(t)·e^{−(τ−t)} dt`.
* `rtFormal_const` — **exact**: a constant source recovers `slabIntensity S₀ τ`.
* `rtFormal_sandwich` — the continuous companion of `rtEmergent_sandwich` via `integral_mono`.
* `rtFormalLinear` — the exact real-analysis evaluation of the linear (Eddington–Barbier) source
  `∫₀^τ (S₀ + S₁t)·e^{−(τ−t)} dt = S₀·(1 − e^{−τ}) + S₁·(τ − 1 + e^{−τ})`.

## Honest scope

`S` is an **abstract input** function of depth (LTE, `S = B_λ(T(t))` in physics); no Planck source,
no non-LTE scattering coupling `S = (1−ε)J + εB`, and `τ` is a **scalar per zone** — the emergent
line *profile* over a frequency-resolved Voigt/Stark `τ_λ(t)` needs the Faddeeva function absent
from mathlib (cf. `SelfReversal`'s and Frontier 07's deferrals) and is out of scope. The
`rtFormalLinear` linear-in-τ source is the **stellar-atmosphere** Eddington–Barbier idealization,
not a faithful LIBS profile: it is a PURE-MATH integral evaluation, never claimed EXACT-for-LIBS.

## Literature

I. B. Gornushkin et al., "Curve of growth methodology applied to laser-induced plasma emission
spectroscopy," *Spectrochim. Acta B* **54** (1999) 1207 — the homogeneous-slab radiative-transfer
kernel `S·(1 − e^{−τ})` these zones stack. R. D. Cowan, G. H. Dieke, "Self-Absorption of Spectrum
Lines," *Rev. Mod. Phys.* **20** (1948) 418 — the two-layer (non-isothermal) treatment the `N = 2`
base case and the `N`-zone sandwich generalize. The formal-solution integral form is standard
radiative transfer (Mihalas, *Stellar Atmospheres*; already cited in `EquivalentWidth.lean` as
prose background).
-/

namespace CflibsFormal

open MeasureTheory

/-- **One homogeneous zone.** Accumulated intensity `I` entering a zone of source `z.1` and optical
depth `z.2` is attenuated by `e^{−z.2}` and gains the zone's own emission `z.1·(1 − e^{−z.2})`:
`rtStep I (S,τ) = I·e^{−τ} + S·(1 − e^{−τ})`. -/
noncomputable def rtStep (I : ℝ) (z : ℝ × ℝ) : ℝ :=
  I * Real.exp (-z.2) + z.1 * (1 - Real.exp (-z.2))

/-- **`N`-zone stacked emergent intensity.** Fold `rtStep` over the zone stack ordered
**deepest-first** (zone `0` farthest from the observer, the last element at the surface), starting
from zero incident intensity. Subsumes both hard-coded kernels: `slabIntensity` (`N = 1`) and
`emergentIntensity` (`N = 2`). -/
noncomputable def rtEmergent (zs : List (ℝ × ℝ)) : ℝ := zs.foldl rtStep 0

/-- **Single-zone base case (exact).** For one zone the stack is the homogeneous-slab kernel:
`rtEmergent [(S,τ)] = slabIntensity S τ`. -/
theorem rtEmergent_single (S τ : ℝ) : rtEmergent [(S, τ)] = slabIntensity S τ := by
  simp [rtEmergent, rtStep, slabIntensity]

/-- **Two-zone base case (exact).** For a core (source `Score`, depth `τc`) then a shell (source
`Sshell`, depth `τs`) the stack is the Cowan–Dieke two-layer emergent intensity **verbatim**:
`rtEmergent [(Score,τc),(Sshell,τs)] = emergentIntensity Score Sshell τc τs`. This pins the
deepest-first convention (`[core, shell]`, core first). -/
theorem rtEmergent_two (Score Sshell τc τs : ℝ) :
    rtEmergent [(Score, τc), (Sshell, τs)] = emergentIntensity Score Sshell τc τs := by
  simp only [rtEmergent, List.foldl_cons, List.foldl_nil, rtStep, emergentIntensity]
  ring

/-- Single-zone upper step: if the accumulator is below the `Smax` slab of depth `T₀`, one more
zone (source `≤ Smax`, depth `≥ 0`) keeps it below the `Smax` slab of depth `T₀ + z.2`. The
telescoping identity `(1 − e^{−T₀})·e^{−τ} + (1 − e^{−τ}) = 1 − e^{−(T₀+τ)}`. -/
private theorem rtStep_le {Smax I₀ T₀ : ℝ} (z : ℝ × ℝ)
    (hI : I₀ ≤ Smax * (1 - Real.exp (-T₀))) (hS : z.1 ≤ Smax) (hτ : 0 ≤ z.2) :
    rtStep I₀ z ≤ Smax * (1 - Real.exp (-(T₀ + z.2))) := by
  unfold rtStep
  have he0 : (0 : ℝ) ≤ Real.exp (-z.2) := (Real.exp_pos _).le
  have he1 : (0 : ℝ) ≤ 1 - Real.exp (-z.2) := by
    have : Real.exp (-z.2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    linarith
  have h1 : I₀ * Real.exp (-z.2) ≤ Smax * (1 - Real.exp (-T₀)) * Real.exp (-z.2) :=
    mul_le_mul_of_nonneg_right hI he0
  have h2 : z.1 * (1 - Real.exp (-z.2)) ≤ Smax * (1 - Real.exp (-z.2)) :=
    mul_le_mul_of_nonneg_right hS he1
  have htel : Smax * (1 - Real.exp (-T₀)) * Real.exp (-z.2) + Smax * (1 - Real.exp (-z.2))
      = Smax * (1 - Real.exp (-(T₀ + z.2))) := by
    have hadd : Real.exp (-(T₀ + z.2)) = Real.exp (-T₀) * Real.exp (-z.2) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [hadd]; ring
  linarith [h1, h2, htel]

/-- Single-zone lower step (mirror of `rtStep_le`): needs no sign hypothesis on `Smin`, only the
nonnegativity of the weights `e^{−τ}` and `1 − e^{−τ}`. -/
private theorem rtStep_ge {Smin I₀ T₀ : ℝ} (z : ℝ × ℝ)
    (hI : Smin * (1 - Real.exp (-T₀)) ≤ I₀) (hS : Smin ≤ z.1) (hτ : 0 ≤ z.2) :
    Smin * (1 - Real.exp (-(T₀ + z.2))) ≤ rtStep I₀ z := by
  unfold rtStep
  have he0 : (0 : ℝ) ≤ Real.exp (-z.2) := (Real.exp_pos _).le
  have he1 : (0 : ℝ) ≤ 1 - Real.exp (-z.2) := by
    have : Real.exp (-z.2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    linarith
  have h1 : Smin * (1 - Real.exp (-T₀)) * Real.exp (-z.2) ≤ I₀ * Real.exp (-z.2) :=
    mul_le_mul_of_nonneg_right hI he0
  have h2 : Smin * (1 - Real.exp (-z.2)) ≤ z.1 * (1 - Real.exp (-z.2)) :=
    mul_le_mul_of_nonneg_right hS he1
  have htel : Smin * (1 - Real.exp (-T₀)) * Real.exp (-z.2) + Smin * (1 - Real.exp (-z.2))
      = Smin * (1 - Real.exp (-(T₀ + z.2))) := by
    have hadd : Real.exp (-(T₀ + z.2)) = Real.exp (-T₀) * Real.exp (-z.2) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [hadd]; ring
  linarith [h1, h2, htel]

/-- Generalized-accumulator upper invariant: fold from any accumulator below the `Smax` slab of any
depth `T₀` stays below the `Smax` slab of depth `T₀ + Σ τₖ`. -/
private theorem rtFold_le (Smax : ℝ) :
    ∀ (zs : List (ℝ × ℝ)) (I₀ T₀ : ℝ), I₀ ≤ Smax * (1 - Real.exp (-T₀)) →
      (∀ z ∈ zs, z.1 ≤ Smax ∧ 0 ≤ z.2) →
      zs.foldl rtStep I₀ ≤ Smax * (1 - Real.exp (-(T₀ + (zs.map Prod.snd).sum))) := by
  intro zs
  induction zs with
  | nil => intro I₀ T₀ hI _; simpa using hI
  | cons a rest ih =>
    intro I₀ T₀ hI hall
    rw [List.foldl_cons, List.map_cons, List.sum_cons]
    have ha := hall a (by simp)
    have hstep : rtStep I₀ a ≤ Smax * (1 - Real.exp (-(T₀ + a.2))) := rtStep_le a hI ha.1 ha.2
    have hrest : ∀ z ∈ rest, z.1 ≤ Smax ∧ 0 ≤ z.2 :=
      fun z hz => hall z (List.mem_cons_of_mem a hz)
    have hih := ih (rtStep I₀ a) (T₀ + a.2) hstep hrest
    rwa [add_assoc] at hih

/-- Generalized-accumulator lower invariant (mirror of `rtFold_le`). -/
private theorem rtFold_ge (Smin : ℝ) :
    ∀ (zs : List (ℝ × ℝ)) (I₀ T₀ : ℝ), Smin * (1 - Real.exp (-T₀)) ≤ I₀ →
      (∀ z ∈ zs, Smin ≤ z.1 ∧ 0 ≤ z.2) →
      Smin * (1 - Real.exp (-(T₀ + (zs.map Prod.snd).sum))) ≤ zs.foldl rtStep I₀ := by
  intro zs
  induction zs with
  | nil => intro I₀ T₀ hI _; simpa using hI
  | cons a rest ih =>
    intro I₀ T₀ hI hall
    rw [List.foldl_cons, List.map_cons, List.sum_cons]
    have ha := hall a (by simp)
    have hstep : Smin * (1 - Real.exp (-(T₀ + a.2))) ≤ rtStep I₀ a := rtStep_ge a hI ha.1 ha.2
    have hrest : ∀ z ∈ rest, Smin ≤ z.1 ∧ 0 ≤ z.2 :=
      fun z hz => hall z (List.mem_cons_of_mem a hz)
    have hih := ih (rtStep I₀ a) (T₀ + a.2) hstep hrest
    rwa [add_assoc] at hih

/-- **The monotone sandwich (exact).** If every zone source lies in `[Smin, Smax]` and every zone
optical depth is nonnegative, the emergent intensity of the depth-structured stack is bracketed by
the uniform slabs at the coldest and hottest source values, sharing the total-depth escape factor
`(1 − e^{−T})`, `T = Σ τₖ`:
`Smin·(1 − e^{−T}) ≤ rtEmergent zs ≤ Smax·(1 − e^{−T})`.
Depth structure can only move `I` *within* this band — it cannot brighten past `Smax·(1 − e^{−T})`
nor darken below `Smin·(1 − e^{−T})` — so the spatial-non-uniformity temperature bias is confined,
of size at most `(Smax − Smin)·(1 − e^{−T})`. -/
theorem rtEmergent_sandwich {zs : List (ℝ × ℝ)} {Smin Smax : ℝ}
    (hS : ∀ z ∈ zs, Smin ≤ z.1 ∧ z.1 ≤ Smax) (hτ : ∀ z ∈ zs, 0 ≤ z.2) :
    Smin * (1 - Real.exp (-(zs.map Prod.snd).sum)) ≤ rtEmergent zs
    ∧ rtEmergent zs ≤ Smax * (1 - Real.exp (-(zs.map Prod.snd).sum)) := by
  refine ⟨?_, ?_⟩
  · have h := rtFold_ge Smin zs 0 0 (by simp) (fun z hz => ⟨(hS z hz).1, hτ z hz⟩)
    simpa [rtEmergent] using h
  · have h := rtFold_le Smax zs 0 0 (by simp) (fun z hz => ⟨(hS z hz).2, hτ z hz⟩)
    simpa [rtEmergent] using h

/-- **Uniform slab is the extremal case (exact).** An isothermal stack (all zone sources equal `S`)
with nonnegative optical depths collapses to a single slab of the combined depth:
`rtEmergent zs = slabIntensity S (Σ τₖ)`. The degenerate zero-width case of the sandwich — depth
structure carries no information iff the column is isothermal. Generalizes
`selfReversal_uniformSource` to `N` zones. -/
theorem rtEmergent_uniform (S : ℝ) {zs : List (ℝ × ℝ)} (hS : ∀ z ∈ zs, z.1 = S)
    (hτ : ∀ z ∈ zs, 0 ≤ z.2) :
    rtEmergent zs = slabIntensity S (zs.map Prod.snd).sum := by
  have hb := rtEmergent_sandwich (Smin := S) (Smax := S)
    (fun z hz => ⟨le_of_eq (hS z hz).symm, le_of_eq (hS z hz)⟩) hτ
  unfold slabIntensity
  exact le_antisymm hb.2 hb.1

/-- Non-vacuity witness: the sandwich brackets a genuine two-zone gradient (`Smin = 1 < Smax = 3`,
`τ = {1,1}`, total depth `2`), the band `[1·(1−e^{−2}), 3·(1−e^{−2})]` being non-degenerate. -/
example :
    (1 : ℝ) * (1 - Real.exp (-(2 : ℝ))) ≤ rtEmergent [((1 : ℝ), (1 : ℝ)), (3, 1)]
    ∧ rtEmergent [((1 : ℝ), (1 : ℝ)), (3, 1)] ≤ 3 * (1 - Real.exp (-(2 : ℝ))) := by
  have h := rtEmergent_sandwich (zs := [((1 : ℝ), (1 : ℝ)), (3, 1)]) (Smin := 1) (Smax := 3)
    (by intro z hz; fin_cases hz <;> constructor <;> norm_num)
    (by intro z hz; fin_cases hz <;> norm_num)
  have hsum : ([((1 : ℝ), (1 : ℝ)), (3, 1)].map Prod.snd).sum = 2 := by
    norm_num [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  rw [hsum] at h
  exact h

/-- **The continuous formal solution.** The depth-integrated formal solution of radiative transfer
`I(τ) = ∫₀^τ S(t)·e^{−(τ−t)} dt` for an abstract depth-dependent source `S`. -/
noncomputable def rtFormal (S : ℝ → ℝ) (τ : ℝ) : ℝ := ∫ t in (0 : ℝ)..τ, S t * Real.exp (-(τ - t))

/-- **Constant source recovers the slab (exact).** A depth-independent source `S t = S₀` reduces the
formal solution to the homogeneous-slab kernel: `rtFormal (fun _ => S₀) τ = slabIntensity S₀ τ`. -/
theorem rtFormal_const (S₀ τ : ℝ) : rtFormal (fun _ => S₀) τ = slabIntensity S₀ τ := by
  unfold rtFormal slabIntensity
  have hcongr : (∫ t in (0 : ℝ)..τ, (fun _ => S₀) t * Real.exp (-(τ - t)))
      = ∫ t in (0 : ℝ)..τ, S₀ * Real.exp (-τ) * Real.exp t := by
    apply intervalIntegral.integral_congr
    intro t _
    change S₀ * Real.exp (-(τ - t)) = S₀ * Real.exp (-τ) * Real.exp t
    rw [mul_assoc, ← Real.exp_add, show -τ + t = -(τ - t) from by ring]
  rw [hcongr, intervalIntegral.integral_const_mul, integral_exp, Real.exp_zero]
  have hcancel : Real.exp (-τ) * Real.exp τ = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  linear_combination S₀ * hcancel

/-- **The continuous sandwich (exact).** For a continuous source globally bounded in `[Smin, Smax]`
and `0 ≤ τ`, the formal solution is bracketed by the uniform slabs at the bounds:
`Smin·(1 − e^{−τ}) ≤ rtFormal S τ ≤ Smax·(1 − e^{−τ})`. The continuous companion of
`rtEmergent_sandwich`, by `integral_mono` against the constant-source integrals (the integrand is
monotone in `S t` because `e^{−(τ−t)} ≥ 0`). -/
theorem rtFormal_sandwich {S : ℝ → ℝ} {Smin Smax τ : ℝ} (hτ : 0 ≤ τ) (hcont : Continuous S)
    (hlo : ∀ t, Smin ≤ S t) (hhi : ∀ t, S t ≤ Smax) :
    Smin * (1 - Real.exp (-τ)) ≤ rtFormal S τ ∧ rtFormal S τ ≤ Smax * (1 - Real.exp (-τ)) := by
  have hcexp : Continuous (fun t : ℝ => Real.exp (-(τ - t))) := by fun_prop
  have hint_min : IntervalIntegrable (fun t => Smin * Real.exp (-(τ - t))) volume 0 τ :=
    (hcexp.const_mul Smin).intervalIntegrable 0 τ
  have hint_mid : IntervalIntegrable (fun t => S t * Real.exp (-(τ - t))) volume 0 τ :=
    (hcont.mul hcexp).intervalIntegrable 0 τ
  have hint_max : IntervalIntegrable (fun t => Smax * Real.exp (-(τ - t))) volume 0 τ :=
    (hcexp.const_mul Smax).intervalIntegrable 0 τ
  refine ⟨?_, ?_⟩
  · change slabIntensity Smin τ ≤ rtFormal S τ
    rw [← rtFormal_const Smin τ]
    exact intervalIntegral.integral_mono hτ hint_min hint_mid
      (fun t => mul_le_mul_of_nonneg_right (hlo t) (Real.exp_pos _).le)
  · change rtFormal S τ ≤ slabIntensity Smax τ
    rw [← rtFormal_const Smax τ]
    exact intervalIntegral.integral_mono hτ hint_mid hint_max
      (fun t => mul_le_mul_of_nonneg_right (hhi t) (Real.exp_pos _).le)

/-- Non-vacuity: the continuous sandwich brackets a genuinely varying bounded source
`S t = 2 + sin t` in `[1, 3]` on a slab of depth `1` (a non-degenerate band). -/
example :
    (1 : ℝ) * (1 - Real.exp (-(1 : ℝ))) ≤ rtFormal (fun t => 2 + Real.sin t) 1
    ∧ rtFormal (fun t => 2 + Real.sin t) 1 ≤ 3 * (1 - Real.exp (-(1 : ℝ))) :=
  rtFormal_sandwich (by norm_num) (by fun_prop)
    (fun t => by have := Real.neg_one_le_sin t; linarith)
    (fun t => by have := Real.sin_le_one t; linarith)

/-- **Linear (Eddington–Barbier) source — exact evaluation.** For a source linear in optical depth,
`S t = S₀ + S₁·t`, the formal solution evaluates in closed form:
`∫₀^τ (S₀ + S₁t)·e^{−(τ−t)} dt = S₀·(1 − e^{−τ}) + S₁·(τ − 1 + e^{−τ})`.
This is the **stellar-atmosphere** Eddington–Barbier idealization (a PURE-MATH integral evaluation),
**not** a faithful LIBS source profile — see the honest-scope note. Antiderivative
`G(t) = (S₀ − S₁ + S₁t)·e^{t−τ}` via FTC-2. -/
theorem rtFormalLinear (S₀ S₁ τ : ℝ) :
    (∫ t in (0 : ℝ)..τ, (S₀ + S₁ * t) * Real.exp (-(τ - t)))
      = S₀ * (1 - Real.exp (-τ)) + S₁ * (τ - 1 + Real.exp (-τ)) := by
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) τ,
      HasDerivAt (fun t => (S₀ - S₁ + S₁ * t) * Real.exp (t - τ))
        ((S₀ + S₁ * t) * Real.exp (-(τ - t))) t := by
    intro t _
    have hlin : HasDerivAt (fun t : ℝ => S₀ - S₁ + S₁ * t) S₁ t :=
      (hasDerivAt_const_mul S₁).const_add (S₀ - S₁)
    have hsub : HasDerivAt (fun t : ℝ => t - τ) 1 t := by
      simpa using (hasDerivAt_id t).sub_const τ
    have hexp : HasDerivAt (fun t : ℝ => Real.exp (t - τ)) (Real.exp (t - τ)) t := by
      simpa using hsub.exp
    have hprod := hlin.mul hexp
    have heq : (S₀ + S₁ * t) * Real.exp (-(τ - t))
        = S₁ * Real.exp (t - τ) + (S₀ - S₁ + S₁ * t) * Real.exp (t - τ) := by
      rw [show -(τ - t) = t - τ from by ring]; ring
    rw [heq]
    exact hprod
  have hint : IntervalIntegrable (fun t => (S₀ + S₁ * t) * Real.exp (-(τ - t))) volume 0 τ := by
    have hc : Continuous (fun t : ℝ => (S₀ + S₁ * t) * Real.exp (-(τ - t))) := by fun_prop
    exact hc.intervalIntegrable 0 τ
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  rw [show τ - τ = (0 : ℝ) from by ring, Real.exp_zero, show (0 : ℝ) - τ = -τ from by ring]
  ring

/-- Non-vacuity: at `S₁ = 0` the linear evaluation collapses to the constant-source slab. -/
example (S₀ τ : ℝ) :
    (∫ t in (0 : ℝ)..τ, (S₀ + 0 * t) * Real.exp (-(τ - t))) = S₀ * (1 - Real.exp (-τ)) := by
  rw [rtFormalLinear]; ring

end CflibsFormal
