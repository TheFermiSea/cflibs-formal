/-
Copyright (c) 2026 Brian Squires. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Squires
-/
import Mathlib
import CflibsFormal.Analysis
import CflibsFormal.SelfAbsorption
import CflibsFormal.ForwardMap
import CflibsFormal.Boltzmann

/-!
# Saha–Boltzmann formalization — the curve of growth and multi-line self-absorption

When the optical depth (equivalently the lower-level **column density**) of a line is
unknown, a *single* self-absorbed line does not determine the column density: the
emergent intensity `I = S · (1 - exp(-τ))` couples the unknown source/plateau scale `S`
and the unknown opacity into one observable, the genuine `(N, τ)` aliasing recorded in
`SelfAbsorptionInverse.selfAbsorption_breaks_identifiability`.

This module formalizes the **curve of growth** as the bridge that *breaks* that
degeneracy. With the line optical depth written `τ = w · n` — a per-line opacity
coefficient `w` (proportional to oscillator strength) times the shared lower-level column
density `n` — the emergent self-absorbed line intensity is

  `cogIntensity S w n = S · (1 - exp(-(w · n)))`.

We prove two complementary identifiability facts.

* **Single line, known scale.** `cogIntensity_strictMono` / `cogIntensity_injective`:
  for `S > 0`, `w > 0` the map `n ↦ cogIntensity S w n` is strictly increasing, hence
  injective. So with a *known* opacity `w` and source `S`, one self-absorbed line already
  pins the column density `n`. This **sharpens**
  `selfAbsorption_breaks_identifiability`: the degeneracy is specifically about the
  *unknown* opacity/source scale, not optical thickness per se.

* **Two lines, unknown scale.** `cogRatio_strictAntiOn` / `cogRatio_injOn`: for two lines
  of the *same* species sharing the column density `n` but with *distinct* known opacities
  `w₁ > w₂ > 0`, the intensity **ratio**

    `cogRatio w₁ w₂ n = (1 - exp(-(w₁ · n))) / (1 - exp(-(w₂ · n)))`

  has the common (possibly unknown) source `S` cancelled (`cogRatio_eq_intensity_ratio`),
  and is strictly *antitone* — hence injective — in `n` on `(0, ∞)`. So the column density
  `n` (and thus the relative composition) is recovered from the line ratio **even when the
  common source scale `S` is unknown**: multiple lines of distinct opacity break the
  single-line self-absorption degeneracy. This is the positive counterpart to
  `selfAbsorption_breaks_identifiability`.

`cogIntensity_slab_eq` records that `cogIntensity` is exactly the audited radiative-transfer
slab kernel `slabIntensity` of `SelfAbsorption.lean` under `τ = w · n`, so no new physical
kernel is introduced and the optically-thin limit recovers `ForwardMap`.

## Literature

The curve-of-growth diagnostic and its use to correct/exploit self-absorption in
calibration-free LIBS are formalized here following:
Gornushkin, Stevenson, Smith, Omenetto, Winefordner, "Curve of growth methodology applied
to laser-induced plasma emission", *Spectrochimica Acta Part B* **54** (1999) 491 — which
establishes the curve-of-growth relation `I = S·(1 - exp(-τ))` for laser-induced plasma
line emission (the `cogIntensity` definition here);
Bulajic, Corsi, Cristoforetti, Legnaioli, Palleschi, Salvetti, Tognoni, "A procedure for
correcting self-absorption in calibration-free LIBS", *Spectrochimica Acta Part B* **57**
(2002) 339 — the self-absorption correction procedure for CF-LIBS that uses the curve of
growth to recover the optically-thin intensity; and
Cristoforetti and Tognoni, "Calculation of elemental columnar density from self-absorbed
lines", *Spectrochimica Acta Part B* **79–80** (2013) 63 — the column-density method that
inverts self-absorbed lines (`τ = w·n` with `n` the columnar density) directly, the inverse
formalized by the injectivity/identifiability theorems below. The `cogRatio`-based
cancellation of the common source scale is a generic algebraic helper and carries no
citation.
-/

namespace CflibsFormal

open Finset Real
open scoped BigOperators

/-- **Curve-of-growth (self-absorbed) line intensity.** With the line optical depth
written as `τ = w · n` — a per-line opacity coefficient `w` (proportional to oscillator
strength) times the lower-level **column density** `n` — the emergent self-absorbed line
intensity is `I = S · (1 - exp(-(w · n)))`, with `S` the source/plateau term. This is the
curve-of-growth relation of Gornushkin et al. (1999); it equals the audited slab kernel
`slabIntensity S (w·n)` of `SelfAbsorption.lean` (see `cogIntensity_slab_eq`). -/
noncomputable def cogIntensity (S w n : ℝ) : ℝ :=
  S * (1 - Real.exp (-(w * n)))

/-- **Source-free curve-of-growth ratio.** The ratio of two same-species self-absorbed
lines sharing the column density `n` with distinct opacities `w₁, w₂`. The common source
scale `S` cancels (see `cogRatio_eq_intensity_ratio`), so this is the observable that
remains available when `S` is unknown. -/
noncomputable def cogRatio (w₁ w₂ n : ℝ) : ℝ :=
  (1 - Real.exp (-(w₁ * n))) / (1 - Real.exp (-(w₂ * n)))

/-- **The curve-of-growth intensity is the radiative-transfer slab kernel.** `cogIntensity`
is exactly `slabIntensity` (from `SelfAbsorption.lean`) under `τ = w · n`; no new physical
kernel is introduced, so `cogIntensity` inherits the audited slab facts. -/
@[simp] theorem cogIntensity_slab_eq (S w n : ℝ) :
    cogIntensity S w n = slabIntensity S (w * n) := rfl

/-- **Single-line monotonicity in column density.** For `S > 0`, `w > 0` the emergent
self-absorbed intensity `n ↦ cogIntensity S w n` is strictly increasing on all of `ℝ`
(a fortiori on `[0, ∞)`): more column density means a brighter — never dimmer — line. The
proof routes through strict antitonicity of `exp` in `-(w · n)`. -/
theorem cogIntensity_strictMono {S w : ℝ} (hS : 0 < S) (hw : 0 < w) :
    StrictMono (fun n => cogIntensity S w n) := by
  intro n₁ n₂ h
  have hwn : w * n₁ < w * n₂ := mul_lt_mul_of_pos_left h hw
  have hexp : Real.exp (-(w * n₂)) < Real.exp (-(w * n₁)) :=
    Real.exp_lt_exp.mpr (by linarith)
  have hsub : 1 - Real.exp (-(w * n₁)) < 1 - Real.exp (-(w * n₂)) := by linarith
  unfold cogIntensity
  exact mul_lt_mul_of_pos_left hsub hS

/-- **Single-line injectivity (column-density recovery).** With known source `S > 0` and
opacity `w > 0`, equal self-absorbed intensities force equal column densities: a single
self-absorbed line determines `n`. This is the single-line inverse of
Cristoforetti–Tognoni (2013). -/
theorem cogIntensity_injective {S w : ℝ} (hS : 0 < S) (hw : 0 < w) :
    Function.Injective (fun n => cogIntensity S w n) :=
  (cogIntensity_strictMono hS hw).injective

/-- **The common source scale cancels in the ratio.** For `S ≠ 0`,
`cogIntensity S w₁ n / cogIntensity S w₂ n = cogRatio w₁ w₂ n`: the unknown source/plateau
term `S` divides out, so `cogRatio` is observable without knowing `S`. This is the
load-bearing cancellation behind the unknown-scale multi-line identifiability below. -/
theorem cogRatio_eq_intensity_ratio {S w₁ w₂ n : ℝ} (hS : S ≠ 0) :
    cogIntensity S w₁ n / cogIntensity S w₂ n = cogRatio w₁ w₂ n := by
  unfold cogIntensity cogRatio
  rw [mul_div_mul_left _ _ hS]

/-- Positivity of the curve-of-growth denominator on `(0, ∞)`: for `w > 0`, `n > 0` we
have `0 < 1 - exp(-(w·n))` (since `w·n > 0` makes `exp(-(w·n)) < 1`). Reused for the
ratio's continuity and the `HasDerivAt.div` side condition. -/
theorem cog_denom_pos {w n : ℝ} (hw : 0 < w) (hn : 0 < n) :
    0 < 1 - Real.exp (-(w * n)) := by
  have hwn : 0 < w * n := mul_pos hw hn
  have : Real.exp (-(w * n)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  linarith

/-- Key transcendental inequality: `exp x · (1 - x) < 1` for `x > 0`. Proof: `1 - x <
exp(-x)` (`Real.one_sub_lt_exp_neg`), multiply by `exp x > 0`, and `exp x · exp(-x) = 1`. -/
theorem exp_mul_one_sub_lt_one {x : ℝ} (hx : 0 < x) :
    Real.exp x * (1 - x) < 1 := by
  have h1 : 1 - x < Real.exp (-x) := Real.one_sub_lt_exp_neg hx.ne'
  have h2 : Real.exp x * (1 - x) < Real.exp x * Real.exp (-x) :=
    mul_lt_mul_of_pos_left h1 (Real.exp_pos x)
  rwa [← Real.exp_add, add_neg_cancel, Real.exp_zero] at h2

/-- The per-line *slope function* `φ(x) = x / (exp x - 1)` is strictly antitone on
`(0, ∞)`. This is the analytic core of the curve-of-growth ratio monotonicity: the larger
opacity (larger `x = w·n`) has the smaller normalized slope. Proved by
`strictAntiOn_of_deriv_neg`; the derivative numerator `exp x · (1 - x) - 1` is negative by
`exp_mul_one_sub_lt_one`. -/
theorem cogSlope_strictAntiOn :
    StrictAntiOn (fun x => x / (Real.exp x - 1)) (Set.Ioi 0) := by
  apply strictAntiOn_div_of_deriv_num_neg
    (f := fun x => x) (g := fun x => Real.exp x - 1)
    (f' := fun _ => 1) (g' := fun x => Real.exp x)
  · intro x hx
    have : (1 : ℝ) < Real.exp x := Real.one_lt_exp_iff.mpr (Set.mem_Ioi.mp hx)
    linarith
  · intro x _
    exact hasDerivAt_id x
  · intro x _
    simpa using (Real.hasDerivAt_exp x).sub_const 1
  · intro x hx
    have hkey : Real.exp x * (1 - x) < 1 := exp_mul_one_sub_lt_one (Set.mem_Ioi.mp hx)
    nlinarith [hkey]

/-- The curve-of-growth ratio derivative numerator is negative on `(0, ∞)` for
`w₁ > w₂ > 0`: `w₁ · exp(-(w₁·n)) · (1 - exp(-(w₂·n))) < (1 - exp(-(w₁·n))) · w₂ ·
exp(-(w₂·n))`. Reduces to `φ(w₁·n) < φ(w₂·n)` (slope strictly antitone), the analytic
heart of the unknown-source multi-line identifiability. -/
theorem cogRatio_deriv_num_neg {w₁ w₂ : ℝ} (hw : w₂ < w₁) (hw₂ : 0 < w₂) {n : ℝ}
    (hn : 0 < n) :
    w₁ * Real.exp (-(w₁ * n)) * (1 - Real.exp (-(w₂ * n)))
      < (1 - Real.exp (-(w₁ * n))) * (w₂ * Real.exp (-(w₂ * n))) := by
  have hw₁ : 0 < w₁ := lt_trans hw₂ hw
  have ha : 0 < w₁ * n := mul_pos hw₁ hn
  have hb : 0 < w₂ * n := mul_pos hw₂ hn
  have hab : w₂ * n < w₁ * n := mul_lt_mul_of_pos_right hw hn
  -- slope inequality: φ(w₁ n) < φ(w₂ n)
  have hslope := cogSlope_strictAntiOn (Set.mem_Ioi.mpr hb) (Set.mem_Ioi.mpr ha) hab
  simp only at hslope
  -- φ(x) = x/(exp x - 1); denominators positive
  have hea : (1 : ℝ) < Real.exp (w₁ * n) := Real.one_lt_exp_iff.mpr ha
  have heb : (1 : ℝ) < Real.exp (w₂ * n) := Real.one_lt_exp_iff.mpr hb
  have hda : 0 < Real.exp (w₁ * n) - 1 := by linarith
  have hdb : 0 < Real.exp (w₂ * n) - 1 := by linarith
  -- clear denominators: w₁ n (exp(w₂ n) - 1) < w₂ n (exp(w₁ n) - 1)
  rw [div_lt_div_iff₀ hda hdb] at hslope
  -- multiply out: w₁ n (exp(w₂ n) - 1) < w₂ n (exp(w₁ n) - 1)
  have hkey : w₁ * (Real.exp (w₂ * n) - 1) < w₂ * (Real.exp (w₁ * n) - 1) := by
    have hn' : 0 < n := hn
    nlinarith [hslope, hn']
  -- rewrite 1 - exp(-x) = exp(-x) * (exp x - 1)
  have ra : 1 - Real.exp (-(w₁ * n)) = Real.exp (-(w₁ * n)) * (Real.exp (w₁ * n) - 1) := by
    rw [mul_sub, mul_one, ← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have rb : 1 - Real.exp (-(w₂ * n)) = Real.exp (-(w₂ * n)) * (Real.exp (w₂ * n) - 1) := by
    rw [mul_sub, mul_one, ← Real.exp_add, neg_add_cancel, Real.exp_zero]
  rw [ra, rb]
  have hexpa : 0 < Real.exp (-(w₁ * n)) := Real.exp_pos _
  have hexpb : 0 < Real.exp (-(w₂ * n)) := Real.exp_pos _
  -- both sides share factor exp(-(w₁ n)) * exp(-(w₂ n)); reduce to hkey
  have hfac : 0 < Real.exp (-(w₁ * n)) * Real.exp (-(w₂ * n)) := mul_pos hexpa hexpb
  nlinarith [mul_lt_mul_of_pos_left hkey hfac, hexpa, hexpb]

/-- **Multi-line, unknown-scale identifiability (monotonicity).** For two same-species
lines with distinct known opacities `w₁ > w₂ > 0` sharing the column density `n`, the
source-free ratio `n ↦ cogRatio w₁ w₂ n` is strictly *antitone* on `(0, ∞)` (its thin/thick
limit values `w₁/w₂` as `n → 0⁺` and `1` as `n → ∞` are descriptive curve-of-growth context,
not proved by this theorem). Strict monotonicity
(either direction) gives injectivity, so the column density is recovered from the ratio
even with the common source scale `S` unknown — the curve-of-growth break of the
single-line self-absorption degeneracy (Bulajic et al. 2002; Cristoforetti–Tognoni 2013). -/
theorem cogRatio_strictAntiOn {w₁ w₂ : ℝ} (hw : w₂ < w₁) (hw₂ : 0 < w₂) :
    StrictAntiOn (fun n => cogRatio w₁ w₂ n) (Set.Ioi 0) := by
  have hw₁ : 0 < w₁ := lt_trans hw₂ hw
  -- HasDerivAt of `n ↦ 1 - exp(-(w·n))` (numerator/denominator share this shape)
  have hderiv : ∀ w : ℝ, ∀ n : ℝ, HasDerivAt (fun n => 1 - Real.exp (-(w * n)))
      (w * Real.exp (-(w * n))) n := by
    intro w n
    have h0 : HasDerivAt (fun n : ℝ => -(w * n)) (-w) n := by
      have hm : HasDerivAt (fun n : ℝ => -(w * n)) (-(w * 1)) n :=
        ((hasDerivAt_id n).const_mul w).fun_neg
      simpa using hm
    have h1 : HasDerivAt (fun n => Real.exp (-(w * n)))
        (Real.exp (-(w * n)) * -w) n := h0.exp
    have h2 := (h1.const_sub 1)
    have heq : w * Real.exp (-(w * n)) = -(Real.exp (-(w * n)) * -w) := by ring
    rw [heq]
    exact h2
  unfold cogRatio
  apply strictAntiOn_div_of_deriv_num_neg
    (f := fun n => 1 - Real.exp (-(w₁ * n))) (g := fun n => 1 - Real.exp (-(w₂ * n)))
    (f' := fun n => w₁ * Real.exp (-(w₁ * n))) (g' := fun n => w₂ * Real.exp (-(w₂ * n)))
  · intro n hn
    exact cog_denom_pos hw₂ (Set.mem_Ioi.mp hn)
  · intro n _
    exact hderiv w₁ n
  · intro n _
    exact hderiv w₂ n
  · intro n hn
    have := cogRatio_deriv_num_neg hw hw₂ (Set.mem_Ioi.mp hn)
    nlinarith [this]

/-- **Multi-line, unknown-scale identifiability (injectivity).** The source-free ratio is
injective on `(0, ∞)`: distinct positive column densities give distinct ratios, so `n`
(hence the relative composition) is recovered from the ratio observable alone, without
knowing the common source scale `S`. This is the genuine two-line break of the
self-absorption degeneracy — the positive counterpart to
`selfAbsorption_breaks_identifiability`. -/
theorem cogRatio_injOn {w₁ w₂ : ℝ} (hw : w₂ < w₁) (hw₂ : 0 < w₂) :
    Set.InjOn (fun n => cogRatio w₁ w₂ n) (Set.Ioi 0) :=
  (cogRatio_strictAntiOn hw hw₂).injOn

end CflibsFormal

