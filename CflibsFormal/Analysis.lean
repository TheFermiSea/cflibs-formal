/-
Copyright (c) 2026 Brian Squires. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Squires
-/
import Mathlib

/-!
# Shared analysis scaffolding

Small, function-agnostic real-analysis helpers reused across the proofs. The
physics-specific content stays in the originating modules; only generic facts live here:

* `strictAntiOn_div_of_deriv_num_neg` — quotient strictly antitone from a negative
  derivative numerator (curve-of-growth / escape-factor monotonicity scaffold).
* `exp_sub_le_mul` / `abs_exp_sub_le` — the one-sided and two-point exponential slope
  bounds (`exp a − exp b ≤ exp a·(a−b)`, `|exp a − exp b| ≤ max(exp a, exp b)·|a−b|`),
  the kernel of every temperature-sensitivity bound.
* `abs_exp_sub_one_le` — the exponential perturbation bound `|x| ≤ η ⇒ |exp x − 1| ≤ exp η − 1`
  (log-domain error ⇒ relative error).
* `inv_kT_sub_le` — the inverse-temperature gap bound
  `|1/(k_B T₁) − 1/(k_B T₂)| ≤ |T₁ − T₂|/(k_B·Tmin²)` on a temperature floor.

Formerly, isolated per-module `private` copies of the exponential and inverse-temperature
lemmas lived in `Identifiability`, `PartitionLipschitz`, `SahaStability`, `ErrorBudget`, and
`AtomicDataPerturbation`; this module is their single public home.
-/

namespace CflibsFormal

open Set

/-- **Quotient strictly antitone from a negative derivative numerator.** On `(0, ∞)`, if `g > 0`
and `f`, `g` are differentiable with `f'·g − f·g' < 0`, then `x ↦ f x / g x` is strictly antitone.
The shared scaffold behind the curve-of-growth / escape-factor monotonicity proofs
(`strictAntiOn_of_deriv_neg` + the quotient rule). -/
theorem strictAntiOn_div_of_deriv_num_neg {f g f' g' : ℝ → ℝ}
    (hg : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < g x)
    (hf : ∀ x ∈ Set.Ioi (0 : ℝ), HasDerivAt f (f' x) x)
    (hg' : ∀ x ∈ Set.Ioi (0 : ℝ), HasDerivAt g (g' x) x)
    (hnum : ∀ x ∈ Set.Ioi (0 : ℝ), f' x * g x - f x * g' x < 0) :
    StrictAntiOn (fun x => f x / g x) (Set.Ioi 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioi 0)
  · intro x hx
    exact (((hf x hx).continuousAt.continuousWithinAt).div
      ((hg' x hx).continuousAt.continuousWithinAt) (hg x hx).ne')
  · intro x hx
    rw [interior_Ioi] at hx
    have hd : HasDerivAt (fun x => f x / g x)
        ((f' x * g x - f x * g' x) / g x ^ 2) x :=
      (hf x hx).div (hg' x hx) (hg x hx).ne'
    rw [hd.deriv]
    exact div_neg_of_neg_of_pos (hnum x hx) (pow_pos (hg x hx) 2)

/-! ### Exponential Lipschitz-below bound (temperature metric stability) -/

/-- One-directional exponential mean-value bound: for `y ≤ x`,
    `exp y * (x - y) ≤ exp x - exp y`.  Follows from `x - y + 1 ≤ exp (x - y)`.
    (The hypothesis `_h` is unused: the bound in fact holds for all reals.) -/
private lemma exp_sub_ge {x y : ℝ} (_h : y ≤ x) :
    Real.exp y * (x - y) ≤ Real.exp x - Real.exp y := by
  have hpos := Real.exp_pos y
  have key : (x - y) + 1 ≤ Real.exp (x - y) := Real.add_one_le_exp (x - y)
  have step : Real.exp y * (x - y) ≤ Real.exp y * (Real.exp (x - y) - 1) :=
    mul_le_mul_of_nonneg_left (by linarith) hpos.le
  have harg : y + (x - y) = x := by ring
  have eqn : Real.exp y * (Real.exp (x - y) - 1) = Real.exp x - Real.exp y := by
    rw [mul_sub, mul_one, ← Real.exp_add, harg]
  linarith [step, eqn]

/-- General exponential Lipschitz-below bound:
    `exp (min x y) * |x - y| ≤ |exp x - exp y|` for all reals. -/
private lemma exp_diff_lower (x y : ℝ) :
    Real.exp (min x y) * |x - y| ≤ |Real.exp x - Real.exp y| := by
  rcases le_total y x with h | h
  · -- `y ≤ x`, so `min x y = y`
    rw [min_eq_right h]
    have hd : |x - y| = x - y := abs_of_nonneg (by linarith)
    have hsub : Real.exp y * (x - y) ≤ Real.exp x - Real.exp y := exp_sub_ge h
    have hge : 0 ≤ Real.exp x - Real.exp y := by
      nlinarith [hsub, mul_nonneg (Real.exp_pos y).le (show (0:ℝ) ≤ x - y by linarith)]
    rw [hd, abs_of_nonneg hge]; exact hsub
  · -- `x ≤ y`, so `min x y = x`
    rw [min_eq_left h]
    have hd : |x - y| = y - x := by rw [abs_of_nonpos (by linarith)]; ring
    have hsub : Real.exp x * (y - x) ≤ Real.exp y - Real.exp x := exp_sub_ge h
    have hle : Real.exp x - Real.exp y ≤ 0 := by
      nlinarith [hsub, mul_nonneg (Real.exp_pos x).le (show (0:ℝ) ≤ y - x by linarith)]
    rw [hd, abs_of_nonpos hle]; linarith [hsub]

/-- On a temperature box `[Tmin,Tmax]` (`0 < Tmin`), the map `T ↦ exp (D / T)` is
    Lipschitz-below in `T`, with explicit positive constant
    `exp (-(|D| / Tmin)) * (|D| / Tmax ^ 2)`. -/
lemma temp_exp_diff_lower {D Tmin Tmax T T0 : ℝ}
    (hTmin : 0 < Tmin) (hT : Tmin ≤ T) (hTM : T ≤ Tmax)
    (hT0 : Tmin ≤ T0) (hT0M : T0 ≤ Tmax) :
    Real.exp (-(|D| / Tmin)) * (|D| / Tmax ^ 2) * |T - T0|
      ≤ |Real.exp (D / T) - Real.exp (D / T0)| := by
  have hTpos : 0 < T := lt_of_lt_of_le hTmin hT
  have hT0pos : 0 < T0 := lt_of_lt_of_le hTmin hT0
  have hTmaxpos : 0 < Tmax := lt_of_lt_of_le hTpos hTM
  -- Step 2: lower bound the arguments, hence `min`.
  have hDT : -(|D| / Tmin) ≤ D / T :=
    neg_le_of_abs_le (by rw [abs_div, abs_of_pos hTpos]; gcongr)
  have hDT0 : -(|D| / Tmin) ≤ D / T0 :=
    neg_le_of_abs_le (by rw [abs_div, abs_of_pos hT0pos]; gcongr)
  have hmin : -(|D| / Tmin) ≤ min (D / T) (D / T0) := le_min hDT hDT0
  have ha : Real.exp (-(|D| / Tmin)) ≤ Real.exp (min (D / T) (D / T0)) :=
    Real.exp_le_exp.mpr hmin
  -- Step 3: lower bound the argument gap.
  have hTT0 : T * T0 ≤ Tmax ^ 2 := by
    rw [sq]; exact mul_le_mul hTM hT0M hT0pos.le (le_trans hT0pos.le hT0M)
  have heq : |D / T - D / T0| = |D| * |T - T0| / (T * T0) := by
    have hb1 : D / T - D / T0 = D * (T0 - T) / (T * T0) := by
      rw [div_sub_div D D (ne_of_gt hTpos) (ne_of_gt hT0pos)]; ring
    rw [hb1, abs_div, abs_mul, abs_of_pos (mul_pos hTpos hT0pos), abs_sub_comm T0 T]
  have hb : |D| / Tmax ^ 2 * |T - T0| ≤ |D / T - D / T0| := by
    rw [heq, div_mul_eq_mul_div]
    gcongr
  -- Combine the two factors, then chain with the general bound.
  have hA2 : (0:ℝ) ≤ |D| / Tmax ^ 2 * |T - T0| := by positivity
  have hcomb :
      Real.exp (-(|D| / Tmin)) * (|D| / Tmax ^ 2 * |T - T0|)
        ≤ Real.exp (min (D / T) (D / T0)) * |D / T - D / T0| :=
    mul_le_mul ha hb hA2 (Real.exp_pos _).le
  calc Real.exp (-(|D| / Tmin)) * (|D| / Tmax ^ 2) * |T - T0|
      = Real.exp (-(|D| / Tmin)) * (|D| / Tmax ^ 2 * |T - T0|) := by ring
    _ ≤ Real.exp (min (D / T) (D / T0)) * |D / T - D / T0| := hcomb
    _ ≤ |Real.exp (D / T) - Real.exp (D / T0)| := exp_diff_lower (D / T) (D / T0)
/-- **Elementary exponential slope bound.** For all reals `a, b`,
`exp a − exp b ≤ exp a · (a − b)` (from `Real.add_one_le_exp (b − a)`). No ordering
hypothesis is needed. Pure real analysis. -/
theorem exp_sub_le_mul (a b : ℝ) :
    Real.exp a - Real.exp b ≤ Real.exp a * (a - b) := by
  have hstep : b - a + 1 ≤ Real.exp (b - a) := Real.add_one_le_exp (b - a)
  have hle : Real.exp a * (1 - Real.exp (b - a)) ≤ Real.exp a * (a - b) :=
    mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos a).le
  have hrw : Real.exp a * (1 - Real.exp (b - a)) = Real.exp a - Real.exp b := by
    have hab : a + (b - a) = b := by ring
    rw [mul_sub, mul_one, ← Real.exp_add, hab]
  rwa [hrw] at hle

/-- **Two-point Lipschitz-type bound for `exp`.** `|exp a − exp b| ≤ max(exp a, exp b)·|a − b|`:
the slope is controlled by the larger endpoint value. Symmetrising `exp_sub_le_mul` over
`le_total b a`. The kernel of every temperature-sensitivity bound in the spec. -/
theorem abs_exp_sub_le (a b : ℝ) :
    |Real.exp a - Real.exp b| ≤ max (Real.exp a) (Real.exp b) * |a - b| := by
  rcases le_total b a with h | h
  · rw [max_eq_left (Real.exp_le_exp.mpr h),
      abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr h)),
      abs_of_nonneg (sub_nonneg.mpr h)]
    exact exp_sub_le_mul a b
  · rw [max_eq_right (Real.exp_le_exp.mpr h),
      abs_sub_comm (Real.exp a) (Real.exp b), abs_sub_comm a b,
      abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr h)),
      abs_of_nonneg (sub_nonneg.mpr h)]
    exact exp_sub_le_mul b a

/-- **Exponential perturbation bound.** `|exp x − 1| ≤ exp η − 1` whenever `|x| ≤ η`. The
kernel of "log-domain error ⇒ relative error": a bounded additive error on a log-quantity (an
intercept, a temperature) maps to a bounded relative error. Exact (no linearization); the
leading term is `η`, since `exp η − 1 → η` as `η → 0`. -/
theorem abs_exp_sub_one_le {x eta : ℝ} (hx : |x| ≤ eta) :
    |Real.exp x - 1| ≤ Real.exp eta - 1 := by
  have h := abs_le.mp hx
  have hup : Real.exp x ≤ Real.exp eta := Real.exp_le_exp.mpr h.2
  have hlo : Real.exp (-eta) ≤ Real.exp x := Real.exp_le_exp.mpr h.1
  have hsum : (2 : ℝ) ≤ Real.exp eta + Real.exp (-eta) := by
    have a := Real.add_one_le_exp eta
    have b := Real.add_one_le_exp (-eta)
    linarith
  rw [abs_le]
  exact ⟨by nlinarith [hlo, hsum], by linarith [hup]⟩

/-- **Inverse-temperature gap bound.** On a floor `Tmin ≤ T₁, T₂` (`0 < Tmin`, `0 < k_B`),
`|1/(k_B T₁) − 1/(k_B T₂)| ≤ |T₁ − T₂|/(k_B·Tmin²)`, since the difference equals
`(T₂ − T₁)/(k_B T₁ T₂)` and `T₁ T₂ ≥ Tmin²`. Pure real algebra; the bridge from a
temperature error to an inverse-temperature (Boltzmann-exponent) error. -/
theorem inv_kT_sub_le {kB Tmin T1 T2 : ℝ}
    (hkB : 0 < kB) (hTmin : 0 < Tmin) (hT1 : Tmin ≤ T1) (hT2 : Tmin ≤ T2) :
    |1 / (kB * T1) - 1 / (kB * T2)| ≤ |T1 - T2| / (kB * Tmin ^ 2) := by
  have hT1pos : 0 < T1 := lt_of_lt_of_le hTmin hT1
  have hT2pos : 0 < T2 := lt_of_lt_of_le hTmin hT2
  have hbig : 0 < kB * T1 * T2 := mul_pos (mul_pos hkB hT1pos) hT2pos
  have hsmall : 0 < kB * Tmin ^ 2 := mul_pos hkB (pow_pos hTmin 2)
  have heq : 1 / (kB * T1) - 1 / (kB * T2) = (T2 - T1) / (kB * T1 * T2) := by
    field_simp
  rw [heq, abs_div, abs_of_pos hbig, abs_sub_comm T2 T1, div_le_div_iff₀ hbig hsmall]
  have hTsq : Tmin ^ 2 ≤ T1 * T2 := by
    rw [sq]; exact mul_le_mul hT1 hT2 hTmin.le hT1pos.le
  have hden : kB * Tmin ^ 2 ≤ kB * T1 * T2 := by
    calc kB * Tmin ^ 2 ≤ kB * (T1 * T2) := mul_le_mul_of_nonneg_left hTsq hkB.le
      _ = kB * T1 * T2 := by ring
  exact mul_le_mul_of_nonneg_left hden (abs_nonneg _)

/-! ### Log-ratio transfer bound (Frontier 05 shared infrastructure) -/
/-! ## M1 — log-ratio transfer lemma (PURE-MATH; destined for `Analysis.lean`) -/

/-- **Log-ratio transfer bound.** If `a'` is a relative perturbation of `a` bounded by `δ < 1`
(`|a' - a| ≤ δ * a`), then the log-ratio `log (a / a')` is bounded by `δ / (1 - δ)`. This is the
two-sided sharpening of `Real.log_le_sub_one_of_pos`: the upper side `log r ≤ r - 1 ≤ δ/(1-δ)`
comes from `r = a/a' ≤ 1/(1-δ)` directly (so `r - 1 ≤ 1/(1-δ) - 1 = δ/(1-δ)`; `δ < 1` keeps the
denominator positive); the lower side `-log r = log r⁻¹ ≤ r⁻¹ - 1` needs `r⁻¹ = a'/a ≤ 1 + δ`,
giving the tighter `r⁻¹ - 1 ≤ δ`, which is widened to the stated `δ/(1-δ)` via `δ ≤ δ/(1-δ)` — so
the single constant `δ/(1-δ)` (the WORSE of the two sides, attained on the upper side) bounds
`|log r|` on both sides. Pure real analysis; no physics content. -/
theorem abs_log_ratio_le {a a' δ : ℝ} (ha : 0 < a) (ha' : 0 < a')
    (hδ1 : δ < 1) (hpert : |a' - a| ≤ δ * a) :
    |Real.log (a / a')| ≤ δ / (1 - δ) := by
  have hδ0 : 0 ≤ δ := by
    have := abs_nonneg (a' - a)
    nlinarith [this, hpert, ha]
  have h1δ : 0 < 1 - δ := by linarith
  have hbound := abs_le.mp hpert
  -- a' ≤ a + δ a = a(1+δ), and a - δ a ≤ a' i.e. a(1-δ) ≤ a'
  have hub : a' ≤ a * (1 + δ) := by nlinarith [hbound.2]
  have hlb : a * (1 - δ) ≤ a' := by nlinarith [hbound.1]
  have hr : 0 < a / a' := div_pos ha ha'
  have hrinv : 0 < a' / a := div_pos ha' ha
  -- Upper bound on log (a/a')
  have hupper : Real.log (a / a') ≤ δ / (1 - δ) := by
    have hle1 : a / a' ≤ 1 / (1 - δ) := by
      rw [div_le_div_iff₀ ha' h1δ]
      nlinarith [hlb]
    have hstep : Real.log (a / a') ≤ a / a' - 1 := Real.log_le_sub_one_of_pos hr
    have hstep2 : a / a' - 1 ≤ 1 / (1 - δ) - 1 := by linarith [hle1]
    have heq : (1 : ℝ) / (1 - δ) - 1 = δ / (1 - δ) := by
      rw [eq_div_iff h1δ.ne']; field_simp; ring
    linarith [hstep, hstep2, heq.le, heq.ge]
  -- Lower bound: -log(a/a') = log(a'/a) ≤ a'/a - 1 ≤ δ ≤ δ/(1-δ)
  have hlower : -(δ / (1 - δ)) ≤ Real.log (a / a') := by
    have hloginv : Real.log (a' / a) ≤ a' / a - 1 := Real.log_le_sub_one_of_pos hrinv
    have hle2 : a' / a ≤ 1 + δ := by
      rw [div_le_iff₀ ha]
      linarith [hub]
    have hstep2 : a' / a - 1 ≤ δ := by linarith [hle2]
    have hδled : δ ≤ δ / (1 - δ) := by
      rw [le_div_iff₀ h1δ]
      nlinarith [hδ0]
    have hlogeq : Real.log (a' / a) = -Real.log (a / a') := by
      rw [← Real.log_inv]; congr 1; field_simp
    linarith [hloginv, hstep2, hδled, hlogeq]
  rw [abs_le]
  exact ⟨hlower, hupper⟩

/-- **Non-vacuity witness for `abs_log_ratio_le`.** `a = 1`, `a' = 1.2`, `δ = 0.25`: genuinely
`0 < 0.25 < 1`, `|1.2 - 1| = 0.2 ≤ 0.25 * 1`, and the bound `δ/(1-δ) = 1/3 ≈ 0.333` is a
non-trivial (non-zero, finite) constant, confirming the hypotheses are jointly satisfiable and
the conclusion is not vacuous. -/
example : |Real.log ((1 : ℝ) / 1.2)| ≤ (0.25 : ℝ) / (1 - 0.25) :=
  abs_log_ratio_le (a := 1) (a' := 1.2) (δ := 0.25)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-! ## M0 — `olsIntercept_stable_hetero` (PURE-MATH; destined for `ErrorBudget.lean`) -/

/-! ### Symmetric 2×2 quadratic-form / coercivity bounds (relocated from OLSConditioning) -/

section Sym2x2

open Matrix Finset Real
open scoped BigOperators

/-- **Quadratic form of a symmetric `2×2` matrix.** For `M = ![![a, b], ![b, d]]` and
`v : Fin 2 → ℝ`, the Rayleigh numerator `v ⬝ᵥ (M *ᵥ v)` expands to
`a·v₀² + 2b·v₀v₁ + d·v₁²`. Pure `dotProduct`/`mulVec` bookkeeping for `Fin 2`. -/
theorem sym2x2_quadForm (a b d : ℝ) (v : Fin 2 → ℝ) :
    v ⬝ᵥ (!![a, b; b, d] *ᵥ v) = a * v 0 ^ 2 + 2 * b * (v 0 * v 1) + d * v 1 ^ 2 := by
  simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_two, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
    Matrix.of_apply]
  ring

/-- **THE coercivity bound (lower Rayleigh bound = `λ_min ≥ Δ/t`).** For a symmetric
`M = ![![a, b], ![b, d]]` with `a, d > 0`, `Δ := a·d − b² ≥ 0`, `t := a + d > 0`:

  `(Δ/t) · (v₀² + v₁²) ≤ v ⬝ᵥ (M *ᵥ v)`   for all `v : Fin 2 → ℝ`.

Proof by completing the square: `t·(v ⬝ᵥ M v) − Δ·(v₀²+v₁²) = (a·v₀+b·v₁)² + (b·v₀+d·v₁)²`,
a sum of squares, so after dividing by `t > 0` the coercivity constant `Δ/t` bounds the
Rayleigh quotient below. No spectral theory. (`_hΔ` documents the coercivity regime in which
`Δ/t ≥ 0`; the inequality itself follows from `t > 0` alone.) -/
theorem sym2x2_coercive (a b d : ℝ) (ha : 0 < a) (hd : 0 < d)
    (_hΔ : 0 ≤ a * d - b ^ 2) (v : Fin 2 → ℝ) :
    (a * d - b ^ 2) / (a + d) * (v 0 ^ 2 + v 1 ^ 2) ≤ v ⬝ᵥ (!![a, b; b, d] *ᵥ v) := by
  have ht : 0 < a + d := by linarith
  rw [sym2x2_quadForm, div_mul_eq_mul_div, div_le_iff₀ ht]
  nlinarith [sq_nonneg (a * v 0 + b * v 1), sq_nonneg (b * v 0 + d * v 1)]

/-- **The upper Rayleigh bound (`λ_max ≤ t = trace M`).** For a symmetric
`M = ![![a, b], ![b, d]]` with `a, d > 0` and `Δ := a·d − b² ≥ 0`:

  `v ⬝ᵥ (M *ᵥ v) ≤ t · (v₀² + v₁²)`   with `t = a + d`.

Proof: `a·(t·(v₀²+v₁²) − v ⬝ᵥ M v) = (a·v₁ − b·v₀)² + Δ·v₀² ≥ 0`, so after dividing by
`a > 0` the trace `t` bounds the Rayleigh quotient above. Together with `sym2x2_coercive`
this brackets every eigenvalue in `[Δ/t, t]`. (`_hd` completes the symmetric `a, d > 0`
setting; the proof divides by `a > 0`.) -/
theorem sym2x2_upper (a b d : ℝ) (ha : 0 < a) (_hd : 0 < d)
    (hΔ : 0 ≤ a * d - b ^ 2) (v : Fin 2 → ℝ) :
    v ⬝ᵥ (!![a, b; b, d] *ᵥ v) ≤ (a + d) * (v 0 ^ 2 + v 1 ^ 2) := by
  rw [sym2x2_quadForm]
  nlinarith [sq_nonneg (a * v 1 - b * v 0), mul_nonneg hΔ (sq_nonneg (v 0)), ha]

/-- **The condition-number bound `κ ≤ t²/Δ`** (cross-multiplied to avoid division). For a
symmetric `M = ![![a, b], ![b, d]]` with `a, d > 0` and `Δ := a·d − b² > 0`, for *all* pairs
of vectors `v, w`:

  `Δ · (v ⬝ᵥ M v) · (w₀² + w₁²) ≤ t² · (w ⬝ᵥ M w) · (v₀² + v₁²)`   with `t = a + d`.

Reading `R(v) := (v ⬝ᵥ M v)/(v₀²+v₁²)` as the Rayleigh quotient, this says `R(v)/R(w) ≤ t²/Δ`
for all nonzero `v, w`: the spread of the Rayleigh quotient — hence the condition number
`κ = λ_max/λ_min` — is bounded by `t²/Δ`. Chains the upper bound `R(v) ≤ t` (`sym2x2_upper`)
with the lower bound `Δ·‖w‖² ≤ t·(w ⬝ᵥ M w)` (`sym2x2_coercive`). -/
theorem sym2x2_condition (a b d : ℝ) (ha : 0 < a) (hd : 0 < d)
    (hΔ : 0 < a * d - b ^ 2) (v w : Fin 2 → ℝ) :
    (a * d - b ^ 2) * (v ⬝ᵥ (!![a, b; b, d] *ᵥ v)) * (w 0 ^ 2 + w 1 ^ 2)
      ≤ (a + d) ^ 2 * (w ⬝ᵥ (!![a, b; b, d] *ᵥ w)) * (v 0 ^ 2 + v 1 ^ 2) := by
  have ht : 0 < a + d := by linarith
  have hnv : (0 : ℝ) ≤ v 0 ^ 2 + v 1 ^ 2 := by positivity
  set Qv := v ⬝ᵥ (!![a, b; b, d] *ᵥ v) with hQvdef
  set Qw := w ⬝ᵥ (!![a, b; b, d] *ᵥ w) with hQwdef
  -- upper bound on `Qv`
  have hup_v : Qv ≤ (a + d) * (v 0 ^ 2 + v 1 ^ 2) := by
    rw [hQvdef]; exact sym2x2_upper a b d ha hd hΔ.le v
  -- lower bound on `Qw`, cleared of the denominator: `Δ·‖w‖² ≤ t·Qw`
  have hlo_w : (a * d - b ^ 2) * (w 0 ^ 2 + w 1 ^ 2) ≤ (a + d) * Qw := by
    have hc := sym2x2_coercive a b d ha hd hΔ.le w
    rw [← hQwdef, div_mul_eq_mul_div, div_le_iff₀ ht] at hc
    linarith [hc]
  have sA := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hup_v hΔ.le)
    (by positivity : (0 : ℝ) ≤ w 0 ^ 2 + w 1 ^ 2)
  have sB := mul_le_mul_of_nonneg_left hlo_w (mul_nonneg ht.le hnv)
  nlinarith [sA, sB]

end Sym2x2

/-! ### Monotone fixed-point comparative statics (relocated from MatrixIonizationCoupling) -/

/-- **Strict comparative statics of an antitone fixed point** (`PURE-MATH`).  If `f` is
antitone on `[0, ∞)`, `x` is a fixed point of `f` and `y` a fixed point of `g` (both
nonnegative), and `f` lies strictly below `g` at `y`, then `x < y`.  Proof: were `y ≤ x`,
antitonicity gives `f x ≤ f y`, so `x = f x ≤ f y < g y = y ≤ x`, a contradiction. -/
theorem coupledFixedPoint_lt_of_map_lt {f g : ℝ → ℝ}
    (hf : AntitoneOn f (Set.Ici 0)) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hfx : x = f x) (hgy : y = g y) (hlt : f y < g y) : x < y := by
  by_contra hc
  rw [not_lt] at hc
  have hmono : f x ≤ f y := hf (Set.mem_Ici.mpr hy) (Set.mem_Ici.mpr hx) hc
  rw [← hfx] at hmono
  rw [← hgy] at hlt
  linarith

/-- **Weak comparative statics of an antitone fixed point** (`PURE-MATH`).  Same hypotheses
as `coupledFixedPoint_lt_of_map_lt` but with a non-strict domination `f y ≤ g y`, yielding
`x ≤ y`.  The one-directional bound: pointwise domination of the closure map moves the fixed
point in the matching direction. -/
theorem coupledFixedPoint_le_of_map_le {f g : ℝ → ℝ}
    (hf : AntitoneOn f (Set.Ici 0)) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hfx : x = f x) (hgy : y = g y) (hle : f y ≤ g y) : x ≤ y := by
  by_contra hc
  rw [not_le] at hc
  have hmono : f x ≤ f y := hf (Set.mem_Ici.mpr hy) (Set.mem_Ici.mpr hx) hc.le
  rw [← hfx] at hmono
  rw [← hgy] at hle
  linarith

end CflibsFormal

