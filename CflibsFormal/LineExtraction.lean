/-
Copyright (c) 2026 Brian Squires. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Squires
-/
import Mathlib

/-!
# CF-LIBS formalization — a metamorphic specification of line extraction

The companion pipeline turns a detected peak into an integrated line intensity with a *line
extraction kernel* `extract_line(wavelength, intensity, peak_idx, half_width_px, wl_step) ->
(area, sigma) | None`. The incumbent kernel is the trapezoid rule over the window
`peak_idx ± half_width_px` of the (optionally baseline-subtracted) spectrum, with the shot-noise
sigma `√(∑ max(counts, 1)) · wl_step`. Nothing in the Lean spec said what such a kernel must
satisfy; the inverse-problem layer starts *after* the integrated intensities exist.

This module states the **metamorphic relations** an extraction kernel must satisfy, for the
incumbent trapezoid kernel, as machine-checked theorems. A metamorphic relation needs no ground
truth: it relates the kernel's outputs on two *related inputs*, so it can be run as a cheap,
truth-free gate on any candidate kernel before it is scored. Each theorem below has a numerical
fixture twin (`oracle/line_extraction/`) that the companion pins.

## The model

The window is `n + 1` nodes `x 0 ≤ … ≤ x n` carrying samples `y 0, …, y n`
(`trapArea x y n = ∑ᵢ₍₀..ₙ₋₁₎ (x(i+1) − x i)(y i + y(i+1))/2`, the trapezoid rule). `shotSigma`
is the incumbent sigma. A kernel is *specified by* these relations; the relations are proved for
the trapezoid rule and are the contract a replacement kernel is tested against.

* **(a) linearity in amplitude** (`trapArea_smul`, `trapArea_add`): scaling the line by `k`
  scales the area by `k`; areas add.
* **(b) pedestal** (`trapArea_line_pedestal`, `trapArea_sub_pedestal`):
  `area(k·line + c) = k·area(line) + c·W`; subtracting the pedestal restores the line area.
* **(c) sub-pixel shift** (`trapArea_shift_le`): a translated line changes the area by at most
  `W · L · |δ|`.
* **(d) separated blend** (`trapArea_blend_le`, `trapArea_blend_eq`): the other line contributes
  at most `W · ε`, and exactly `0` if it vanishes on the window.
* **(e) sigma** (`shotSigma_pos`, `shotSigma_mono`): sigma is positive and non-decreasing in
  the counts.
* **(f) antisymmetric noise** (`trapArea_antisymm_noise`): for any noise vector `n`,
  `area(y + n) + area(y − n) = 2·area(y)`; exact, needs no statistics, and is broken by any
  kernel that floors or clips samples.

(`W = x n − x 0` is the window width.) Positivity of the area for a non-negative line is
`trapArea_nonneg`, and the common perturbation lemma behind (c) and (d) is `trapArea_sub_le`.

## Honest limitations

* **Pure mathematics.** Every statement is about the finite sum `trapArea`; none says that the
  trapezoid area is the *physical* line intensity, that the peak window is well chosen, or that
  the profile is Gaussian/Voigt.
* **(b) is not an invariance for a raw integral.** A raw-intensity integral shifts by exactly
  `c·W` under an additive pedestal `c`, so the contract for such a kernel is "area of `line + c`
  minus area of `line` equals `c·W`" (`trapArea_line_pedestal`), and after subtracting an exact
  pedestal estimate, equality (`trapArea_sub_pedestal`). A *baseline-aware* kernel is a different
  contract (shift `0`); this module proves the raw-integral side only, and the fixtures accept
  either outcome and reject anything in between.
* **(b) for negative pedestals.** The theorem holds for every real `c`, negative included. After
  the pipeline's baseline subtraction, negative samples are measurement noise, not impossible
  counts, so a kernel that floors them at `0` biases weak-line areas upward; clipping is
  legitimate only on raw, non-negative counts. The fixtures therefore keep `c < 0` as a gated
  case, and relation (f) tests the same failure directly.
* **(c) is a Lipschitz bound, loose by design.** The true sub-pixel error of a smooth, sampled
  line is far smaller than `W·L·|δ|`; the bound is the tolerance a fixture may *rely on* without
  assuming any profile shape.
* **(d) `trapArea_blend_eq` is window-only.** Its hypothesis is that the other line vanishes at
  the window nodes; a kernel that also reads flanks (a flank or edge baseline) sees the neighbour
  there and so changes by construction. That is not a defect of the kernel, so the fixtures treat
  the vanishing-neighbour case as a descriptor, not a gate.
* **(d) is a contamination bound, not a separation criterion.** The theorem is stated for the
  other line's sampled magnitude `ε` on the window. Turning "separated by `k` FWHM" into an `ε`
  needs the *profile's tail* (Gaussian tails vanish super-exponentially, Lorentzian wings fall
  only as `1/(1+4k²)`), which is a physical input, not proved here.
* **(e) is the incumbent's sigma, not a proved 1σ.** `shotSigma` is the seed's definition. The
  theorems say it is positive and monotone in the counts; they do *not* say it equals the
  standard deviation of the trapezoid area (the trapezoid weights are not all `wl_step`).
* **The seed's fallback branch is outside the model.** When the trapezoid area is `≤ 0` the seed
  substitutes a Gaussian-equivalent area from the peak height and FWHM, and returns `None` if that
  is also `≤ 0`; the relations here apply to the main branch (positive trapezoid area).

## Literature

**Scope: PURE-MATH.** The trapezoid rule is textbook numerical quadrature (e.g. Davis & Rabinowitz,
*Methods of Numerical Integration*, 2nd ed., Academic Press, 1984); the relations are elementary
linearity and a sup-norm perturbation bound, and no spectroscopy source is relied on. The
shot-noise form `√N` is the Poisson standard deviation of a count `N`; it is the pipeline's
convention, not a result proved here.
-/

namespace CflibsFormal.LineExtraction

open Finset

/-- The trapezoid rule over the `n + 1` window nodes `x 0, …, x n` with samples `y 0, …, y n`:
`∑ᵢ₍₀..ₙ₋₁₎ (x(i+1) − x i)(y i + y(i+1))/2` (the incumbent extraction kernel's integral). -/
noncomputable def trapArea (x y : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ range n, (x (i + 1) - x i) * (y i + y (i + 1)) / 2

/-- The incumbent kernel's shot-noise sigma over the `n + 1` window samples:
`√(∑ max(yᵢ, 1)) · step` (the seed's `sqrt(sum(maximum(counts, 1))) * wl_step`). -/
noncomputable def shotSigma (y : ℕ → ℝ) (step : ℝ) (n : ℕ) : ℝ :=
  Real.sqrt (∑ i ∈ range (n + 1), max (y i) 1) * step

/-! ### (a) Linearity in amplitude -/

/-- Scaling the sampled line by `k` scales the trapezoid area by `k`. -/
theorem trapArea_smul (x y : ℕ → ℝ) (n : ℕ) (k : ℝ) :
    trapArea x (fun i => k * y i) n = k * trapArea x y n := by
  simp only [trapArea]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The trapezoid area of a sum of two sampled profiles is the sum of their areas. -/
theorem trapArea_add (x y z : ℕ → ℝ) (n : ℕ) :
    trapArea x (fun i => y i + z i) n = trapArea x y n + trapArea x z n := by
  simp only [trapArea]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **Antisymmetric noise cancels.** For any noise vector `nz`, the areas of `y + nz` and
`y − nz` sum to twice the area of `y`. Exact and statistics-free: a kernel that floors or clips
samples (so is not linear on its window) breaks it as soon as the noise drives a sample negative. -/
theorem trapArea_antisymm_noise (x y nz : ℕ → ℝ) (n : ℕ) :
    trapArea x (fun i => y i + nz i) n + trapArea x (fun i => y i - nz i) n
      = 2 * trapArea x y n := by
  simp only [trapArea]
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-! ### (b) Additive pedestal -/

/-- A constant pedestal `c` adds exactly `c · (x n − x 0)`: the area of the constant function
telescopes to the window width. -/
theorem trapArea_const (x : ℕ → ℝ) (n : ℕ) (c : ℝ) :
    trapArea x (fun _ => c) n = c * (x n - x 0) := by
  simp only [trapArea]
  have h : ∀ i ∈ range n, (x (i + 1) - x i) * (c + c) / 2 = c * (x (i + 1) - x i) :=
    fun i _ => by ring
  rw [Finset.sum_congr rfl h, ← Finset.mul_sum, Finset.sum_range_sub]

/-- A line of amplitude `k` on a constant pedestal `c`: `area(k·line + c) = k·area(line) + c·W`
with `W = x n − x 0` the window width. -/
theorem trapArea_line_pedestal (x y : ℕ → ℝ) (n : ℕ) (k c : ℝ) :
    trapArea x (fun i => k * y i + c) n = k * trapArea x y n + c * (x n - x 0) := by
  have h := trapArea_add x (fun i => k * y i) (fun _ => c) n
  rw [trapArea_smul, trapArea_const] at h
  exact h

/-- Subtracting an exact pedestal estimate restores the line area:
`area(line + c) − c·W = area(line)`. -/
theorem trapArea_sub_pedestal (x y : ℕ → ℝ) (n : ℕ) (c : ℝ) :
    trapArea x (fun i => y i + c) n - c * (x n - x 0) = trapArea x y n := by
  have h := trapArea_add x y (fun _ => c) n
  rw [trapArea_const] at h
  rw [h]
  ring

/-! ### The perturbation lemma behind (c) and (d) -/

/-- **Sup-norm perturbation of the trapezoid area.** On an increasing window, if two sampled
profiles differ by at most `ε` at every node, their areas differ by at most `W · ε`. -/
theorem trapArea_sub_le (x y z : ℕ → ℝ) (n : ℕ) (ε : ℝ)
    (hx : ∀ i < n, x i ≤ x (i + 1)) (hε : ∀ i ≤ n, |y i - z i| ≤ ε) :
    |trapArea x y n - trapArea x z n| ≤ (x n - x 0) * ε := by
  have hsub : trapArea x y n - trapArea x z n
      = ∑ i ∈ range n, (x (i + 1) - x i) * ((y i - z i) + (y (i + 1) - z (i + 1))) / 2 := by
    simp only [trapArea]
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hsub]
  calc |∑ i ∈ range n, (x (i + 1) - x i) * ((y i - z i) + (y (i + 1) - z (i + 1))) / 2|
      ≤ ∑ i ∈ range n,
          |(x (i + 1) - x i) * ((y i - z i) + (y (i + 1) - z (i + 1))) / 2| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ range n, (x (i + 1) - x i) * ε := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hi' : i < n := Finset.mem_range.mp hi
        have h0 : 0 ≤ x (i + 1) - x i := sub_nonneg.mpr (hx i hi')
        have h1 := hε i hi'.le
        have h2 := hε (i + 1) hi'
        have h3 : |(y i - z i) + (y (i + 1) - z (i + 1))| ≤ 2 * ε :=
          (abs_add_le _ _).trans (by linarith)
        rw [abs_div, abs_mul, abs_of_nonneg h0, abs_two]
        have h4 := mul_le_mul_of_nonneg_left h3 h0
        linarith
    _ = (x n - x 0) * ε := by
        rw [← Finset.sum_mul, Finset.sum_range_sub]

/-- A non-negative sampled line has non-negative trapezoid area on an increasing window. -/
theorem trapArea_nonneg (x y : ℕ → ℝ) (n : ℕ)
    (hx : ∀ i < n, x i ≤ x (i + 1)) (hy : ∀ i ≤ n, 0 ≤ y i) : 0 ≤ trapArea x y n := by
  refine Finset.sum_nonneg fun i hi => ?_
  have hi' : i < n := Finset.mem_range.mp hi
  have h0 : 0 ≤ x (i + 1) - x i := sub_nonneg.mpr (hx i hi')
  exact div_nonneg (mul_nonneg h0 (add_nonneg (hy i hi'.le) (hy (i + 1) hi'))) (by norm_num)

/-! ### (c) Sub-pixel shift -/

/-- **Sub-pixel shift tolerance.** Let the line profile `f` be `L`-Lipschitz. Sampling the
translated line `t ↦ f (t − δ)` instead of `f` on the same increasing window changes the
trapezoid area by at most `W · L · |δ|`. -/
theorem trapArea_shift_le (x : ℕ → ℝ) (n : ℕ) (f : ℝ → ℝ) (L δ : ℝ)
    (hL : ∀ s t, |f s - f t| ≤ L * |s - t|) (hx : ∀ i < n, x i ≤ x (i + 1)) :
    |trapArea x (fun i => f (x i)) n - trapArea x (fun i => f (x i - δ)) n|
      ≤ (x n - x 0) * (L * |δ|) := by
  refine trapArea_sub_le x _ _ n (L * |δ|) hx fun i _ => ?_
  have h := hL (x i) (x i - δ)
  simpa using h

/-! ### (d) Separated blend -/

/-- **Blend contamination bound.** If a second line `g` has magnitude at most `ε` at every node
of the window of line `f`, measuring the blend `f + g` instead of `f` changes the area by at most
`W · ε`. -/
theorem trapArea_blend_le (x f g : ℕ → ℝ) (n : ℕ) (ε : ℝ)
    (hx : ∀ i < n, x i ≤ x (i + 1)) (hg : ∀ i ≤ n, |g i| ≤ ε) :
    |trapArea x (fun i => f i + g i) n - trapArea x f n| ≤ (x n - x 0) * ε := by
  refine trapArea_sub_le x _ _ n ε hx fun i hi => ?_
  simpa using hg i hi

/-- **Separated blends add exactly.** If the second line vanishes at every node of the window of
line `f`, the blend and the lone line have the same area there. -/
theorem trapArea_blend_eq (x f g : ℕ → ℝ) (n : ℕ) (hg : ∀ i ≤ n, g i = 0) :
    trapArea x (fun i => f i + g i) n = trapArea x f n := by
  simp only [trapArea]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i < n := Finset.mem_range.mp hi
  rw [hg i hi'.le, hg (i + 1) hi']
  ring

/-! ### (e) Sigma -/

/-- The shot-noise sigma is strictly positive for a positive sampling step. -/
theorem shotSigma_pos (y : ℕ → ℝ) (n : ℕ) {step : ℝ} (hstep : 0 < step) :
    0 < shotSigma y step n := by
  unfold shotSigma
  refine mul_pos (Real.sqrt_pos.mpr ?_) hstep
  have h : ∑ _i ∈ range (n + 1), (1 : ℝ) ≤ ∑ i ∈ range (n + 1), max (y i) 1 :=
    Finset.sum_le_sum fun i _ => le_max_right _ _
  have h1 : (0 : ℝ) < ∑ _i ∈ range (n + 1), (1 : ℝ) := by
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    positivity
  exact lt_of_lt_of_le h1 h

/-- The shot-noise sigma is non-decreasing in the counts: more counts, no smaller sigma. -/
theorem shotSigma_mono (y y' : ℕ → ℝ) (n : ℕ) {step : ℝ} (hstep : 0 ≤ step)
    (hy : ∀ i ≤ n, y i ≤ y' i) : shotSigma y step n ≤ shotSigma y' step n := by
  unfold shotSigma
  refine mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt ?_) hstep
  refine Finset.sum_le_sum fun i hi => ?_
  exact max_le_max (hy i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))) le_rfl

end CflibsFormal.LineExtraction
