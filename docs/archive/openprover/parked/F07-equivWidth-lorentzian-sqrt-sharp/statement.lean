import Mathlib

open MeasureTheory Real Filter
open scoped Topology

namespace DryRun

/-- **Equivalent width (curve of growth).** For a line of central optical-depth scale `τ` and
nonnegative profile `φ` (area `∫φ`), the equivalent width is the integrated line deficit
`W(τ) = ∫ (1 - exp(-(τ · φ x))) dx`. The optically-thin value is `τ·∫φ`; `W` saturates below it. -/
noncomputable def equivWidth (φ : ℝ → ℝ) (τ : ℝ) : ℝ :=
  ∫ x, (1 - Real.exp (-(τ * φ x)))


/-- **The (normalized) Lorentzian profile** `L(x) = (1/π)·1/(1+x²)` — the natural / pressure-
broadening line shape, a unit-area probability density (`∫L = 1`, `lorentzian_integral`) with
heavy `∼1/x²` wings. The slow wing decay is exactly what makes the equivalent-width curve of growth
grow without bound (the √τ damping-wing regime), in contrast to the rectangular / slab profile whose
equivalent width saturates at `1` (`equivWidth_rectangular`). -/
noncomputable def lorentzian (x : ℝ) : ℝ := (1 / Real.pi) * (1 / (1 + x ^ 2))

/-- **M4 — the sharp Ladenburg–Reiche wing constant `C = 2` (EXACT, within the model).**
The Lorentzian equivalent width obeys the sharp slope-½ asymptotic
`W(τ)/√τ → 2` as `τ → ∞`, upgrading the two-sided envelope
`equivWidth_lorentzian_sqrt_two_sided` (constants `≈ 0.126` and `≈ 2.257`) to the exact
Ladenburg–Reiche damping-wing law `W(τ) ∼ 2√τ`. Combining the rescaling identity
`equivWidth_lorentzian_scaled` (M1) — which gives `W(τ)/√τ = (1/√π)·S(τ)` with
`S(τ) = ∫ (1 − exp(−((τ/π)/(1+(τ/π)u²))))` — with the dominated-convergence limit
`S(τ) → 2√π` (`tendsto_integral_g_beta`, M3, evaluated by `integral_one_sub_exp_neg_inv_sq`, M2)
yields the limit `(1/√π)·2√π = 2`. The exact constant `2` lies strictly inside the previously
proven bracket `[0.126, 2.257]`, confirming consistency. This is the bessel-free capstone of the
`equivWidth_lorentzian_*` development (the full `x·e^{−x}(I₀+I₁)` curve needs modified Bessel
functions, absent from mathlib, and is out of scope). Gornushkin 1999 / Ladenburg–Reiche. -/
theorem equivWidth_lorentzian_sqrt_sharp :
    Filter.Tendsto (fun τ => equivWidth lorentzian τ / Real.sqrt τ) Filter.atTop (nhds 2) := by
  sorry

end DryRun
