import Mathlib

/-!
# FT-01 (b): a derivative-window certificate for a damped iteration on an invariant box

Staged queue target, 2026-09-24 audit, frontier FT-01, queue item 7 (the verifier dropped
`lam ≤ 1`). The definition `dampedMap` is shared verbatim (definition line and body) with the
sibling target `tDamped_mobius_converges`. Real analysis only.
-/

open Filter Topology

namespace Plan.FT01

/-- Krasnoselskii–Mann damped map `u ↦ (1−λ)u + λ g(u)` (the pipeline uses `λ = 1/2`).
One relaxation step of the fixed-point iteration for `g` with damping `lam` (`lam = 1` is plain
substitution). The CF-LIBS pipeline relaxes its outer temperature update with `lam = 1/2`,
`T_K = 0.5 * T_prev + 0.5 * T_new` (CF-LIBS-improved `cflibs/inversion/solve/iterative.py`,
lines 908 and 2454), so there the damped coordinate `u` is the temperature `T` itself. -/
def dampedMap (lam : ℝ) (g : ℝ → ℝ) (u : ℝ) : ℝ := (1 - lam) * u + lam * g u

/-- **Derivative-window certificate for a damped fixed-point iteration on an invariant box.**
Let `g` have derivative `g' T ∈ [m, M]` at every point of the box `[a, b]` (`a ≤ b`), and let the
damped map `H := dampedMap lam g`, `T ↦ (1 - lam) * T + lam * g T`, map `[a, b]` into itself. If
`1 - 2/lam < m` and `M < 1`, then `H` has a fixed point `Tstar ∈ [a, b]` (equivalently, since
`lam > 0`, `g Tstar = Tstar`) and the `H`-iterates converge to `Tstar` from every start in
`[a, b]`.

Why: `H' = 1 - lam + lam * g' ∈ [1 - lam + lam * m, 1 - lam + lam * M] ⊂ (-1, 1)`, so by the mean
value theorem `H` is a `q`-contraction on `[a, b]` with
`q = max |1 - lam + lam * m| |1 - lam + lam * M| < 1`, and Banach's theorem applies on the
complete nonempty interval.

Use: for the T-damped outer loop this replaces the product-of-Lipschitz gate `L1 * L2 < 1` of
`outerContraction_box` (`SahaEquilibrium.lean`), which the audit found 10^3 to 10^5 too loose. It
is to be bound with `g'` the derivative of the undamped T-map, not a constant gain. `hmaps` can
be checked a posteriori from the temperature window.

Hypotheses. `hlam0`: any positive damping (no upper bound is needed). `hab`: the box is nonempty.
`hd`: two-sided differentiability at every box point, endpoints included. `hmM`, `hlo`, `hhi`: the
derivative window; it cannot be widened, since `g' < 1 - 2/lam` gives `H' < -1` and a fixed point
with `g' > 1` repels for every `lam > 0` (FT-01, separate target). `hmaps`: box invariance, which
is not automatic.

Scope, two-axis prediction (owner rule 2026-09-24): PURE-MATH on both axes (no model definitions);
published tag PURE-MATH. Whether the pipeline's T-map satisfies `hd`, `hmM` and `hmaps` on a given
window is the REDUCED binding (FT-01 step 10), not claimed here. -/
theorem dampedMap_contracts {g g' : ℝ → ℝ} {a b m M lam : ℝ} (hlam0 : 0 < lam) (hab : a ≤ b)
    (hd : ∀ T ∈ Set.Icc a b, HasDerivAt g (g' T) T)
    (hmM : ∀ T ∈ Set.Icc a b, m ≤ g' T ∧ g' T ≤ M) (hlo : 1 - 2 / lam < m) (hhi : M < 1)
    (hmaps : Set.MapsTo (dampedMap lam g) (Set.Icc a b) (Set.Icc a b)) :
    ∃ Tstar ∈ Set.Icc a b, dampedMap lam g Tstar = Tstar ∧
      ∀ T0 ∈ Set.Icc a b, Tendsto (fun n => (dampedMap lam g)^[n] T0) atTop (𝓝 Tstar) := by
  sorry

end Plan.FT01
