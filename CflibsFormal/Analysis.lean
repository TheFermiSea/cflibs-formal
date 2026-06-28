/-
Copyright (c) 2026 Brian Squires. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Squires
-/
import Mathlib

/-!
# Shared analysis scaffolding

A small, function-agnostic real-analysis helper reused across the curve-of-growth /
escape-factor monotonicity proofs. The physics-specific content (the sign of each
derivative numerator) stays in the originating modules; only the generic
`strictAntiOn_of_deriv_neg` + quotient-rule plumbing lives here.
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

end CflibsFormal
