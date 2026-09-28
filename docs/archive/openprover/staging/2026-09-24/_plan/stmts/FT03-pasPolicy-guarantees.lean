import Mathlib

open Finset

namespace Plan.FT03


/-- Three-branch refuse-to-report policy on per-item losses `l` with certified bounds
`L ≤ l ≤ U`, group weights `w`, reference cost `lam`: answer if `U ≤ lam`, refuse if
`lam < L`, and on the ambiguous set answer iff `ansA`. -/
noncomputable def pasPolicy {N : ℕ} (w l L U : Fin N → ℝ) (lam : ℝ) (ansA : Fin N → Prop)
    [DecidablePred ansA] : ℝ :=
  ∑ i, w i * (if U i ≤ lam then l i else if lam < L i then lam else if ansA i then l i else lam)

theorem pasPolicy_guarantees {N : ℕ} {w l L U : Fin N → ℝ} {lam : ℝ} (hw : ∀ i, 0 < w i)
    (hL : ∀ i, L i ≤ l i) (hU : ∀ i, l i ≤ U i) :
    pasPolicy w l L U lam (fun _ => False) ≤ (∑ i, w i) * lam ∧
    pasPolicy w l L U lam (fun _ => False) - ∑ i, w i * min (l i) lam
      ≤ ∑ i, w i * (if L i ≤ lam ∧ lam < U i then lam - L i else 0) ∧
    pasPolicy w l L U lam (fun _ => True) ≤ ∑ i, w i * l i := by
  sorry

end Plan.FT03
