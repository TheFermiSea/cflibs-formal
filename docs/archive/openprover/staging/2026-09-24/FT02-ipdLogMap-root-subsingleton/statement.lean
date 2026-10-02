import Mathlib

/-!
# FT-02 (item 6): at most one regular root of the IPD-aware Saha inverse

Staged target, 2026-09-24 deep audit, frontier FT-02 (verdict REVISE, grade A; this item was
confirmed true by the verifier unchanged). The 2026-09-24 statement audit dropped the decoration
hypothesis `0 < b` (the statement holds for every real `b`). Pure real analysis on `ipdLogMap`
with the lowering coefficient `b` abstract. No module on main mentions IPD, and `ipdLogMap` is
defined nowhere on main.
-/

open Filter Topology

namespace Plan.FT02

/-- **Log-coordinate IPD-aware Saha inverse map** `F(ℓ) = log a + b·exp(ℓ/2)`, with `ℓ = log n_e`.

Physical reading (used by no proof here; the binding is a separate target, FT-02 item 8): with an
ionization-potential depression of the form `Δχ = k_B T·b·√n_e` (`b ≥ 0` kept abstract; the
concrete lowering model is a pending owner decision), the Saha-factor gauge
`S(χ − Δχ) = S(χ)·exp(Δχ/(k_B T))` turns the IPD-aware ratio equation `R·n_e = S(χ − Δχ)` into
`n_e = (S(χ)/R)·exp(b·√n_e)`, i.e. `ℓ = F(ℓ)` with `a = S(χ)/R`, partition functions held fixed
inside the inner loop. The slope `F'(ℓ) = b·exp(ℓ/2)/2` equals `q = Δχ/(2 k_B T)`. For `a ≤ 0`,
`Real.log a` is Lean's junk value. -/
noncomputable def ipdLogMap (a b ℓ : ℝ) : ℝ := Real.log a + b * Real.exp (ℓ / 2)

/-- **At most one regular root of the IPD-aware inverse (FT-02 item 6).**

The fixed-point equation `ℓ = log a + b·exp(ℓ/2)` has at most one solution in the regular
branch `b·exp(ℓ/2) < 2`, i.e. `q = Δχ/(2 k_B T) < 1` in the physical reading. On the regular
branch `ℓ ↦ ℓ − b·exp(ℓ/2)` is strictly increasing, and every root satisfies
`ℓ − b·exp(ℓ/2) = log a`. A second root, if any, lies beyond the fold (`q ≥ 1`), outside the
regular branch. The statement asserts uniqueness only, not existence: for `0 < b` and large `a`
there is no root.

No sign condition on `b` is needed: for `b ≤ 0` the map `ℓ ↦ ℓ − b·exp(ℓ/2)` is strictly
increasing on all of ℝ and the regular-branch condition is automatic. `a` is unconstrained; for
`a ≤ 0` `Real.log a` is a junk value, which does not affect uniqueness.

Scope (two-axis): own relation PURE-MATH (`b` abstract; no physics definition is used); predicted
published tag PURE-MATH. The physical reading is REDUCED and belongs to the separate binding
target (FT-02 item 8). -/
theorem ipdLogMap_root_subsingleton {a b : ℝ} :
    {ℓ | ipdLogMap a b ℓ = ℓ ∧ b * Real.exp (ℓ / 2) < 2}.Subsingleton := by
  sorry

end Plan.FT02
