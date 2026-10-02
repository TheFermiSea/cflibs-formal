import Mathlib

/-!
# FT-02 (item 7): two-point log-sensitivity bracket for the IPD-aware Saha inverse

Staged queue target, 2026-09-24 deep audit, frontier FT-02 (verdict REVISE, grade A; the
verifier's restated form with `0 < a1` and `0 ≤ b`). Pure real analysis on `ipdLogMap` with the
lowering coefficient `b` abstract, so it does not depend on the pending choice of IPD model. No
module on main mentions IPD, and `ipdLogMap` is defined nowhere on main.
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

/-- **Two-point log-sensitivity bracket for the IPD-aware inverse (FT-02 item 7).**

Let `l1`, `l2` be fixed points of `ipdLogMap a1 b` and `ipdLogMap a2 b` for data `0 < a1 ≤ a2`,
both in the regular regime `b·exp(max l1 l2 / 2)/2 ≤ q < 1`. Then
`log a2 − log a1 ≤ l2 − l1 ≤ (log a2 − log a1)/(1 − q)`: the fixed point moves in the same
direction as the data, at least one-for-one and at most by the factor `1/(1 − q)`, in log
coordinates. In the physical reading `a = S(χ)/R` at fixed `T` this brackets
`|Δ log n_e| / |Δ log R|` in `[1, 1/(1 − q)]` (the sign is negative, since `a ∝ 1/R`).

Hypotheses and why each is present:
* `ha1 : 0 < a1`: otherwise `Real.log a1` is the junk value `log |a1|` and the statement is false
  (deep-audit counterexample `twoPoint_sensitivity_false`, evidence
  `frontier-verifier/Verify.lean`). With `ha` it also gives `0 < a2`.
* `hb : 0 ≤ b`: lowering is nonnegative; for `b < 0` the lower bound fails (counterexample
  `twoPoint_sensitivity_false_negb`, same file).
* `hreg`, `hq`: the regular regime. `hreg` at `max l1 l2` bounds the slope of `ipdLogMap` on the
  whole segment between the two fixed points. `q < 1` is sharp: the two roots of `ℓ = F(ℓ)` merge
  at `q = 1` (a fold), where the sensitivity is unbounded.

Scope (two-axis): own relation PURE-MATH (real analysis, `b` abstract; no physics definition is
used); predicted published tag PURE-MATH. The physical reading (a `√n_e` lowering, one
ionization edge, element-independent `Δχ`, partition functions frozen in the inner loop) is
REDUCED and belongs to the separate binding target (FT-02 item 8). -/
theorem ipdInverse_twoPoint_sensitivity {a1 a2 b l1 l2 q : ℝ} (ha1 : 0 < a1) (hb : 0 ≤ b)
    (hq : q < 1) (h1 : ipdLogMap a1 b l1 = l1) (h2 : ipdLogMap a2 b l2 = l2) (ha : a1 ≤ a2)
    (hreg : b * Real.exp (max l1 l2 / 2) / 2 ≤ q) :
    Real.log a2 - Real.log a1 ≤ l2 - l1 ∧ l2 - l1 ≤ (Real.log a2 - Real.log a1) / (1 - q) := by
  sorry

end Plan.FT02
