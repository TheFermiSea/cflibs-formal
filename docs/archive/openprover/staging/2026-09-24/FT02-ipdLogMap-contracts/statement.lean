import Mathlib

/-!
# FT-02 (items 3-5): the IPD-aware Saha inverse contracts on an invariant half-line

Staged queue target, 2026-09-24 deep audit, frontier FT-02 (verdict REVISE, grade A; this item
was confirmed true by the verifier unchanged). Banach's fixed-point theorem for `ipdLogMap` on a
closed half-line, with the lowering coefficient `b` abstract. No module on main mentions IPD,
and `ipdLogMap` is defined nowhere on main.
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

/-- **The IPD inner loop contracts on an invariant half-line (FT-02 items 3-5).**

Suppose the half-line `(−∞, ℓ1]` is invariant under `F = ipdLogMap a b` (`hmaps`) and the slope
of `F` on it is at most `q < 1`: `b·exp(ℓ1/2)/2 ≤ q < 1` (the slope `b·exp(ℓ/2)/2` is increasing
in `ℓ`, so its supremum on the half-line is attained at `ℓ1`). Then `F` has a fixed point
`ℓs ≤ ℓ1`, it is the only fixed point in the half-line, and the fixed-point iteration `F^[n] ℓ0`
converges to it from every start `ℓ0 ≤ ℓ1`.

Hypotheses and why each is present:
* `hb : 0 ≤ b`: lowering is nonnegative. With `hq` it gives `0 ≤ q`, so `q` is a valid
  contraction constant, and it makes `F` nondecreasing.
* `hq`, `hq1`: the contraction rate `q < 1` on the half-line.
* `hmaps`: invariance of the half-line; it does not follow from `hq`. Since `F` is
  nondecreasing, `F ℓ1 ≤ ℓ1` suffices, which a pipeline can check a posteriori.

Pipeline note: the jitpipe inner IPD loop runs three steps starting from a pinned `n_e`, which
need not lie in the half-line, so its `q³` error factor (about `3.7e-5` at `1e17 cm⁻³`, `11 kK`,
per the audit's numerics) applies only once `hmaps` holds and the start lies in the half-line.
No rate or error bound is part of this statement.

Scope (two-axis): own relation PURE-MATH (`b` abstract; no physics definition is used); predicted
published tag PURE-MATH. The physical reading is REDUCED and belongs to the separate binding
target (FT-02 item 8). -/
theorem ipdLogMap_contracts {a b ℓ1 q : ℝ} (hb : 0 ≤ b)
    (hq : b * Real.exp (ℓ1 / 2) / 2 ≤ q) (hq1 : q < 1)
    (hmaps : Set.MapsTo (ipdLogMap a b) (Set.Iic ℓ1) (Set.Iic ℓ1)) :
    ∃ ℓs ∈ Set.Iic ℓ1, ipdLogMap a b ℓs = ℓs ∧
      (∀ ℓ ∈ Set.Iic ℓ1, ipdLogMap a b ℓ = ℓ → ℓ = ℓs) ∧
      ∀ ℓ0 ∈ Set.Iic ℓ1, Tendsto (fun n => (ipdLogMap a b)^[n] ℓ0) atTop (𝓝 ℓs) := by
  sorry

end Plan.FT02
