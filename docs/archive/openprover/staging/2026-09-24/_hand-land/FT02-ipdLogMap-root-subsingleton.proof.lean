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

/-- Chord below the tangent at the right end (from `Real.add_one_le_exp`): for all reals,
`exp(y/2) − exp(x/2) ≤ exp(y/2)/2 · (y − x)`. -/
lemma exp_half_sub_le (x y : ℝ) :
    Real.exp (y / 2) - Real.exp (x / 2) ≤ Real.exp (y / 2) / 2 * (y - x) := by
  have h1 := Real.add_one_le_exp ((x - y) / 2)
  have h2 : Real.exp (x / 2) = Real.exp (y / 2) * Real.exp ((x - y) / 2) := by
    rw [← Real.exp_add]; ring_nf
  have hy := Real.exp_pos (y / 2)
  rw [h2]
  nlinarith [mul_le_mul_of_nonneg_left h1 hy.le]

/-- `exp(·/2)` is monotone. -/
lemma exp_half_mono {x y : ℝ} (h : x ≤ y) : Real.exp (x / 2) ≤ Real.exp (y / 2) :=
  Real.exp_le_exp.mpr (by linarith)

/-- One-sided core, any sign of `b`: two roots `x < y` with `y` regular are impossible. -/
lemma no_two_roots {a b x y : ℝ} (hxy : x < y) (hx : ipdLogMap a b x = x)
    (hy : ipdLogMap a b y = y) (hr : b * Real.exp (y / 2) < 2) : False := by
  unfold ipdLogMap at hx hy
  have key : y - x = b * (Real.exp (y / 2) - Real.exp (x / 2)) := by linarith
  have hd : 0 ≤ Real.exp (y / 2) - Real.exp (x / 2) := sub_nonneg.mpr (exp_half_mono hxy.le)
  rcases le_or_gt b 0 with hb | hb
  · nlinarith [mul_nonpos_of_nonpos_of_nonneg hb hd]
  · have c := mul_le_mul_of_nonneg_left (exp_half_sub_le x y) hb.le
    have hr' : b * Real.exp (y / 2) / 2 * (y - x) < 1 * (y - x) :=
      mul_lt_mul_of_pos_right (by linarith) (sub_pos.mpr hxy)
    nlinarith

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
  intro x hx y hy
  obtain ⟨hxf, hxr⟩ := hx
  obtain ⟨hyf, hyr⟩ := hy
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact no_two_roots hlt hxf hyf hyr
  · exact no_two_roots hlt hyf hxf hxr

/-- Non-vacuity witness: at `a = exp(−1/2)`, `b = 1/2`, `ℓ = 0` is a regular root
(`−1/2 + 1/2 = 0` and `1/2 < 2`), so the set is nonempty. -/
example :
    (0:ℝ) ∈ {ℓ | ipdLogMap (Real.exp (-1/2)) (1/2) ℓ = ℓ ∧ (1/2) * Real.exp (ℓ / 2) < 2} := by
  refine ⟨?_, ?_⟩
  · unfold ipdLogMap; rw [Real.log_exp]; simp; norm_num
  · simp; norm_num

/-- Non-vacuity witness: the theorem pins every regular root at that instance to `0`. -/
example (ℓ : ℝ)
    (h : ℓ ∈ {ℓ | ipdLogMap (Real.exp (-1/2)) (1/2) ℓ = ℓ ∧ (1/2) * Real.exp (ℓ / 2) < 2}) :
    ℓ = 0 :=
  ipdLogMap_root_subsingleton (a := Real.exp (-1/2)) (b := 1/2) h
    ⟨by unfold ipdLogMap; rw [Real.log_exp]; simp; norm_num, by simp; norm_num⟩

end Plan.FT02
