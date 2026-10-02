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

/-- The fixed-point equation rearranged: `ℓ − b·exp(ℓ/2) = log a`. -/
lemma ipdLogMap_fixed_iff {a b ℓ : ℝ} :
    ipdLogMap a b ℓ = ℓ ↔ ℓ - b * Real.exp (ℓ / 2) = Real.log a := by
  unfold ipdLogMap; constructor <;> intro h <;> linarith

/-- `ipdLogMap a b` is `q`-Lipschitz on `Iic ℓ1` when `b·exp(ℓ1/2)/2 ≤ q`, `0 ≤ b`. -/
lemma ipdLogMap_lipschitz_Iic {a b ℓ1 q : ℝ} (hb : 0 ≤ b) (hq : b * Real.exp (ℓ1 / 2) / 2 ≤ q)
    {x y : ℝ} (hx : x ≤ ℓ1) (hy : y ≤ ℓ1) :
    |ipdLogMap a b x - ipdLogMap a b y| ≤ q * |x - y| := by
  have key : ∀ u v : ℝ, u ≤ v → v ≤ ℓ1 →
      |ipdLogMap a b u - ipdLogMap a b v| ≤ q * |u - v| := by
    intro u v huv hv
    have h0 : 0 ≤ Real.exp (v / 2) - Real.exp (u / 2) := sub_nonneg.mpr (exp_half_mono huv)
    have h1 := exp_half_sub_le u v
    have h2 : Real.exp (v / 2) ≤ Real.exp (ℓ1 / 2) := exp_half_mono hv
    have hdiff : ipdLogMap a b u - ipdLogMap a b v
        = -(b * (Real.exp (v / 2) - Real.exp (u / 2))) := by
      unfold ipdLogMap; ring
    rw [hdiff, abs_neg, abs_of_nonneg (mul_nonneg hb h0),
      abs_of_nonpos (by linarith : u - v ≤ 0)]
    calc b * (Real.exp (v / 2) - Real.exp (u / 2))
        ≤ b * (Real.exp (v / 2) / 2 * (v - u)) := mul_le_mul_of_nonneg_left h1 hb
      _ = (b * Real.exp (v / 2) / 2) * (v - u) := by ring
      _ ≤ q * (v - u) := by
          apply mul_le_mul_of_nonneg_right _ (by linarith)
          nlinarith [mul_le_mul_of_nonneg_left h2 hb]
      _ = q * -(u - v) := by ring
  rcases le_total x y with hxy | hxy
  · exact key x y hxy hy
  · rw [abs_sub_comm, abs_sub_comm x y]; exact key y x hxy hx

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
  have hq0 : 0 ≤ q := le_trans (by positivity) hq
  have hcomplete : IsComplete (Set.Iic ℓ1) := isClosed_Iic.isComplete
  set K : NNReal := ⟨q, hq0⟩ with hKdef
  have hKcoe : (K : ℝ) = q := rfl
  have hK : K < 1 := by rw [← NNReal.coe_lt_one, hKcoe]; exact hq1
  have hlip : LipschitzWith K (hmaps.restrict (ipdLogMap a b) (Set.Iic ℓ1) (Set.Iic ℓ1)) := by
    refine lipschitzWith_iff_dist_le_mul.mpr ?_
    rintro ⟨x, hx⟩ ⟨y, hy⟩
    rw [Subtype.dist_eq, Subtype.dist_eq, Set.MapsTo.val_restrict_apply,
      Set.MapsTo.val_restrict_apply, Real.dist_eq, Real.dist_eq, hKcoe]
    exact ipdLogMap_lipschitz_Iic hb hq hx hy
  have hcontract : ContractingWith K
      (hmaps.restrict (ipdLogMap a b) (Set.Iic ℓ1) (Set.Iic ℓ1)) := ⟨hK, hlip⟩
  have hxs : ℓ1 ∈ Set.Iic ℓ1 := le_refl ℓ1
  obtain ⟨ℓs, hℓs, hfixpt, -, -⟩ :=
    hcontract.exists_fixedPoint' hcomplete hmaps hxs (edist_ne_top _ _)
  have hfix : ipdLogMap a b ℓs = ℓs := hfixpt
  have huniq : ∀ ℓ ∈ Set.Iic ℓ1, ipdLogMap a b ℓ = ℓ → ℓ = ℓs := by
    intro ℓ hℓ hℓfix
    have hc := ipdLogMap_lipschitz_Iic (a := a) hb hq hℓ hℓs
    rw [hℓfix, hfix] at hc
    by_contra hne
    have habs : 0 < |ℓ - ℓs| := abs_pos.mpr (sub_ne_zero.mpr hne)
    have hpos : 0 < (1 - q) * |ℓ - ℓs| := mul_pos (by linarith) habs
    nlinarith [hc, hpos]
  refine ⟨ℓs, hℓs, hfix, huniq, ?_⟩
  intro ℓ0 hℓ0
  obtain ⟨y, hy, hyfix, htend, -⟩ :=
    hcontract.exists_fixedPoint' hcomplete hmaps hℓ0 (edist_ne_top _ _)
  have : y = ℓs := huniq y hy hyfix
  rwa [this] at htend

end Plan.FT02
