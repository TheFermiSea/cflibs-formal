# FT02: the IPD-aware Saha inverse contracts on an invariant half-line

Source: 2026-09-24 deep audit, FT-02 items 3-5 (`hasDerivAt`, Lipschitz on `Iic`, contraction);
verdict REVISE, grade A (this item confirmed true unchanged). Priority 27, group g2. Rated the
riskiest FT-02 item (Banach on an unbounded closed half-line).

**Status note for the lead (2026-09-24, statement author g2):** while checking the route, the
statement author completed a proof: sections 4a + 4b + the uniqueness block below, assembled, pass
`verify.py` end to end (kernel replay, standard axioms, identical elaborated type). The file is
`staging/2026-09-24/_g2/FT02-ipdLogMap-contracts.proof.lean`. Recommend hand-landing rather than
spending planner budget; queue it only as a harness calibration run.

## 1. Goal

```lean
theorem ipdLogMap_contracts {a b ℓ1 q : ℝ} (hb : 0 ≤ b)
    (hq : b * Real.exp (ℓ1 / 2) / 2 ≤ q) (hq1 : q < 1)
    (hmaps : Set.MapsTo (ipdLogMap a b) (Set.Iic ℓ1) (Set.Iic ℓ1)) :
    ∃ ℓs ∈ Set.Iic ℓ1, ipdLogMap a b ℓs = ℓs ∧
      (∀ ℓ ∈ Set.Iic ℓ1, ipdLogMap a b ℓ = ℓ → ℓ = ℓs) ∧
      ∀ ℓ0 ∈ Set.Iic ℓ1, Tendsto (fun n => (ipdLogMap a b)^[n] ℓ0) atTop (𝓝 ℓs)
```

Meaning: on an invariant half-line where the slope of `F` is at most `q < 1`, `F` has a unique
fixed point there and fixed-point iteration converges to it from every start in the half-line.

## 2. Definitions

The only definition, identical (byte-for-byte) in all three FT02 targets; nothing from the repo
is imported (imports: `Mathlib` only; `open Filter Topology`; namespace `Plan.FT02`):

```lean
noncomputable def ipdLogMap (a b ℓ : ℝ) : ℝ := Real.log a + b * Real.exp (ℓ / 2)
```

Physical reading (context only; no proof uses it): `ℓ = log n_e`. With an ionization-potential
depression `Δχ = k_B T·b·√n_e` (`b ≥ 0` abstract; the concrete lowering model is a pending owner
decision) and the exact Saha gauge `S(χ − Δχ) = S(χ)·exp(Δχ/(k_B T))`, the IPD-aware ratio equation
`R·n_e = S(χ − Δχ)` becomes `ℓ = ipdLogMap a b ℓ` with `a = S(χ)/R`. The slope
`F'(ℓ) = b·exp(ℓ/2)/2` is `q = Δχ/(2 k_B T)`; the two roots merge (fold) at `q = 1`. Audit numbers
at `1e17 cm⁻³`, `11 kK`: `Δχ ≈ 0.0629 eV`, `q ≈ 0.0332`, fold near `9.08e19 cm⁻³`.
No module on main mentions IPD (`rg -i 'debye|\bIPD\b|depression|lowering' CflibsFormal`: 0 hits,
positive control `rg -i aitken` hits).

## 3. Mathematical proof

1. **Lipschitz on the half-line.** For `x, y ≤ ℓ1`,
   `|F x − F y| = b·|e^{x/2} − e^{y/2}| ≤ (b·e^{max(x,y)/2}/2)·|x − y| ≤ (b·e^{ℓ1/2}/2)·|x − y| ≤ q|x − y|`
   (chord bound; `e^{·/2}` monotone; `hb`). Verified as `ipdLogMap_lipschitz_Iic` below.
2. **Banach.** `Iic ℓ1` is closed in the complete space `ℝ`, hence complete; `F` maps it to
   itself (`hmaps`); `q ≥ 0` (from `hb`, `hq`) and `q < 1`, so the restriction is a contraction.
   `ContractingWith.exists_fixedPoint'` gives a fixed point `ℓs ∈ Iic ℓ1` and convergence of the
   iterates from any start in `Iic ℓ1`.
3. **Uniqueness in the half-line.** If `F ℓ = ℓ` with `ℓ ≤ ℓ1`, then
   `|ℓ − ℓs| = |F ℓ − F ℓs| ≤ q|ℓ − ℓs|`, so `(1 − q)|ℓ − ℓs| ≤ 0`, so `ℓ = ℓs`.
4. **Convergence to `ℓs` from every start.** For `ℓ0 ≤ ℓ1`, apply `exists_fixedPoint'` again with
   start `ℓ0`: it returns some fixed point `y ∈ Iic ℓ1` with `F^[n] ℓ0 → y`; by step 3, `y = ℓs`.

## 4. Lean route

## 4a. Verified helpers (compiled in exactly this import/namespace context)

Derivative-free: everything follows from `Real.add_one_le_exp` (tangent line below `exp`). Place
these after `ipdLogMap` (keep a blank line after the definition) and before the target.

```lean
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
```

Key fact, for any reals `x ≤ y`: `0 ≤ exp(y/2) − exp(x/2) ≤ exp(y/2)/2 · (y − x)`
(`exp_half_mono`, `exp_half_sub_le`). Multiplying by `b ≥ 0` bounds the change of `b·exp(ℓ/2)` by
the slope at the right end.

## 4b. Verified skeleton (compiles against the real statement with only `huniq` open)

Adapted from the repo's `CflibsFormal.outerContraction_box` (`SahaEquilibrium.lean:1269`), the
same Banach wiring on `Set.Icc`:

```lean
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
    sorry
  refine ⟨ℓs, hℓs, hfix, huniq, ?_⟩
  intro ℓ0 hℓ0
  obtain ⟨y, hy, hyfix, htend, -⟩ :=
    hcontract.exists_fixedPoint' hcomplete hmaps hℓ0 (edist_ne_top _ _)
  have : y = ℓs := huniq y hy hyfix
  rwa [this] at htend
```

The open step `huniq`, adapted from the uniqueness block of `outerContraction_box`
(verified: replacing the `sorry` above with this block makes the whole proof pass `verify.py`):

```lean
    intro ℓ hℓ hℓfix
    have hc := ipdLogMap_lipschitz_Iic (a := a) hb hq hℓ hℓs
    rw [hℓfix, hfix] at hc
    by_contra hne
    have habs : 0 < |ℓ - ℓs| := abs_pos.mpr (sub_ne_zero.mpr hne)
    have hpos : 0 < (1 - q) * |ℓ - ℓs| := mul_pos (by linarith) habs
    nlinarith [hc, hpos]
```

## 4c. Extra Mathlib names used by the skeleton (`#check`ed)

- `ContractingWith.exists_fixedPoint' {s : Set α} (hsc : IsComplete s) (hsf : MapsTo f s s)
  (hf : ContractingWith K (hsf.restrict f s s)) {x : α} (hxs : x ∈ s) (hx : edist x (f x) ≠ ⊤) :
  ∃ y ∈ s, IsFixedPt f y ∧ Tendsto (fun n ↦ f^[n] x) atTop (𝓝 y) ∧ ∀ n, edist … ≤ …`
  (`Topology/MetricSpace/Contracting.lean:152`).
- `ContractingWith K f := K < 1 ∧ LipschitzWith K f` (`K : NNReal`); build `K := ⟨q, hq0⟩`.
- `IsClosed.isComplete`, `isClosed_Iic`, `lipschitzWith_iff_dist_le_mul`, `Subtype.dist_eq`,
  `Set.MapsTo.val_restrict_apply`, `Real.dist_eq`, `NNReal.coe_lt_one`, `edist_ne_top`.
- `Set.right_mem_Iic` does not exist; use `le_refl ℓ1` for `ℓ1 ∈ Set.Iic ℓ1`.

## 5. Mathlib lemmas (all `#check`ed on the pinned v4.33.1 tree)

- `Real.add_one_le_exp (x : ℝ) : x + 1 ≤ Real.exp x` (`Analysis/Complex/Exponential.lean:633`).
- `Real.exp_add : exp (x + y) = exp x * exp y`; `Real.exp_le_exp : exp x ≤ exp y ↔ x ≤ y`;
  `Real.exp_pos`.
- `Real.log_le_log (hx : 0 < x) (h : x ≤ y) : log x ≤ log y`.
- `le_div_iff₀ (hc : 0 < c) : a ≤ b / c ↔ a * c ≤ b`; `div_le_iff₀`.
- `max_eq_left : b ≤ a → max a b = a`; `max_eq_right : a ≤ b → max a b = b`; `le_total`;
  `lt_or_gt_of_ne`.
- `abs_sub_comm`, `abs_of_nonneg`, `abs_of_nonpos`, `abs_pos`, `mul_le_mul_of_nonneg_left`,
  `mul_lt_mul_of_pos_right`.

## 6. Pitfalls

- `Real.log` is total: `Real.log a = Real.log |a|` for `a < 0`, `Real.log 0 = 0`. Never assume
  `exp (log a) = a` without `0 < a`.
- `max l1 l2 / 2` is `(max l1 l2) / 2`; after deciding the order, rewrite with
  `max_eq_left`/`max_eq_right` before using the bound.
- Prefer `nlinarith` with explicit product hints (e.g. `mul_le_mul_of_nonneg_left h hb`,
  `mul_lt_mul_of_pos_right h (sub_pos.mpr hlt)`) over bare `nlinarith`.
- Verifier rules: copy the imports, the `open` line and the `ipdLogMap` definition
  byte-for-byte, with a blank line after the definition (it is matched textually up to the next
  blank line or `theorem`/`lemma`/docstring). Keep the theorem signature byte-identical,
  hypothesis names included. Helper names must not begin with the target theorem's name and must
  come before the target. No new imports, no `set_option` beyond heartbeat/recursion limits, no
  `#` commands.
- `IsFixedPt f y` unfolds to `f y = y`; `have hfix : ipdLogMap a b ℓs = ℓs := hfixpt` works.
- The statement's `Tendsto`, `atTop`, `𝓝` come from `open Filter Topology`.

## 8. Pipeline caveat for the docstring reader

The jitpipe loop starts from a pinned `n_e` that need not lie in `Iic ℓ1`, so its `q³` error
factor (about `3.7e-5` at `1e17 cm⁻³`, `11 kK`) applies only once `hmaps` holds and the start is in
the half-line. No rate is part of this statement.

## 7. Scope and consumers

Own relation PURE-MATH (`b` abstract; no physics definition is used); predicted published tag
PURE-MATH. The physical reading (a `√n_e` lowering, one ionization edge, element-independent
`Δχ`, partition functions frozen inside the inner loop) is REDUCED and is the separate binding
target FT-02 item 8. Consumers: [backlog-id] (bead 3n4a), [backlog-id], the A11 IPD regression test (RF-25),
`jitpipe/solve.py:842-866` (three-step inner IPD loop). Literature: none needed for these
PURE-MATH lemmas; the gauge's Saha–Eggert form is `Saha–Eggert (Griem)` / Griem 1997
(whitelisted). Ristić et al. 2024 is off-whitelist; do not cite it.
