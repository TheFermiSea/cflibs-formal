# FT02: two-point log-sensitivity bracket for the IPD-aware Saha inverse

Source: 2026-09-24 deep audit, FT-02 item 7, in the verifier's restated form (adds `0 < a1`,
`0 ≤ b`); verdict REVISE, grade A. Priority 8, group g2.

## 1. Goal

```lean
theorem ipdInverse_twoPoint_sensitivity {a1 a2 b l1 l2 q : ℝ} (ha1 : 0 < a1) (hb : 0 ≤ b)
    (hq : q < 1) (h1 : ipdLogMap a1 b l1 = l1) (h2 : ipdLogMap a2 b l2 = l2) (ha : a1 ≤ a2)
    (hreg : b * Real.exp (max l1 l2 / 2) / 2 ≤ q) :
    Real.log a2 - Real.log a1 ≤ l2 - l1 ∧ l2 - l1 ≤ (Real.log a2 - Real.log a1) / (1 - q)
```

Meaning: fixed points move with the data, at least one-for-one and at most by `1/(1 − q)`, in
log coordinates.

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

## 3. Mathematical proof (derivative-free)

Write `Δ = log a2 − log a1` and `h(ℓ) = ℓ − b·e^{ℓ/2}`. The fixed-point equations say
`h(l1) = log a1`, `h(l2) = log a2`, so `Δ = (l2 − l1) − b(e^{l2/2} − e^{l1/2})`.
Since `0 < a1 ≤ a2`, `Δ ≥ 0` (`Real.log_le_log ha1 ha`). From `hb`, `hreg`: `q ≥ 0`.

1. **Order: `l1 ≤ l2`.** Suppose `l2 < l1`. Then `max l1 l2 = l1`, so `b·e^{l1/2}/2 ≤ q`, and by the
   chord bound `b(e^{l1/2} − e^{l2/2}) ≤ (b·e^{l1/2}/2)(l1 − l2) ≤ q(l1 − l2)`. Hence
   `Δ = (l2 − l1) + b(e^{l1/2} − e^{l2/2}) ≤ −(1 − q)(l1 − l2) < 0`, contradicting `Δ ≥ 0`. This is
   where `ha1` (through `Δ ≥ 0`) and `hq` are spent.
2. **Lower bound.** With `l1 ≤ l2`: `b(e^{l2/2} − e^{l1/2}) ≥ 0` (`hb`, `exp_half_mono`), so
   `Δ ≤ l2 − l1`.
3. **Upper bound.** `max l1 l2 = l2`, so `b·e^{l2/2}/2 ≤ q`, and
   `b(e^{l2/2} − e^{l1/2}) ≤ (b·e^{l2/2}/2)(l2 − l1) ≤ q(l2 − l1)`. Hence
   `Δ ≥ (1 − q)(l2 − l1)`, i.e. `l2 − l1 ≤ Δ/(1 − q)` (`le_div_iff₀`, `1 − q > 0`).

Fallback (not recommended): the mean value theorem on `h` over `[l1, l2]` with
`h' = 1 − (b/2)e^{ℓ/2} ∈ [1 − q, 1]`.

Why each hypothesis is needed (Lean counterexamples in the audit evidence,
`docs/research/audit-2026-09-24/evidence/frontier-verifier/Verify.lean:59,80`):
- without `0 < a1`: `a1 = −e^{−1/2}`, `a2 = e^{−2 − e^{−1}/2}`, `b = q = 1/2`, `l1 = 0`, `l2 = −2`
  breaks the lower bound (`log` of a negative number is junk);
- with `0 < a1` but `b = −1/2`: `l1 = 0`, `l2 = 2`, `q = 0` breaks the lower bound.
Numerics (audit, `_plan/numcheck.py`): 0 violations over 20000 draws with `0 ≤ b`, `0 < a1 ≤ a2`.

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

## 4b. Assembly sketch (not compiled as a whole)

```lean
  have ha2 : 0 < a2 := lt_of_lt_of_le ha1 ha
  have hΔ : 0 ≤ Real.log a2 - Real.log a1 := sub_nonneg.mpr (Real.log_le_log ha1 ha)
  have e1 := ipdLogMap_fixed_iff.mp h1   -- l1 - b * exp (l1/2) = log a1
  have e2 := ipdLogMap_fixed_iff.mp h2   -- l2 - b * exp (l2/2) = log a2
  have hle : l1 ≤ l2 := by
    by_contra hlt
    push_neg at hlt                        -- hlt : l2 < l1
    rw [max_eq_left hlt.le] at hreg
    have c := mul_le_mul_of_nonneg_left (exp_half_sub_le l2 l1) hb
    -- combine c, hreg (times l1 - l2 > 0), e1, e2, hΔ, hq with nlinarith
    sorry
  rw [max_eq_right hle] at hreg
  have c := mul_le_mul_of_nonneg_left (exp_half_sub_le l1 l2) hb
  have m := mul_nonneg hb (sub_nonneg.mpr (exp_half_mono hle))
  refine ⟨by nlinarith, ?_⟩
  rw [le_div_iff₀ (by linarith)]
  -- goal: (l2 - l1) * (1 - q) ≤ log a2 - log a1; use c, hreg * (l2 - l1 ≥ 0), e1, e2
  sorry
```

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

## 7. Scope and consumers

Own relation PURE-MATH (`b` abstract; no physics definition is used); predicted published tag
PURE-MATH. The physical reading (a `√n_e` lowering, one ionization edge, element-independent
`Δχ`, partition functions frozen inside the inner loop) is REDUCED and is the separate binding
target FT-02 item 8. Consumers: BL-42 (bead 3n4a), R1-07, the A11 IPD regression test (RF-25),
`jitpipe/solve.py:842-866` (three-step inner IPD loop). Literature: none needed for these
PURE-MATH lemmas; the gauge's Saha–Eggert form is `Saha–Eggert (Griem)` / Griem 1997
(whitelisted). Ristić et al. 2024 is off-whitelist; do not cite it.
