# FT02: at most one regular root of the IPD-aware Saha inverse

Source: 2026-09-24 deep audit, FT-02 item 6 (root subsingleton via strict monotonicity of
`ℓ − F(ℓ)`); verdict REVISE, grade A (this item confirmed true unchanged). Priority 19, group g2.

**Statement audit (2026-09-24, M6 round): FIX; HAND-LAND, queue only as a calibration run.**
The decoration hypothesis `hb : 0 < b` is dropped (it was not needed for truth, was stricter
than the siblings' `0 ≤ b`, and excluded the no-IPD case `b = 0`). The new statement holds for
every real `b`. A verified, axiom-clean proof (about 25 lines, derivative-free) is at
`staging/2026-09-24/_hand-land/FT02-ipdLogMap-root-subsingleton.proof.lean`; with the helper
`no_two_roots` in 4a, a queued run exercises only the final assembly.

## 1. Goal

```lean
theorem ipdLogMap_root_subsingleton {a b : ℝ} :
    {ℓ | ipdLogMap a b ℓ = ℓ ∧ b * Real.exp (ℓ / 2) < 2}.Subsingleton
```

Meaning: in the regular branch `q = b·e^{ℓ/2}/2 < 1` the IPD-aware inverse has at most one root,
so the physical `n_e` is unique there. No existence claim. No sign condition on `b`.

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

Let `x, y` be two roots in the set and suppose `x < y`. The fixed-point equations give
`x − b·e^{x/2} = log a = y − b·e^{y/2}`, so `y − x = b(e^{y/2} − e^{x/2})`, and
`e^{y/2} − e^{x/2} ≥ 0`. Split on the sign of `b` (`le_or_gt b 0`; `le_or_lt` does not exist on
this toolchain):
- `b ≤ 0`: the right side `b(e^{y/2} − e^{x/2})` is `≤ 0 < y − x`, a contradiction
  (`nlinarith` with `mul_nonpos_of_nonpos_of_nonneg`). Here the regular-branch condition is
  automatic and not used.
- `b > 0`: by the chord bound, `b(e^{y/2} − e^{x/2}) ≤ (b·e^{y/2}/2)(y − x)`. The regular-branch
  condition at `y` gives `b·e^{y/2}/2 < 1`, so, with `y − x > 0`, `(b·e^{y/2}/2)(y − x) < y − x`.
  Hence `y − x < y − x`, a contradiction (`mul_lt_mul_of_pos_right`, then `nlinarith`).

The case `y < x` is symmetric (swap roles). So `x = y`.

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

One-sided core, any sign of `b` (verified in this context; it is the whole of section 3):

```lean
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
```

## 4b. Assembly sketch

```lean
  intro x hx y hy
  obtain ⟨hxf, hxr⟩ := hx          -- membership in a setOf is the predicate itself
  obtain ⟨hyf, hyr⟩ := hy
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · -- x < y: apply the one-sided core with `y` regular
    sorry
  · -- y < x: the same with the roles of x and y swapped
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
target FT-02 item 8. Consumers: [backlog-id] (bead 3n4a), [backlog-id], the A11 IPD regression test (RF-25),
`jitpipe/solve.py:842-866` (three-step inner IPD loop). Literature: none needed for these
PURE-MATH lemmas; the gauge's Saha–Eggert form is `Saha–Eggert (Griem)` / Griem 1997
(whitelisted). Ristić et al. 2024 is off-whitelist; do not cite it.
