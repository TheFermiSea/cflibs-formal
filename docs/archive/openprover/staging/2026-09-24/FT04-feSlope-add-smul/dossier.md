# FT04-feSlope-add-smul: the fixed-effects slope is linear in the ordinates

*Planning dossier for the proof queue. Source: 2026-09-24 deep audit, frontier FT-04, queue
items 1-3 (`gMean` linearity, `withinCross_add_right`, `feSlope_add_smul`); verifier verdict
KEEP, grade A. Priority 2 in group g1. Lemma names checked with `#check` on the pinned
toolchain (Lean/mathlib v4.33.1), 2026-09-24.*

**A complete candidate assembled from the route in this dossier passed `verify.py` on 2026-09-24** (text checks, compile, leanchecker kernel replay, olean axiom probe `[Classical.choice, Quot.sound, propext]`, elaborated type identical): `staging/2026-09-24/_g1-scratch-proofs/FT04-feSlope-add-smul.lean`.

## 1. Goal

```lean
theorem feSlope_add_smul (grp : ι → κ) (w x y s : ι → ℝ) (c : ℝ) :
    feSlope grp w x (fun k => y k + c * s k) = feSlope grp w x y + c * feSlope grp w x s
```

in `namespace Plan.FT04`, `variable {ι κ : Type*} [Fintype ι] [DecidableEq κ]`, `open Finset`.
Fully qualified name: `Plan.FT04.feSlope_add_smul`. Imports: `Mathlib` only. **No hypotheses**:
the identity holds for all real weights and also when `withinSS grp w x = 0`.

## 2. Definitions (verbatim; must be kept verbatim)

```lean
noncomputable def gMean (grp : ι → κ) (w f : ι → ℝ) (e : κ) : ℝ :=
  (∑ k ∈ univ.filter (fun k => grp k = e), w k * f k) /
    ∑ k ∈ univ.filter (fun k => grp k = e), w k

noncomputable def withinCross (grp : ι → κ) (w x y : ι → ℝ) : ℝ :=
  ∑ k, w k * (x k - gMean grp w x (grp k)) * (y k - gMean grp w y (grp k))

noncomputable def withinSS (grp : ι → κ) (w x : ι → ℝ) : ℝ := withinCross grp w x x

noncomputable def feSlope (grp : ι → κ) (w x y : ι → ℝ) : ℝ :=
  withinCross grp w x y / withinSS grp w x
```

## 3. Proof route (three short steps; all three checked end to end in scratch on 2026-09-24,
compiling with axioms `[propext, Classical.choice, Quot.sound]`)

**Step 1, `gMean` is linear (tested, compiles):**

```lean
theorem gMean_add_smul (grp : ι → κ) (w y s : ι → ℝ) (c : ℝ) (e : κ) :
    gMean grp w (fun k => y k + c * s k) e = gMean grp w y e + c * gMean grp w s e := by
  unfold gMean
  have : ∑ k ∈ univ.filter (fun k => grp k = e), w k * (y k + c * s k)
      = ∑ k ∈ univ.filter (fun k => grp k = e), w k * y k
        + c * ∑ k ∈ univ.filter (fun k => grp k = e), w k * s k := by
    rw [mul_sum, ← sum_add_distrib]
    exact sum_congr rfl (fun k _ => by ring)
  rw [this, add_div, mul_div_assoc]
```

It needs no hypothesis: `(A + c * B) / D = A / D + c * (B / D)` holds for `D = 0` too
(`add_div`, `mul_div_assoc` are unconditional in a field).

**Step 2, `withinCross` is linear in its last argument:**

```lean
theorem withinCross_add_smul (grp : ι → κ) (w x y s : ι → ℝ) (c : ℝ) :
    withinCross grp w x (fun k => y k + c * s k)
      = withinCross grp w x y + c * withinCross grp w x s
```

Proof (checked):

```lean
  unfold withinCross
  simp only [gMean_add_smul]
  rw [mul_sum, ← sum_add_distrib]
  exact sum_congr rfl (fun k _ => by ring)
```

**Step 3, the target (checked):** `unfold feSlope` then
`rw [withinCross_add_smul, add_div, mul_div_assoc]`.

## 4. Lemmas (checked)

- `Finset.mul_sum : a * ∑ i ∈ s, f i = ∑ i ∈ s, a * f i`
- `Finset.sum_add_distrib : ∑ x ∈ s, (f x + g x) = ∑ x ∈ s, f x + ∑ x ∈ s, g x`
- `Finset.sum_congr : s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum f = s₂.sum g`
- `add_div : (a + b) / c = a / c + b / c`, `mul_div_assoc : a * b / c = a * (b / c)`
- tactics: `ring`, `simp only [...]`

## 5. Pitfalls

- Do NOT introduce `withinSS grp w x ≠ 0` or case-split on it: no division needs a
  nonzero denominator here; `field_simp` would demand one and stall.
- Do not unfold `gMean` inside `withinCross` before using Step 1: the fully unfolded goal
  (nested filtered sums with `⁻¹`) is hard for `ring_nf` (the battery attempt
  `unfold …; simp [...]; ring_nf` failed).
- The argument `fun k => y k + c * s k` appears as a lambda; Step 1's left side must match it
  syntactically (it does, as stated).
- Candidate may not add imports; keep the definitions and theorem signature verbatim.

## 6. Scope and provenance

- Two-axis tag prediction: relation PURE-MATH; definitions PURE-MATH; published PURE-MATH.
- Consumer: FT-01's physics binding (audit step 10): a change `c` of the `ln n_e` offset moves
  the ordinates of ion-stage lines by `c * s k` (`s` = ion-stage indicator), and this lemma makes
  the induced slope change exactly `c * feSlope grp w x s`. That binding is REDUCED and not
  part of this statement.
- Literature (whitelist rows 48, 50): Aguilera & Aragón 2007, Spectrochim. Acta B 62, 378;
  Aitken 1935, Proc. Roy. Soc. Edinburgh 55, 42.
- Novelty: 0 hits for `gMean|withinCross|withinSS|feSlope` in `CflibsFormal/` and `upstream/`
  on main (fb1681d); positive control `rg -c olsSlope CflibsFormal/OLS.lean` = 24.
- Tactic battery (simp, linarith, positivity, nlinarith, field_simp, aesop, exact?, and an
  unfold+simp+ring_nf attempt): none closes it.
