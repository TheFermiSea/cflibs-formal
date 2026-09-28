# FT16-kernelLS-error-linfty: planning dossier

*Source: deep audit 2026-09-24 (`docs/research/audit-2026-09-24/REPORT.md` §5 FT-16, queue
decomposition item 3; KEEP, grade A). Group g3, priority 24. Toolchain: Lean / mathlib v4.33.1 (the
built `lean-main` checkout). Every Lean snippet below was compiled against that checkout on
2026-09-24 under the statement's own imports (`Mathlib` only).*

## 1. Goal

Statement file: `statement.lean`, namespace `Plan.FT16`, imports **`Mathlib` only**,
`open Finset Matrix`, `variable {P L : Type*} [Fintype P] [Fintype L] [DecidableEq L]`.

```lean
theorem kernelLS_error_linfty [Nonempty L] (K Kt : Matrix P L ℝ) (I Ihat : L → ℝ) (η : P → ℝ)
    {δ : ℝ} (hδ : 0 < δ)
    (hdom : ∀ k, δ + ∑ j ∈ univ.erase k, |(Kᵀ * K) k j| ≤ |(Kᵀ * K) k k|)
    (hnormal : (Kᵀ * K).mulVec Ihat = Kᵀ.mulVec (Kt.mulVec I + η)) (l : L) :
    |Ihat l - I l|
      ≤ (univ.sup' univ_nonempty fun k => |(Kᵀ.mulVec ((Kt - K).mulVec I + η)) k|) / δ
```

Physics reading: pixels `P`, lines `L`; data `Kt·I + η`; the extractor solves the normal equations
with an assumed kernel `K`; a Gram-matrix diagonal-dominance margin `δ` bounds every intensity
error by the misspecification-plus-noise residual over `δ`.

## 2. Definitions

None new. `Matrix.mulVec`, `Matrix.transpose` (`ᵀ`), `Finset.sup'`, `Finset.univ_nonempty` are
mathlib. `M *ᵥ x` is notation for `M.mulVec x` (same term).

## 3. Proof route (two helpers, then three lines; all compiled)

1. **Error equation.** `(KᵀK)(Î − I) = Kᵀ((Kt − K)I + η)` from `hnormal` by `mulVec` linearity.
2. **Row-diagonal-dominance ℓ∞ lemma** (the classical diagonal-dominance bound; citation pending
   citation-integrity, do not cite a paper): for `M` with `δ + ∑_{j≠k} |M k j| ≤ |M k k|`,
   `|x i| ≤ max_k |(M x)_k| / δ`. Proof: take `i0` maximising `|x i|`; row `i0` gives
   `δ·|x i0| ≤ |(M x) i0|`.
3. Apply 2 to `M := KᵀK`, `x := Î − I`, rewrite with 1 and `Pi.sub_apply`.

Helpers (paste inside `namespace Plan.FT16`, after the `variable` line, before the target). The
first is the audit's `frontier-mathlib/Varah.lean` lemma, re-typed for `L`:

```lean
theorem linfty_le_of_rowDiagDominant [Nonempty L]
    (A : Matrix L L ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hdom : ∀ k, δ + ∑ j ∈ univ.erase k, |A k j| ≤ |A k k|) (x : L → ℝ) :
    ∀ i, |x i| ≤ (univ.sup' univ_nonempty fun k => |(A *ᵥ x) k|) / δ := by
  intro i
  obtain ⟨i0, -, hi0⟩ := Finset.exists_max_image univ (fun i => |x i|) univ_nonempty
  have hsplit : (A *ᵥ x) i0 = A i0 i0 * x i0 + ∑ j ∈ univ.erase i0, A i0 j * x j := by
    simp only [mulVec, dotProduct]
    rw [← Finset.add_sum_erase _ _ (mem_univ i0)]
  have hrest : |∑ j ∈ univ.erase i0, A i0 j * x j|
      ≤ (∑ j ∈ univ.erase i0, |A i0 j|) * |x i0| := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum (fun j _ => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hi0 j (mem_univ j)) (abs_nonneg _)
  have hkey : δ * |x i0| ≤ |(A *ᵥ x) i0| := by
    have h1 : |A i0 i0 * x i0| ≤ |(A *ᵥ x) i0| + |∑ j ∈ univ.erase i0, A i0 j * x j| := by
      have hA : A i0 i0 * x i0 = (A *ᵥ x) i0 - ∑ j ∈ univ.erase i0, A i0 j * x j := by
        rw [hsplit]; ring
      rw [hA]
      exact abs_sub _ _
    rw [abs_mul] at h1
    have h2 := mul_le_mul_of_nonneg_right (hdom i0) (abs_nonneg (x i0))
    nlinarith [h1, h2, hrest]
  have hsup : |(A *ᵥ x) i0| ≤ univ.sup' univ_nonempty fun k => |(A *ᵥ x) k| :=
    Finset.le_sup' (fun k => |(A *ᵥ x) k|) (mem_univ i0)
  rw [le_div_iff₀ hδ]
  nlinarith [hi0 i (mem_univ i), hkey, hsup, abs_nonneg (x i)]

omit [DecidableEq L] in
theorem normal_error_identity (K Kt : Matrix P L ℝ) (I Ihat : L → ℝ) (η : P → ℝ)
    (hnormal : (Kᵀ * K).mulVec Ihat = Kᵀ.mulVec (Kt.mulVec I + η)) :
    (Kᵀ * K).mulVec (Ihat - I) = Kᵀ.mulVec ((Kt - K).mulVec I + η) := by
  rw [Matrix.mulVec_sub, hnormal, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_sub]
  abel
```

Target body:

```lean
  have h := linfty_le_of_rowDiagDominant (Kᵀ * K) hδ hdom (Ihat - I) l
  rw [normal_error_identity K Kt I Ihat η hnormal, Pi.sub_apply] at h
  exact h
```

(`omit [DecidableEq L] in` only silences the unused-section-variable linter; without it the file
still compiles with a warning.)

## 4. Mathlib lemmas (all resolved in v4.33.1; `open Finset Matrix` is in effect)

`Finset.exists_max_image (s) (f) (h : s.Nonempty) : ∃ x ∈ s, ∀ x' ∈ s, f x' ≤ f x`,
`Finset.le_sup' (f) (h : b ∈ s) : f b ≤ s.sup' _ f`,
`Finset.add_sum_erase (s) (f) (h : a ∈ s) : f a + ∑ x ∈ s.erase a, f x = ∑ x ∈ s, f x`,
`Finset.abs_sum_le_sum_abs (f) (s) : |∑ i ∈ s, f i| ≤ ∑ i ∈ s, |f i|`,
`abs_sub (a b) : |a - b| ≤ |a| + |b|`, `abs_mul`, `le_div_iff₀`,
`Matrix.mulVec_mulVec (v) (M) (N) : M.mulVec (N.mulVec v) = (M * N).mulVec v`,
`Matrix.sub_mulVec`, `Matrix.mulVec_sub`, `Matrix.mulVec_add`, `Pi.sub_apply`,
`Matrix.mulVec`, `dotProduct` (unfolded in `hsplit`). Related (not needed): the root-namespace
Gershgorin lemma `det_ne_zero_of_sum_row_lt_diag` (`Mathlib/LinearAlgebra/Matrix/Gershgorin.lean:63`),
which gives invertibility of `KᵀK` from the same margin (the audit's C16′ ⇒ C16 follow-up).

## 5. Pitfalls and verifier rules

- The rewrite with `normal_error_identity` happens under the `sup'` lambda; it works because the
  rewritten term does not mention the bound variable.
- `abs_sub` in this mathlib is the triangle inequality `|a − b| ≤ |a| + |b|` (not `abs_sub_comm`).
- Keep the statement header verbatim (`import Mathlib` only, no new imports; `open Finset Matrix`;
  `namespace Plan.FT16`; the `variable` line) and the target signature text up to `:=`; state it
  with `theorem`; do not name a helper `kernelLS_error_linfty'`. `omit … in` is allowed.
  Forbidden: `sorry`, `admit`, `native_decide`, `axiom`, `macro`/`syntax`/`elab`, `#`-commands,
  `set_option` other than heartbeat/recursion limits.

## 6. Scope, literature, consumers

Relation PURE-MATH on abstract real matrices; no physics definitions; published PURE-MATH. The
physics reading (optically thin, additive line profiles, kernel fixed per solver step) is REDUCED
and stays in prose. The numerator is an assumed input; only `δ` is runtime-checkable. Literature:
the diagonal-dominance ℓ∞ bound is classical, but the audit's source (a 1975 linear-algebra paper)
is **not on the citation whitelist**; cite nothing until citation-integrity whitelists it.
Consumers: BL-28, BL-27, BL-29, BL-31, R3-01, BL-49, the spec Phase 6 K8 gain. The landing module
depends on SpectrometerForward (spec 03 §3); this abstract statement does not.
