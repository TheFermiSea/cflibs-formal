# FT10-interceptDiff-noiseGain: the common-slope intercept difference is linear with gain 1/n_a + 1/n_b + (Ē_a − Ē_b)²/SS

*Planning dossier for the proof queue. Source: 2026-09-24 deep audit, frontier FT-10 item 6
(deterministic core of the log-ratio floor); verifier verdict KEEP, grade A. Priority 28 in
group g1. Names checked with `#check` on the pinned toolchain (Lean/mathlib v4.33.1). A complete
candidate following the route below passed `verify.py` (compile, leanchecker kernel replay,
axioms `[Classical.choice, Quot.sound, propext]`, elaborated type identical) on 2026-09-24:
`staging/2026-09-24/_g1-scratch-proofs/FT10-interceptDiff-noiseGain.lean`.*

**Change from the plan's scratch statement** (`_plan/stmts/FT10-interceptDiff-noiseGain.lean`):
the `let`-bound `SS`, `wa`, `wb` became named definitions (`pooledSS`, `idWeightA`, `idWeightB`),
and a first conjunct was added that ties the weights to the estimator
(`interceptDiff = ∑ idWeightA * ya + ∑ idWeightB * yb`, with `interceptDiff` and `commonSlope`
defined). Without it the theorem would be an identity about arbitrary-looking weights, and the
docstring's "this is the noise gain of d̂" would be unproved. Named definitions also let the
verifier's text check cover them (`verify.py`'s signature regex stops at the first `:=`, which a
`let` inside the statement would trigger early).

## 1. Goal

```lean
theorem interceptDiff_noiseGain [Nonempty ιa] [Nonempty ιb] (Ea : ιa → ℝ) (Eb : ιb → ℝ)
    (hSS : 0 < pooledSS Ea Eb) :
    (∀ (ya : ιa → ℝ) (yb : ιb → ℝ),
        interceptDiff Ea ya Eb yb
          = ∑ k, idWeightA Ea Eb k * ya k + ∑ k, idWeightB Ea Eb k * yb k) ∧
      ∑ k, idWeightA Ea Eb k ^ 2 + ∑ k, idWeightB Ea Eb k ^ 2
        = (1 : ℝ) / (Fintype.card ιa : ℝ) + (1 : ℝ) / (Fintype.card ιb : ℝ)
            + (mean Ea - mean Eb) ^ 2 / pooledSS Ea Eb
```

in `namespace Plan.FT10`, `variable {ιa ιb : Type*} [Fintype ιa] [Fintype ιb]`,
`open Finset CflibsFormal`. Fully qualified name: `Plan.FT10.interceptDiff_noiseGain`.
Imports: `Mathlib`, `CflibsFormal.OLS` (no others may be added).

## 2. Definitions

From `CflibsFormal.OLS` (read-only): `noncomputable def mean (f : ι → ℝ) : ℝ := (∑ k, f k) / (Fintype.card ι)`.

New (verbatim; must be kept verbatim):

```lean
noncomputable def pooledSS (Ea : ιa → ℝ) (Eb : ιb → ℝ) : ℝ :=
  ∑ k, (Ea k - mean Ea) ^ 2 + ∑ k, (Eb k - mean Eb) ^ 2

noncomputable def commonSlope (Ea ya : ιa → ℝ) (Eb yb : ιb → ℝ) : ℝ :=
  (∑ k, (Ea k - mean Ea) * (ya k - mean ya) + ∑ k, (Eb k - mean Eb) * (yb k - mean yb))
    / pooledSS Ea Eb

noncomputable def interceptDiff (Ea ya : ιa → ℝ) (Eb yb : ιb → ℝ) : ℝ :=
  (mean ya - commonSlope Ea ya Eb yb * mean Ea) - (mean yb - commonSlope Ea ya Eb yb * mean Eb)

noncomputable def idWeightA (Ea : ιa → ℝ) (Eb : ιb → ℝ) (k : ιa) : ℝ :=
  (1 : ℝ) / (Fintype.card ιa : ℝ) - (mean Ea - mean Eb) * (Ea k - mean Ea) / pooledSS Ea Eb

noncomputable def idWeightB (Ea : ιa → ℝ) (Eb : ιb → ℝ) (k : ιb) : ℝ :=
  -((1 : ℝ) / (Fintype.card ιb : ℝ)) - (mean Ea - mean Eb) * (Eb k - mean Eb) / pooledSS Ea Eb
```

## 3. Repo lemmas available (imported; exact signatures)

- `CflibsFormal.centered_sum_zero : ∀ [Nonempty ι] (E : ι → ℝ), ∑ k, (E k - mean E) = 0`
- `CflibsFormal.olsSlope_eq_centered` (pattern for dropping `mean y` from a centred cross sum)
- `CflibsFormal.olsSlope_noise_gain : 0 < ∑ k, (E k - mean E) ^ 2 → ∑ k, ((E k - mean E) / ∑ j, (E j - mean E) ^ 2) ^ 2 = 1 / ∑ k, (E k - mean E) ^ 2`
  (single-species analogue; not needed)

## 4. Proof route (checked)

Write `D = mean Ea − mean Eb`, `SS = pooledSS Ea Eb`, `n_a = card ιa`.

**Helpers (checked; stated over the section variable `ιa`, they generalize and apply to `ιb`
as well):**

```lean
theorem centered_cross [Nonempty ιa] (E y : ιa → ℝ) :
    ∑ k, (E k - mean E) * (y k - mean y) = ∑ k, (E k - mean E) * y k := by
  have h0 := centered_sum_zero E
  have : ∑ k, (E k - mean E) * (y k - mean y)
      = ∑ k, (E k - mean E) * y k - (∑ k, (E k - mean E)) * mean y := by
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  rw [this, h0, zero_mul, sub_zero]

theorem sum_sq_affine_centered [Nonempty ιa] (E : ιa → ℝ) (c0 c1 : ℝ) :
    ∑ k, (c0 + c1 * (E k - mean E)) ^ 2
      = (Fintype.card ιa : ℝ) * c0 ^ 2 + c1 ^ 2 * ∑ k, (E k - mean E) ^ 2 := by
  have h0 := centered_sum_zero E
  have : ∑ k, (c0 + c1 * (E k - mean E)) ^ 2
      = ∑ k, (c0 ^ 2 + (2 * c0 * c1) * (E k - mean E) + c1 ^ 2 * (E k - mean E) ^ 2) :=
    Finset.sum_congr rfl (fun k _ => by ring)
  rw [this, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    h0, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring
```

**Conjunct 1 (representation).** Show
`∑ idWeightA * ya = mean ya − D * (∑ (Ea − Ēa) * ya) / SS` and
`∑ idWeightB * yb = −mean yb − D * (∑ (Eb − Ēb) * yb) / SS` (termwise `ring` into
`(1/n_a) * ya k − D/SS * ((Ea k − Ēa) * ya k)`, then `sum_sub_distrib`, `← mul_sum`, and rewrite
ONLY `mean ya` with `have hm : mean ya = (∑ k, ya k) / (Fintype.card ιa : ℝ) := rfl`). Then
`unfold interceptDiff commonSlope`, `rw [centered_cross Ea ya, centered_cross Eb yb]`, `ring`.

**Conjunct 2 (noise gain).** `idWeightA k = c0 + c1 * (Ea k − Ēa)` with `c0 = 1/n_a`,
`c1 = −D/SS`; by `sum_sq_affine_centered`,
`∑ idWeightA² = n_a (1/n_a)² + (D/SS)² SS_a`; likewise
`∑ idWeightB² = n_b (1/n_b)² + (D/SS)² SS_b` with `c0 = −1/n_b`. Sum, use
`SS = SS_a + SS_b` (`rfl` for `pooledSS`), `field_simp` (with `n_a ≠ 0`, `n_b ≠ 0`, `SS ≠ 0`),
`rw [hSSdef]`, `ring`.

Nonzero facts: `(Fintype.card ιa : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero`
(needs `[Nonempty ιa]`); `pooledSS Ea Eb ≠ 0 := hSS.ne'`.

## 5. mathlib lemmas (checked)

`Finset.sum_congr`, `Finset.sum_add_distrib`, `Finset.sum_sub_distrib`, `Finset.mul_sum`,
`Finset.sum_mul`, `Finset.sum_const : ∑ _x ∈ s, b = s.card • b`, `Finset.card_univ`,
`nsmul_eq_mul : n • a = ↑n * a`, `Nat.cast_ne_zero`, `Fintype.card_ne_zero`; tactics `ring`,
`field_simp`.

## 6. Pitfalls

- `rw [mean]` unfolds the FIRST `mean` it meets (often `mean Ea`), not `mean ya`; this broke the
  first attempt. Rewrite `mean ya` with an explicit `rfl` equation.
- Keep `(1 : ℝ) / (Fintype.card ιa : ℝ)` as a real division; `Fintype.card` is `ℕ` and the casts
  are explicit in the statement.
- `commonSlope` centres the ordinates too; `centered_cross` removes `mean ya`, `mean yb`.
- `hSS` is used only for `field_simp` in conjunct 2 (on paper both conjuncts also hold at
  `SS = 0` by totalized division; not claimed).

## 7. Scope and provenance

- Two-axis tag prediction: relation PURE-MATH; definitions PURE-MATH; published PURE-MATH.
- Physics reading (REDUCED, landing docstring only): under uncorrelated homoscedastic ordinate
  noise, `Var d̂ = σ² (1/n_a + 1/n_b + (Ē_a − Ē_b)²/SS)`. `d̂` estimates
  `b_a − b_b = ln (F N_a / U_a) − ln (F N_b / U_b)`, so `ln (N_a / N_b)` also carries the
  temperature-dependent `ln (U_a / U_b)`. The variance statement over a `Sum` index and the BLUE
  property of `d̂` are separate FT-10 targets (items 7-8).
- Numerics: the representation and the gain were checked on 4862 random two-species designs
  (0 violations), and `d̂` matched the difference of the two intercepts of a generic
  least-squares fit with design `[1_a | 1_b | E]` on 200 random cases.
- Consumers: [backlog-id] (log-ratio mode), R6 pair selection (companion).
- Literature (whitelist rows 50, 69): Aitken 1935, Proc. Roy. Soc. Edinburgh 55, 42-48;
  Tognoni et al. 2010, Spectrochim. Acta B 65, 1-14.
- Novelty: 0 hits for `interceptDiff|pooledSS|commonSlope|idWeight` in `CflibsFormal/`,
  `upstream/` on main (fb1681d). `Robustness.lean` treats intercept differences as given
  measured numbers (`logRatioIntercept_stable`), with no common-slope estimator.
- Tactic battery (simp, linarith, positivity, nlinarith, field_simp, aesop, exact?, and an
  unfold+simp+ring_nf+field_simp attempt): none closes it.
