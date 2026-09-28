# FT10-wls-min-noiseGain: WLS attains the noise floor 1/wSS among linear unbiased slope estimators

*Planning dossier for the proof queue. Source: 2026-09-24 deep audit, frontier FT-10 items 1-3
(weight sums, equality part, weighted Cauchy–Schwarz); verifier verdict KEEP, grade A for the
deterministic core. Priority 18 in group g1. Names checked with `#check` on the pinned toolchain
(Lean/mathlib v4.33.1), 2026-09-24.*

**Statement audit (Mode B, 2026-09-24): fix applied, the goal changed.** The earlier goal proved
only that the WLS weights have gain `1/wSS` and that every unbiased `a` has gain `≥ 1/wSS`. It never
showed that the WLS weights are themselves unbiased, so "WLS attains the floor among linear
unbiased estimators" was unproved. The conclusion now starts with the conjunct
`∑ ω = 0 ∧ ∑ ω E = 1` (item 0). The pre-audit files are kept in
`staging/2026-09-24/_g4-pre-statement-audit/`.

**A complete candidate for the NEW goal passed `verify.py` on 2026-09-24** (text checks, compile,
leanchecker kernel replay, olean axiom probe `[Classical.choice, Quot.sound, propext]`, elaborated
type identical): `staging/2026-09-24/_g1-scratch-proofs/FT10-wls-min-noiseGain.lean`, verdict
`verdict-FT10-wls-min-noiseGain.json` next to it. The pre-audit candidate fails against the new
statement (`signature_identical: false`), as it should.

## 1. Goal

```lean
theorem wls_min_noiseGain {w E a : ι → ℝ} (hw : ∀ k, 0 < w k) (hSS : 0 < wSS w E)
    (ha0 : ∑ k, a k = 0) (ha1 : ∑ k, a k * E k = 1) :
    (∑ k, wlsWeight w E k = 0 ∧ ∑ k, wlsWeight w E k * E k = 1) ∧
      ∑ k, wlsWeight w E k ^ 2 / w k = 1 / wSS w E ∧ 1 / wSS w E ≤ ∑ k, a k ^ 2 / w k
```

The shape is `(P ∧ Q) ∧ (R ∧ S)`: item 0 (the WLS weights are linear-unbiased), item 1 (their
gain is `1/wSS`), item 2 (every unbiased `a` has gain `≥ 1/wSS`).

in `namespace Plan.FT10`, `variable {ι : Type*} [Fintype ι]`, `open Finset`. Fully qualified
name: `Plan.FT10.wls_min_noiseGain`. Imports: `Mathlib` only.

Meaning: `w k = 1/σ_k²` (line weights), `E` upper-level energies, `a` the weights of any linear
slope estimator unbiased for straight lines (`∑ a = 0`, `∑ a E = 1`). Noise gain = `∑ a²/w`.
The WLS weights are themselves unbiased, have gain exactly `1/wSS`, and no unbiased `a` does
better. This is a BLUE floor, not a Cramér–Rao bound (no new name may contain "crlb"). That
`∑ ω y` is the weighted-RSS-minimizing slope is not part of this goal (it is the one-group case
of FT-04 `feSlope_isMin`).

## 2. Definitions (verbatim; must be kept verbatim)

```lean
noncomputable def wMean (w E : ι → ℝ) : ℝ := (∑ k, w k * E k) / ∑ k, w k
noncomputable def wSS (w E : ι → ℝ) : ℝ := ∑ k, w k * (E k - wMean w E) ^ 2
noncomputable def wlsWeight (w E : ι → ℝ) (k : ι) : ℝ := w k * (E k - wMean w E) / wSS w E
```

## 3. Proof route (checked end to end in scratch, 2026-09-24; axioms
`[propext, Classical.choice, Quot.sound]`)

Write `d k := E k - wMean w E`, `S := wSS w E = ∑ w d²`.

**Item 0, helper (checked; place it after the definitions, before the theorem).** `S ≠ 0` gives
some `k0` with a nonzero term, hence `ι` is non-empty and `∑ w > 0`. Then
`∑ w d = ∑ w E − wMean · ∑ w = 0`, so `∑ ω = (∑ w d)/S = 0` and
`∑ ω E = (∑ w d² + wMean · ∑ w d)/S = S/S = 1`.

```lean
theorem wlsWeight_unbiased {w E : ι → ℝ} (hw : ∀ k, 0 < w k) (hSS : 0 < wSS w E) :
    ∑ k, wlsWeight w E k = 0 ∧ ∑ k, wlsWeight w E k * E k = 1 := by
  have hSne : wSS w E ≠ 0 := hSS.ne'
  obtain ⟨k0, -, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero
    (show ∑ k, w k * (E k - wMean w E) ^ 2 ≠ 0 from hSne)
  have hW : 0 < ∑ k, w k := Finset.sum_pos (fun k _ => hw k) ⟨k0, Finset.mem_univ _⟩
  have hc : ∑ k, w k * (E k - wMean w E) = 0 := by
    have : ∑ k, w k * (E k - wMean w E) = ∑ k, w k * E k - wMean w E * ∑ k, w k := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun k _ => by ring)
    rw [this, wMean, div_mul_cancel₀ _ hW.ne', sub_self]
  constructor
  · simp only [wlsWeight]; rw [← Finset.sum_div, hc, zero_div]
  · have : ∑ k, wlsWeight w E k * E k
        = (∑ k, w k * (E k - wMean w E) ^ 2 + wMean w E * ∑ k, w k * (E k - wMean w E))
          / wSS w E := by
      simp only [wlsWeight]
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_div]
      exact Finset.sum_congr rfl (fun k _ => by ring)
    rw [this, hc, mul_zero, add_zero]
    exact div_self hSne
```

Top level of the theorem: `refine ⟨wlsWeight_unbiased hw hSS, ?_, ?_⟩`, then the two bullets
below (the anonymous constructor flattens `⟨p, r, s⟩` into `⟨p, ⟨r, s⟩⟩`).

**Equality part.** Termwise `wlsWeight² / w = (w d / S)² / w = w d² / S²` (needs `w k ≠ 0`),
sum to `S / S² = 1 / S` (needs `S ≠ 0`).

```lean
  · have hterm : ∀ k, wlsWeight w E k ^ 2 / w k
        = w k * (E k - wMean w E) ^ 2 / wSS w E ^ 2 := by
      intro k
      have hwk := (hw k).ne'
      unfold wlsWeight
      field_simp
    simp only [hterm]
    rw [← Finset.sum_div]
    change wSS w E / wSS w E ^ 2 = 1 / wSS w E
    field_simp
```

**Inequality part (weighted Cauchy–Schwarz, no square roots).** First `∑ a d = 1`: it equals
`∑ a E − (∑ a) · wMean = 1 − 0`. Then Cauchy–Schwarz in the form
`Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul` with `r = a d`, `f = a²/w`, `g = w d²`
(`r² = f g` exactly, since `w ≠ 0`) gives `1 ≤ (∑ a²/w) · S`, i.e. `1/S ≤ ∑ a²/w`.

```lean
  · have hd : ∑ k, a k * (E k - wMean w E) = 1 := by
      have : ∑ k, a k * (E k - wMean w E) = ∑ k, a k * E k - (∑ k, a k) * wMean w E := by
        rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl (fun k _ => by ring)
      rw [this, ha1, ha0]; ring
    have hCS : (∑ k, a k * (E k - wMean w E)) ^ 2
        ≤ (∑ k, a k ^ 2 / w k) * ∑ k, w k * (E k - wMean w E) ^ 2 := by
      apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
      · intro k _; exact div_nonneg (sq_nonneg _) (hw k).le
      · intro k _; exact mul_nonneg (hw k).le (sq_nonneg _)
      · intro k _
        have hwk := (hw k).ne'
        apply le_of_eq
        field_simp
    rw [hd, one_pow] at hCS
    change 1 ≤ (∑ k, a k ^ 2 / w k) * wSS w E at hCS
    rw [div_le_iff₀ hSS]
    linarith
```

(Top level: `refine ⟨wlsWeight_unbiased hw hSS, ?_, ?_⟩` and the two bullets above.)

Alternative (Pythagorean) route, if Cauchy–Schwarz misbehaves: with `ω = wlsWeight`,
`∑ a ω / w = (∑ a d)/S = 1/S` and `∑ ω²/w = 1/S`, so
`∑ (a − ω)²/w = ∑ a²/w − 1/S ≥ 0`. This mirrors the repo's unweighted
`CflibsFormal.Alt.weight_sq_ge_noiseGain` (`Alt/GaussMarkov.lean:156`, not importable here).

## 4. mathlib lemmas (checked)

- `Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul : (∀ i ∈ s, 0 ≤ f i) → (∀ i ∈ s, 0 ≤ g i) → (∀ i ∈ s, r i ^ 2 ≤ f i * g i) → (∑ i ∈ s, r i) ^ 2 ≤ (∑ i ∈ s, f i) * ∑ i ∈ s, g i`
- `Finset.sum_mul_sq_le_sq_mul_sq : (∑ i ∈ s, f i * g i) ^ 2 ≤ (∑ i ∈ s, f i ^ 2) * ∑ i ∈ s, g i ^ 2`
  (needs square roots of `w`; avoid)
- `Finset.sq_sum_div_le_sum_sq_div : (∀ i ∈ s, 0 < g i) → (∑ i ∈ s, f i) ^ 2 / ∑ i ∈ s, g i ≤ ∑ i ∈ s, f i ^ 2 / g i` (Sedrakyan; another option)
- `Finset.sum_div : (∑ i ∈ s, f i) / a = ∑ i ∈ s, f i / a`, `Finset.sum_mul`,
  `Finset.sum_sub_distrib`, `Finset.sum_congr`
- `div_le_iff₀`, `div_nonneg`, `mul_nonneg`, `sq_nonneg`, `one_pow`; tactic `field_simp`
- item 0: `Finset.exists_ne_zero_of_sum_ne_zero`, `Finset.sum_pos`, `Finset.mul_sum`,
  `Finset.sum_add_distrib`, `div_mul_cancel₀`, `zero_div`, `div_self`

## 5. Pitfalls

- `wSS` and `wMean` are opaque definitions; `change` (or `unfold wSS`) is needed to see
  `∑ k, w k * (E k - wMean w E) ^ 2` as `wSS w E`. Do not unfold `wMean`.
- `field_simp` needs `w k ≠ 0` in context (`have hwk := (hw k).ne'`) and `wSS w E ≠ 0`
  (derivable from `hSS`).
- `hSS` is logically implied by `hw`, `ha0`, `ha1` (a constant `E` would give `∑ a E = 0`), but
  it is a hypothesis: use it directly.
- No `Nonempty ι` is available or needed; item 0 gets a line `k0` from `hSS` when it needs one.
- Candidate may not add imports; keep the definitions and theorem signature verbatim.

## 6. Scope and provenance

- Two-axis tag prediction: relation PURE-MATH; definitions PURE-MATH; published PURE-MATH. The
  noise-model reading (uncorrelated additive noise, `Var ε_k = 1/w k`) is REDUCED and belongs in
  the landing docstring; `gA` uncertainties are bias and must stay out of `w`.
- Homoscedastic twin on main: `CflibsFormal.Alt.weight_sq_ge_noiseGain` / `ols_is_blue`
  (`Alt/GaussMarkov.lean:156, :194`; the verifier recommends retagging `ols_is_blue` PURE-MATH).
- Consumers: BL-33/BL-32 (weighting), BL-07/F7 budget (companion).
- Literature (whitelist rows 50, 69): Aitken 1935, Proc. Roy. Soc. Edinburgh 55, 42-48;
  Tognoni et al. 2010, Spectrochim. Acta B 65, 1-14. Cramér 1946 and Rao 1945 are prose lineage
  only (no CRLB is proved).
- Novelty: 0 hits for `wMean|wSS|wlsWeight|wls_min_noiseGain|weighted least` in `CflibsFormal/`
  and `upstream/` on main (fb1681d); positive control `rg -c olsSlope CflibsFormal/OLS.lean` = 24.
- Tactic battery (simp, linarith, positivity, nlinarith, field_simp, aesop, exact?, and an
  unfold+field_simp+nlinarith attempt): none closes it. The battery ran on the pre-audit goal;
  the new goal contains that goal as its second conjunct, so no battery closes it either.
- Non-vacuity (statement audit, `/tmp/audit/mb/w_FT10_wls.lean`, exit 0): `Fin 3`,
  `E = (0,1,2)`, `w ≡ 1`, `a = (−1,1,0)`: `wSS = 2`, floor `1/2`, competitor gain `2` (strict).
  Heteroscedastic `w = (1,2,4)` gives `wSS = 26/7` and discharges every hypothesis.
- WLS identification: `∑ ω y` as the weighted-RSS-minimizing slope is the one-group case of
  FT-04 `feSlope` / `feSlope_isMin`; the landing should relate `wMean` to FT-04 `gMean`.
