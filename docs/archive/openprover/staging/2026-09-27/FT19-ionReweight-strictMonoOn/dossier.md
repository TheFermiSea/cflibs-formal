# FT19-ionReweight-strictMonoOn: the ion zone reweight is strictly increasing in `T`

Planning dossier for the proof queue (2026-09-24 audit, frontier FT-19, REVISE verdict applied).
Written for a planner who cannot open the repository. Every repo definition and lemma is
quoted, and every Mathlib name was checked with `#check` against the pinned Mathlib (v4.33.1).

## 1. Goal

```lean
import Mathlib
import CflibsFormal.SahaStability

open CflibsFormal

namespace Plan.FT19

noncomputable def ionReweight (kB me h chi ne T : ℝ) : ℝ :=
  2 * thermalBracket kB T me h ^ (3/2 : ℝ) * Real.exp (-chi / (kB * T)) / ne

theorem ionReweight_strictMonoOn {kB me h chi ne : ℝ} (hkB : 0 < kB) (hme : 0 < me)
    (hh : 0 < h) (hchi : 0 ≤ chi) (hne : 0 < ne) :
    StrictMonoOn (ionReweight kB me h chi ne) (Set.Ioi 0) := by
  sorry
```

Keep the def and the signature verbatim; helper lemmas may be added. `CflibsFormal.SahaStability`
brings in `CflibsFormal.Saha` (where `thermalBracket` lives) and `thermalBracket_strictMono`.
Parsing: `thermalBracket kB T me h ^ (3/2 : ℝ)` is `(thermalBracket kB T me h) ^ (3/2 : ℝ)`
(`Real.rpow`); `-chi / (kB * T)` is `(-chi) / (kB * T)`.

## 2. Repo definition (namespace `CflibsFormal`, `Saha.lean:45`)

```lean
noncomputable def thermalBracket (kB T me h : ℝ) : ℝ :=
  (2 * Real.pi * me * kB * T) / h ^ 2
```

## 3. Repo lemmas (signatures checked)

- `thermalBracket_pos {kB T me h : ℝ} (hkB : 0 < kB) (hT : 0 < T) (hme : 0 < me) (hh : 0 < h) :
  0 < thermalBracket kB T me h` (`Saha.lean`)
- `thermalBracket_strictMono {kB me h Ta Tb : ℝ} (hkB : 0 < kB) (hme : 0 < me) (hh : 0 < h)
  (hab : Ta < Tb) : thermalBracket kB Ta me h < thermalBracket kB Tb me h`
  (`SahaStability.lean:694`)

## 4. Proof route

`intro T1 hT1 T2 hT2 hlt`, `simp only [Set.mem_Ioi] at hT1 hT2`, `unfold ionReweight`.
Write `X t := thermalBracket kB t me h ^ (3/2 : ℝ)`, `Y t := Real.exp (-chi / (kB * t))`.
1. `X T1 < X T2`: `Real.rpow_lt_rpow (thermalBracket_pos hkB hT1 hme hh).le
   (thermalBracket_strictMono hkB hme hh hlt) (by norm_num)`.
2. `Y T1 ≤ Y T2`: `Real.exp_le_exp.mpr`; goal `-chi / (kB * T1) ≤ -chi / (kB * T2)`;
   `rw [neg_div, neg_div, neg_le_neg_iff]`; then
   `div_le_div_of_nonneg_left hchi (mul_pos hkB hT1) (mul_le_mul_of_nonneg_left hlt.le hkB.le)`.
3. `2 * X T1 * Y T1 < 2 * X T2 * Y T2`:
   `mul_lt_mul_of_lt_of_le_of_nonneg_of_pos (h₁ : 2 * X T1 < 2 * X T2) h2 (nonneg) (Y T2 > 0)`
   with `h₁` by `linarith`, positivity from `Real.rpow_pos_of_pos`, `Real.exp_pos`.
4. Divide by `ne`: `div_lt_div_of_pos_right h3 hne`.

## 5. Mathlib lemmas (signatures checked)

- `Real.rpow_lt_rpow : 0 ≤ x → x < y → 0 < z → x ^ z < y ^ z`; `Real.rpow_pos_of_pos : 0 < x →
  ∀ y, 0 < x ^ y`
- `Real.exp_le_exp : exp x ≤ exp y ↔ x ≤ y`; `Real.exp_pos x : 0 < exp x`
- `neg_div (a b) : -b / a = -(b / a)`; `neg_le_neg_iff : -a ≤ -b ↔ b ≤ a`
- `div_le_div_of_nonneg_left : 0 ≤ a → 0 < c → c ≤ b → a / b ≤ a / c`
- `mul_le_mul_of_nonneg_left : b ≤ c → 0 ≤ a → a * b ≤ a * c`
- `mul_lt_mul_of_lt_of_le_of_nonneg_of_pos : a < b → c ≤ d → 0 ≤ a → 0 < d → a * c < b * d`
- `mul_lt_mul'' : a < b → c < d → 0 ≤ a → 0 ≤ c → a * c < b * d`
- `div_lt_div_of_pos_right : a < b → 0 < c → a / c < b / c`

## 6. Pitfalls

- Strictness comes only from `θ^{3/2}`; the exponential factor is merely nondecreasing (it is
  constant when `χ = 0`). Do not try to make the exponential strict.
- Do not route through `sahaFactor_strictMonoOn_temp`: it needs `∀ k, EZ k ≤ chi` and carries
  partition functions that `ionReweight` does not have (that was the verdict's reason (1)).
- `StrictMonoOn f s` unfolds to `∀ a ∈ s, ∀ b ∈ s, a < b → f a < f b`.
- Budget: low. Expect 15-25 lines.

## 7. Satisfiability witness

`kB = me = h = ne = 1`, `chi = 1` satisfy all hypotheses; the conclusion (strict increase on
all of `(0, ∞)`) is a genuine claim, not vacuous. `chi = 0` is also admitted (then only
`θ^{3/2}` varies).

## 8. Scope

Relation tag PURE-MATH (monotonicity of an explicit real function). Physics reading REDUCED:
`ionReweight` is the ion/neutral zone-weight ratio only under uniform `n_e` and per-zone LTE
Saha balance (verdict evidence `ion_zoneWeight_eq`, not on main). Saha–Eggert: Griem, Plasma
Spectroscopy (1964). Not a claim about measurement accuracy.
