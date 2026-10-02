# FT14-source-eq-planck: a Kirchhoff-consistent line opacity has the Planck source function

Planning dossier (2026-09-24 audit, frontier FT-14 (i), verdict REVISE with (i) kept, grade A).
Written for a planner who cannot open the repository. Every Mathlib name was checked with
`#check` against the pinned Mathlib (v4.33.1). **Status: proved in scratch (axioms
`propext, Classical.choice, Quot.sound`); hand-land candidate at
`_hand-land/FT14-source-eq-planck.proof.lean`. Do not queue unless hand-landing fails.**

## 1. Goal (only `import Mathlib`; no repo definitions)

```lean
namespace Plan.FT14

noncomputable def lineOpacity (κ0 nl x : ℝ) : ℝ := κ0 * nl * (1 - Real.exp (-x))

noncomputable def lineEmissivity (ε0 nu : ℝ) : ℝ := ε0 * nu

theorem source_eq_planck {κ0 ε0 B0 nl nu x gu gl : ℝ} (hx : 0 < x) (hκ : 0 < κ0) (hnl : 0 < nl)
    (hpop : nu / nl = gu / gl * Real.exp (-x)) (hein : ε0 * gu / gl = κ0 * B0) :
    lineEmissivity ε0 nu / lineOpacity κ0 nl x = B0 / (Real.exp x - 1) := by
  sorry
```

Keep both defs and the signature verbatim; helper lemmas may be added.

## 2. Mathematics

From `hpop`, `nu = (gu/gl) e^{-x} nl`. Then `ε0 nu = nl e^{-x} (ε0 gu/gl) = κ0 B0 nl e^{-x}` by
`hein`. Divide by `κ0 nl (1 - e^{-x})`: `B0 e^{-x}/(1 - e^{-x}) = B0/(e^x - 1)`.

## 3. Lemmas (checked)

- `div_eq_iff : b ≠ 0 → (a / b = c ↔ a = c * b)`
- `Real.exp_neg : Real.exp (-x) = (Real.exp x)⁻¹`
- `Real.add_one_lt_exp : x ≠ 0 → x + 1 < Real.exp x` (gives `Real.exp x - 1 > 0`)
- tactics: `linear_combination`, `field_simp`

## 4. Route (the scratch proof, 10 lines)

1. `hnu : nu = gu / gl * Real.exp (-x) * nl := (div_eq_iff hnl.ne').mp hpop`.
2. `hnum : ε0 * nu = κ0 * B0 * nl * Real.exp (-x)` by `rw [hnu]` then
   `linear_combination (nl * Real.exp (-x)) * hein`.
3. `Real.exp x - 1 ≠ 0` from `Real.add_one_lt_exp hx.ne'`; `κ0 ≠ 0`, `nl ≠ 0` from `hκ`, `hnl`.
4. `unfold lineEmissivity lineOpacity; rw [hnum, Real.exp_neg]; field_simp` closes the goal.

Pitfall: `ε0 * gu / gl` is `(ε0 * gu) / gl`; `linear_combination` handles it (ring normal form).

## 5. Scope and hypotheses

EXACT given `hpop` (LTE Boltzmann ratio of one transition, `x = hν/(k_B T)`) and `hein` (the
Einstein-Milne relation, `B0 = 2hν³/c²` in the frequency form, owner decision D19). The identity
is algebra; the physics is in the two hypotheses. `κ0`, `ε0`, `B0` stay abstract. `hx`, `hnl`
are physical-domain guards: under Lean's `a / 0 = 0` the identity also holds at `x = 0` and
`nl = 0`, but the proof consumes them (`hx.ne'`, `hnl.ne'`). `hκ` is necessary (at `κ0 = 0`,
`hein` leaves `B0` free while the left side is `0`). Witness: `x = κ0 = nl = gu = gl = ε0 =
B0 = 1`, `nu = exp (-1)` (checked in Lean). Literature: Griem 1997 (Kirchhoff's law in LTE).
