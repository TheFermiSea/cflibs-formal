# FT01-exists-weights-iff: a unit-invariant weighted gate for the 2×2 contraction exists iff a<1, d<1, bc<(1−a)(1−d)

*Planning dossier for the proof queue. Source: 2026-09-24 deep audit, frontier FT-01 part (d)
("weights ⇔"; the audit's decomposition item 5: `weights_of_gate` ⇐ done in evidence,
`gate_of_weights` ⇒ open). Verifier verdict on FT-01: REVISE; for this item "exists_weights_iff,
both directions given b, c ≥ 0" is confirmed and the unused `ha`/`hd` were dropped. Priority 9
in group g1. Lemma names checked with `#check` on the pinned toolchain (v4.33.1), 2026-09-24.*

**A complete candidate assembled from the route in this dossier passed `verify.py` on 2026-09-24** (text checks, compile, leanchecker kernel replay, olean axiom probe `[Classical.choice, Quot.sound, propext]`, elaborated type identical): `staging/2026-09-24/_g1-scratch-proofs/FT01-exists-weights-iff.lean`.

## 1. Goal

```lean
theorem exists_weights_iff {a b c d : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c) :
    (∃ wT wn : ℝ, 0 < wT ∧ 0 < wn ∧ max (a + b * wn / wT) (c * wT / wn + d) < 1)
      ↔ (a < 1 ∧ d < 1 ∧ b * c < (1 - a) * (1 - d))
```

in `namespace Plan.FT01`. Fully qualified name: `Plan.FT01.exists_weights_iff`. Imports:
`Mathlib` only. No definitions. Parsing: `b * wn / wT` is `(b * wn) / wT`, and
`c * wT / wn` is `(c * wT) / wn`.

Meaning: `a, b, c, d ≥ 0`-type Lipschitz coefficients of a joint update of temperature and
electron density; `wT, wn` rescale the two coordinates. The weighted row-sum gate exists iff the
unit-invariant 2×2 condition holds (for nonnegative matrices this is the spectral-radius-< 1
condition of `[[a, b], [c, d]]`, but no matrix theory is needed).

## 2. Proof route

Put `r := wn / wT > 0`. Then `b * wn / wT = b * r` and `c * wT / wn = c / r`.

**(⇒)** (checked in scratch on v4.33.1; this exact block compiles as the `mp` direction):

```lean
  rintro ⟨wT, wn, hT, hn, h⟩
  rw [max_lt_iff] at h
  obtain ⟨h1, h2⟩ := h
  set u := b * wn / wT with hu_def
  set v := c * wT / wn with hv_def
  have hu : 0 ≤ u := div_nonneg (mul_nonneg hb hn.le) hT.le
  have hv : 0 ≤ v := div_nonneg (mul_nonneg hc hT.le) hn.le
  have huv : u * v = b * c := by
    rw [hu_def, hv_def]; field_simp
  have ha1 : a < 1 := by linarith
  have hd1 : d < 1 := by linarith
  refine ⟨ha1, hd1, ?_⟩
  rw [← huv]
  nlinarith [mul_pos (sub_pos.2 h1) (sub_pos.2 hd1), mul_nonneg hu (sub_pos.2 h2).le]
```

Why it works: `(1 - a)(1 - d) - u v = (1 - a - u)(1 - d) + u (1 - d - v)` with
`1 - a - u > 0`, `1 - d > 0`, `u ≥ 0`, `1 - d - v > 0`. The battery's plain `nlinarith`
(without `huv` and the product hints) failed, so the explicit `u`, `v`, `huv` matter.

**(⇐)** From `h1 : a < 1`, `h2 : d < 1`, `h3 : b * c < (1 - a) * (1 - d)` produce `r > 0`
with `a + b * r < 1` and `c / r + d < 1`, then use `wT := 1`, `wn := r` and simplify
`b * r / 1 = b * r`, `c * 1 / r = c / r` (`div_one`, `mul_one`), finishing with
`max_lt_iff.2 ⟨_, _⟩`.

The constructive helper below is **checked** (compiles on v4.33.1, axioms
`[propext, Classical.choice, Quot.sound]`; it is the audit's `weights_of_gate` from
`evidence/frontier-proposer/Proofs2.lean:56-84` with the unused `ha`, `hd` removed). Paste it
into the candidate before the theorem:

```lean
theorem weights_of_gate {a b c d : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h1 : a < 1) (h2 : d < 1) (h3 : b * c < (1 - a) * (1 - d)) :
    ∃ r : ℝ, 0 < r ∧ a + b * r < 1 ∧ c / r + d < 1 := by
  have hd1 : 0 < 1 - d := by linarith
  have ha1 : 0 < 1 - a := by linarith
  rcases hb.eq_or_lt with hb0 | hbpos
  · subst hb0
    refine ⟨c / (1 - d) + 1, by positivity, by linarith, ?_⟩
    have hr : 0 < c / (1 - d) + 1 := by positivity
    rw [div_add' _ _ _ hr.ne', div_lt_one hr]
    have : c = c / (1 - d) * (1 - d) := by field_simp
    nlinarith
  · set r := (c / (1 - d) + (1 - a) / b) / 2
    have hlo : c / (1 - d) < (1 - a) / b := by
      rw [div_lt_div_iff₀ hd1 hbpos]; nlinarith
    have hr : 0 < r := by
      have : 0 ≤ c / (1 - d) := by positivity
      have : 0 < (1 - a) / b := by positivity
      simp only [r]; linarith
    refine ⟨r, hr, ?_, ?_⟩
    · have : r < (1 - a) / b := by simp only [r]; linarith
      have := (lt_div_iff₀ hbpos).mp this
      linarith
    · have : c / (1 - d) < r := by simp only [r]; linarith
      have h' : c < r * (1 - d) := by rwa [div_lt_iff₀ hd1] at this
      have : c / r < 1 - d := by rw [div_lt_iff₀ hr]; linarith
      linarith
```

Idea behind the witness: with `b > 0`, any `r` strictly between `c / (1 - d)` and
`(1 - a) / b` works, and that interval is non-empty exactly because `b c < (1 - a)(1 - d)`;
with `b = 0`, any `r > c / (1 - d)` works.

## 3. Lemmas (checked)

- `max_lt_iff : max b c < a ↔ b < a ∧ c < a`
- `div_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a / b`, `mul_nonneg`, `mul_pos`, `sub_pos`
- `lt_div_iff₀ : 0 < c → (a < b / c ↔ a * c < b)`, `div_lt_iff₀ : 0 < c → (b / c < a ↔ b < a * c)`
- `div_lt_one : 0 < b → (a / b < 1 ↔ a < b)`, `div_lt_div_iff₀`, `div_add'`
- tactics: `field_simp`, `nlinarith`, `linarith`, `positivity`

## 4. Pitfalls

- `max` must be split with `max_lt_iff` (not `lt_max_iff`, which is the other direction).
- The ⇒ direction genuinely needs `hb`, `hc`: with `b < 0`, `a` can exceed 1 (e.g.
  `a = 5, b = -10, c = d = 0, wT = wn = 1`). Do not try to drop them.
- `nlinarith` does not see through divisions: introduce `u`, `v` and the product identity
  `u * v = b * c` explicitly.
- No imports may be added; the theorem signature must stay verbatim; helper lemmas are fine.

## 5. Scope and provenance

- Two-axis tag prediction: relation PURE-MATH; no definitions used; published PURE-MATH.
- Consumer: the existing spine `CflibsFormal.jointOuterContraction_box`
  (`SahaEquilibrium.lean:1585`, gate `hq : max (a + b) (c + d) < 1`, with hypotheses
  `0 ≤ a`, `0 ≤ b`, `0 ≤ c`, `0 ≤ d`). Audit finding PS-10: this unweighted gate is not
  unit-invariant; with T in eV and n_e in cm⁻³ the coefficient `c` is of order 1e18 and the gate
  always fails. Rescaling `n_e` by `s` maps `b ↦ b / s`, `c ↦ s * c`, leaving `a`, `d`, `b * c`
  unchanged. A follow-up target (`jointOuterContraction_weighted`, not this one) applies the
  spine in rescaled coordinates.
- Non-vacuity: `a = d = 1/2, b = 100, c = 1/1000` fails the unweighted gate but satisfies the
  right-hand side (`b c = 1/10 < 1/4`).
- Literature: pure real algebra. The loop it serves is the multi-element Saha–Boltzmann
  iteration of Aguilera & Aragón 2007, Spectrochim. Acta B 62, 378 (whitelist row 48).
- Novelty: 0 hits for `exists_weights|weights_of_gate|gate_of_weights` in `CflibsFormal/` and
  `upstream/` on main (fb1681d). The ⇐ half exists only in the audit's evidence scratch file.
- Tactic battery (simp, linarith, positivity, nlinarith, field_simp, aesop, exact?, and a
  `constructor`/`nlinarith` attempt): none closes it.
