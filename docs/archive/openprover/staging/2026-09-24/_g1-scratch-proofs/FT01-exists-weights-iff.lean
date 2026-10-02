import Mathlib

/-!
# FT-01 (part d): a unit-invariant weighted gate for the joint (T, n_e) contraction

Staged queue target, 2026-09-24 audit, frontier FT-01 (pure-mathematics item "weights ⇔").
Real-number algebra only; no definitions.
-/

namespace Plan.FT01

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

/-- **FT-01(d): when a weighted row-sum gate exists for a 2×2 Lipschitz coupling.**
Let `a, b, c, d` be the two-variable Lipschitz coefficients of a joint update
`(T, n) ↦ (fT T n, fNe T n)`: `|ΔfT| ≤ a|ΔT| + b|Δn|` and `|ΔfNe| ≤ c|ΔT| + d|Δn|`.
Measuring `T` in units of `wT` and `n` in units of `wn` (positive scale factors) turns these
into `|ΔfT| ≤ a|ΔT| + b(wn/wT)|Δn|` and `|ΔfNe| ≤ c(wT/wn)|ΔT| + d|Δn|`. The theorem says that
some choice of positive scales makes the weighted row-sum gate
`max (a + b * wn / wT) (c * wT / wn + d) < 1` hold iff `a < 1`, `d < 1` and
`b * c < (1 - a) * (1 - d)`.

Why it matters: the existing spine `jointOuterContraction_box` (`SahaEquilibrium.lean`) is gated
by the unweighted row sums `max (a + b) (c + d) < 1`. That gate depends on the units: with
`T` in eV and `n_e` in cm⁻³ the off-diagonal coefficients differ by many orders of magnitude,
and the audit found (PS-10) that the gate always fails in those units. Rescaling `n_e` by `s`
sends `b ↦ b / s` and `c ↦ s * c`, so `a`, `d` and `b * c` are unit-invariant, and so is the
right-hand side here. A contraction certificate can therefore test the right-hand side and then
apply `jointOuterContraction_box` in the rescaled coordinates. Example: `a = d = 1/2`, `b = 100`,
`c = 1/1000` fails the unweighted gate (`a + b > 1`) but satisfies `b * c = 1/10 < 1/4`.

Hypotheses. `hb : 0 ≤ b` and `hc : 0 ≤ c` are needed for (⇒): with `b < 0` the weighted row
`a + b * wn / wT` can be below `1` although `a ≥ 1` (e.g. `a = 5`, `b = -10`, `c = d = 0`,
`wT = wn = 1`). Lipschitz coefficients are nonnegative, so these hypotheses are free in use.
No sign condition on `a` or `d` is needed (the audit's verifier dropped the unused `0 ≤ a`,
`0 ≤ d` from the constructive direction).

Scope, two-axis prediction: relation PURE-MATH; no definitions are used; published tag
PURE-MATH. Whether the real CF-LIBS legs satisfy the Lipschitz bounds, and with which
coefficients, is not claimed here.

Literature: none needed (real-number algebra). The joint (T, n_e) iteration it serves is the
multi-element Saha–Boltzmann loop of Aguilera & Aragón 2007 (Spectrochim. Acta B 62, 378). -/
theorem exists_weights_iff {a b c d : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c) :
    (∃ wT wn : ℝ, 0 < wT ∧ 0 < wn ∧ max (a + b * wn / wT) (c * wT / wn + d) < 1)
      ↔ (a < 1 ∧ d < 1 ∧ b * c < (1 - a) * (1 - d)) := by
  constructor
  · rintro ⟨wT, wn, hT, hn, h⟩
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
  · rintro ⟨h1, h2, h3⟩
    obtain ⟨r, hr, har, hcr⟩ := weights_of_gate hb hc h1 h2 h3
    refine ⟨1, r, one_pos, hr, ?_⟩
    rw [max_lt_iff]
    constructor
    · simpa using har
    · simpa using hcr

end Plan.FT01
