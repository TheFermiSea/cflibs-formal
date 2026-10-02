# FT17-neutralityNewton-enclosure: one Newton step brackets the charge-neutrality root

Planning dossier for the proof queue (2026-09-24 audit, frontier FT-17, "remaining steps").
Written for a planner who cannot open the repository: every repo definition and lemma the proof
needs is quoted verbatim below, and every Mathlib name was checked with `#check` against the
pinned Mathlib (Lean/Mathlib v4.33.1) on 2026-09-24.

## 1. Goal

```lean
import Mathlib
import CflibsFormal.SahaEquilibrium

open Finset CflibsFormal

namespace Plan.FT17

variable {ι : Type*} [Fintype ι]

noncomputable def neutralityNewton (S Ntot : ι → ℝ) (x : ℝ) : ℝ :=
  x - (x - multiElementIonized S Ntot x) / (1 + ∑ s, Ntot s * S s / (x + S s) ^ 2)

theorem neutralityNewton_enclosure {S Ntot : ι → ℝ} {x r : ℝ} (hS : ∀ s, 0 < S s)
    (hN : ∀ s, 0 ≤ Ntot s) (hx : 0 ≤ x) (hr : 0 ≤ r)
    (hfix : r = multiElementIonized S Ntot r) :
    neutralityNewton S Ntot x ≤ r ∧
      r ≤ multiElementIonized S Ntot (neutralityNewton S Ntot x) := by
  sorry
```

The audited file is `statement.lean` in this directory (docstrings omitted above). The
candidate must keep the definition and the theorem signature verbatim and may add helper
lemmas above the theorem. It may not add imports: only `Mathlib` and
`CflibsFormal.SahaEquilibrium` (which also brings in `CflibsFormal.Saha` and
`CflibsFormal.Boltzmann`).

## 2. Definitions

Repo definition (`CflibsFormal/SahaEquilibrium.lean:286`, namespace `CflibsFormal`):

```lean
noncomputable def multiElementIonized {ι : Type*} [Fintype ι] (S Ntot : ι → ℝ)
    (x : ℝ) : ℝ :=
  ∑ s, Ntot s * S s / (x + S s)
```

Write `G := multiElementIonized S Ntot`, `D x := ∑ s, Ntot s * S s / (x + S s) ^ 2 ≥ 0`, and
`N := neutralityNewton S Ntot`, so `N x = x - (x - G x) / (1 + D x)`. `G` is unfolded by
`unfold multiElementIonized` or by `change (∑ s, Ntot s * S s / (x + S s)) = _`.

Physics (for orientation only): `x` is the electron density, `S s` the Saha factor of species
`s`, `Ntot s` its elemental density; `x = G x` is charge neutrality with one two-stage Saha
balance per species. `N` is Newton's method on `f x = x - G x`, with `f' x = 1 + D x`.

## 3. Mathematical proof

Fix `x ≥ 0`. All denominators `x + S s`, `r + S s`, `1 + D x` are positive.

**Part 1, `N x ≤ r`.** Exact error identity (already proved in Lean, pasted in §5):

    N x - r = -((x - r)^2 * ∑ s, Ntot s * S s / ((x + S s)^2 * (r + S s))) / (1 + D x).

The numerator inside the minus sign is `≥ 0` and the denominator `> 0`, so `N x - r ≤ 0`.
(Derivation: the two-point identity `G x - G r = (r - x) * c` with
`c = ∑ Ntot s S s / ((x + S s)(r + S s))` gives `x - G x = (x - r)(1 + c)`, and
`D x - c = (r - x) * ∑ Ntot s S s / ((x + S s)^2 (r + S s))`.)

**Part 2, `r ≤ G (N x)`.**
(a) `N x ≥ 0`: `N x = (x * D x + G x) / (1 + D x)` (clear the denominator: `N x * (1 + D x) =
x * (1 + D x) - (x - G x) = x * D x + G x`), and `x ≥ 0`, `D x ≥ 0`, `G x ≥ 0`
(each summand `Ntot s * S s / (x + S s) ≥ 0`).
(b) `G` is antitone on `[0, ∞)` for `Ntot ≥ 0`: for `0 ≤ a ≤ b`,
`G a - G b = (b - a) * ∑ s, Ntot s * S s / ((a + S s) * (b + S s)) ≥ 0`
(two-point identity `multiElementIonized_two_point`, which needs only `hS`).
(c) With `0 ≤ N x ≤ r` from (a) and Part 1: `G (N x) ≥ G r = r` (`hfix`).

Degenerate cases are covered: with no species or all `Ntot s = 0`, `G ≡ 0`, `D ≡ 0`, `r = 0`,
`N x = 0`, and both parts read `0 ≤ 0`.

## 4. Suggested Lean decomposition

1. `neutralityNewton_error_eq` and `neutralityNewton_le_root`: paste §5 verbatim (they compile
   against this exact statement file; checked 2026-09-24). This is Part 1.
2. `G_nonneg (hx : 0 ≤ x) : 0 ≤ multiElementIonized S Ntot x`:
   `Finset.sum_nonneg fun s _ => div_nonneg (mul_nonneg (hN s) (hS s).le) (by linarith [hS s])`
   after `unfold multiElementIonized` (or `change`).
3. `neutralityNewton_nonneg (hx : 0 ≤ x) : 0 ≤ neutralityNewton S Ntot x`: rewrite
   `N x = (x * D + G x) / (1 + D)` (prove by `unfold neutralityNewton; field_simp; ring`, with
   `hD : 0 < 1 + D` in context) and apply `div_nonneg` / `positivity`-style reasoning.
4. `G_antitone (ha : 0 ≤ a) (hab : a ≤ b) : G b ≤ G a`: from
   `multiElementIonized_two_point S Ntot hS a b ha (ha.trans hab)` and nonnegativity of the slope
   sum (`Finset.sum_nonneg`, `div_nonneg`, `mul_nonneg`), then `nlinarith`/`mul_nonneg`.
5. Assemble: `⟨le_root, by have := G_antitone (nonneg) (le_root); rw [← hfix] at this; exact this⟩`
   (orientation: `G_antitone` gives `G r ≤ G (N x)`, and `G r = r` by `hfix.symm`).

## 5. Pasteable proved helpers (evidence/adv-verifier-2/Newton2.lean, compiled here)

These two lemmas compile verbatim when placed between the definition and the theorem of
`statement.lean` (checked 2026-09-24 against lean-main fb1681d; only the target's own `sorry`
remained).

```lean
theorem neutralityNewton_error_eq (S Ntot : ι → ℝ) (hS : ∀ s, 0 < S s) (hN : ∀ s, 0 ≤ Ntot s)
    {x r : ℝ} (hx : 0 ≤ x) (hr : 0 ≤ r) (hfix : r = multiElementIonized S Ntot r) :
    neutralityNewton S Ntot x - r
      = -((x - r) ^ 2 * ∑ s, Ntot s * S s / ((x + S s) ^ 2 * (r + S s)))
          / (1 + ∑ s, Ntot s * S s / (x + S s) ^ 2) := by
  have hD : 0 < 1 + ∑ s, Ntot s * S s / (x + S s) ^ 2 := by
    have : 0 ≤ ∑ s, Ntot s * S s / (x + S s) ^ 2 :=
      Finset.sum_nonneg (fun s _ => div_nonneg (mul_nonneg (hN s) (hS s).le) (sq_nonneg _))
    linarith
  have htp := multiElementIonized_two_point S Ntot hS x r hx hr
  -- x - G x = (x - r) * (1 + Σ a/((x+S)(r+S)))
  have hf : x - multiElementIonized S Ntot x
      = (x - r) * (1 + ∑ s, Ntot s * S s / ((x + S s) * (r + S s))) := by
    have : multiElementIonized S Ntot x = r + (r - x) *
        ∑ s, Ntot s * S s / ((x + S s) * (r + S s)) := by
      linarith [htp, hfix]
    rw [this]; ring
  have hterm : (∑ s, Ntot s * S s / (x + S s) ^ 2)
      - (∑ s, Ntot s * S s / ((x + S s) * (r + S s)))
      = (r - x) * ∑ s, Ntot s * S s / ((x + S s) ^ 2 * (r + S s)) := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    have h1 : 0 < x + S s := by linarith [hS s]
    have h2 : 0 < r + S s := by linarith [hS s]
    field_simp
    ring
  unfold neutralityNewton
  rw [hf, eq_div_iff hD.ne']
  have hD' := hD.ne'
  field_simp
  nlinarith [hterm]

/-- FT-17 step 3: one Newton step from any `x ≥ 0` lands at or below the root. -/
theorem neutralityNewton_le_root (S Ntot : ι → ℝ) (hS : ∀ s, 0 < S s) (hN : ∀ s, 0 ≤ Ntot s)
    {x r : ℝ} (hx : 0 ≤ x) (hr : 0 ≤ r) (hfix : r = multiElementIonized S Ntot r) :
    neutralityNewton S Ntot x ≤ r := by
  have hid := neutralityNewton_error_eq S Ntot hS hN hx hr hfix
  have hD : 0 < 1 + ∑ s, Ntot s * S s / (x + S s) ^ 2 := by
    have : 0 ≤ ∑ s, Ntot s * S s / (x + S s) ^ 2 :=
      Finset.sum_nonneg (fun s _ => div_nonneg (mul_nonneg (hN s) (hS s).le) (sq_nonneg _))
    linarith
  have hnum : 0 ≤ (x - r) ^ 2 * ∑ s, Ntot s * S s / ((x + S s) ^ 2 * (r + S s)) := by
    refine mul_nonneg (sq_nonneg _) (Finset.sum_nonneg (fun s _ => ?_))
    have h1 : 0 < x + S s := by linarith [hS s]
    have h2 : 0 < r + S s := by linarith [hS s]
    exact div_nonneg (mul_nonneg (hN s) (hS s).le) (by positivity)
  have : neutralityNewton S Ntot x - r ≤ 0 := by
    rw [hid]; exact div_nonpos_of_nonpos_of_nonneg (by linarith) hD.le
  linarith
```

## 6. Repo lemmas in scope (all in namespace `CflibsFormal`, file `SahaEquilibrium.lean`)

- `multiElementIonized_two_point (S Ntot : ι → ℝ) (hS : ∀ s, 0 < S s) (x y : ℝ) (hx : 0 ≤ x)
  (hy : 0 ≤ y) : multiElementIonized S Ntot x - multiElementIonized S Ntot y
  = (y - x) * ∑ s, Ntot s * S s / ((x + S s) * (y + S s))` (line 671). Needs no sign on `Ntot`.
- `multiElementIonized_strictAntiOn [Nonempty ι] (S Ntot) (hS : ∀ s, 0 < S s)
  (hN : ∀ s, 0 < Ntot s) : StrictAntiOn (multiElementIonized S Ntot) (Set.Ici 0)` (line 295).
  **Not usable here**: it needs `Nonempty ι` and `Ntot > 0`; this target has neither. Use the
  two-point identity instead (§4 step 4).
- `multiElementIonized_lipschitz` (line 693) needs `Ntot > 0`; not needed.

## 7. Mathlib lemmas (signatures checked)

- `Finset.sum_nonneg`, `Finset.sum_sub_distrib`, `Finset.mul_sum`, `Finset.sum_congr`.
- `div_nonneg`, `mul_nonneg`, `sq_nonneg`, `div_nonpos_of_nonpos_of_nonneg`, `eq_div_iff`.
- `div_le_div_iff₀ : 0 < b → 0 < d → (a / b ≤ c / d ↔ a * d ≤ c * b)`.
- Tactics that work on this algebra: `field_simp` (needs the positivity facts `0 < x + S s`
  as hypotheses in context), `ring`, `nlinarith`, `linarith`, `positivity`.

## 8. Pitfalls

- `hfix` is oriented `r = G r`; rewrite with `hfix.symm` or `← hfix` when you need `G r = r`.
- `field_simp` inside a `Finset.sum_congr` needs the per-summand facts
  `have h1 : 0 < x + S s := by linarith [hS s]` stated before it (see §5).
- Do not reach for `multiElementIonized_strictAntiOn` (wrong hypotheses, see §6) or for
  convexity: the identity route needs none.
- Do not add `[Nonempty ι]` or strengthen `hN`: the signature is audited and must stay verbatim.
- Budget: this is a short target (Part 1 is pasteable; Part 2 is about 15 lines).
