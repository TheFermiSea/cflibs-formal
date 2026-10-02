# FT17-neutralityNewton-tendsto: Newton on charge neutrality converges from every `x0 ≥ 0`

Planning dossier for the proof queue (2026-09-24 audit, frontier FT-17, global convergence).
Written for a planner who cannot open the repository: every repo definition and lemma the proof
needs is quoted below, and every Mathlib name was checked with `#check` against the pinned
Mathlib (v4.33.1) on 2026-09-24.

Dependency note: the sibling target `FT17-neutralityNewton-enclosure` proves one step of the
argument, but it is not on main, so this target must re-prove what it needs inline. The two
hardest helpers are already proved and are pasted in §5.

## 1. Goal

```lean
import Mathlib
import CflibsFormal.SahaEquilibrium

open Finset CflibsFormal Filter Topology

namespace Plan.FT17

variable {ι : Type*} [Fintype ι]

noncomputable def neutralityNewton (S Ntot : ι → ℝ) (x : ℝ) : ℝ :=
  x - (x - multiElementIonized S Ntot x) / (1 + ∑ s, Ntot s * S s / (x + S s) ^ 2)

theorem neutralityNewton_tendsto {S Ntot : ι → ℝ} {r x0 : ℝ} (hS : ∀ s, 0 < S s)
    (hN : ∀ s, 0 ≤ Ntot s) (hr : 0 ≤ r) (hfix : r = multiElementIonized S Ntot r)
    (hx0 : 0 ≤ x0) :
    Tendsto (fun n => (neutralityNewton S Ntot)^[n] x0) atTop (𝓝 r) := by
  sorry
```

The audited file is `statement.lean` here. Keep the definition and the theorem signature
verbatim; helper lemmas may be added above the theorem; no new imports.

## 2. Definitions

`CflibsFormal/SahaEquilibrium.lean:286`:

```lean
noncomputable def multiElementIonized {ι : Type*} [Fintype ι] (S Ntot : ι → ℝ)
    (x : ℝ) : ℝ :=
  ∑ s, Ntot s * S s / (x + S s)
```

Notation: `G := multiElementIonized S Ntot`, `D x := ∑ s, Ntot s * S s / (x + S s) ^ 2`,
`N := neutralityNewton S Ntot`, so `N x = x - (x - G x) / (1 + D x)`.

## 3. Mathematical proof

For `x ≥ 0` every denominator is positive and `1 + D x ≥ 1`.

1. **One step lands in `[0, r]`.** `N x ≤ r` from the error identity
   `N x - r = -((x - r)^2 * ∑ Ntot s S s / ((x + S s)^2 (r + S s))) / (1 + D x)` (pasted, §5);
   `N x ≥ 0` because `N x = (x * D x + G x) / (1 + D x)` with all three terms `≥ 0`.
2. **`G` is antitone on `[0, ∞)`** (for `Ntot ≥ 0`): `G a - G b = (b - a) * (slope sum ≥ 0)`.
3. **Monotone step below the root.** For `0 ≤ x ≤ r`: `N x - x = (G x - x) / (1 + D x)` and
   `G x ≥ G r = r ≥ x`, so `x ≤ N x`; and `N x ≤ r` by step 1.
4. **Orbit.** Let `y0 := N x0 ∈ [0, r]` and `u k := N^[k] y0`. By induction `u k ∈ [0, r]`, and
   `u k ≤ u (k + 1)` by step 3. A monotone sequence bounded by `r` converges:
   `u → L := ⨆ k, u k`, with `0 ≤ L ≤ r` (limits of bounds).
5. **Limit is a fixed point.** `N` is continuous at `L ≥ 0` (sums of `c / (x + S s)` and
   `c / (x + S s)^2` with positive denominators, and `1 + D L ≠ 0`), so `N L = L`
   (`isFixedPt_of_tendsto_iterate`). Then `(L - G L) / (1 + D L) = 0` forces `G L = L`.
6. **Identify the limit.** `L ≤ r` and step 2 give `L = G L ≥ G r = r`, so `L = r`.
7. **Undo the index shift.** `N^[n + 1] x0 = N^[n] (N x0) = u n` (`Function.iterate_succ_apply`),
   so `Tendsto (fun n => N^[n + 1] x0) atTop (𝓝 r)`, and `tendsto_add_atTop_iff_nat 1` removes
   the shift.

No `Nonempty ι` is needed anywhere; do not use lemmas that require it.

## 4. Suggested Lean decomposition (helpers above the theorem)

1. Paste §5 (`neutralityNewton_error_eq`, `neutralityNewton_le_root`).
2. `G_nonneg (hx : 0 ≤ x) : 0 ≤ multiElementIonized S Ntot x`.
3. `G_antitone (ha : 0 ≤ a) (hab : a ≤ b) : multiElementIonized S Ntot b ≤ multiElementIonized
   S Ntot a` via `multiElementIonized_two_point S Ntot hS a b ha (ha.trans hab)`.
4. `newton_nonneg (hx : 0 ≤ x) : 0 ≤ neutralityNewton S Ntot x` via
   `N x * (1 + D x) = x * D x + G x`.
5. `newton_ge_self (hx : 0 ≤ x) (hxr : x ≤ r) : x ≤ neutralityNewton S Ntot x`: unfold, show
   `(x - G x) / (1 + D x) ≤ 0` with `div_nonpos_of_nonpos_of_nonneg` and `G x ≥ r ≥ x` from
   `G_antitone` (§4.3) applied to `x ≤ r`, plus `hfix`.
6. `newton_continuousAt (hL : 0 ≤ L) : ContinuousAt (neutralityNewton S Ntot) L`: build from
   `continuousAt_id`, `tendsto_finsetSum` / `continuousAt_finset_sum`-style lemmas, and
   `ContinuousAt.div` with nonzero denominators (template in §6).
7. Main proof: orbit invariance `∀ k, 0 ≤ u k ∧ u k ≤ r` (induction with
   `Function.iterate_succ_apply'`), monotonicity (`monotone_nat_of_le_succ`), limit
   (`tendsto_atTop_ciSup` with `BddAbove` witness `r`), bounds on `L` (`ge_of_tendsto'`,
   `le_of_tendsto'`), fixed point (`isFixedPt_of_tendsto_iterate`), identification (steps 5-6),
   shift (step 7).

## 5. Pasteable proved helpers (evidence/adv-verifier-2/Newton2.lean)

Checked 2026-09-24: these compile verbatim between the definition and the theorem of this
`statement.lean` (only the target's own `sorry` remained).

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

## 6. Templates from main (`SahaEquilibrium.lean`, proof of `multiElementIonized_iter_tendsto`)

Continuity of `G` at a nonnegative point (adapt for `D`, whose summands are
`Ntot s * S s / (x + S s) ^ 2`, using `(continuousAt_id.add continuousAt_const).pow 2` and
`pow_ne_zero`):

```lean
  have hG_contAt : ∀ z : ℝ, 0 ≤ z → ContinuousAt (multiElementIonized S Ntot) z := by
    intro z hz
    change Filter.Tendsto (fun x => ∑ s, Ntot s * S s / (x + S s)) (nhds z)
      (nhds (∑ s, Ntot s * S s / (z + S s)))
    refine tendsto_finsetSum Finset.univ (fun s _ => ?_)
    have hden : (0 : ℝ) < z + S s := by linarith [hS s]
    exact continuousAt_const.div (continuousAt_id.add continuousAt_const) hden.ne'
```

Monotone bounded orbit to a limit, then to a fixed point (here `F` is a monotone self-map of
`[0, M]`; in this target use `N`, the bound `r`, and the monotone-step lemma of §4.5):

```lean
      · have hmono : Monotone (fun k => F^[k] y0) := by
          refine monotone_nat_of_le_succ (fun k => ?_)
          ...
        exact ⟨_, tendsto_atTop_ciSup hmono
          ⟨M, by rintro x ⟨k, rfl⟩; exact (hmem k).2⟩⟩
    have hL0 : 0 ≤ L := ge_of_tendsto' htends (fun k => (hmem k).1)
    have hLfixF : F L = L := isFixedPt_of_tendsto_iterate htends (hF_contAt L hL0)
```

In this target the monotone step is simpler than on main: `u (k + 1) = N (u k)` and
`u k ≤ N (u k)` directly from §4.5 applied at `u k ∈ [0, r]`, so no induction inside the
monotonicity proof is needed (use `Function.iterate_succ_apply'` to rewrite `u (k + 1)`).

## 7. Mathlib lemmas (signatures checked)

- `tendsto_atTop_ciSup : Monotone f → BddAbove (Set.range f) → Tendsto f atTop (𝓝 (⨆ i, f i))`
- `monotone_nat_of_le_succ : (∀ n, f n ≤ f (n + 1)) → Monotone f`
- `isFixedPt_of_tendsto_iterate : Tendsto (fun n => f^[n] x) atTop (𝓝 y) → ContinuousAt f y →
  Function.IsFixedPt f y` (`IsFixedPt f y` unfolds to `f y = y`)
- `ge_of_tendsto' : Tendsto f x (𝓝 a) → (∀ c, b ≤ f c) → b ≤ a`; `le_of_tendsto'` dually.
- `Filter.tendsto_add_atTop_iff_nat (k : ℕ) : Tendsto (fun n => f (n + k)) atTop l ↔
  Tendsto f atTop l`
- `Function.iterate_succ_apply : f^[n.succ] x = f^[n] (f x)` (use for the shift);
  `Function.iterate_succ_apply' : f^[n.succ] x = f (f^[n] x)` (use for invariance/monotonicity).
- `tendsto_finsetSum`, `ContinuousAt.div`, `ContinuousAt.sub`, `ContinuousAt.add`,
  `ContinuousAt.pow`, `continuousAt_const`, `continuousAt_id`.
- `div_eq_zero_iff`, `div_nonpos_of_nonpos_of_nonneg`, `sub_eq_zero`.

## 8. Pitfalls

- The orbit from `x0` itself is NOT monotone when `x0 > r` (the first step jumps below `r`).
  Start the monotone argument at `y0 = N x0` and shift the index at the end.
- `multiElementIonized_strictAntiOn`, `multiElement_pos_fixedPoint_unique` and
  `multiElementIonized_iter_tendsto` on main all need `[Nonempty ι]` and `Ntot > 0`; this target
  has neither, so derive antitonicity from `multiElementIonized_two_point` (needs only `hS`).
- `hfix` is oriented `r = G r`.
- `ContinuousAt` of the `if`-free rational expression is routine but verbose; prove it once as
  a helper lemma.
- This is a moderate-to-hard target (iterate plumbing and the limit identification); the
  algebra is already done in §5. No rate is required by the statement.
