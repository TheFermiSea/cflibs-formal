# FT01-tDamped-mobius-converges: the T-damped Möbius iteration converges for `0 < g < 1`

Planning dossier for the proof queue (2026-09-24 audit, frontier FT-01, verifier revision (a)).
Mathlib only; one local definition. Every Mathlib name was checked with `#check` against the
pinned Mathlib (v4.33.1) on 2026-09-24.

## 1. Goal

```lean
import Mathlib

open Filter Topology

namespace Plan.FT01

def dampedMap (lam : ℝ) (g : ℝ → ℝ) (u : ℝ) : ℝ := (1 - lam) * u + lam * g u

theorem tDamped_mobius_converges {g c lam : ℝ} (hg0 : 0 < g) (hg1 : g < 1) (hc : 0 < c)
    (hl0 : 0 < lam) (hl1 : lam ≤ 1) (T0 : ℝ) (hT0 : 0 < T0) :
    Tendsto (fun n => (dampedMap lam (fun T => T / (g + c * T)))^[n] T0) atTop
      (𝓝 ((1 - g) / c)) := by
  sorry
```

Note the name clash: in the theorem `g` is a real number (the gain), while in `dampedMap` the
argument named `g` is a function; here it is instantiated with `fun T => T / (g + c * T)`.
Keep the definition and the theorem signature verbatim; helper lemmas may be added; no imports
beyond `Mathlib`. `dampedMap lam φ T` unfolds by `rfl` / `simp only [dampedMap]` /
`unfold dampedMap` to `(1 - lam) * T + lam * φ T`.

## 2. Notation

`φ T := T / (g + c * T)`, `H := dampedMap lam φ`, `T* := (1 - g) / c > 0`, `T_n := H^[n] T0`.
For `T > 0`: `g + c * T > g > 0`.

## 3. Mathematical proof

1. **Positivity.** For `T > 0`: `φ T > 0` and `H T = (1 - lam) T + lam φ T > 0`
   (`1 - lam ≥ 0`, `lam > 0`).
2. **Fixed point.** `c * T* = 1 - g`, so `g + c T* = 1`, `φ T* = T*`, `H T* = T*`.
3. **Displacement sign.** `H T - T = lam (φ T - T) = lam * T * (1 - g - c T) / (g + c T)` and
   `1 - g - c T = c (T* - T)`. So for `T > 0`: `H T ≥ T ⟺ T ≤ T*` (and `≤` for `T ≥ T*`).
4. **Monotonicity of `H` on `(0, ∞)`.** For `0 < S ≤ T`:
   `φ T - φ S = g (T - S) / ((g + c S)(g + c T)) ≥ 0`; with `1 - lam ≥ 0`, `H S ≤ H T`.
   (This is where `lam ≤ 1` is used.)
5. **Case `T0 ≤ T*`.** By induction `T0 ≤ T_n ≤ T*` and `T_n ≤ T_(n+1)`
   (upper bound: `T_(n+1) = H T_n ≤ H T* = T*` by step 4; step: step 3). Monotone, bounded
   above: `T_n → L := ⨆ n, T_n` with `T0 ≤ L ≤ T*`, so `L > 0`.
6. **Case `T* ≤ T0`.** Symmetric: `T* ≤ T_(n+1) ≤ T_n ≤ T0`, antitone, bounded below by
   `T* > 0`: `T_n → L := ⨅ n, T_n ≥ T* > 0`.
7. **Identify the limit.** `H` is continuous at `L > 0` (denominator `g + c L > 0`), so
   `H L = L` (`isFixedPt_of_tendsto_iterate`). Then `lam (φ L - L) = 0`, `lam > 0`, so
   `L / (g + c L) = L`, and `L ≠ 0` gives `g + c L = 1`, i.e. `L = (1 - g) / c`.

A clean decomposition is a generic lemma used twice (or once, with `le_total T0 T*`):

```lean
-- sketch, not compiled
lemma orbit_tendsto_of_monotone {H : ℝ → ℝ} {Ts T0 : ℝ} (hTs : 0 < Ts) (hT0 : 0 < T0)
    (hpos : ∀ T, 0 < T → 0 < H T)
    (hmono : ∀ S T, 0 < S → S ≤ T → H S ≤ H T) (hfix : H Ts = Ts)
    (hup : ∀ T, 0 < T → T ≤ Ts → T ≤ H T) (hdown : ∀ T, Ts ≤ T → H T ≤ T)
    (hcont : ∀ T, 0 < T → ContinuousAt H T)
    (huniq : ∀ L, 0 < L → H L = L → L = Ts) :
    Tendsto (fun n => H^[n] T0) atTop (𝓝 Ts)
```

## 4. Lean ingredients

- Unfolding iterates: `Function.iterate_succ_apply' : f^[n.succ] x = f (f^[n] x)`.
- Monotone sequences: `monotone_nat_of_le_succ : (∀ n, f n ≤ f (n + 1)) → Monotone f`,
  `antitone_nat_of_succ_le : (∀ n, f (n + 1) ≤ f n) → Antitone f`.
- Limits: `tendsto_atTop_ciSup : Monotone f → BddAbove (Set.range f) →
  Tendsto f atTop (𝓝 (⨆ i, f i))`; `tendsto_atTop_ciInf : Antitone f → BddBelow (Set.range f) →
  Tendsto f atTop (𝓝 (⨅ i, f i))`. `BddAbove` witness: `⟨Ts, by rintro x ⟨k, rfl⟩; exact …⟩`.
- Bounds on the limit: `ge_of_tendsto' : Tendsto f x (𝓝 a) → (∀ c, b ≤ f c) → b ≤ a`,
  `le_of_tendsto'` dually.
- Fixed point of the limit: `isFixedPt_of_tendsto_iterate : Tendsto (fun n => f^[n] x) atTop
  (𝓝 y) → ContinuousAt f y → Function.IsFixedPt f y` (`IsFixedPt f y` is `f y = y`).
- Continuity: `ContinuousAt.add`, `ContinuousAt.mul`, `ContinuousAt.div` (needs the denominator
  `≠ 0`), `continuousAt_const`, `continuousAt_id`.
- Algebra: `div_le_div_iff₀ : 0 < b → 0 < d → (a / b ≤ c / d ↔ a * d ≤ c * b)`, `div_eq_iff`,
  `field_simp`, `nlinarith`, `positivity`.

## 5. Template on main (`CflibsFormal/SahaEquilibrium.lean`, `multiElementIonized_iter_tendsto`)

The same monotone-orbit argument, for a monotone self-map `F` of `[0, M]`:

```lean
    obtain ⟨L, htends⟩ :
        ∃ L, Filter.Tendsto (fun k => F^[k] y0) Filter.atTop (nhds L) := by
      rcases le_total (F y0) y0 with hdec | hinc
      · have hanti : Antitone (fun k => F^[k] y0) := by
          refine antitone_nat_of_succ_le (fun k => ?_)
          induction k with
          | zero =>
            simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
            exact hdec
          | succ n ih =>
            have h1 : F^[n + 1] y0 = F (F^[n] y0) := Function.iterate_succ_apply' F n y0
            have h2 : F^[n + 1 + 1] y0 = F (F^[n + 1] y0) :=
              Function.iterate_succ_apply' F (n + 1) y0
            rw [h1, h2]
            exact hF_mono _ _ (hmem (n + 1)).1 (hmem n).1 ih
        exact ⟨_, tendsto_atTop_ciInf hanti
          ⟨0, by rintro x ⟨k, rfl⟩; exact (hmem k).1⟩⟩
      · -- symmetric, with monotone_nat_of_le_succ and tendsto_atTop_ciSup
        ...
    have hL0 : 0 ≤ L := ge_of_tendsto' htends (fun k => (hmem k).1)
    have hLfixF : F L = L := isFixedPt_of_tendsto_iterate htends (hF_contAt L hL0)
```

(Branching on `le_total (H T0) T0` is an alternative to branching on `le_total T0 T*`.)

## 6. Pitfalls

- The limit must be shown POSITIVE before dividing by it or using continuity of `φ` there: get
  `L ≥ min T0 T* > 0` from the bounds, not from the limit itself.
- `hl1 : lam ≤ 1` is load-bearing only for monotonicity of `H` (step 4); `hg0` makes
  `g + c T > 0` on `T > 0`.
- Do not try to prove a global contraction: `H' T = 1 - lam + lam * g / (g + c T) ^ 2` tends to
  `1 - lam + lam / g > 1` as `T → 0⁺`, so `H` is expanding near `0`. The statement asks only for
  convergence, which the monotone argument gives.
- Budget: moderate-high, mostly iterate plumbing; two symmetric cases. Prove the generic
  orbit lemma once.
