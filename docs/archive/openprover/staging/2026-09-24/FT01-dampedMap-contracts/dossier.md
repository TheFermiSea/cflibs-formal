# FT01-dampedMap-contracts: derivative-window certificate for a damped iteration on a box

Planning dossier for the proof queue (2026-09-24 audit, frontier FT-01, queue item 7).
Mathlib only; one local definition. Every Mathlib name was checked with `#check` against the
pinned Mathlib (v4.33.1) on 2026-09-24.

## 1. Goal

```lean
import Mathlib

open Filter Topology

namespace Plan.FT01

def dampedMap (lam : ℝ) (g : ℝ → ℝ) (u : ℝ) : ℝ := (1 - lam) * u + lam * g u

theorem dampedMap_contracts {g g' : ℝ → ℝ} {a b m M lam : ℝ} (hlam0 : 0 < lam) (hab : a ≤ b)
    (hd : ∀ T ∈ Set.Icc a b, HasDerivAt g (g' T) T)
    (hmM : ∀ T ∈ Set.Icc a b, m ≤ g' T ∧ g' T ≤ M) (hlo : 1 - 2 / lam < m) (hhi : M < 1)
    (hmaps : Set.MapsTo (dampedMap lam g) (Set.Icc a b) (Set.Icc a b)) :
    ∃ Tstar ∈ Set.Icc a b, dampedMap lam g Tstar = Tstar ∧
      ∀ T0 ∈ Set.Icc a b, Tendsto (fun n => (dampedMap lam g)^[n] T0) atTop (𝓝 Tstar) := by
  sorry
```

Keep the definition and the theorem signature verbatim; helper lemmas may be added; no imports
beyond `Mathlib`. `dampedMap lam g T` unfolds by `rfl` / `simp only [dampedMap]` to
`(1 - lam) * T + lam * g T`.

## 2. Mathematical proof

Let `H := dampedMap lam g`, `mH := 1 - lam + lam * m`, `MH := 1 - lam + lam * M`.

1. **Derivative of `H`.** For `T ∈ [a, b]`, `HasDerivAt H (1 - lam + lam * g' T) T`
   (`(1 - lam) * id` has derivative `1 - lam`; `lam * g` has `lam * g' T`).
2. **Derivative window.** From `hmM` and `lam > 0`: `mH ≤ H' T ≤ MH` on `[a, b]`.
3. **`|H'| ≤ q < 1`.** `q := max |mH| |MH|`; `|H' T| ≤ q` by `abs_le_max_abs_abs`. And `q < 1`:
   - `MH < 1` since `M < 1`; `mH < 1` since `m ≤ g' a ≤ M < 1` (use `hmM a ⟨le_rfl, hab⟩`).
   - `mH > -1`: `hlo` times `lam > 0` is `lam - 2 < lam * m` (`lam * (2 / lam) = 2` by
     `mul_div_cancel₀ _ hlam0.ne'`), i.e. `1 - lam + lam * m > -1`; and `MH ≥ mH > -1` since
     `m ≤ M`.
   So `|mH| < 1`, `|MH| < 1`, `q < 1` (`max_lt`, `abs_lt`).
4. **Contraction on the box.** Mean value inequality on the convex set `[a, b]`:
   `|H y - H x| ≤ q * |y - x|` for `x, y ∈ [a, b]`
   (`Convex.norm_image_sub_le_of_norm_hasDerivWithin_le` with `(hH T hT).hasDerivWithinAt`).
5. **Fixed point and convergence (Banach).** `[a, b]` is closed, hence complete, nonempty
   (`hab`), and `H` maps it into itself (`hmaps`). With `K : NNReal := ⟨q, _⟩`, the restriction
   `hmaps.restrict H (Icc a b) (Icc a b)` is `ContractingWith K`; `ContractingWith.exists_fixedPoint'`
   from the start `a` gives `Tstar ∈ [a, b]` with `H Tstar = Tstar`. For an arbitrary
   `T0 ∈ [a, b]`, either (i) call `exists_fixedPoint'` again from `T0` to get a fixed point
   `y0` with `H^[n] T0 → y0`, and show `y0 = Tstar` because
   `|y0 - Tstar| = |H y0 - H Tstar| ≤ q |y0 - Tstar|` with `q < 1`; or (ii) prove
   `|H^[n] T0 - Tstar| ≤ q^n |T0 - Tstar|` by induction (iterates stay in the box by
   `hmaps`) and squeeze with `tendsto_pow_atTop_nhds_zero_of_lt_one`.

## 3. Template on main (`CflibsFormal/SahaEquilibrium.lean:1269`, `outerContraction_box`)

The Banach step already works in this Mathlib for a box contraction (the old ROADMAP advice
"do not start from ContractingWith" is stale; the audit's RF-26 records that the code uses it):

```lean
  have hmaps : Set.MapsTo (outerMap legNe legT) (Set.Icc Tmin Tmax) (Set.Icc Tmin Tmax) :=
    fun x hx => outerMap_mapsTo hmapsNe hmapsT x hx
  have hcomplete : IsComplete (Set.Icc Tmin Tmax) := isClosed_Icc.isComplete
  set K : ℝ≥0 := ⟨L1 * L2, mul_nonneg hL1nn hL2nn⟩ with hKdef
  have hKcoe : (K : ℝ) = L1 * L2 := rfl
  have hK : K < 1 := by rw [← NNReal.coe_lt_one, hKcoe]; exact hq
  have hlip : LipschitzWith K
      (hmaps.restrict (outerMap legNe legT) (Set.Icc Tmin Tmax) (Set.Icc Tmin Tmax)) := by
    refine lipschitzWith_iff_dist_le_mul.mpr ?_
    rintro ⟨x, hx⟩ ⟨y, hy⟩
    rw [Subtype.dist_eq, Subtype.dist_eq, Set.MapsTo.val_restrict_apply,
        Set.MapsTo.val_restrict_apply, Real.dist_eq, Real.dist_eq, hKcoe]
    exact outerMap_contraction hmapsNe hL1 hL2 hL2nn hx hy
  have hcontract : ContractingWith K
      (hmaps.restrict (outerMap legNe legT) (Set.Icc Tmin Tmax) (Set.Icc Tmin Tmax)) :=
    ⟨hK, hlip⟩
  have hxs : Tmin ∈ Set.Icc Tmin Tmax := Set.left_mem_Icc.mpr hTle
  have hx : edist Tmin (outerMap legNe legT Tmin) ≠ ⊤ := edist_ne_top _ _
  obtain ⟨Tstar, hTstar, hfixpt, _htend, _herr⟩ :=
    hcontract.exists_fixedPoint' hcomplete hmaps hxs hx
```

(`ℝ≥0` needs `open scoped NNReal`; in this file write `NNReal` instead, since the statement
file does not open that scope. The `outerMap_contraction` call is where this target's
step-4 Lipschitz bound goes.)

## 4. Mathlib lemmas (signatures checked)

- `Convex.norm_image_sub_le_of_norm_hasDerivWithin_le {f f' : 𝕜 → G} {s : Set 𝕜} {x y : 𝕜}
  {C : ℝ} (hf : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x) (bound : ∀ x ∈ s, ‖f' x‖ ≤ C)
  (hs : Convex ℝ s) (xs : x ∈ s) (ys : y ∈ s) : ‖f y - f x‖ ≤ C * ‖y - x‖`
  (`Mathlib/Analysis/Calculus/MeanValue.lean:696`; note the argument order: `hf`, `bound`,
  then `hs`); `convex_Icc a b`; `Real.norm_eq_abs`.
- `HasDerivAt.hasDerivWithinAt`, `HasDerivAt.const_mul (c) : HasDerivAt d d' x →
  HasDerivAt (fun y => c * d y) (c * d') x`, `HasDerivAt.add`, `hasDerivAt_id`.
- `abs_le_max_abs_abs : a ≤ b → b ≤ c → |b| ≤ max |a| |c|`; `max_lt`; `abs_lt`;
  `mul_le_mul_of_nonneg_left`; `mul_div_cancel₀ (a) : b ≠ 0 → b * (a / b) = a`.
- `ContractingWith.exists_fixedPoint' (hsc : IsComplete s) (hsf : Set.MapsTo f s s)
  (hf : ContractingWith K (hsf.restrict f s s)) (hxs : x ∈ s) (hx : edist x (f x) ≠ ⊤) :
  ∃ y ∈ s, Function.IsFixedPt f y ∧ Tendsto (fun n => f^[n] x) atTop (𝓝 y) ∧ …`
- `isClosed_Icc.isComplete`, `lipschitzWith_iff_dist_le_mul`, `Subtype.dist_eq`,
  `Set.MapsTo.val_restrict_apply`, `Real.dist_eq`, `NNReal.coe_lt_one`, `edist_ne_top`,
  `Set.left_mem_Icc`.
- Route (ii): `tendsto_pow_atTop_nhds_zero_of_lt_one : 0 ≤ r → r < 1 →
  Tendsto (fun n => r ^ n) atTop (𝓝 0)`, `squeeze_zero`, `tendsto_iff_dist_tendsto_zero`,
  `Function.iterate_succ_apply'`, `Set.MapsTo.iterate`.

## 5. Pitfalls

- `hd` gives `HasDerivAt g` only at points of `[a, b]`; build `HasDerivAt H` pointwise there,
  convert with `convert … using 1` + `funext`/`simp [dampedMap]` if the function shape differs.
- The derivative bound must be stated for `‖·‖` (`Real.norm_eq_abs`), and the MVT lemma takes
  `HasDerivWithinAt … (Set.Icc a b)`, obtained from `HasDerivAt` by `.hasDerivWithinAt`.
- `m ≤ M` is not a hypothesis; get it from `hmM a ⟨le_rfl, hab⟩`.
- `q` may be `0`; `K := ⟨q, le_max_of_le_left (abs_nonneg _)⟩` is fine.
- Budget: moderate-high (MVT to Lipschitz, then Banach on a subtype). Prove the Lipschitz bound
  as its own helper lemma.
