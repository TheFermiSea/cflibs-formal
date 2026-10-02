# FT13-log-selfAbsorptionFactor-lipschitz: `log SA` is `½`-Lipschitz on `[0, ∞)`

Planning dossier for the proof queue (2026-09-24 audit, frontier FT-13 (b), queue items 4-5).
Written for a planner who cannot open the repository. Every repo definition and lemma is
quoted, and every Mathlib name was checked with `#check` against the pinned Mathlib (v4.33.1).

Dependency note: the analytic crux `0 < 1/τ - 1/(e^τ - 1) < 1/2` is the sibling target
`FT13-inv-sub-inv-expm1-bounds`, which is not on main. This target must re-prove it inline (its
dossier's route is summarized in §4 step 1; it is a short monotonicity argument).

## 1. Goal

```lean
import Mathlib
import CflibsFormal.SelfAbsorption

open CflibsFormal

namespace Plan.FT13

theorem log_selfAbsorptionFactor_lipschitz {τ τ' : ℝ} (hτ : 0 ≤ τ) (hτ' : 0 ≤ τ') :
    |Real.log (selfAbsorptionFactor τ) - Real.log (selfAbsorptionFactor τ')|
      ≤ |τ - τ'| / 2 := by
  sorry
```

No new definitions. Keep the signature verbatim; helper lemmas may be added; imports are only
`Mathlib` and `CflibsFormal.SelfAbsorption` (which also brings in `CflibsFormal.Analysis`,
`CflibsFormal.ForwardMap`, `CflibsFormal.Boltzmann`).

## 2. Definition (namespace `CflibsFormal`, `SelfAbsorption.lean:63`)

```lean
noncomputable def selfAbsorptionFactor (tau : ℝ) : ℝ :=
  if tau = 0 then 1 else (1 - Real.exp (-tau)) / tau
```

Write `SA := selfAbsorptionFactor` and `ℓ τ := Real.log (SA τ)`.

## 3. Mathematics

Key identity for `τ > 0`: `SA τ = e^(-τ/2) · sinh(τ/2) / (τ/2)`, so
`ℓ τ = -τ/2 + log(sinh u / u)` with `u = τ/2`. The factor `e^(-τ/2)` is exactly where the
constant `1/2` comes from.

Derivative for `t > 0`: `ℓ t = log (1 - e^(-t)) - log t`, so
`ℓ' t = e^(-t)/(1 - e^(-t)) - 1/t = 1/(e^t - 1) - 1/t`, and the crux
`0 < 1/t - 1/(e^t - 1) < 1/2` says `-1/2 < ℓ' t < 0`.

The constant is sharp (`ℓ' t → -1/2` as `t → 0⁺`; audit numerics: largest ratio 0.999995 over
200000 random pairs), so no step may lose a constant factor.

### Route A (mean value theorem)

WLOG `τ < τ'` (the case `τ = τ'` is `0 ≤ 0`; swap with `abs_sub_comm` otherwise).
`ℓ` is continuous on `[τ, τ']` (at a point `> 0` because `SA` agrees with the smooth formula
on the open set `(0, ∞)`; at `0`, if `τ = 0`, because `SA → 1 = SA 0` from the right,
`selfAbsorptionFactor_tendsto_one`). `ℓ` has derivative `ℓ' c = 1/(e^c - 1) - 1/c` at every
`c ∈ (τ, τ') ⊂ (0, ∞)`. MVT (`exists_hasDerivAt_eq_slope`) gives
`ℓ τ' - ℓ τ = ℓ' c · (τ' - τ)` with `|ℓ' c| < 1/2`, hence the bound.

### Route B (two monotonicity facts, no limit at 0)

For `0 ≤ τ ≤ τ'`:
- lower side `ℓ τ' ≤ ℓ τ`: `SA` is antitone on `[0, ∞)` (`selfAbsorptionFactor_strictAntiOn` on
  `(0, ∞)`, plus `SA t ≤ 1 = SA 0` at the endpoint) and `log` is monotone on positives;
- upper side `ℓ τ - ℓ τ' ≤ (τ' - τ)/2`: `h t := ℓ t + t/2` is monotone on `[0, ∞)`. On
  `(0, ∞)`, `h' t = 1/2 - (1/t - 1/(e^t - 1)) > 0` (crux). At the endpoint, `h 0 = 0 ≤ h t` for
  `t > 0` is `SA t ≥ e^(-t/2)`, i.e. `e^(t/2) - e^(-t/2) ≥ t`, i.e. `sinh(t/2) ≥ t/2`
  (`Real.self_le_sinh_iff`, `Real.sinh_eq`), so no continuity argument at `0` is needed.
Then `0 ≤ ℓ τ - ℓ τ' = (h τ - h τ') + (τ' - τ)/2 ≤ (τ' - τ)/2`.

## 4. Suggested Lean decomposition

1. **Crux** (re-prove inline): `crux {t : ℝ} (ht : 0 < t) : 0 < 1/t - 1/(Real.exp t - 1) ∧
   1/t - 1/(Real.exp t - 1) < 1/2`. Lower: `Real.add_one_lt_exp ht.ne'` and
   `one_div_lt_one_div_of_lt`. Upper: `f t := Real.exp t * (t - 2) + t + 2` has `f 0 = 0` and
   `f' t = Real.exp t * (t - 1) + 1 > 0` for `t > 0` (from
   `Real.one_sub_lt_exp_neg : x ≠ 0 → 1 - x < Real.exp (-x)` times `e^t`), so `f` is strictly
   increasing on `Set.Ici 0` (`strictMonoOn_of_hasDerivWithinAt_pos (convex_Ici 0) …`,
   `interior_Ici`), so `f t > 0`, then clear denominators.
2. **Clean form on `(0, ∞)`**: `SA_eq {t} (ht : 0 < t) : selfAbsorptionFactor t =
   (1 - Real.exp (-t)) / t := by rw [selfAbsorptionFactor, if_neg ht.ne']`.
3. **Derivative**: for `t > 0`, `HasDerivAt (fun s => Real.log (selfAbsorptionFactor s))
   (1 / (Real.exp t - 1) - 1 / t) t`. Build it for the clean function
   `fun s => Real.log (1 - Real.exp (-s)) - Real.log s` (`HasDerivAt.log`, `HasDerivAt.sub`,
   `Real.hasDerivAt_log`), transfer with `HasDerivAt.congr_of_eventuallyEq` using that the two
   functions agree on `Set.Ioi 0 ∈ 𝓝 t` (`Ioi_mem_nhds ht`, `Filter.eventually_of_mem`), with
   `Real.log_div` for `log ((1 - e^(-s))/s) = log (1 - e^(-s)) - log s`. Identify the derivative
   value with `Real.exp_neg` and `field_simp`.
4. Route A: continuity on `Set.Icc τ τ'` + MVT. Route B: steps above with
   `monotoneOn_of_hasDerivWithinAt_nonneg` on `Set.Ioi 0` (open, so `interior = Ioi 0`) and the
   `sinh` endpoint.
5. Assemble with `abs_sub_comm`, `abs_of_nonneg`, `abs_le`, `le_total τ τ'`, `linarith`.

## 5. Repo lemmas in scope (namespace `CflibsFormal`)

- `selfAbsorptionFactor_pos {tau : ℝ} (htau : 0 ≤ tau) : 0 < selfAbsorptionFactor tau`
- `selfAbsorptionFactor_le_one {tau : ℝ} (htau : 0 ≤ tau) : selfAbsorptionFactor tau ≤ 1`
- `selfAbsorptionFactor_strictAntiOn : StrictAntiOn selfAbsorptionFactor (Set.Ioi 0)`
- `selfAbsorptionFactor_tendsto_one :
  Filter.Tendsto selfAbsorptionFactor (nhdsWithin 0 (Set.Ioi 0)) (nhds 1)`
- `strictAntiOn_div_of_deriv_num_neg {f g f' g' : ℝ → ℝ} (hg : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < g x)
  (hf : ∀ x ∈ Set.Ioi (0 : ℝ), HasDerivAt f (f' x) x) (hg' : ∀ x ∈ Set.Ioi (0 : ℝ),
  HasDerivAt g (g' x) x) (hnum : ∀ x ∈ Set.Ioi (0 : ℝ), f' x * g x - f x * g' x < 0) :
  StrictAntiOn (fun x => f x / g x) (Set.Ioi 0)` (`CflibsFormal/Analysis.lean:43`).

Templates from main:

```lean
-- derivative of exp(-t) (SelfAbsorption.lean, proof of selfAbsorptionFactor_strictAntiOn)
have he : HasDerivAt (fun t : ℝ => Real.exp (-t)) (Real.exp (-x) * -1) x :=
  (Real.hasDerivAt_exp (-x)).comp x ((hasDerivAt_id x).neg)

-- transferring a fact across the `if` of selfAbsorptionFactor on (0, ∞)
have heqon : Set.EqOn (fun t : ℝ => (1 - Real.exp (-t)) / t) selfAbsorptionFactor
    (Set.Ioi 0) := by
  intro t ht
  rw [selfAbsorptionFactor, if_neg (Set.mem_Ioi.mp ht).ne']

-- log SA → 0 at 0⁺ (Alt/CSigmaCurveOfGrowth.lean)
have hlog : Filter.Tendsto (fun tau => Real.log (selfAbsorptionFactor tau))
    (nhdsWithin 0 (Set.Ioi 0)) (nhds (Real.log 1)) :=
  (Real.continuousAt_log one_ne_zero).tendsto.comp selfAbsorptionFactor_tendsto_one

-- 2x < e^x - e^(-x) for x > 0 (OpacityBroadening.lean)
have hsinh : 2 * x < Real.exp x - Real.exp (-x) := by
  have h := Real.self_lt_sinh_iff.mpr hx0
  rw [Real.sinh_eq] at h
  linarith
```

## 6. Mathlib lemmas (signatures checked)

- `exists_hasDerivAt_eq_slope (f f' : ℝ → ℝ) {a b : ℝ} (hab : a < b)
  (hfc : ContinuousOn f (Set.Icc a b)) (hff' : ∀ x ∈ Set.Ioo a b, HasDerivAt f (f' x) x) :
  ∃ c ∈ Set.Ioo a b, f' c = (f b - f a) / (b - a)`
- `monotoneOn_of_hasDerivWithinAt_nonneg {D} (hD : Convex ℝ D) (hf : ContinuousOn f D)
  (hf' : ∀ x ∈ interior D, HasDerivWithinAt f (f' x) (interior D) x)
  (hf'₀ : ∀ x ∈ interior D, 0 ≤ f' x) : MonotoneOn f D`; `strictMonoOn_of_hasDerivWithinAt_pos`
  is the strict analogue.
- `HasDerivAt.log : HasDerivAt f f' x → f x ≠ 0 → HasDerivAt (fun y => Real.log (f y))
  (f' / f x) x`; `Real.hasDerivAt_log : x ≠ 0 → HasDerivAt Real.log x⁻¹ x`.
- `HasDerivAt.congr_of_eventuallyEq : HasDerivAt f f' x → f₁ =ᶠ[𝓝 x] f → HasDerivAt f₁ f' x`
- `continuousWithinAt_Ioi_iff_Ici : ContinuousWithinAt f (Set.Ioi a) a ↔
  ContinuousWithinAt f (Set.Ici a) a`; `ContinuousWithinAt.mono`; `ContinuousOn.log`.
- `Real.self_le_sinh_iff : x ≤ Real.sinh x ↔ 0 ≤ x`; `Real.self_lt_sinh_iff`;
  `Real.sinh_eq (x) : Real.sinh x = (Real.exp x - Real.exp (-x)) / 2`.
- `Real.log_le_log : 0 < x → x ≤ y → log x ≤ log y`; `Real.log_exp`; `Real.log_div`;
  `Real.log_mul`; `Real.exp_neg`; `Real.add_one_lt_exp`; `Real.one_sub_lt_exp_neg`;
  `one_div_lt_one_div_of_lt`; `interior_Ici`; `convex_Ici`; `interior_Ioi`.
- There is NO `Real.tanh_lt_self` in this Mathlib (checked).

## 7. Pitfalls

- The `if tau = 0` branch of `selfAbsorptionFactor`: never differentiate `selfAbsorptionFactor`
  directly; work with the clean formula on the open set `(0, ∞)` and transfer
  (`congr_of_eventuallyEq`, `EqOn`), exactly like `selfAbsorptionFactor_strictAntiOn` does.
- The endpoint `τ = 0` is the F07-style friction point. Route B avoids the limit entirely by
  the `sinh` inequality; prefer it if continuity at `0` starts to cost many steps.
- Constants: the target is exactly `|τ - τ'| / 2`; losing any factor (e.g. bounding `|ℓ'|` by
  `1` somewhere) makes it unprovable.
- `Real.log` of a nonpositive number is junk; carry `selfAbsorptionFactor_pos` for every `log`
  step.
- Budget: high for a worker (derivative bookkeeping plus the endpoint). Splitting the crux,
  the derivative identity and the endpoint into separate helper lemmas is strongly advised.

## Addendum 2026-09-25: the crux is now proved

The sibling target `FT13-inv-sub-inv-expm1-bounds` passed independent verification (kernel
replay, standard axioms only). It is still not on main, so copy the helper lemmas below into
this proof verbatim, above the target theorem, instead of re-deriving them:

```lean

namespace Plan.FT13

theorem exp_mul_one_sub_lt_one {x : ℝ} (hx : 0 < x) :
    Real.exp x * (1 - x) < 1 := by
  have h1 : 1 - x < Real.exp (-x) := Real.one_sub_lt_exp_neg hx.ne'
  have h2 : Real.exp x * (1 - x) < Real.exp x * Real.exp (-x) :=
    mul_lt_mul_of_pos_left h1 (Real.exp_pos x)
  rwa [← Real.exp_add, add_neg_cancel, Real.exp_zero] at h2

theorem f_hasDerivAt (t : ℝ) :
    HasDerivAt (fun t => Real.exp t * (t - 2) + t + 2)
      (Real.exp t * (t - 2) + Real.exp t * 1 + 1) t :=
  (((Real.hasDerivAt_exp t).mul ((hasDerivAt_id t).sub_const 2)).add (hasDerivAt_id t)).add_const 2

theorem f_pos {τ : ℝ} (hτ : 0 < τ) : 0 < Real.exp τ * (τ - 2) + τ + 2 := by
  have hmono : StrictMonoOn (fun t => Real.exp t * (t - 2) + t + 2) (Set.Ici (0:ℝ)) := by
    refine strictMonoOn_of_hasDerivWithinAt_pos (convex_Ici (0:ℝ)) ?_
      (fun x _ => (f_hasDerivAt x).hasDerivWithinAt) ?_
    · fun_prop
    · intro x hx
      rw [interior_Ici] at hx
      have hx' : 0 < x := hx
      nlinarith [exp_mul_one_sub_lt_one hx', Real.exp_pos x]
  have h0 : (0:ℝ) ∈ Set.Ici (0:ℝ) := Set.mem_Ici.mpr le_rfl
  have hτ' : τ ∈ Set.Ici (0:ℝ) := Set.mem_Ici.mpr hτ.le
  have := hmono h0 hτ' hτ
  simp at this
  linarith

theorem inv_sub_inv_exp_sub_one_mem {τ : ℝ} (hτ : 0 < τ) :
    0 < 1 / τ - 1 / (Real.exp τ - 1) ∧ 1 / τ - 1 / (Real.exp τ - 1) < 1 / 2 := by
  constructor
  · have hlt : τ < Real.exp τ - 1 := by linarith [Real.add_one_lt_exp hτ.ne']
    have := one_div_lt_one_div_of_lt hτ hlt
    linarith
  · have hE : 0 < Real.exp τ - 1 := by linarith [Real.add_one_lt_exp hτ.ne']
    have hf := f_pos hτ
    rw [div_sub_div _ _ hτ.ne' hE.ne', div_lt_div_iff₀ (mul_pos hτ hE) (by norm_num : (0:ℝ) < 2)]
    nlinarith [hf, Real.exp_pos τ]

end Plan.FT13
```
