# FT20-equivWidth-stepProfile: closed-form equivalent width of the two-step profile

Planning dossier for the proof queue (frontier FT-20 (b), decomposition item 1; audit verdict
REVISE, revision applied). Written for a planner who cannot open the repository. Every repo
definition is quoted verbatim; every Mathlib name was checked with `#check` against the pinned
Mathlib (v4.33.1, `lean-main`). The route in §4 was compiled end-to-end in a scratch file on
2026-09-27 (no errors), so treat it as a verified skeleton, not a guess.

## 1. Goal

```lean
import Mathlib
import CflibsFormal.EquivalentWidth

open CflibsFormal

namespace Plan.FT20

noncomputable def stepProfile (η M : ℝ) : ℝ → ℝ := fun x =>
  Set.indicator (Set.Icc 0 1) (fun _ => 1) x + η * Set.indicator (Set.Icc 0 M) (fun _ => 1) x

theorem equivWidth_stepProfile {η M τ : ℝ} (hM : 1 ≤ M) :
    equivWidth (stepProfile η M) τ
      = (1 - Real.exp (-(τ * (1 + η)))) + (M - 1) * (1 - Real.exp (-(τ * η))) := by
  sorry
```

Keep `stepProfile` and the signature verbatim. Helper lemmas are fine. Imports: only `Mathlib`
and `CflibsFormal.EquivalentWidth`. Put `open MeasureTheory` inside the proof or after the
namespace line if you need it; do not change the def.

## 2. Repo definitions (namespace `CflibsFormal`, `EquivalentWidth.lean:75`)

```lean
noncomputable def equivWidth (φ : ℝ → ℝ) (τ : ℝ) : ℝ :=
  ∫ x, (1 - Real.exp (-(τ * φ x)))
```

A Bochner integral over all of `ℝ` for `volume`. A non-integrable integrand integrates to `0`,
so integrability must be proved (it is easy here: indicators of bounded intervals).

The model proof is the repo's flat case (`EquivalentWidth.lean:130`), verbatim:

```lean
theorem equivWidth_rectangular (τ : ℝ) :
    equivWidth (Set.indicator (Set.Icc 0 1) (fun _ => 1)) τ = 1 - Real.exp (-τ) := by
  have hrw : (fun x => 1 - Real.exp (-(τ * Set.indicator (Set.Icc (0:ℝ) 1) (fun _ => 1) x)))
      = Set.indicator (Set.Icc 0 1) (fun _ => 1 - Real.exp (-τ)) := by
    funext x
    by_cases hx : x ∈ Set.Icc (0:ℝ) 1
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]; norm_num
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]; norm_num
  rw [equivWidth, hrw, integral_indicator_const _ measurableSet_Icc, measureReal_def,
    Real.volume_Icc]
  simp
```

## 3. Mathematics

For `M ≥ 1`, pointwise in `x`:
`1 - exp (-(τ ψ x)) = 1_[0,1](x) (1 - e^{-τ(1+η)}) + 1_(1,M](x) (1 - e^{-τη})`.
Cases: `x ∈ [0,1]` (then `x ∈ [0,M]`, `ψ = 1 + η`); `x ∈ (1,M]` (`ψ = η`); otherwise
(`x < 0` or `x > M`, `ψ = 0`, both sides `0`). Integrate: `vol [0,1] = 1`, `vol (1,M] = M - 1`.
No condition on `η` or `τ` is needed (midpoint-rule check agrees to 1e-6 at
`(η, M, τ) = (0.01, 20, 3), (-0.3, 5, 2), (0.5, 1, -1.5)`). `M ≥ 1` is needed.

## 4. Route (compiled in scratch, 2026-09-27)

```lean
  have hrw : (fun x => 1 - Real.exp (-(τ * stepProfile η M x)))
      = fun x => Set.indicator (Set.Icc 0 1) (fun _ => 1 - Real.exp (-(τ * (1 + η)))) x
          + Set.indicator (Set.Ioc 1 M) (fun _ => 1 - Real.exp (-(τ * η))) x := by
    funext x
    unfold stepProfile
    by_cases h1 : x ∈ Set.Icc (0:ℝ) 1
    · have hM' : x ∈ Set.Icc (0:ℝ) M := ⟨h1.1, by linarith [h1.2]⟩
      have h2 : x ∉ Set.Ioc (1:ℝ) M := fun h => by linarith [h.1, h1.2]
      simp only [Set.indicator_of_mem h1, Set.indicator_of_mem hM', Set.indicator_of_notMem h2]
      ring_nf
    · by_cases h2 : x ∈ Set.Ioc (1:ℝ) M
      · -- x ∈ Icc 0 M; simp only [..notMem h1, ..mem hM', ..mem h2]; ring_nf
      · -- x ∉ Icc 0 M (split on x ≤ 1); simp only [three notMem]; simp
  have hi1 : Integrable (Set.indicator (Set.Icc (0:ℝ) 1)
      (fun _ => 1 - Real.exp (-(τ * (1 + η))))) :=
    (integrable_indicator_iff measurableSet_Icc).2 (integrableOn_const measure_Icc_lt_top.ne)
  have hi2 : Integrable (Set.indicator (Set.Ioc (1:ℝ) M)
      (fun _ => 1 - Real.exp (-(τ * η)))) :=
    (integrable_indicator_iff measurableSet_Ioc).2 (integrableOn_const measure_Ioc_lt_top.ne)
  rw [equivWidth, hrw, integral_add hi1 hi2, integral_indicator_const _ measurableSet_Icc,
    integral_indicator_const _ measurableSet_Ioc, measureReal_def, measureReal_def,
    Real.volume_Icc, Real.volume_Ioc, ENNReal.toReal_ofReal (by norm_num),
    ENNReal.toReal_ofReal (by linarith)]
  simp
```
(needs `open MeasureTheory`; the two elided branches follow the first one exactly.)

## 5. Mathlib lemmas (checked)

- `MeasureTheory.integral_add : Integrable f μ → Integrable g μ → ∫ a, f a + g a ∂μ = ...`
- `MeasureTheory.integral_indicator_const (e : E) ⦃s⦄ : MeasurableSet s →
  ∫ x, s.indicator (fun _ => e) x ∂μ = μ.real s • e`; `MeasureTheory.integral_indicator`
- `MeasureTheory.integrable_indicator_iff : MeasurableSet s → (Integrable (s.indicator f) μ ↔
  IntegrableOn f s μ)`; `MeasureTheory.integrableOn_const` (autoParams `μ s ≠ ⊤`, `‖C‖ₑ ≠ ⊤`);
  `MeasureTheory.IntegrableOn.integrable_indicator`; `measure_Icc_lt_top`, `measure_Ioc_lt_top`
- `MeasureTheory.measureReal_def : μ.real s = (μ s).toReal`; `Real.volume_Icc`, `Real.volume_Ioc`
  (`= ENNReal.ofReal (b - a)`); `ENNReal.toReal_ofReal : 0 ≤ r → (ENNReal.ofReal r).toReal = r`
- `Set.indicator_of_mem : a ∈ s → ∀ f, s.indicator f a = f a`; `Set.indicator_of_notMem`
- `measurableSet_Icc`, `measurableSet_Ioc`

## 6. Pitfalls

- `integrableOn_const` alone fails: its default tactic cannot prove `volume (Set.Icc 0 1) ≠ ⊤`.
  Pass `measure_Icc_lt_top.ne` / `measure_Ioc_lt_top.ne` explicitly.
- Use `Set.Ioc 1 M` for the wing, not `Icc`, so the pointwise identity holds at `x = 1`.
- `rw [Set.indicator_of_mem h]` rewrites one instantiation of `f` only; use `simp only [...]`.
- The name is `Set.indicator_of_notMem` (not `..._nmem`).
- Do not add hypotheses on `η` or `τ`; the signature has only `hM`.

## 7. Scope reading

PURE-MATH: an exact integral identity for a surrogate kernel. `stepProfile` is not a physical
line shape; it is the counterexample kernel behind FT-20 (b). With `η = 0` it collapses to
`equivWidth_rectangular`. Curve of growth: Gornushkin et al., Spectrochim. Acta B 54 (1999)
491-503; equivalent width: Mihalas, Stellar Atmospheres (1978).
