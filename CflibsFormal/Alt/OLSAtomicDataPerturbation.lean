/-
Copyright (c) 2026 Brian Squires. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Squires
-/
import Mathlib
import CflibsFormal.OLS
import CflibsFormal.ErrorBudget
import CflibsFormal.Analysis
import CflibsFormal.AtomicDataPerturbation
import CflibsFormal.Alt.LeastSquares

/-!
# CF-LIBS formalization — per-line atomic-data error in the OLS density reader

`AtomicDataPerturbation.lean` covers the SINGLE-LINE `Classic.classicDensity` reader under
wrong atomic data `(g', E', A')`: `classicDensity_aliasing` (EXACT) shows the recovered
density is the true density scaled by a ratio of response factors, and
`classicDensity_aliasing_error` / `classicComposition_atomicData_error` turn that into a
REDUCED error budget. This module proves the **OLS mirror** for the MULTI-LINE
`Alt.olsDensity` reader (`Alt/LeastSquares.lean`), populating the previously empty
(multi-line reader × atomic-data error) cell (Frontier 05).

## The key observation

The Boltzmann-plot ordinate the OLS reader fits from measured intensities is
`ŷ_k = log(I_k/(g_k A'_k))`. With the true spectrum emitted at density `N` with the TRUE
transition probabilities `A` (correct `g`, `E`; the `A`-channel, the physically dominant
CF-LIBS atomic-data error per Tognoni et al. 2010),
```
ŷ_k = y_k^true + log((A_k)/(A'_k)),        y_k^true = olsBoltzmannOrdinate … k.
```
So a per-line atomic-data error is **exactly an additive per-line ordinate error**
`δ_k = log(A_k/A'_k)`. Because `olsIntercept` is linear in the ordinates
(`olsIntercept E (f + h) = olsIntercept E f + olsIntercept E h`, from linearity of `mean` and,
via `olsSlope_eq_centered`, of `olsSlope` — proved here as private helpers `mean_add` /
`olsSlope_add` / `olsIntercept_add`), the intercept shift is an **EXACT identity, with no
approximation and no centering needed**:
```
N̂ = olsDensity … A' I = N · exp(olsIntercept E (fun k => log(A_k/A'_k))).
```
This is the OLS mirror of `classicDensity_aliasing`
(`olsDensity_aliasing_A`). In the repo's centered Boltzmann-plot convention
(`mean E = 0`) `olsIntercept E δ = mean δ`, so the multiplicative bias is exactly the
**geometric mean** of the per-line data ratios `A_k/A'_k` — the formal reason the multi-line
reader tolerates a single bad line better than the single-line reader (which carries the raw,
undivided ratio): a single outlier `δ_k` is divided by `n`. `olsDensity_aliasing_A_error`
turns the identity into a REDUCED closed-form bound via `olsIntercept_stable_hetero`
(`ErrorBudget.lean`) and `abs_log_ratio_le` (`Analysis.lean`), and
`olsComposition_atomicData_error` propagates the per-species density bound into the
recovered composition via `composition_abs_sub_le_uniform` (`ErrorBudget.lean`), exactly as
`classicComposition_atomicData_error` does for the classic reader.

## Honest scope

* `olsDensity_aliasing_A` is **EXACT**: a faithful cancellation identity (`U` is
  `A`-independent so the partition-function factor is untouched — the "A-channel" of the
  three atomic-data sub-channels `g,E,A`), no centering hypothesis, no approximation.
* `olsDensity_aliasing_A_error` / `olsComposition_atomicData_error` are **REDUCED**: the
  per-line log-ratios `log(A_k/A'_k)` are lumped through the centered-convention intercept
  bound `olsIntercept_stable_hetero` (so `hcent : mean E = 0` is required, the repo's
  standard Boltzmann-plot normalization — WLOG on the energy origin, since a shift is
  absorbed into the intercept) and the two-sided log-transfer bound `abs_log_ratio_le`.
* **This is a worst-case BIAS bound, not a variance bound — do NOT read it as
  "more lines ⇒ better".** `δ_k = log(A_k/A'_k)` is a fixed, systematic atomic-data error, not
  zero-mean measurement noise; the `olsSlope_noise_gain` / `Alt.OLSVariance` machinery that
  underwrites the statistical "more lines ⇒ lower variance" rule does not apply here. The
  geometric mean divides an outlier `δ_k` by `n`, but a uniformly-signed systematic error
  (e.g. every tabulated `A'_k` biased the same direction) is **not** averaged away:
  `exp(mean δ) ≠ 1` even as `n → ∞` if the `δ_k` share a sign. This mirrors the honest-scope
  note already in `ErrorBudget.lean`.
* Only the **A-channel** (`g` and `E` correct, `A'` wrong) is closed here; the `g`-channel
  (which perturbs the partition function `U` too) and the `E`-channel (which perturbs the
  fit abscissa itself, breaking the affine collinearity) are deferred — see the frontier
  dossier `docs/frontiers/05-heterogeneous-delta.md`.

## Literature

Tognoni, Cristoforetti, Legnaioli, Palleschi, "Calibration-Free LIBS: State of the art,"
*Spectrochim. Acta B* **65** (2010) 1–14 — atomic-parameter (chiefly transition-probability)
uncertainty is the dominant CF-LIBS accuracy contributor once the plasma is characterized;
the citation already carried by the classic-method mirror `classicDensity_aliasing` /
`classicComposition_atomicData_error` (`AtomicDataPerturbation.lean`). The
"OLS averages atomic-data errors in the log domain (geometric mean)" reading is a *derived*
algebraic consequence of the affine structure, not itself a literature claim.
-/

namespace CflibsFormal.Alt

open CflibsFormal
open Finset Real
open scoped BigOperators

variable {ι : Type*} [Fintype ι]
variable {κ : Type*} [Fintype κ]

/-! ## Additivity helpers (private, pure algebra)

`olsIntercept` is linear in the ordinates: `mean` is linear by `Finset.sum_add_distrib`, and
`olsSlope` is linear via its centered representation `olsSlope_eq_centered` (a common
denominator `SS_E`, so the numerator sum splits). These three helpers are the algebraic
lever behind the EXACT identity `olsDensity_aliasing_A`. -/

private theorem mean_add [Nonempty ι] (f h : ι → ℝ) :
    mean (fun k => f k + h k) = mean f + mean h := by
  unfold mean
  rw [Finset.sum_add_distrib, add_div]

private theorem olsSlope_add [Nonempty ι] (E f h : ι → ℝ) :
    olsSlope E (fun k => f k + h k) = olsSlope E f + olsSlope E h := by
  rw [olsSlope_eq_centered, olsSlope_eq_centered, olsSlope_eq_centered, ← add_div]
  congr 1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  ring

private theorem olsIntercept_add [Nonempty ι] (E f h : ι → ℝ) :
    olsIntercept E (fun k => f k + h k) = olsIntercept E f + olsIntercept E h := by
  unfold olsIntercept
  rw [mean_add, olsSlope_add]
  ring

/-! ## M2 — the EXACT aliasing identity (the OLS mirror of `classicDensity_aliasing`) -/

/-- **EXACT aliasing identity, OLS density reader, A-channel.** The spectrum is emitted with
the TRUE transition probabilities `A` (correct `g`, `E`) at density `N`; the analyst inverts
ALL lines with the WRONG `A'` via the multi-line OLS Boltzmann-plot fit. The recovered
density is exactly the true density scaled by the exponential of the OLS INTERCEPT of the
per-line log-ratios `log(A_k/A'_k)`:
  `N̂ = N · exp(olsIntercept E (fun k => log(A_k/A'_k)))`.
This is the OLS mirror of `classicDensity_aliasing`: the single-line reader carries the raw
ratio of response factors, the multi-line OLS reader carries its intercept — the log-domain
(geometric-mean, in the centered convention) AVERAGE of the per-line data ratios. Proof: the
observed ordinate splits as `ŷ_k = y_k^true + log(A_k/A'_k)` (via `Real.log_mul` on
`I_k/(g_k A'_k) = (I_k/(g_k A_k))·(A_k/A'_k)`, all factors positive), `olsIntercept` is linear
in the ordinate (`olsIntercept_add`), the true-ordinate intercept is `log(Fcal·N/U)`
(`olsIntercept_of_forward`), and `Real.exp_add` + `Real.exp_log` repackage the sum of
intercepts into `N · exp(...)`. `U` is untouched (`partitionFunction` does not depend on `A`),
so no `g`/`U`-channel factor appears — this is the clean single-channel EXACT identity. -/
theorem olsDensity_aliasing_A [Nonempty ι] {kB T N Fcal : ℝ} {g E A A' : ι → ℝ}
    (hg : ∀ k, 0 < g k) (hN : 0 < N) (hFcal : 0 < Fcal)
    (hA : ∀ k, 0 < A k) (hA' : ∀ k, 0 < A' k)
    (hvar : 0 < ∑ k, (E k - mean E) ^ 2) :
    olsDensity kB T Fcal g E A' (fun k => lineIntensity kB T N Fcal g E A k)
      = N * Real.exp (olsIntercept E (fun k => Real.log (A k / A' k))) := by
  unfold olsDensity
  have hU : 0 < partitionFunction kB T g E := partitionFunction_pos hg
  have hsplit : (fun k => Real.log (lineIntensity kB T N Fcal g E A k / (g k * A' k)))
      = (fun k => olsBoltzmannOrdinate kB T N Fcal g E A k + Real.log (A k / A' k)) := by
    funext k
    have hI : 0 < lineIntensity kB T N Fcal g E A k := lineIntensity_pos hg hN hFcal hA k
    have hgk : 0 < g k := hg k
    have hAk : 0 < A k := hA k
    have hA'k : 0 < A' k := hA' k
    unfold olsBoltzmannOrdinate
    have hrw : lineIntensity kB T N Fcal g E A k / (g k * A' k)
          = (lineIntensity kB T N Fcal g E A k / (g k * A k)) * (A k / A' k) := by
      field_simp
    rw [hrw, Real.log_mul (by positivity) (by positivity)]
  rw [hsplit, olsIntercept_add, olsIntercept_of_forward hg hN hFcal hA hvar, Real.exp_add,
    Real.exp_log (by positivity)]
  field_simp

/-- **Non-vacuity witness for `olsDensity_aliasing_A`.** Two lines (`ι = Fin 2`), unit
degeneracies and calibration, energies `E = (0,1)`, TRUE transition probabilities
`A = (1,2)` perturbed to a genuinely WRONG `A' = (1,3)` (line 1 off by 50%), density `N = 2`:
all positivity hypotheses hold and `hvar` (`SS_E = 1/2 > 0`) is satisfied by the distinct
energies, so the identity is non-vacuously exercised on a genuine `A ≠ A'` mismatch. -/
private def nvA05Kb : ℝ := 1
private def nvA05T : ℝ := 1
private def nvA05N : ℝ := 2
private def nvA05Fcal : ℝ := 1
private def nvA05g : Fin 2 → ℝ := ![1, 1]
private def nvA05E : Fin 2 → ℝ := ![0, 1]
private def nvA05A : Fin 2 → ℝ := ![1, 2]
private def nvA05A' : Fin 2 → ℝ := ![1, 3]

example :
    olsDensity nvA05Kb nvA05T nvA05Fcal nvA05g nvA05E nvA05A'
        (fun k => lineIntensity nvA05Kb nvA05T nvA05N nvA05Fcal nvA05g nvA05E nvA05A k)
      = nvA05N * Real.exp (olsIntercept nvA05E (fun k => Real.log (nvA05A k / nvA05A' k))) :=
  olsDensity_aliasing_A
    (g := nvA05g) (E := nvA05E) (A := nvA05A) (A' := nvA05A')
    (by intro k; fin_cases k <;> norm_num [nvA05g])
    (by norm_num [nvA05N])
    (by norm_num [nvA05Fcal])
    (by intro k; fin_cases k <;> norm_num [nvA05A])
    (by intro k; fin_cases k <;> norm_num [nvA05A'])
    (by simp [mean, nvA05E, Fin.sum_univ_two]; norm_num)

/-! ## M3 — REDUCED closed-form error bound -/

/-- **REDUCED closed-form density-error bound, OLS reader, A-channel.** In the centered
Boltzmann-plot convention (`mean E = 0`) with a per-line RELATIVE transition-probability
error `|A'_k − A_k| ≤ δ_k·A_k` (`δ_k < 1`), the recovered density obeys
  `|N̂ − N| ≤ N·(exp(η) − 1)`,   `η = (∑_k δ_k/(1−δ_k)) / card ι`.
Derivation: `olsDensity_aliasing_A` gives the EXACT `N̂ − N = N·(exp(olsIntercept E δlog) − 1)`
with `δlog_k = log(A_k/A'_k)`; `abs_log_ratio_le` bounds each `|δlog_k| ≤ δ_k/(1−δ_k)`;
`olsIntercept_stable_hetero` (centered convention) bounds the intercept of `δlog` against the
zero ordinate by the AVERAGE `η` of those per-line bounds; `abs_exp_sub_one_le` closes the
exponential step. REDUCED because the per-line `δ_k` are lumped into the single average `η`
(rather than kept fully per-line downstream) and the centered convention (`mean E = 0`) is
assumed. **Honest scope — bias, not variance**: `η` is the worst-case average of a SYSTEMATIC
per-line error, not a statistical standard error; a uniformly-signed `δ_k` does not shrink as
`card ι` grows (`exp η − 1` does not vanish as `n → ∞` unless the signed average `η → 0`). -/
theorem olsDensity_aliasing_A_error [Nonempty ι] {kB T N Fcal : ℝ} {g E A A' δ : ι → ℝ}
    (hg : ∀ k, 0 < g k) (hN : 0 < N) (hFcal : 0 < Fcal)
    (hA : ∀ k, 0 < A k) (hA' : ∀ k, 0 < A' k)
    (hvar : 0 < ∑ k, (E k - mean E) ^ 2) (hcent : mean E = 0)
    (hδ1 : ∀ k, δ k < 1)
    (hpert : ∀ k, |A' k - A k| ≤ δ k * A k) :
    |olsDensity kB T Fcal g E A' (fun k => lineIntensity kB T N Fcal g E A k) - N|
      ≤ N * (Real.exp ((∑ k, δ k / (1 - δ k)) / (Fintype.card ι)) - 1) := by
  rw [olsDensity_aliasing_A hg hN hFcal hA hA' hvar]
  set x := olsIntercept E (fun k => Real.log (A k / A' k)) with hx_def
  have hxbound : |x| ≤ (∑ k, δ k / (1 - δ k)) / (Fintype.card ι) := by
    have hzero : olsIntercept E (fun _ : ι => (0:ℝ)) = 0 := by
      have hmean0 : mean (fun _ : ι => (0:ℝ)) = 0 := by unfold mean; simp
      have hslope0 : olsSlope E (fun _ : ι => (0:ℝ)) = 0 := by
        unfold olsSlope mean; simp
      unfold olsIntercept
      rw [hmean0, hslope0]; ring
    have hb := olsIntercept_stable_hetero (E := E) (y := fun _ : ι => (0:ℝ))
      (yHat := fun k => Real.log (A k / A' k)) (eps := fun k => δ k / (1 - δ k))
      hcent (fun k => by
        rw [sub_zero]
        exact abs_log_ratio_le (hA k) (hA' k) (hδ1 k) (hpert k))
    rw [hzero, sub_zero] at hb
    exact hb
  have heq : N * Real.exp x - N = N * (Real.exp x - 1) := by ring
  rw [heq, abs_mul, abs_of_pos hN]
  exact mul_le_mul_of_nonneg_left (abs_exp_sub_one_le hxbound) hN.le

/-- **Non-vacuity witness for `olsDensity_aliasing_A_error`.** Two lines with CENTERED
energies `E = (-1,1)` (`mean E = 0`, `SS_E = 2 > 0`), the same `A = (1,2)`, `A' = (1,3)`
mismatch as the M2 witness, and a genuinely PER-LINE relative-error budget `δ = (0, 0.6)`
(line 0 exact, `δ₀ = 0`; line 1 at a real `60%` budget, `δ₁ = 0.6 < 1`, and
`|A'₁ − A₁| = 1 ≤ 0.6·2 = 1.2`): all hypotheses are jointly satisfiable on a genuine
heteroscedastic budget. -/
private def nvA05Ec : Fin 2 → ℝ := ![-1, 1]
private def nvA05Delta : Fin 2 → ℝ := ![0, 0.6]

example :
    |olsDensity nvA05Kb nvA05T nvA05Fcal nvA05g nvA05Ec nvA05A'
        (fun k => lineIntensity nvA05Kb nvA05T nvA05N nvA05Fcal nvA05g nvA05Ec nvA05A k)
      - nvA05N|
      ≤ nvA05N * (Real.exp
          ((∑ k, nvA05Delta k / (1 - nvA05Delta k)) / (Fintype.card (Fin 2))) - 1) :=
  olsDensity_aliasing_A_error
    (g := nvA05g) (E := nvA05Ec) (A := nvA05A) (A' := nvA05A') (δ := nvA05Delta)
    (by intro k; fin_cases k <;> norm_num [nvA05g])
    (by norm_num [nvA05N])
    (by norm_num [nvA05Fcal])
    (by intro k; fin_cases k <;> norm_num [nvA05A])
    (by intro k; fin_cases k <;> norm_num [nvA05A'])
    (by simp [mean, nvA05Ec, Fin.sum_univ_two])
    (by simp [mean, nvA05Ec, Fin.sum_univ_two])
    (by intro k; fin_cases k <;> norm_num [nvA05Delta])
    (by intro k; fin_cases k <;> norm_num [nvA05A, nvA05A', nvA05Delta])

/-! ## M4 — composition corollary -/

/-- **Per-species OLS density reader under wrong `A'`.** For each species `s` the analyst
inverts that species' FULL line vector — emitted with TRUE `A s` at density `N s` — using the
WRONG `A' s` (correct `g s`, `E s`). Pure packaging (a `κ → ℝ` density vector) so the
composition corollary reads cleanly; not an estimator. -/
noncomputable def olsRecoveredDensity (kB T Fcal : ℝ) (g E A A' : κ → ι → ℝ) (N : κ → ℝ)
    (s : κ) : ℝ :=
  olsDensity kB T Fcal (g s) (E s) (A' s)
    (fun k => lineIntensity kB T (N s) Fcal (g s) (E s) (A s) k)

/-- **REDUCED composition corollary, OLS reader, A-channel.** Feeding the per-species
`olsDensity_aliasing_A_error` bound into `composition_abs_sub_le_uniform`
(`ErrorBudget.lean`) via a uniform density-error cap `delta` (an analyst-supplied bound on
`N_s·(exp(η_s) − 1)` across all species, exactly as `classicComposition_atomicData_error`
lumps its per-species bound into a uniform `δ`, `Nmax`), the recovered composition error is
controlled by the atomic-data error:
  `|Ĉ_s − C_s| ≤ (card κ + 1)·delta / Ŝ`.
REDUCED: the per-species, per-line `δ_{s,k}` are collapsed through `olsDensity_aliasing_A_error`
into the single uniform cap `delta`; the composition algebra itself is exact
(`composition_abs_sub_le_uniform`). Same honest bias-not-variance scope as
`olsDensity_aliasing_A_error`: `delta` bounds a worst-case SYSTEMATIC per-species bias, not a
statistical composition variance. -/
theorem olsComposition_atomicData_error [Nonempty ι] [Nonempty κ]
    {kB T Fcal delta : ℝ} {N : κ → ℝ} {g E A A' : κ → ι → ℝ} {δ : κ → ι → ℝ}
    (hg : ∀ s k, 0 < g s k) (hN : ∀ s, 0 < N s) (hFcal : 0 < Fcal)
    (hA : ∀ s k, 0 < A s k) (hA' : ∀ s k, 0 < A' s k)
    (hvar : ∀ s, 0 < ∑ k, (E s k - mean (E s)) ^ 2)
    (hcent : ∀ s, mean (E s) = 0)
    (hδ1 : ∀ s k, δ s k < 1)
    (hpert : ∀ s k, |A' s k - A s k| ≤ δ s k * A s k)
    (hdelta : ∀ s, N s * (Real.exp ((∑ k, δ s k / (1 - δ s k)) / (Fintype.card ι)) - 1) ≤ delta)
    (s : κ) :
    |composition (olsRecoveredDensity kB T Fcal g E A A' N) s - composition N s|
      ≤ ((Fintype.card κ : ℝ) + 1) * delta
          / totalDensity (olsRecoveredDensity kB T Fcal g E A A' N) := by
  have haliasing : ∀ t, olsRecoveredDensity kB T Fcal g E A A' N t
      = N t * Real.exp (olsIntercept (E t) (fun k => Real.log (A t k / A' t k))) := by
    intro t
    unfold olsRecoveredDensity
    exact olsDensity_aliasing_A (hg t) (hN t) hFcal (hA t) (hA' t) (hvar t)
  have hNhat_pos : ∀ t, 0 < olsRecoveredDensity kB T Fcal g E A A' N t := by
    intro t
    rw [haliasing t]
    exact mul_pos (hN t) (Real.exp_pos _)
  have hN0 : ∀ t, 0 ≤ N t := fun t => (hN t).le
  have hStot : 0 < totalDensity N := totalDensity_pos hN
  have hShat : 0 < totalDensity (olsRecoveredDensity kB T Fcal g E A A' N) :=
    totalDensity_pos hNhat_pos
  have hbound : ∀ t, |olsRecoveredDensity kB T Fcal g E A A' N t - N t| ≤ delta := by
    intro t
    have hstep : |olsRecoveredDensity kB T Fcal g E A A' N t - N t|
        ≤ N t * (Real.exp ((∑ k, δ t k / (1 - δ t k)) / (Fintype.card ι)) - 1) := by
      unfold olsRecoveredDensity
      exact olsDensity_aliasing_A_error (hg t) (hN t) hFcal (hA t) (hA' t) (hvar t)
        (hcent t) (hδ1 t) (hpert t)
    exact hstep.trans (hdelta t)
  exact composition_abs_sub_le_uniform hN0 hStot hShat hbound s

end CflibsFormal.Alt
