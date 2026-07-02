/-
Copyright (c) 2026 Brian Squires. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Squires
-/
import Mathlib
import CflibsFormal.OLS
import CflibsFormal.LeastSquaresFit
import CflibsFormal.Boltzmann
import CflibsFormal.ForwardMap
import CflibsFormal.Closure
import CflibsFormal.Classic

/-!
# CF-LIBS formalization — the multi-line ordinary-least-squares Boltzmann-plot estimator

This module formalizes an **alternative** calibration-free CF-LIBS composition estimator
that fits ALL lines of a species by **ordinary least squares (OLS)** rather than using only
two lines for the slope (the classic method).

The Boltzmann-plot ordinate of line `k` is
  `y_k = log (I_k / (g_k A_k)) = −E_k / (k_B T) + b`,
with intercept `b = log (Fcal · N / U(T))` — exactly `ForwardMap.boltzmann_plot_intensity`.
The intercept carries the species concentration (Ciucci et al. 1999). The classic method
uses TWO lines for the slope; this alternative fits ALL `n` lines of a species by OLS.

Given a `Fintype` `ι` of lines and points `(E_k, y_k)`, the core `OLS` module defines
  `Ebar = (∑ E_k) / card`,   `ybar = (∑ y_k) / card`,
  `olsSlope     = (∑_k (E_k − Ebar)(y_k − ybar)) / (∑_k (E_k − Ebar)²)`,
  `olsIntercept = ybar − olsSlope · Ebar`.

The OLS algebra — `mean`, `olsSlope`, `olsIntercept`, and the crux `OLS.ols_recovers_line`
(noise-free collinear points ⇒ OLS recovers the exact slope `m0` and intercept `b0`, a genuine
Finset covariance/variance identity) — lives in the core `OLS` module and is reused here
verbatim. On top of it we prove the *physics*:

* `olsIntercept_of_forward` — the OLS intercept of the FORWARD-MODEL Boltzmann-plot
  ordinates equals the composition-bearing offset `q_s = log (Fcal·N/U)`.
* `olsDensity_recovers` — feeding a species' FULL forward-model spectrum through the OLS
  density reader recovers the true density `N`.
* `leastSquares_sound` — **MAIN soundness:** run on the genuine multi-line forward-model
  spectrum (full per-species line vector, no `N` input), the OLS estimator returns the
  TRUE composition `C_s = N_s / ∑ N`.
* `leastSquares_agrees_classic` — **same-spectrum agreement on the noise-free forward
  fixpoint:** fed the SAME underlying forward spectrum (OLS reads the full per-species line
  vector, classic reads the single chosen line `u t` of that very same spectrum), the two
  genuinely different procedures return the SAME composition — a corollary of joint soundness
  (both land on `composition N`). NOT claimed off the fixpoint: on noisy data the two
  disagree, and that robustness is the point of the OLS variant.

Two index types appear: `κ` (species/stages, from `Closure.lean`) and `ι` (energy levels,
from `Boltzmann.lean` / `ForwardMap.lean`). This is the ALTERNATIVE method
(namespace `CflibsFormal.Alt`); it reuses the core forward map verbatim.

## Literature

This formalizes the least-squares variant of the calibration-free LIBS Boltzmann-plot
method. The founding CF-LIBS procedure — in which the Boltzmann-plot INTERCEPT yields the
species concentration — is Ciucci, A.; Corsi, M.; Palleschi, V.; Rastelli, S.; Salvetti,
A.; Tognoni, E. "New Procedure for Quantitative Elemental Analysis by Laser-Induced Plasma
Spectroscopy." *Applied Spectroscopy* **53** (1999) 960–964. The use of least-squares
regression over MANY lines of a species to improve the intercept (and slope) estimate is
reviewed in Tognoni, E.; Cristoforetti, G.; Legnaioli, S.; Palleschi, V. "Calibration-Free
Laser-Induced Breakdown Spectroscopy: State of the art." *Spectrochimica Acta Part B*
**65** (2010) 1–14. The mean / covariance / variance helpers (`mean`, `olsSlope`, now in the
core `OLS` module) are plain arithmetic and carry no specific citation; the physics content lives in
`olsIntercept_of_forward` and `leastSquares_sound`, which match the intercept-borne
concentration of Ciucci et al. (1999) recovered by the multi-line regression of Tognoni et
al. (2010).
-/

namespace CflibsFormal.Alt

open CflibsFormal
open Finset Real
open scoped BigOperators

variable {ι : Type*} [Fintype ι]
variable {κ : Type*} [Fintype κ]

/-- The Boltzmann-plot ordinate `y_k = log (I_k / (g_k A_k))` built from a (measured /
forward-model) line intensity. By `ForwardMap.boltzmann_plot_intensity` it equals
`log (Fcal·N/U) − E_k/(k_B T)`, i.e. affine in `E k`; this is the per-line observation fed
to the OLS fit. -/
noncomputable def olsBoltzmannOrdinate (kB T N Fcal : ℝ) (g E A : ι → ℝ) (k : ι) : ℝ :=
  Real.log (lineIntensity kB T N Fcal g E A k / (g k * A k))

/-- The forward-model Boltzmann-plot ordinates are AFFINE in the energy:
`olsBoltzmannOrdinate … k = −(1/(k_B T))·E k + log(Fcal·N/U)` — a direct restatement of
`ForwardMap.boltzmann_plot_intensity` in slope–intercept form. The single collinearity witness
consumed by both the intercept recovery (`olsIntercept_of_forward`, via `ols_recovers_line`)
and the zero-residual feasibility (`olsBoltzmann_forward_feasible`, via
`ols_minimizer_eq_inverse`). -/
private theorem olsBoltzmannOrdinate_affine [Nonempty ι] {kB T N Fcal : ℝ} {g E A : ι → ℝ}
    (hg : ∀ k, 0 < g k) (hN : 0 < N) (hFcal : 0 < Fcal) (hA : ∀ k, 0 < A k) (k : ι) :
    olsBoltzmannOrdinate kB T N Fcal g E A k
      = -(1 / (kB * T)) * E k + Real.log (Fcal * N / partitionFunction kB T g E) := by
  unfold olsBoltzmannOrdinate
  rw [boltzmann_plot_intensity hg hN hFcal hA k]
  ring

/-- Per-species density read off the OLS intercept:
  `N_s = exp(b_s) · U_s(T) / Fcal`,
where `b_s = olsIntercept` of the observed ordinates `y_k = log (I_k / (g_k A_k))`. A
genuine function of the FULL intensity vector `I` (all lines), not of `N`; it consumes the
whole line set per species (robustness focus). -/
noncomputable def olsDensity (kB T Fcal : ℝ) (g E A : ι → ℝ) (I : ι → ℝ) : ℝ :=
  Real.exp (olsIntercept E (fun k => Real.log (I k / (g k * A k))))
    * partitionFunction kB T g E / Fcal

/-- **Full OLS CF-LIBS composition estimator.** Per species `t` it takes that species'
ENTIRE line-intensity vector `I t : ι → ℝ` (all lines), runs the OLS Boltzmann-plot fit to
recover the intercept-borne density `olsDensity`, then applies `Closure.composition` for the
closure constraint `∑ C_s = 1`. Note the input type `κ → ι → ℝ` (a full spectrum per
species) differs from the classic/csigma one-line-per-species `κ → ℝ`; the agreement theorem
feeds the classic estimator the single line at a chosen `u s` while feeding OLS the full
vector built from the same forward spectrum. -/
noncomputable def leastSquaresComposition (kB T Fcal : ℝ) (g E A : κ → ι → ℝ)
    (I : κ → ι → ℝ) (s : κ) : ℝ :=
  composition (fun t => olsDensity kB T Fcal (g t) (E t) (A t) (I t)) s

/-- **Links OLS recovery to the physics.** The OLS intercept of the FORWARD-MODEL
Boltzmann-plot ordinates equals the composition-bearing offset `q_s = log (Fcal·N/U)` —
exactly the Ciucci et al. (1999) claim that the Boltzmann-plot intercept gives the
concentration, now via a least-squares fit over all lines. Reduces to `ols_recovers_line`
with `m0 = −1/(k_B T)`, `b0 = log (Fcal·N/U)` supplied by
`ForwardMap.boltzmann_plot_intensity` (reused, not reproven). -/
theorem olsIntercept_of_forward [Nonempty ι] {kB T N Fcal : ℝ} {g E A : ι → ℝ}
    (hg : ∀ k, 0 < g k) (hN : 0 < N) (hFcal : 0 < Fcal) (hA : ∀ k, 0 < A k)
    (hvar : 0 < ∑ k, (E k - mean E) ^ 2) :
    olsIntercept E (fun k => olsBoltzmannOrdinate kB T N Fcal g E A k)
      = Real.log (Fcal * N / partitionFunction kB T g E) :=
  (ols_recovers_line (olsBoltzmannOrdinate_affine hg hN hFcal hA) hvar).2

/-- **Per-species soundness core.** Feeding the FULL forward-model spectrum of a species
through the OLS density reader recovers the true density `N`. The OLS intercept recovers
`q_s` (`olsIntercept_of_forward`) and `exp(q_s)·U/Fcal` inverts it. Engine of soundness; the
estimator sees only intensities, never `N`. -/
theorem olsDensity_recovers [Nonempty ι] {kB T N Fcal : ℝ} {g E A : ι → ℝ}
    (hg : ∀ k, 0 < g k) (hN : 0 < N) (hFcal : 0 < Fcal) (hA : ∀ k, 0 < A k)
    (hvar : 0 < ∑ k, (E k - mean E) ^ 2) :
    olsDensity kB T Fcal g E A
      (fun k => lineIntensity kB T N Fcal g E A k) = N := by
  have hU : 0 < partitionFunction kB T g E := partitionFunction_pos hg
  unfold olsDensity
  -- Fold the ordinate lambda to `olsBoltzmannOrdinate` (definitionally equal).
  change Real.exp (olsIntercept E (fun k => olsBoltzmannOrdinate kB T N Fcal g E A k))
      * partitionFunction kB T g E / Fcal = N
  rw [olsIntercept_of_forward hg hN hFcal hA hvar, Real.exp_log (by positivity)]
  field_simp

/-- **MAIN soundness.** Run on the genuine multi-line forward-model spectrum (full
per-species line vector, no `N` input), the OLS estimator returns the TRUE composition
`C_s = N_s / ∑ N`. Assembles `olsDensity_recovers` pointwise then `Closure.composition`;
soundness is the assembly. Realizes the multi-line least-squares CF-LIBS intercept method of
Tognoni et al. (2010). -/
theorem leastSquares_sound [Nonempty ι] [Nonempty κ] {kB T Fcal : ℝ}
    {N : κ → ℝ} {g E A : κ → ι → ℝ}
    (hg : ∀ s k, 0 < g s k) (hN : ∀ s, 0 < N s) (hFcal : 0 < Fcal)
    (hA : ∀ s k, 0 < A s k)
    (hvar : ∀ s, 0 < ∑ k, (E s k - mean (E s)) ^ 2) (s : κ) :
    leastSquaresComposition kB T Fcal g E A
        (fun t k => lineIntensity kB T (N t) Fcal (g t) (E t) (A t) k) s
      = composition N s := by
  unfold leastSquaresComposition
  have hrec : (fun t => olsDensity kB T Fcal (g t) (E t) (A t)
      (fun k => lineIntensity kB T (N t) Fcal (g t) (E t) (A t) k)) = N :=
    funext (fun t => olsDensity_recovers (hg t) (hN t) hFcal (hA t) (hvar t))
  rw [hrec]

/-- **Same-spectrum agreement on the noise-free forward fixpoint.** Fed the SAME underlying
forward spectrum (the classic input `fun t => lineIntensity … (u t)` is literally the
`u t`-slice of the OLS input `fun t k => lineIntensity … k`), the OLS estimator and the
classic two-line estimator return the SAME composition. Neither side ingests `N` or
`composition N`, and the two procedures are genuinely different (OLS = regression intercept
over `n` lines via `olsDensity`; classic = single-line inversion via `classicDensity`).

Honest content: this is a COROLLARY OF JOINT SOUNDNESS — the proof rewrites both sides to
`composition N` (`leastSquares_sound` and `Classic.classic_sound`), so it holds precisely
because both are exact ON the noise-free forward fixpoint. It is NOT an observation-level
identity and is NOT claimed off the fixpoint: on noisy/perturbed intensities the two
estimators genuinely DISAGREE — OLS averages all lines while classic uses one — and that
robustness-to-noise is the entire reason to prefer the OLS variant. (`hNtot` is forwarded to
`classic_sound`, whose total-density hypothesis is unused.) -/
theorem leastSquares_agrees_classic [Nonempty ι] [Nonempty κ] {kB T Fcal : ℝ}
    {N : κ → ℝ} {g E A : κ → ι → ℝ} {u : κ → ι}
    (hg : ∀ s k, 0 < g s k) (hN : ∀ s, 0 < N s) (hFcal : 0 < Fcal)
    (hA : ∀ s k, 0 < A s k) (hNtot : 0 < totalDensity N)
    (hvar : ∀ s, 0 < ∑ k, (E s k - mean (E s)) ^ 2) (s : κ) :
    leastSquaresComposition kB T Fcal g E A
        (fun t k => lineIntensity kB T (N t) Fcal (g t) (E t) (A t) k) s
      = Classic.classicComposition kB T Fcal g E A u
          (fun t => lineIntensity kB T (N t) Fcal (g t) (E t) (A t) (u t)) s := by
  rw [leastSquares_sound hg hN hFcal hA hvar s,
    Classic.classic_sound hg hFcal (fun t => hA t (u t)) hNtot s]

/-- **The noise-free forward spectrum is exactly least-squares-feasible.** Fed the genuine
forward-model Boltzmann-plot ordinates, the least-squares fit has ZERO minimal residual: the data
lies exactly on the line `−E_k/(k_B T) + log(Fcal·N/U)`, so the projection inverse coincides with
the identifiable inverse (`olsSlope = −1/(k_B T)`, `olsIntercept = log(Fcal·N/U)`, cf.
`olsIntercept_of_forward`) and the fit is `LeastSquaresFeasible` at every tolerance `ε ≥ 0`. This
is the on-manifold anchor of the projection inverse (`LeastSquaresFit.ols_minimizer_eq_inverse`):
it is precisely why the OLS estimator is `Sound` on the noise-free fixpoint (`leastSquares_sound`).
Off the fixpoint the residual is positive and quantifies the model/measurement mismatch, which is
what the strict-mode feasibility gate tests. -/
theorem olsBoltzmann_forward_feasible [Nonempty ι] {kB T N Fcal : ℝ} {g E A : ι → ℝ}
    (hg : ∀ k, 0 < g k) (hN : 0 < N) (hFcal : 0 < Fcal) (hA : ∀ k, 0 < A k)
    (hvar : 0 < ∑ k, (E k - mean E) ^ 2) :
    leastSquaresResidual E (fun k => olsBoltzmannOrdinate kB T N Fcal g E A k) = 0 :=
  (ols_minimizer_eq_inverse (olsBoltzmannOrdinate_affine hg hN hFcal hA) hvar).2.2

/-- **Feasibility form.** The noise-free forward spectrum is `LeastSquaresFeasible` at every
tolerance `ε ≥ 0`: the zero minimal residual (`olsBoltzmann_forward_feasible`) meets any
nonnegative gate. This is the docstring claim above made formal, and the exact shape the
strict-mode runtime feasibility gate consumes. -/
theorem olsBoltzmann_forward_feasible_at [Nonempty ι] {kB T N Fcal : ℝ} {g E A : ι → ℝ}
    (hg : ∀ k, 0 < g k) (hN : 0 < N) (hFcal : 0 < Fcal) (hA : ∀ k, 0 < A k)
    (hvar : 0 < ∑ k, (E k - mean E) ^ 2) {ε : ℝ} (hε : 0 ≤ ε) :
    LeastSquaresFeasible E (fun k => olsBoltzmannOrdinate kB T N Fcal g E A k) ε := by
  unfold LeastSquaresFeasible
  rw [olsBoltzmann_forward_feasible hg hN hFcal hA hvar]
  exact hε

/-! ### Non-vacuity witness for `leastSquares_sound`

Two species with DISTINCT densities `N = (1, 3)`, TWO lines each at DISTINCT energies `E = (0, 1)`
(so the energy spread `∑ₖ (Eₖ − Ē)² = 1/2 > 0` satisfies `hvar`), `kB = T = Fcal = g = A = 1`: the
multi-line OLS estimator, run on the genuine forward-model spectrum (full per-species line vector,
never `N`), recovers the non-trivial composition `C₀ = 1/4` — not the degenerate `= 1`. So
`leastSquares_sound`'s hypotheses — including the load-bearing nonzero-energy-spread `hvar` — are
jointly satisfiable and its conclusion is non-vacuous. -/

private def nvlsN : Fin 2 → ℝ := ![1, 3]
private def nvlsg : Fin 2 → Fin 2 → ℝ := fun _ _ => 1
private def nvlsE : Fin 2 → Fin 2 → ℝ := fun _ => ![0, 1]
private def nvlsA : Fin 2 → Fin 2 → ℝ := fun _ _ => 1

example :
    leastSquaresComposition 1 1 1 nvlsg nvlsE nvlsA
        (fun t k => lineIntensity 1 1 (nvlsN t) 1 (nvlsg t) (nvlsE t) (nvlsA t) k) 0
      = 1 / 4 := by
  have h := leastSquares_sound (kB := 1) (T := 1) (Fcal := 1)
    (N := nvlsN) (g := nvlsg) (E := nvlsE) (A := nvlsA)
    (fun _ _ => one_pos) (by intro s; fin_cases s <;> norm_num [nvlsN]) one_pos
    (fun _ _ => one_pos)
    (by intro s; fin_cases s <;> simp [nvlsE, mean, Fin.sum_univ_two] <;> norm_num)
    (0 : Fin 2)
  rw [h]
  norm_num [composition, totalDensity, nvlsN, Fin.sum_univ_two]

end CflibsFormal.Alt

