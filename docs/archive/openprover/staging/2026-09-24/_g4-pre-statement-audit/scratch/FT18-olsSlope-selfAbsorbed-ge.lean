import Mathlib
import CflibsFormal.OLS
import CflibsFormal.SelfAbsorption

/-!
# FT-18: sign of the self-absorption bias on the Boltzmann-plot slope

Staged queue target, 2026-09-24 audit, frontier FT-18 (main theorem, verifier-revised form).
Uses `CflibsFormal.olsSlope` (`OLS.lean`) and `CflibsFormal.selfAbsorptionFactor`
(`SelfAbsorption.lean`) verbatim; no new definitions.
-/

open Finset CflibsFormal

namespace Plan.FT18

variable {ι : Type*} [Fintype ι]

theorem olsSlope_add' [Nonempty ι] (E f h : ι → ℝ) :
    olsSlope E (fun k => f k + h k) = olsSlope E f + olsSlope E h := by
  rw [olsSlope_eq_centered, olsSlope_eq_centered, olsSlope_eq_centered, ← add_div]
  congr 1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  ring

theorem centered_cov_nonneg [Nonempty ι] (E z : ι → ℝ)
    (hmono : ∀ i j, E i < E j → z i ≤ z j) : 0 ≤ ∑ k, (E k - mean E) * z k := by
  have hM : Monovary z E := fun i j h => hmono i j h
  have hC := hM.sum_mul_sum_le_card_mul_sum
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hsplit : ∑ k, (E k - mean E) * z k = ∑ k, z k * E k - mean E * ∑ k, z k := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  rw [hsplit, mean]
  have : (∑ k, E k) / (Fintype.card ι : ℝ) * ∑ k, z k = ((∑ k, z k) * ∑ k, E k) / Fintype.card ι := by
    ring
  rw [this, sub_nonneg, div_le_iff₀ hn]
  linarith

omit [Fintype ι] in
theorem logSA_mono {E τ : ι → ℝ} (hτ : ∀ k, 0 < τ k)
    (hanti : ∀ i j, E i < E j → τ j ≤ τ i) :
    ∀ i j, E i < E j →
      Real.log (selfAbsorptionFactor (τ i)) ≤ Real.log (selfAbsorptionFactor (τ j)) := by
  intro i j hij
  apply Real.log_le_log (selfAbsorptionFactor_pos (hτ i).le)
  exact selfAbsorptionFactor_strictAntiOn.antitoneOn (hτ j) (hτ i) (hanti i j hij)

/-- **FT-18: if optical depth falls with upper-level energy, self-absorption can only raise the
Boltzmann-plot slope.**
Lines `k` have upper-level energies `E k`, optically thin Boltzmann-plot ordinates `y k`, and
optical depths `τ k > 0`. In the flat-profile slab model the measured intensity is the thin
intensity times `SA(τ) = (1 − exp(−τ))/τ` (`selfAbsorptionFactor`), so the measured ordinate is
`y k + log (SA (τ k))`. If `τ` does not increase with upper-level energy (`E i < E j → τ j ≤ τ i`:
resonance and low-lying lines are the most absorbed), then the ordinary-least-squares slope of the
self-absorbed plot is at least the thin slope:
`olsSlope E y ≤ olsSlope E (fun k => y k + log (SA (τ k)))`.
With a thin slope `−1/(kB T) < 0`, the slope moves toward zero, so the apparent temperature is
overestimated while the slope stays negative (the temperature reading is a separate lemma, not
part of this statement).

Mechanism: `SA` is strictly decreasing on `τ > 0`, so `z k = log (SA (τ k))` is nondecreasing
along `E`; the centred covariance `∑ (E k − Ē) z k` of two similarly ordered sequences is `≥ 0`,
and the OLS slope is additive in the ordinates.

What it does not say: the sign is fixed by the ordering of `τ` against `E_upper`. With the
opposite ordering the slope can decrease (a two-line witness is a separate target). This does not
settle the empirical dispute in the literature about the sign of the bias, which is a question
about which ordering real line sets have.

Hypotheses.
* `hτ : ∀ k, 0 < τ k`: puts every `τ k` in the domain `(0, ∞)` of
  `selfAbsorptionFactor_strictAntiOn` and makes `SA (τ k) > 0`, so the logarithm is monotone
  there.
* `hanti`: the ordering assumption. It is stated for strictly ordered energies only, so lines
  sharing an upper level (multiplets) may have different `τ`; equal-energy pairs contribute `0`
  to the covariance. It is an assumption about the line set, not a physical law: `τ` depends on
  the lower-level population and `gf`, and must be checked per line set.
* `[Nonempty ι]`: not logically needed (with no lines both slopes are `0`); kept because the
  repo's centred-slope lemmas (`olsSlope_eq_centered`) carry it.
No energy-spread hypothesis is needed: with `∑ (E k − Ē)² = 0` both slopes are `0` by the
totalized division in `olsSlope`.

Scope, two-axis prediction: relation EXACT relative to its definitions (a mathematical
inequality); model tags of the definitions used: `selfAbsorptionFactor` applied to integrated
line intensity is the flat-profile slab escape factor, REDUCED under the RF-03 policy (rows that
consume SA are REDUCED); `olsSlope` is unweighted OLS at a single temperature, a reduction of the
pipeline's weighted fit. Published tag REDUCED (flat-profile SA, unweighted OLS, single T).

Literature: Gornushkin et al. 1999 (Spectrochim. Acta B 54, 491) for the slab curve of growth and
`SA(τ) = (1 − exp(−τ))/τ`; Bulajic et al. 2002 (Spectrochim. Acta B 57, 339) for self-absorption
correction in CF-LIBS. -/
theorem olsSlope_selfAbsorbed_ge [Nonempty ι] {E y τ : ι → ℝ} (hτ : ∀ k, 0 < τ k)
    (hanti : ∀ i j, E i < E j → τ j ≤ τ i) :
    olsSlope E y ≤ olsSlope E (fun k => y k + Real.log (selfAbsorptionFactor (τ k))) := by
  rw [olsSlope_add' E y (fun k => Real.log (selfAbsorptionFactor (τ k)))]
  have h0 : 0 ≤ olsSlope E (fun k => Real.log (selfAbsorptionFactor (τ k))) := by
    rw [olsSlope_eq_centered]
    exact div_nonneg (centered_cov_nonneg E _ (logSA_mono hτ hanti))
      (Finset.sum_nonneg (fun k _ => sq_nonneg _))
  linarith

end Plan.FT18
