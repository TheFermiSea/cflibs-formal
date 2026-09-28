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

/-- **FT-18: if optical depth falls with upper-level energy, self-absorption can only raise the
Boltzmann-plot slope.**
Lines `k` have upper-level energies `E k`, optically thin Boltzmann-plot ordinates `y k`, and
optical depths `τ k > 0`. In the flat-profile slab model the measured intensity is the thin
intensity times `SA(τ) = (1 − exp(−τ))/τ` (`selfAbsorptionFactor`), so the measured ordinate is
`y k + log (SA (τ k))`. If `τ` does not increase with upper-level energy (`E i < E j → τ j ≤ τ i`:
resonance and low-lying lines are the most absorbed), then the ordinary-least-squares slope of the
self-absorbed plot is at least the thin slope:
`olsSlope E y ≤ olsSlope E (fun k => y k + log (SA (τ k)))`.
If the thin slope is `−1/(kB T) < 0`, the self-absorbed slope is at least that value. If the
self-absorbed slope is still negative, the apparent temperature is at least `T` (a separate lemma,
not part of this statement); the slope can also reach or cross `0`.

Mechanism: `SA` is strictly decreasing on `τ > 0`, so `z k = log (SA (τ k))` is nondecreasing
along `E`; the centred covariance `∑ (E k − Ē) z k` of two similarly ordered sequences is `≥ 0`,
and the OLS slope is additive in the ordinates.

What it does not say: the sign is fixed by the ordering of `τ` against `E_upper`. With the
opposite ordering the slope can decrease (a two-line witness is a separate target). Which
ordering real line sets have is not decided here; it is an empirical, per-line-set question.

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
On the current main TSV the SA-consuming intensity rows (`selfAbsorbedIntensity_le_lineIntensity`,
`selfAbsorbedIntensity_lt_lineIntensity`) are APPROXIMATION; the published tag is REDUCED once
the RF-03 retag lands. Until then the TSV row must follow the current model tag (APPROXIMATION,
the weaker of the two axes).

Literature: Gornushkin et al. 1999 (Spectrochim. Acta B 54, 491) for the slab curve of growth and
`SA(τ) = (1 − exp(−τ))/τ`; Bulajic et al. 2002 (Spectrochim. Acta B 57, 339) for self-absorption
correction in CF-LIBS. -/
theorem olsSlope_selfAbsorbed_ge [Nonempty ι] {E y τ : ι → ℝ} (hτ : ∀ k, 0 < τ k)
    (hanti : ∀ i j, E i < E j → τ j ≤ τ i) :
    olsSlope E y ≤ olsSlope E (fun k => y k + Real.log (selfAbsorptionFactor (τ k))) := by
  sorry

end Plan.FT18
