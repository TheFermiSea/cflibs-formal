import Mathlib
import CflibsFormal.MultiSpecies
import CflibsFormal.Alt.NeutralityScale

/-!
# FT-08 (a2): closure and neutrality normalizations give the same ratios (per-species `U_s`)

Staged queue target, frontier FT-08 (a), decomposition step 2, in the per-species partition
function form required by the 2026-09-24 audit verdict: intensities come from
`MultiSpecies.lineIntensityPerU` (species `s` has its own `U s`), not from the shared-family
`ForwardMap.lineIntensity`. No new definitions: `lineIntensityPerU`, `Alt.closureEstimate` and
`Alt.neutralityScale` are used as they stand on main.
-/

open CflibsFormal CflibsFormal.Alt

namespace Plan.FT08

variable {ι κ : Type*} [Fintype κ]

/-- **Closure and neutrality readers return the same ratios, with per-species `U_s`.**
Species `s` is observed through its designated line `emit s` with its own partition function
`U s`: `I s = lineIntensityPerU kB T (N s) Fcal (U s) g E A (emit s)`, and `unitI s` is the same
line at the unit point `N = 1, Fcal = 1`. Then (i) the closure estimate gives
`closureEstimate I unitI a / closureEstimate I unitI b = N a / N b`, and (ii) for every stage-ratio
vector `R` and electron density `ne` whose neutrality scale is nonzero, the neutrality-normalized
per-unit intensities give the same ratio `N a / N b`.

Reading: `U s` cancels in `I s / unitI s = Fcal * N s`, so both readers are ratio-exact for any
per-species partition functions, and (ii) holds for any `R`, `ne`, including an `ne` that carries
the charge of an undetected species. Normalization choice cannot change a ratio. This says
nothing about the accuracy of the absolute composition or of `Fcal`.

Hypotheses: `hFcal` (at `Fcal = 0` every closure estimate is `0`); `hN` (makes `∑ N ≠ 0`; at
`∑ N = 0` the closure estimates are `0`); `hunit` (division by the unit-point intensity);
`hI`, `hu` define the data.

Scope prediction: REDUCED (LTE optically thin single-`T` forward model, one designated line per
species). Literature: Tognoni et al. 2010 (closure over observed species). -/
theorem neutrality_closure_same_ratio {kB T Fcal : ℝ} {g E A : ι → ℝ} {N U : κ → ℝ}
    {emit : κ → ι} {I unitI : κ → ℝ} (hFcal : 0 < Fcal) (hN : ∀ s, 0 < N s)
    (hI : ∀ s, I s = lineIntensityPerU kB T (N s) Fcal (U s) g E A (emit s))
    (hu : ∀ s, unitI s = lineIntensityPerU kB T 1 1 (U s) g E A (emit s))
    (hunit : ∀ s, 0 < unitI s) (a b : κ) :
    closureEstimate I unitI a / closureEstimate I unitI b = N a / N b ∧
      ∀ (R : κ → ℝ) (ne : ℝ), neutralityScale I unitI R ne ≠ 0 →
        ((I a / unitI a) / neutralityScale I unitI R ne)
            / ((I b / unitI b) / neutralityScale I unitI R ne) = N a / N b := by
  sorry

end Plan.FT08
