import Mathlib
import CflibsFormal.ForwardMap

/-!
# Neutrality scale — the calibration factor from charge neutrality instead of closure

Classic CF-LIBS removes the unknown instrument factor `Fcal` by *closure*
(`∑ C = 1`). Charge neutrality, `n_e = ∑_s n_ion s`, is a second absolute
equation whose left-hand side a Stark width measures independently of `Fcal`.
This file states, on the repository's own forward model, what neutrality buys
and what it does not.

Model (single shared `T`, one neutral line per species, singly ionized stages):
* `I s = lineIntensity kB T (N s) Fcal g E A (emit s)` — the observed neutral
  line of species `s` (`N s` = neutral density);
* `R s` — the Saha stage ratio `n_ion s / N s` of species `s` (positive in the
  physical reading; unconstrained in the statements);
* `unitI s := lineIntensity kB T 1 1 g E A (emit s)` — the per-unit line factor
  (`N = 1`, `Fcal = 1`), a known function of the atomic data and `T`.

Then `I s / unitI s = Fcal · N s` (linearity), so the *neutrality estimate*
`neutralityScale I unitI R ne := (∑ s, I s * R s / unitI s) / ne` equals `Fcal`
whenever `n_e = ∑ s, N s * R s` holds over the species that were summed
(theorem `neutralityScale_eq_Fcal`, in its own file during the Worker test).

## Literature

Prior art for neutrality as the normalization: Abbass, Ahmed, Ahmed & Baig, Plasma Chem.
Plasma Process. 36 (2016) 1287 ("electron density conservation" CF-LIBS, Pb–Sn). Closure failure
when elements are missing: Tognoni, Cristoforetti, Legnaioli & Palleschi, Spectrochim. Acta B 65
(2010) 1. Forward model: Ciucci et al., Appl. Spectrosc. 53 (1999) 960. The identities below are
algebraic consequences of the repository's own forward model and do not rest on any constant,
sign or exponent taken from these papers.

Scope caveat shared by all statements: every species' line is evaluated with the *same* level
family `g E A : ι → ℝ` and hence the same `partitionFunction kB T g E` (the single-family scope
documented in `MultiSpecies.lean`); the partition function cancels in every ratio `I s / unitI s`,
so the identities hold with per-species partition functions as well, but `I` and `unitI` must be
computed with the same one. The identities are sign-free: no positivity of `N`, `R`, `Nu`, `Ru`
or `Fcal` is assumed, and the guards `0 < ne`, `0 < unitI s` are used only as `≠ 0`.
-/

open Finset

namespace CflibsFormal.Alt

variable {κ ι : Type*} [Fintype κ] [Fintype ι]

/-- **Neutrality scale estimator.** From observed neutral intensities `I`, the
per-unit line factors `unitI`, the Saha stage ratios `R` and an independently
measured electron density `ne`, the estimate of the calibration factor:
`(∑ s, I s * R s / unitI s) / ne`. -/
noncomputable def neutralityScale (I unitI R : κ → ℝ) (ne : ℝ) : ℝ :=
  (∑ s, I s * R s / unitI s) / ne

/-- **Undetected species.** If one species (neutral density `Nu`, stage ratio
`Ru`) is absent from the observed set `κ`, but charge neutrality holds over
*all* species, `ne = (∑ s, N s * R s) + Nu * Ru`, then the neutrality scale
computed over the observed species returns `Fcal` scaled by one minus the
undetected species' **charge share** `Nu * Ru / ne` (an identity; the reading as a
fraction in `[0, 1]` presupposes `0 ≤ Nu * Ru ≤ ne`, which is not assumed). `Nu * Ru` may
also stand for the net ion density of several undetected species. The estimator is
therefore blind to an undetected species exactly to the extent that it is
neutral (`Ru → 0`), which is the case for the high-ionization-energy elements
(H, O, N, C) that CF-LIBS typically fails to observe. -/
theorem neutralityScale_undetected
    {kB T Fcal ne Nu Ru : ℝ} {g E A : ι → ℝ} {N R : κ → ℝ} {emit : κ → ι}
    (hne : 0 < ne)
    (hunit : ∀ s, 0 < lineIntensity kB T 1 1 g E A (emit s))
    (hneut : ne = (∑ s, N s * R s) + Nu * Ru) :
    neutralityScale (fun s => lineIntensity kB T (N s) Fcal g E A (emit s))
      (fun s => lineIntensity kB T 1 1 g E A (emit s)) R ne
      = Fcal * (1 - Nu * Ru / ne) := by
  sorry

end CflibsFormal.Alt
