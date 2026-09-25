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

/-- **Closure estimator** over the observed species: the per-unit-normalized
intensities renormalized to sum to one, `(I s / unitI s) / ∑ t, I t / unitI t`. -/
noncomputable def closureEstimate (I unitI : κ → ℝ) (s : κ) : ℝ :=
  (I s / unitI s) / ∑ t, I t / unitI t

/-- **Closure bias from an undetected species.** With an undetected species of
neutral density `Nu ≥ 0` outside the observed set, the closure estimate of an
observed species equals its true composition over all species,
`N s / (∑ t, N t + Nu)`, divided by `1 - Cu` where `Cu = Nu / (∑ t, N t + Nu)`
is the undetected species' true fraction: closure silently redistributes the
missing fraction over the observed species. Load-bearing guards: `Fcal ≠ 0`, `unitI s ≠ 0` and `∑ N + Nu ≠ 0` (the last is
what `hNu` and `hsum` jointly supply; neither alone can be dropped: `Nu = −∑ N`
breaks the identity); `∑ N ≠ 0` additionally keeps the left side away from
`0/0`. Honest reading: the right-hand side equals `N s / ∑ t, N t` by algebra
for every `Nu` with `∑ N + Nu ≠ 0`, so the forward-model content of the theorem
is `closureEstimate = N s / ∑ N` (the `Fcal` and per-unit cancellation), and the
`1/(1 − Cu)` dressing is the inflation identity already stated in
`MatrixEffects.recoveredComposition_eq_inflation`; the eventual module should
state `closureEstimate_eq_composition` and derive the bias from there. `N` is
the *neutral* density, so this is elemental composition only where ionization
is negligible or uniform across species. -/
theorem closureEstimate_bias
    {kB T Fcal Nu : ℝ} {g E A : ι → ℝ} {N : κ → ℝ} {emit : κ → ι}
    (hFcal : 0 < Fcal) (hNu : 0 ≤ Nu) (hsum : 0 < ∑ t, N t)
    (hunit : ∀ s, 0 < lineIntensity kB T 1 1 g E A (emit s)) (s : κ) :
    closureEstimate (fun s => lineIntensity kB T (N s) Fcal g E A (emit s))
      (fun s => lineIntensity kB T 1 1 g E A (emit s)) s
      = (N s / (∑ t, N t + Nu)) / (1 - Nu / (∑ t, N t + Nu)) := by
  sorry

end CflibsFormal.Alt
