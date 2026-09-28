import Mathlib
import CflibsFormal.ForwardMap
import CflibsFormal.Saha

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

/-- **Exact recovery.** If every species' neutral line is observed, the stage
ratios are the true ones, and charge neutrality `ne = ∑ s, N s * R s` holds
(`chargeNeutrality` with unit charge and ion densities `N s * R s`), then the
neutrality scale estimator returns `Fcal` exactly — no closure hypothesis
`∑ C = 1` is used. The per-unit factor cancels because `lineIntensity` is
linear in `N` and `Fcal` (`population` is linear in `N`). `ne ≠ 0` and
`unitI s ≠ 0` are load-bearing (division); their signs are physical decoration.
The stage ratios `R` are unconstrained: they enter only through the neutrality
hypothesis. -/
theorem neutralityScale_eq_Fcal
    {kB T Fcal ne : ℝ} {g E A : ι → ℝ} {N R : κ → ℝ} {emit : κ → ι}
    (hne : 0 < ne)
    (hunit : ∀ s, 0 < lineIntensity kB T 1 1 g E A (emit s))
    (hneut : chargeNeutrality (fun _ : κ => (1 : ℝ)) (fun s => N s * R s) ne) :
    neutralityScale (fun s => lineIntensity kB T (N s) Fcal g E A (emit s))
      (fun s => lineIntensity kB T 1 1 g E A (emit s)) R ne = Fcal := by
  sorry

end CflibsFormal.Alt
