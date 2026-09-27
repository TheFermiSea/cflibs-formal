/-
Copyright (c) 2026 Brian Squires. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Squires
-/
import Mathlib
import CflibsFormal.ForwardMap
import CflibsFormal.Saha

/-!
# Neutrality scale — the calibration factor from charge neutrality instead of closure

Classic CF-LIBS removes the unknown instrument factor `Fcal` by *closure*
(`∑ C = 1`). Charge neutrality, `n_e = ∑_s n_ion s`, is a second absolute
equation whose left-hand side a Stark width measures independently of `Fcal`.
This module states, on the repository's own forward model, what neutrality buys
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
(`neutralityScale_eq_Fcal`), and is biased by exactly the undetected species'
**charge share** when one is missing (`neutralityScale_undetected`). The
companion `closureEstimate_bias` makes "closure fails when elements are
missing" (Tognoni et al. 2010) exact for the classic closure normalization.

## Literature

Prior art for neutrality as the normalization: Abbass, Ahmed, Ahmed & Baig, "A Comparative Study
of Calibration Free Methods for the Elemental Analysis by Laser Induced Breakdown Spectroscopy",
Plasma Chem. Plasma Process. 36 (2016) 1287–1299, DOI 10.1007/s11090-016-9729-y. Only its
bibliographic record was checked (Crossref); the paper was not opened, so the description of it
as "electron density conservation" CF-LIBS on Pb–Sn is unverified. Closure failure
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

`closureEstimate_bias`'s right-hand side is invariant in `Nu` on the domain where it is defined
(algebra: `(x/(S+Nu))/(1−Nu/(S+Nu)) = x/S` for any `Nu` with `S + Nu ≠ 0`), so its forward-model
content is exactly `closureEstimate = N s / ∑ N` (the `Fcal`/per-unit cancellation); the `1/(1−Cu)`
dressing is the same inflation identity already proved on an abstract density in
`MatrixEffects.recoveredComposition_eq_inflation`. This module re-derives it from the raw
`lineIntensity` forward map with the undetected species as a bare real rather than as an omitted
element of a `Finset κ`, so the two do not share a proof term; a follow-up could restate
`closureEstimate_bias` over `MatrixEffects`'s `Finset`-indexed density and derive it from
`recoveredComposition_eq_inflation` directly. Both are EXACT identities and neither overclaims: the
duplication is an architectural note, not a faithfulness gap (statement audit, 2026-09-21).

**Worker provenance.** These three statements were audited (Mode B, three independent reviewers,
2026-09-21; `docs/spec/03-module-specs.md` §7) before any prover saw them, then proved by the local
Worker (Qwen3.8-27B, 3/3; Leanstral 1.5, 0/3 within a 60-minute cap each) as the first real-problem
test of the local-model harness (decision D12). Every proof was independently re-verified by the
lead before landing here: `lake env lean`, `#print axioms` (the standard three), and a signature
diff against the audited statement files.
-/

open Finset

namespace CflibsFormal.Alt

variable {κ ι : Type*} [Fintype κ] [Fintype ι]

/-- **Linearity of the line intensity in density and calibration.** `lineIntensity` at density `N`
and calibration `Fcal` is `Fcal * N` times its value at the unit point `(N = 1, Fcal = 1)` — a pure
algebraic identity (the shared `partitionFunction` denominator cancels), holding unconditionally. -/
theorem lineIntensity_linear (kB T N Fcal : ℝ) (g E A : ι → ℝ) (k : ι) :
    lineIntensity kB T N Fcal g E A k = Fcal * N * lineIntensity kB T 1 1 g E A k := by
  unfold lineIntensity population
  ring

omit [Fintype κ] in
/-- The ratio form of `lineIntensity_linear`, guarded by positivity of the unit-point intensity. -/
theorem lineIntensity_ratio (kB T Fcal : ℝ) (g E A : ι → ℝ) (N : κ → ℝ) (emit : κ → ι) (t : κ)
    (hunit : 0 < lineIntensity kB T 1 1 g E A (emit t)) :
    lineIntensity kB T (N t) Fcal g E A (emit t) / lineIntensity kB T 1 1 g E A (emit t)
      = Fcal * N t := by
  rw [lineIntensity_linear]
  field_simp [hunit.ne']

/-- **Neutrality scale estimator.** From observed neutral intensities `I`, the per-unit line
factors `unitI`, the Saha stage ratios `R` and an independently measured electron density `ne`,
the estimate of the calibration factor: `(∑ s, I s * R s / unitI s) / ne`. -/
noncomputable def neutralityScale (I unitI R : κ → ℝ) (ne : ℝ) : ℝ :=
  (∑ s, I s * R s / unitI s) / ne

/-- **Exact recovery.** If every species' neutral line is observed, the stage ratios are the true
ones, and charge neutrality `ne = ∑ s, N s * R s` holds (`chargeNeutrality` with unit charge and
ion densities `N s * R s`), then the neutrality scale estimator returns `Fcal` exactly — no closure
hypothesis `∑ C = 1` is used. `ne ≠ 0` and `unitI s ≠ 0` are load-bearing (division); their signs
are physical decoration. The stage ratios `R` are unconstrained: they enter only through the
neutrality hypothesis. -/
theorem neutralityScale_eq_Fcal
    {kB T Fcal ne : ℝ} {g E A : ι → ℝ} {N R : κ → ℝ} {emit : κ → ι}
    (hne : 0 < ne)
    (hunit : ∀ s, 0 < lineIntensity kB T 1 1 g E A (emit s))
    (hneut : chargeNeutrality (fun _ : κ => (1 : ℝ)) (fun s => N s * R s) ne) :
    neutralityScale (fun s => lineIntensity kB T (N s) Fcal g E A (emit s))
      (fun s => lineIntensity kB T 1 1 g E A (emit s)) R ne = Fcal := by
  have hterm : ∀ s, lineIntensity kB T (N s) Fcal g E A (emit s) * R s /
      lineIntensity kB T 1 1 g E A (emit s) = Fcal * (N s * R s) := by
    intro s
    rw [lineIntensity_linear]
    field_simp [(hunit s).ne']
  have hsum : (∑ s, lineIntensity kB T (N s) Fcal g E A (emit s) * R s /
      lineIntensity kB T 1 1 g E A (emit s)) = Fcal * ∑ s, N s * R s := by
    calc
      _ = ∑ s, Fcal * (N s * R s) := Finset.sum_congr rfl (fun s _ => hterm s)
      _ = Fcal * ∑ s, N s * R s := by rw [← Finset.mul_sum]
  have hne_eq : ne = ∑ s, N s * R s := by
    simpa only [chargeNeutrality, one_mul] using hneut
  unfold neutralityScale
  rw [hsum, ← hne_eq]
  field_simp [hne.ne']

/-- **Undetected species.** If one species (neutral density `Nu`, stage ratio `Ru`) is absent from
the observed set `κ`, but charge neutrality holds over *all* species,
`ne = (∑ s, N s * R s) + Nu * Ru`, then the neutrality scale computed over the observed species
returns `Fcal` scaled by one minus the undetected species' **charge share** `Nu * Ru / ne`. The
estimator is therefore blind to an undetected species exactly to the extent that it is neutral
(`Ru → 0`), which is the case for the high-ionization-energy elements (H, O, N, C) that CF-LIBS
typically fails to observe: the charge share, not the mass share, controls the bias. The reading as
a fraction in `[0, 1]` presupposes `0 ≤ Nu * Ru ≤ ne`, which is not assumed; the identity itself
holds for any sign. `Nu * Ru` may also stand for the net ion density of several undetected
species. -/
theorem neutralityScale_undetected
    {kB T Fcal ne Nu Ru : ℝ} {g E A : ι → ℝ} {N R : κ → ℝ} {emit : κ → ι}
    (hne : 0 < ne)
    (hunit : ∀ s, 0 < lineIntensity kB T 1 1 g E A (emit s))
    (hneut : ne = (∑ s, N s * R s) + Nu * Ru) :
    neutralityScale (fun s => lineIntensity kB T (N s) Fcal g E A (emit s))
      (fun s => lineIntensity kB T 1 1 g E A (emit s)) R ne
      = Fcal * (1 - Nu * Ru / ne) := by
  have key : ∀ s, lineIntensity kB T (N s) Fcal g E A (emit s) * R s /
      lineIntensity kB T 1 1 g E A (emit s) = Fcal * (N s * R s) := by
    intro s
    rw [lineIntensity_linear, div_eq_iff (hunit s).ne']
    ring
  have hsum : ∑ s, N s * R s = ne - Nu * Ru := by linarith
  unfold neutralityScale
  rw [Finset.sum_congr rfl (fun s _ => key s), ← Finset.mul_sum, hsum]
  field_simp

/-- **Closure estimator** over the observed species: the per-unit-normalized intensities
renormalized to sum to one, `(I s / unitI s) / ∑ t, I t / unitI t`. -/
noncomputable def closureEstimate (I unitI : κ → ℝ) (s : κ) : ℝ :=
  (I s / unitI s) / ∑ t, I t / unitI t

/-- **Closure bias from an undetected species.** With an undetected species of neutral density
`Nu ≥ 0` outside the observed set, the closure estimate of an observed species equals its true
composition over all species, `N s / (∑ t, N t + Nu)`, divided by `1 - Cu` where
`Cu = Nu / (∑ t, N t + Nu)` is the undetected species' true fraction: closure silently
redistributes the missing fraction over the observed species (Tognoni et al. 2010). Load-bearing
guards: `Fcal ≠ 0`, `unitI s ≠ 0` and `∑ N + Nu ≠ 0` (the last is what `hNu` and `hsum` jointly
supply; neither alone can be dropped — `Nu = −∑ N` breaks the identity); `∑ N ≠ 0` additionally
keeps the left side away from `0/0`. `N` is the *neutral* density, so this is elemental composition
only where ionization is negligible or uniform across species. See the module docstring for the
identity's `Nu`-invariance and its relation to `MatrixEffects.recoveredComposition_eq_inflation`. -/
theorem closureEstimate_bias
    {kB T Fcal Nu : ℝ} {g E A : ι → ℝ} {N : κ → ℝ} {emit : κ → ι}
    (hFcal : 0 < Fcal) (hNu : 0 ≤ Nu) (hsum : 0 < ∑ t, N t)
    (hunit : ∀ s, 0 < lineIntensity kB T 1 1 g E A (emit s)) (s : κ) :
    closureEstimate (fun s => lineIntensity kB T (N s) Fcal g E A (emit s))
      (fun s => lineIntensity kB T 1 1 g E A (emit s)) s
      = (N s / (∑ t, N t + Nu)) / (1 - Nu / (∑ t, N t + Nu)) := by
  unfold closureEstimate
  have hSne : (∑ t, N t) ≠ 0 := hsum.ne'
  have haddne : (∑ t, N t + Nu) ≠ 0 := (add_pos_of_pos_of_nonneg hsum hNu).ne'
  have hFne : Fcal ≠ 0 := hFcal.ne'
  have hratio (t : κ) :
      lineIntensity kB T (N t) Fcal g E A (emit t) / lineIntensity kB T 1 1 g E A (emit t)
        = Fcal * N t :=
    lineIntensity_ratio kB T Fcal g E A N emit t (hunit t)
  simp only [hratio]
  rw [← Finset.mul_sum]
  have hden : 1 - Nu / (∑ t, N t + Nu) = (∑ t, N t) / (∑ t, N t + Nu) := by
    field_simp
    ring
  have hdenne : (1 - Nu / (∑ t, N t + Nu)) ≠ 0 := by
    rw [hden]; exact div_ne_zero hSne haddne
  field_simp [hSne, haddne, hFne, hdenne]
  ring

end CflibsFormal.Alt
