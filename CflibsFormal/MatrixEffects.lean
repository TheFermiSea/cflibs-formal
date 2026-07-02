/-
Copyright (c) 2026 Brian Squires. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Squires
-/
import Mathlib
import CflibsFormal.Closure
import CflibsFormal.MultiSpecies

/-!
# CF-LIBS formalization — matrix effects (completeness, ablation, ionization suppression)

"Matrix effects" = the dependence of a LIBS measurement on the overall sample composition (the
*matrix*). CF-LIBS's selling point is that, by measuring `T`/`n_e` in situ and imposing closure, it
is *in principle* matrix-independent. This module makes that precise as **explicit-parameter**
statements, separating the channels and being honest about which CF-LIBS provably removes.

* **Completeness channel (`D`) — the headline.** Model the matrix as the *detected subset*
  `D : Finset κ` of species (the rest fall below the detection limit). The recovered composition
  `Ĉ_D s = n_s / (∑_{t∈D} n_t)` then has TWO faces:
  - the recovered **subcomposition** (pairwise ratios among detected species) is matrix-INDEPENDENT
    — `Ĉ_D s / Ĉ_D t = n_s / n_t` for *any* `D` (`recoveredComposition_ratio_matrix_invariant`);
    Aitchison subcompositional coherence;
  - the recovered **absolute** fractions are matrix-DEPENDENT, over-estimated by the exact factor
    `1/(1−m) ≥ 1` where `m` is the undetected mass fraction
    (`recoveredComposition_eq_inflation`, `composition_le_recoveredComposition`).
  `recoveredComposition` strictly generalizes `Closure.composition` (the `D = univ` case,
  `recoveredComposition_univ`); no subset parameter exists elsewhere in the repo, so this is not a
  restatement of `Closure`/`Classic`.
* **Ablation channel (`F`).** A matrix-dependent overall calibration factor cancels in the ratio
  (the intensity bridge `recovered_ratio_from_intensities`: the recovered subcomposition from REAL
  forward intensities equals the true density ratio `N_s/N_t`, independent of `D`).
* **Ionization-suppression channel (`n_e`).** Flooding the plasma with electrons (e.g. an easily
  ionized matrix element) raises `n_e` and suppresses other elements' ionization: the ion density
  `n_ion = N_tot·S/(S+n_e)` is strictly decreasing in `n_e` (`sahaIonDensity_antitone`).

## Honest scope

* **EXACT, not approximate** — every result is an exact identity/inequality in dimensionless `ℝ`.
* **The matrix-independence is of the COMPLETENESS (`D`) and ABLATION (`F`) channels, with the
  detected densities `n` and the temperature `T` HELD FIXED.** It is NOT unconditional
  matrix-independence: thermodynamic shifts that change `n`, `T`, or `n_e` themselves are handled
  separately (per-shot `T`/`n_e` recovery in `Identifiability`/`SahaInverse`); CF-LIBS alone leaves
  documented residual matrix effects (Borduchi et al. 2022). The `F`-bridge fixes `T` across both
  matrices, so it is the ablation channel ONLY (not a temperature-shift claim).
* **The recovered quantity is the PLASMA composition.** Equality to the SAMPLE composition is the
  separate stoichiometric-ablation assumption; fractionation (its failure) is OUT OF SCOPE, as are
  self-absorption (only mitigated, see `SelfAbsorption`/`CurveOfGrowth`) and molecular/oxide
  sequestration (no states in the LTE/Saha model).
* In the ionization section `S` is the Saha factor — taken here as an abstract `S > 0` (intended
  instantiation `Saha.sahaFactor`, not depended on). `sahaSplit_sum` alone is a trivial partition;
  its content is the PAIR with `sahaSplit_saha`, which certifies the split is Saha-consistent.

## Literature

Closure inflation under incomplete detection: Ciucci, A.; Corsi, M.; Palleschi, V.; Rastelli, S.;
Salvetti, A.; Tognoni, E. *Applied Spectroscopy* **53** (1999) 960 (the sum is over *all* species);
Tognoni, E.; Cristoforetti, G.; Legnaioli, S.; Palleschi, V. *Spectrochimica Acta Part B* **65**
(2010) 1 (completeness / stoichiometric-composition failure). Subcompositional coherence:
J. Aitchison, *The Statistical Analysis of Compositional Data* (Chapman & Hall, 1986). Residual
matrix effects in CF-LIBS: Borduchi, L. C. L.; Milori, D. M. B. P.; Villas-Boas, P. R.
*Spectrochimica Acta Part B* (2022). Ionization suppression / electron-density coupling: Aguilera,
J. A.; Aragón, C. *Spectrochimica Acta Part B* **62** (2007) 378; Aragón, C.; Aguilera, J. A.
*Spectrochimica Acta Part B* **63** (2008) 893.
-/

namespace CflibsFormal

open Finset
open scoped BigOperators

variable {κ : Type*}

/-! ## Completeness channel — the matrix as the detected subset `D`

The subcomposition (ratio) results below need no finiteness of the species type; the
`totalDensity`/`univ`-based inflation results need `[Fintype κ]` (the section below). -/

/-- **Detected density** `∑_{t∈D} n_t`: the total number density summed over only the DETECTED
species `D` (the matrix-completeness parameter). The full `totalDensity` is the `D = univ` case. -/
noncomputable def detectedDensity (n : κ → ℝ) (D : Finset κ) : ℝ := ∑ t ∈ D, n t

/-- **Recovered composition under incomplete detection** `Ĉ_D s = n_s / (∑_{t∈D} n_t)`: closure
applied over only the detected species `D`. Generalizes `Closure.composition` (the `D = univ`
case, `recoveredComposition_univ`). -/
noncomputable def recoveredComposition (n : κ → ℝ) (D : Finset κ) (s : κ) : ℝ :=
  n s / detectedDensity n D

/-- **The recovered fractions still close to one** over the detected set: `∑_{s∈D} Ĉ_D s = 1`.
The bias is in the per-element *values* (inflation), not in the normalization. -/
theorem recoveredComposition_sum_one {n : κ → ℝ} {D : Finset κ}
    (hd : 0 < detectedDensity n D) :
    ∑ s ∈ D, recoveredComposition n D s = 1 := by
  unfold recoveredComposition
  rw [← Finset.sum_div]
  exact div_self hd.ne'

/-- **Subcompositional invariance (the genuinely matrix-independent quantity).** The recovered RATIO
of two detected species equals their true density ratio `n_s/n_t`, independent of the detected set
`D` (Aitchison coherence): the *shared* detected-sum cancels. -/
theorem recoveredComposition_ratio {n : κ → ℝ} {D : Finset κ}
    (hd : detectedDensity n D ≠ 0) {s t : κ} (ht : n t ≠ 0) :
    recoveredComposition n D s / recoveredComposition n D t = n s / n t := by
  unfold recoveredComposition
  field_simp

/-- **THE headline — matrix-independence of the recovered subcomposition.** The recovered ratio of
two detected species is the SAME under any two detected sets `D₁, D₂`: the completeness channel does
not bias pairwise ratios (only absolute fractions). -/
theorem recoveredComposition_ratio_matrix_invariant {n : κ → ℝ} {D₁ D₂ : Finset κ}
    (hd₁ : detectedDensity n D₁ ≠ 0) (hd₂ : detectedDensity n D₂ ≠ 0)
    {s t : κ} (ht : n t ≠ 0) :
    recoveredComposition n D₁ s / recoveredComposition n D₁ t
      = recoveredComposition n D₂ s / recoveredComposition n D₂ t := by
  rw [recoveredComposition_ratio hd₁ ht, recoveredComposition_ratio hd₂ ht]

/-- **The absolute fractions ARE matrix-dependent.** The same species' recovered fraction differs
between two detected sets by exactly the inverse ratio of detected densities — quantifying that
absolute CF-LIBS fractions (unlike subcompositions) carry a completeness-channel matrix effect. -/
theorem recoveredComposition_absolute_matrix_dependent {n : κ → ℝ} {D₁ D₂ : Finset κ}
    (hd₁ : detectedDensity n D₁ ≠ 0) (hd₂ : detectedDensity n D₂ ≠ 0)
    {s : κ} (hs : n s ≠ 0) :
    recoveredComposition n D₁ s / recoveredComposition n D₂ s
      = detectedDensity n D₂ / detectedDensity n D₁ := by
  unfold recoveredComposition
  field_simp

section
variable [Fintype κ]

/-- **Missing (undetected) mass fraction** `m = 1 − (∑_{t∈D} n_t)/(∑_t n_t)`: the share of the true
number density that falls below the detection limit. -/
noncomputable def missingFraction (n : κ → ℝ) (D : Finset κ) : ℝ :=
  1 - detectedDensity n D / totalDensity n

/-- **Inflation factor** `T / (∑_{t∈D} n_t)`: the multiplicative bias of every detected element's
recovered fraction caused by closing over an incomplete species set. Equals `1/(1−m)`. -/
noncomputable def inflationFactor (n : κ → ℝ) (D : Finset κ) : ℝ :=
  totalDensity n / detectedDensity n D

/-- Detecting ALL species recovers the ordinary `totalDensity`. -/
theorem detectedDensity_univ (n : κ → ℝ) : detectedDensity n univ = totalDensity n := rfl

/-- **Complete detection recovers ordinary closure.** `recoveredComposition n univ = composition n`
— the new estimator strictly generalizes `Closure.composition`. -/
theorem recoveredComposition_univ (n : κ → ℝ) (s : κ) :
    recoveredComposition n univ s = composition n s := by
  rw [recoveredComposition, composition, detectedDensity_univ]

/-- The detected density never exceeds the total (omitting nonnegative terms can only shrink it). -/
theorem detectedDensity_le_totalDensity {n : κ → ℝ} {D : Finset κ}
    (hn : ∀ s, 0 ≤ n s) : detectedDensity n D ≤ totalDensity n :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ D) (fun i _ _ => hn i)

/-- **The inflation factor is exactly `1/(1−m)`** with `m` the missing fraction. A definitional
identity (true wherever the densities are; the physical regime is `T, ∑_{t∈D} n_t > 0`). -/
theorem inflationFactor_eq (n : κ → ℝ) (D : Finset κ) :
    inflationFactor n D = 1 / (1 - missingFraction n D) := by
  unfold inflationFactor missingFraction
  rw [sub_sub_cancel, one_div_div]

/-- **Incomplete detection over-estimates: the inflation factor is `≥ 1`.** -/
theorem one_le_inflationFactor {n : κ → ℝ} {D : Finset κ}
    (hn : ∀ s, 0 ≤ n s) (hd : 0 < detectedDensity n D) :
    1 ≤ inflationFactor n D := by
  unfold inflationFactor
  rw [le_div_iff₀ hd, one_mul]
  exact detectedDensity_le_totalDensity hn

/-- **Recovered = true × inflation:** `Ĉ_D s = C_s · (T/∑_{t∈D} n_t)`. The recovered absolute
fraction is the true fraction scaled by the matrix-completeness inflation factor. -/
theorem recoveredComposition_eq_inflation {n : κ → ℝ} {D : Finset κ}
    (hT : 0 < totalDensity n) (hd : 0 < detectedDensity n D) (s : κ) :
    recoveredComposition n D s = composition n s * inflationFactor n D := by
  unfold recoveredComposition composition inflationFactor
  have hTne := hT.ne'
  have hdne := hd.ne'
  field_simp

/-- **Over-estimation of every detected element:** `C_s ≤ Ĉ_D s`. Closing over an incomplete species
set inflates each detected fraction above its true value (Tognoni et al. 2010). -/
theorem composition_le_recoveredComposition {n : κ → ℝ} {D : Finset κ}
    (hn : ∀ s, 0 ≤ n s) (hd : 0 < detectedDensity n D) (s : κ) :
    composition n s ≤ recoveredComposition n D s := by
  unfold composition recoveredComposition
  gcongr
  all_goals first
    | exact hn s
    | exact detectedDensity_le_totalDensity hn

/-- The missing fraction is nonnegative. -/
theorem missingFraction_nonneg {n : κ → ℝ} {D : Finset κ}
    (hn : ∀ s, 0 ≤ n s) (hT : 0 < totalDensity n) : 0 ≤ missingFraction n D := by
  unfold missingFraction
  rw [sub_nonneg, div_le_one hT]
  exact detectedDensity_le_totalDensity hn

end

/-! ## Ablation channel — the intensity bridge (recovered densities come from real forward lines) -/

variable {ι : Type*} [Fintype ι]

/-- The per-species density recovered from each species' representative forward line, via
`MultiSpecies.deNormalizedDensity` (a function of the FULL measured intensity, not of `N`). -/
noncomputable def recoveredDensityOfSpectrum (kB T Fcal : ℝ) (g E A : κ → ι → ℝ)
    (N : κ → ℝ) (u : κ → ι) (s : κ) : ℝ :=
  deNormalizedDensity kB T Fcal (g s) (E s) (A s) (u s)
    (lineIntensity kB T (N s) Fcal (g s) (E s) (A s) (u s))

/-- The recovered-density vector of a forward spectrum equals the true densities `N` pointwise. -/
theorem recoveredDensityOfSpectrum_eq [Nonempty ι] {kB T Fcal : ℝ} {g E A : κ → ι → ℝ}
    {N : κ → ℝ} {u : κ → ι}
    (hg : ∀ s k, 0 < g s k) (hN : ∀ s, 0 < N s) (hFcal : 0 < Fcal) (hA : ∀ s k, 0 < A s k) :
    recoveredDensityOfSpectrum kB T Fcal g E A N u = N := by
  funext s
  exact deNormalized_lineIntensity (hg s) (hN s) hFcal (hA s) (u s)

/-- **The recovered subcomposition from REAL forward intensities is the true ratio `N_s/N_t`,**
independent of the detected set `D`. An overall calibration factor `Fcal` (the ablation channel)
and the completeness channel `D` both cancel in the ratio; `T` is held fixed (so this is the
ablation channel only, not a temperature-shift claim). -/
theorem recovered_ratio_from_intensities [Nonempty ι] {kB T Fcal : ℝ} {g E A : κ → ι → ℝ}
    {N : κ → ℝ} {u : κ → ι} {D : Finset κ}
    (hg : ∀ s k, 0 < g s k) (hN : ∀ s, 0 < N s) (hFcal : 0 < Fcal) (hA : ∀ s k, 0 < A s k)
    (hd : detectedDensity N D ≠ 0) {s t : κ} (ht : N t ≠ 0) :
    recoveredComposition (recoveredDensityOfSpectrum kB T Fcal g E A N u) D s
        / recoveredComposition (recoveredDensityOfSpectrum kB T Fcal g E A N u) D t
      = N s / N t := by
  rw [recoveredDensityOfSpectrum_eq hg hN hFcal hA]
  exact recoveredComposition_ratio hd ht

/-! ## Ionization-suppression channel — an easily ionized matrix floods `n_e` -/

/-- Saha ion density at electron density `n_e`: `n_ion = N_tot·S/(S+n_e)` (the unique solution of
`n_ion·n_e/n_neutral = S` with `n_ion + n_neutral = N_tot`). `S > 0` is the Saha factor. -/
noncomputable def sahaIonDensity (S Ntot ne : ℝ) : ℝ := Ntot * S / (S + ne)

/-- Saha neutral density at electron density `n_e`: `n_neutral = N_tot·n_e/(S+n_e)`. -/
noncomputable def sahaNeutralDensity (S Ntot ne : ℝ) : ℝ := Ntot * ne / (S + ne)

/-- The two stages partition the element's total density: `n_neutral + n_ion = N_tot` (exact at any
`n_e`). On its own a trivial partition; its content is the pair with `sahaSplit_saha`. -/
theorem sahaSplit_sum {S Ntot ne : ℝ} (hS : 0 < S) (hne : 0 < ne) :
    sahaNeutralDensity S Ntot ne + sahaIonDensity S Ntot ne = Ntot := by
  unfold sahaNeutralDensity sahaIonDensity
  have h : S + ne ≠ 0 := by positivity
  field_simp
  ring

/-- The split is genuinely the Saha split: `n_ion·n_e/n_neutral = S`. This certifies that
`sahaSplit_sum` partitions `N_tot` in the *ionization-equilibrium* proportion, not arbitrarily. -/
theorem sahaSplit_saha {S Ntot ne : ℝ} (hS : 0 < S) (hne : 0 < ne) (hN : Ntot ≠ 0) :
    sahaIonDensity S Ntot ne * ne / sahaNeutralDensity S Ntot ne = S := by
  unfold sahaIonDensity sahaNeutralDensity
  have h : S + ne ≠ 0 := by positivity
  field_simp

/-- **Ionization suppression.** The ion density `n_ion = N_tot·S/(S+n_e)` is strictly DECREASING in
the electron density `n_e`: an easily ionized matrix element that floods the plasma with electrons
suppresses the ionization of every other element (Aguilera & Aragón 2007). -/
theorem sahaIonDensity_antitone {S Ntot : ℝ} (hS : 0 < S) (hN : 0 < Ntot) :
    StrictAntiOn (fun ne => sahaIonDensity S Ntot ne) (Set.Ioi 0) := by
  intro x hx y hy hxy
  rw [Set.mem_Ioi] at hx hy
  simp only [sahaIonDensity]
  gcongr

/-! ## Per-shot temperature robustness — the homologous-line-pair technique

Everything above holds `T` (and `n_e`) FIXED. Real LIBS plasmas jitter shot-to-shot: `T` changes
between acquisitions. This section adds the missing per-shot-`T` robustness channel, grounding the
classical **homologous-line-pair** (internal-standard) technique.

The forward line intensity of species `s`'s designated line (`ForwardMap.lineIntensity`) is
`I_s(T) = Fcal · A_s · N_s · g_s · exp(-E_s/(k_B T)) / U(T)`, so the two-species intensity RATIO
carries the plasma temperature through (i) the Boltzmann exponentials `exp(-E_s/(k_B T))`,
`exp(-E_t/(k_B T))` and (ii) the partition function `U(T)`. A **homologous pair** — the two
species' designated lines chosen with EQUAL upper-level energies `E_s = E_t` — kills channel (i)
EXACTLY: the exponentials cancel identically, so the ratio is invariant under ARBITRARY per-shot
temperature change `T ↦ T'` (`homologousPair_ratio_temperature_invariant`).

**How `U` enters (honest scope).** In this module's shared-atomic-data encoding both designated
lines are drawn from a COMMON partition-function manifold (`g E A : ι → ℝ`), so the SAME `U(T)`
sits in numerator and denominator and cancels EXACTLY even though it genuinely depends on `T`
(`homologousPair_ratio_closed_form`): the shared-`U` case is fully EXACT. When the two species
carry genuinely per-species partition functions `U_s(T) ≠ U_t(T)` (`lineIntensityPerU`), energy
matching still cancels channel (i) exactly and the ONLY residual is the partition-function
ratio `U_t/U_s` (`homologousPair_ratio_perU_closed_form`, `= U_s = U_t` recovering the shared case).
That residual — a slowly-varying secondary channel — is left EXPLICIT, not hidden; the derived
`homologousPair_ratio_perU_temperature_invariant` is REDUCED, since it freezes `U_s, U_t` across
shots (the `lineIntensityPerU` convention treats `U` as a per-shot scalar input), isolating the
Boltzmann channel from the genuine `U_s(T)` drift.

**Necessity / contrast.** Invariance is a property OF the energy matching: with `E_s ≠ E_t` the
exponential factor `exp((E_t − E_s)/(k_B T))` genuinely varies with `T`, so the ratio at two
distinct temperatures differs (`nonHomologousPair_ratio_temperature_dependent`).

**Cross-references (out of scope here).** The QUANTITATIVE finite-`|ΔE|` per-shot drift bound
`|ratio(T₁) − ratio(T₂)| ≤ f(ΔE, ΔT)`, linear in `|ΔE|`, is
`Identifiability.temperature_ratio_near_degenerate`; its `ΔE = 0` exact limit is the SAME-species
(`N_s = N_t`, one element's two lines) sibling of the CROSS-species (`N_s ≠ N_t`) invariance proved
here. Per-shot `n_e` variation enters CF-LIBS only through the Saha ionization balance (stage
shuffling), OUTSIDE this module's Boltzmann-only intensity encoding — see the ionization-suppression
channel above (`sahaIonDensity_antitone`) and `SahaInverse`/`Identifiability`. -/

/-- **Cross-species two-line ratio — closed form (shared partition function).** For two species
with designated-line densities `N_s, N_t` emitting from a COMMON atomic-data family `(g, E, A)` at
one temperature `T`, the intensity ratio is
`I_s/I_t = ((N_s·g_s·A_s)/(N_t·g_t·A_t)) · exp((E_t − E_s)/(k_B T))`:
the calibration `Fcal` and the shared partition function `U(T)` cancel EXACTLY. The whole
temperature dependence of the ratio is the single Boltzmann exponential in the energy GAP
`E_t − E_s`. (Ciucci et al. 1999, the two-line Boltzmann ratio; here across two species.) -/
theorem homologousPair_ratio_closed_form [Nonempty ι] {kB T Ns Nt Fcal : ℝ} {g E A : ι → ℝ}
    (hg : ∀ k, 0 < g k) (hNt : 0 < Nt) (hFcal : 0 < Fcal) (hA : ∀ k, 0 < A k) (s t : ι) :
    lineIntensity kB T Ns Fcal g E A s / lineIntensity kB T Nt Fcal g E A t
      = (Ns * g s * A s) / (Nt * g t * A t) * Real.exp ((E t - E s) / (kB * T)) := by
  have hU : 0 < partitionFunction kB T g E := partitionFunction_pos hg
  have hUne : partitionFunction kB T g E ≠ 0 := hU.ne'
  have hgt : g t ≠ 0 := (hg t).ne'
  have hAt : A t ≠ 0 := (hA t).ne'
  have hNtne : Nt ≠ 0 := hNt.ne'
  have hFne : Fcal ≠ 0 := hFcal.ne'
  have hexp : Real.exp ((E t - E s) / (kB * T))
      = Real.exp (-E s / (kB * T)) / Real.exp (-E t / (kB * T)) := by
    rw [← Real.exp_sub]; ring_nf
  rw [hexp]
  simp only [lineIntensity, population, boltzmannFactor]
  field_simp

/-- **THE per-shot-`T` deliverable — homologous-pair exact temperature invariance.** For a
homologous pair (two species' designated lines with EQUAL upper-level energies `E_s = E_t`, drawn
from a common partition-function manifold), the two-species intensity ratio is the SAME at ANY two
temperatures `T`, `T'`:
`I_s(T)/I_t(T) = I_s(T')/I_t(T')`.
The Boltzmann exponentials cancel identically at the matched energy and the shared `U(T)` cancels,
so per-shot temperature jitter leaves the ratio invariant — the exact ground of the
homologous-line-pair technique. No positivity of `T`, `T'` is needed: the collapse is total (both
sides equal the `T`-free constant `(N_s·g_s·A_s)/(N_t·g_t·A_t)`). This is the CROSS-species
(`N_s ≠ N_t`) form; the same-species sibling is `Identifiability.temperature_degeneracy`. -/
theorem homologousPair_ratio_temperature_invariant [Nonempty ι]
    {kB T T' Ns Nt Fcal : ℝ} {g E A : ι → ℝ}
    (hg : ∀ k, 0 < g k) (hNt : 0 < Nt) (hFcal : 0 < Fcal) (hA : ∀ k, 0 < A k)
    (s t : ι) (hE : E s = E t) :
    lineIntensity kB T Ns Fcal g E A s / lineIntensity kB T Nt Fcal g E A t
      = lineIntensity kB T' Ns Fcal g E A s / lineIntensity kB T' Nt Fcal g E A t := by
  rw [homologousPair_ratio_closed_form hg hNt hFcal hA s t,
    homologousPair_ratio_closed_form hg hNt hFcal hA s t, hE]
  simp

/-- **Contrast — invariance is a property OF the energy matching.** With DISTINCT upper-level
energies `E_s ≠ E_t` the two-species intensity ratio genuinely varies with temperature: at two
distinct positive temperatures `T ≠ T'` (with `k_B > 0`) the ratios differ. The surviving
Boltzmann factor `exp((E_t − E_s)/(k_B T))` is a non-constant function of `T` once `ΔE ≠ 0`, so
`homologousPair_ratio_temperature_invariant` genuinely requires the homologous (`E_s = E_t`)
hypothesis. (Ciucci et al. 1999, the two-line Boltzmann ratio.) -/
theorem nonHomologousPair_ratio_temperature_dependent [Nonempty ι]
    {kB T T' Ns Nt Fcal : ℝ} {g E A : ι → ℝ}
    (hkB : 0 < kB) (hT : 0 < T) (hT' : 0 < T') (hTT' : T ≠ T')
    (hg : ∀ k, 0 < g k) (hNs : 0 < Ns) (hNt : 0 < Nt) (hFcal : 0 < Fcal) (hA : ∀ k, 0 < A k)
    (s t : ι) (hE : E s ≠ E t) :
    lineIntensity kB T Ns Fcal g E A s / lineIntensity kB T Nt Fcal g E A t
      ≠ lineIntensity kB T' Ns Fcal g E A s / lineIntensity kB T' Nt Fcal g E A t := by
  rw [homologousPair_ratio_closed_form hg hNt hFcal hA s t,
    homologousPair_ratio_closed_form hg hNt hFcal hA s t]
  intro h
  have hc : (0 : ℝ) < (Ns * g s * A s) / (Nt * g t * A t) :=
    div_pos (mul_pos (mul_pos hNs (hg s)) (hA s)) (mul_pos (mul_pos hNt (hg t)) (hA t))
  have hexp : Real.exp ((E t - E s) / (kB * T)) = Real.exp ((E t - E s) / (kB * T')) :=
    mul_left_cancel₀ hc.ne' h
  rw [Real.exp_eq_exp] at hexp
  have hEts : E t - E s ≠ 0 := sub_ne_zero.mpr (Ne.symm hE)
  rw [div_eq_div_iff (mul_pos hkB hT).ne' (mul_pos hkB hT').ne'] at hexp
  have h2 : kB * T' = kB * T := mul_left_cancel₀ hEts hexp
  exact hTT' (mul_left_cancel₀ hkB.ne' h2).symm

omit [Fintype ι] in
/-- **Per-species-`U` two-line ratio — closed form with the `U`-residual explicit.** With
GENUINELY per-species partition functions `U_s, U_t` (each summed over its own species' internal
manifold, carried as `MultiSpecies.lineIntensityPerU` scalars) and per-species designated-line data
`(g_s, E_s, A_s)`, `(g_t, E_t, A_t)`, the intensity ratio is
`I_s/I_t = ((N_s·g_s·A_s·U_t)/(N_t·g_t·A_t·U_s)) · exp((E_t − E_s)/(k_B T))`.
Energy matching `E_s = E_t` collapses the exponential to `1`, leaving the ratio's ENTIRE residual
equal to the partition-function ratio `U_t/U_s` — the honest per-species form of the
homologous-pair identity (the shared-`U` `homologousPair_ratio_closed_form` is the case
`U_s = U_t`). **Scope EXACT** for the fixed-`T` identity; `U_s, U_t` are free positive inputs. -/
theorem homologousPair_ratio_perU_closed_form {kB T Ns Nt Fcal Us Ut : ℝ} {g E A : ι → ℝ}
    (hg : ∀ k, 0 < g k) (hNt : 0 < Nt) (hFcal : 0 < Fcal) (hA : ∀ k, 0 < A k)
    (hUs : 0 < Us) (hUt : 0 < Ut) (s t : ι) :
    lineIntensityPerU kB T Ns Fcal Us g E A s / lineIntensityPerU kB T Nt Fcal Ut g E A t
      = (Ns * g s * A s * Ut) / (Nt * g t * A t * Us) * Real.exp ((E t - E s) / (kB * T)) := by
  have hgt : g t ≠ 0 := (hg t).ne'
  have hAt : A t ≠ 0 := (hA t).ne'
  have hNtne : Nt ≠ 0 := hNt.ne'
  have hFne : Fcal ≠ 0 := hFcal.ne'
  have hUsne : Us ≠ 0 := hUs.ne'
  have hUtne : Ut ≠ 0 := hUt.ne'
  have hexp : Real.exp ((E t - E s) / (kB * T))
      = Real.exp (-E s / (kB * T)) / Real.exp (-E t / (kB * T)) := by
    rw [← Real.exp_sub]; ring_nf
  rw [hexp]
  simp only [lineIntensityPerU, boltzmannFactor]
  field_simp

omit [Fintype ι] in
/-- **Per-species-`U` homologous-pair temperature invariance (REDUCED).** In the per-species-`U`
forward model, a homologous pair (`E_s = E_t`) has a temperature-invariant intensity ratio
`I_s(T)/I_t(T) = I_s(T')/I_t(T')`, its common value the residual
`(N_s·g_s·A_s·U_t)/(N_t·g_t·A_t·U_s)`.
**REDUCED**, not EXACT: `MultiSpecies.lineIntensityPerU` carries each `U_s` as a per-shot scalar
INPUT, so varying `T` here holds `U_s, U_t` fixed. It therefore isolates the Boltzmann/exponential
temperature channel (killed exactly by energy matching) from the genuine per-species drift
`U_s(T)/U_t(T)`, which is the physical residual left OUT of scope (the shared-`U`
`homologousPair_ratio_temperature_invariant` is EXACT because there the single `U(T)` cancels
regardless of its `T`-dependence). -/
theorem homologousPair_ratio_perU_temperature_invariant {kB T T' Ns Nt Fcal Us Ut : ℝ}
    {g E A : ι → ℝ}
    (hg : ∀ k, 0 < g k) (hNt : 0 < Nt) (hFcal : 0 < Fcal) (hA : ∀ k, 0 < A k)
    (hUs : 0 < Us) (hUt : 0 < Ut) (s t : ι) (hE : E s = E t) :
    lineIntensityPerU kB T Ns Fcal Us g E A s / lineIntensityPerU kB T Nt Fcal Ut g E A t
      = lineIntensityPerU kB T' Ns Fcal Us g E A s
          / lineIntensityPerU kB T' Nt Fcal Ut g E A t := by
  rw [homologousPair_ratio_perU_closed_form hg hNt hFcal hA hUs hUt s t,
    homologousPair_ratio_perU_closed_form hg hNt hFcal hA hUs hUt s t, hE]
  simp

/-! ### Non-vacuity witnesses (per-shot temperature robustness) -/

/-- Emitting-level degeneracies of two species (positive, distinct). -/
private def nvMeG : Fin 2 → ℝ := ![2, 5]

/-- MATCHED upper-level energies of a homologous pair: `E 0 = 1 = E 1`. -/
private def nvMeEmatch : Fin 2 → ℝ := ![1, 1]

/-- Einstein coefficients of the two designated lines (positive). -/
private def nvMeA : Fin 2 → ℝ := ![3, 7]

/-- **Non-vacuity of `homologousPair_ratio_temperature_invariant`.** Two species with genuinely
different densities (`N_0 = 4 ≠ 6 = N_1`), degeneracies (`g 0 = 2 ≠ 5 = g 1`) and Einstein
coefficients but MATCHED upper-level energies (`E 0 = E 1 = 1`) give the SAME intensity ratio at
`T = 1` and at `T = 5` — the per-shot temperature jitter is killed exactly by the energy match. -/
example :
    lineIntensity 1 1 4 1 nvMeG nvMeEmatch nvMeA 0
        / lineIntensity 1 1 6 1 nvMeG nvMeEmatch nvMeA 1
      = lineIntensity 1 5 4 1 nvMeG nvMeEmatch nvMeA 0
          / lineIntensity 1 5 6 1 nvMeG nvMeEmatch nvMeA 1 := by
  have hg : ∀ k : Fin 2, 0 < nvMeG k := fun k => by fin_cases k <;> norm_num [nvMeG]
  have hA : ∀ k : Fin 2, 0 < nvMeA k := fun k => by fin_cases k <;> norm_num [nvMeA]
  have hE : nvMeEmatch 0 = nvMeEmatch 1 := by norm_num [nvMeEmatch]
  exact homologousPair_ratio_temperature_invariant hg (by norm_num) (by norm_num) hA 0 1 hE

/-- Degeneracies for the distinct-energy contrast (positive). -/
private def nvMeGd : Fin 2 → ℝ := ![1, 1]

/-- DISTINCT upper-level energies (`E 0 = 0 ≠ 1 = E 1`): a non-homologous pair. -/
private def nvMeEdiff : Fin 2 → ℝ := ![0, 1]

/-- Einstein coefficients for the distinct-energy contrast (positive). -/
private def nvMeAd : Fin 2 → ℝ := ![1, 1]

/-- **Non-vacuity of `nonHomologousPair_ratio_temperature_dependent`.** With DISTINCT energies
(`E 0 = 0 ≠ 1 = E 1`) the two-species ratio is a genuinely non-constant function of temperature:
at `T = 1` and `T = 2` the ratios differ. So the homologous-pair invariance is not vacuous — it
truly hinges on `E_s = E_t`. -/
example :
    lineIntensity 1 1 4 1 nvMeGd nvMeEdiff nvMeAd 0
        / lineIntensity 1 1 6 1 nvMeGd nvMeEdiff nvMeAd 1
      ≠ lineIntensity 1 2 4 1 nvMeGd nvMeEdiff nvMeAd 0
          / lineIntensity 1 2 6 1 nvMeGd nvMeEdiff nvMeAd 1 := by
  have hg : ∀ k : Fin 2, 0 < nvMeGd k := fun k => by fin_cases k <;> norm_num [nvMeGd]
  have hA : ∀ k : Fin 2, 0 < nvMeAd k := fun k => by fin_cases k <;> norm_num [nvMeAd]
  have hE : nvMeEdiff 0 ≠ nvMeEdiff 1 := by norm_num [nvMeEdiff]
  exact nonHomologousPair_ratio_temperature_dependent one_pos one_pos two_pos (by norm_num)
    hg (by norm_num) (by norm_num) one_pos hA 0 1 hE

end CflibsFormal
