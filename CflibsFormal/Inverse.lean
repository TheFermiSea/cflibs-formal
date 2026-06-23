/-
Copyright (c) 2026 Brian Squires. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Squires
-/
import Mathlib
import CflibsFormal.Boltzmann
import CflibsFormal.ForwardMap
import CflibsFormal.Closure
import CflibsFormal.Identifiability

/-!
# CF-LIBS formalization — Part 6: the algorithm-agnostic inverse-problem framework

This module assembles the *shared core* of the CF-LIBS inverse problem, the part
that is common to **every** composition-extraction algorithm (classical CF-LIBS,
C-sigma, …). It reuses the already-proven forward model (`ForwardMap.lineIntensity`,
the `Boltzmann` populations) and closure (`Closure.composition`) verbatim — nothing
here re-defines or re-proves the forward map or the identifiability cores.

The encoding is deliberately a *plain record of functions over `Fintype` indices*
(no heavy structure/typeclass machinery):

* `PlasmaParams` — the parameters of a multi-species LTE plasma: shared temperature
  `T`, per-species total density `N`, and shared atomic data `g E A` (one emitting
  level per species is selected by a separate `emit : species → levelIndex` map fed
  to the observation map).
* `PlasmaParams.Admissible` — the nondegeneracy bundle (`0 < T`, `0 < N s`, `0 < g`,
  `0 < A`) that makes a `PlasmaParams` a physical LTE state.
* `observe` — the **forward / observation map**: the observable for species `s` is
  the integrated intensity of its single emitting line `emit s`, reusing
  `lineIntensity` (one line per species).
* `CompositionEstimator` — a plain map `(species → ℝ) → (species → ℝ)` from an
  observation vector to an estimated composition vector. Every concrete extraction
  method is an inhabitant.
* `trueComposition` — the ground-truth target `C s = N s / ∑ₜ N t` (= `composition
  p.N`), the estimator-*independent* answer.
* `Sound` — the correctness contract: a sound estimator returns `trueComposition p`
  on any observation arising from the forward model applied to an admissible `p`.

The central results are:

* `general_identifiability` — under explicit nondegeneracy (positive `T`, `N`, `g`,
  `A`; one emitting line per species via `emit`; plus an additional assumed two-line
  Boltzmann ratio on a distinct-energy pair `(i,j)` that fixes `T`), if two admissible
  parameter sets produce **equal observations** (and share calibration / atomic data),
  then they have **equal temperature and equal composition**. *Honest scoping:* the
  temperature equality is delivered by the supplied ratio hypothesis `hTratio` (an
  additional assumed two-line Boltzmann ratio), **not** extracted from `hObs` — the
  one-line-per-species observation map `observe` only constrains the emitting lines.
  Assembled strictly from the proven `temperature_identifiability` and
  `density_identifiability` (neither reproven), plus `Closure.composition`.
* `sound_estimators_agree` — the abstract **cross-method agreement bridge**: any two
  sound estimators return equal compositions on forward-model observations from an
  admissible parameter set. A short `Sound + Sound` consequence (both equal
  `trueComposition p`). This is what makes classical CF-LIBS and C-sigma comparable.
* `rawCompositionEstimator` / `rawCompositionEstimator_sound` — a *concrete* sound
  estimator inhabiting the `Sound` predicate (for the constant-`emit` case, where every
  species shares one emitting level), so `sound_estimators_agree` has a non-vacuous
  premise: the raw estimator simply normalizes the observed intensities, which equals
  the true composition because the shared per-species forward constant cancels under
  the scale-invariant closure normalization.
-/

namespace CflibsFormal

open Finset Real
open scoped BigOperators

variable {species levelIndex : Type*}

/-- Encoding of the parameters of a multi-species LTE plasma for the inverse problem.
`T` is the single shared electron/excitation temperature; `N s` is the total number
density of species `s`; `g`, `E`, `A` are the shared atomic data (statistical
weights, level energies, Einstein A-coefficients) indexed by atomic level. One
*emitting level* per species is selected separately by an `emit : species →
levelIndex` map supplied to the observation map, so the same atomic-data tables
`g E A` serve every species (CF-LIBS shares a level catalog).

Kept as a plain `structure` of fields over `Fintype` indices — no typeclass
machinery — so it is a transparent record the forward map can destructure. -/
structure PlasmaParams (species levelIndex : Type*) where
  /-- shared plasma temperature -/
  T : ℝ
  /-- per-species total number density -/
  N : species → ℝ
  /-- shared statistical weights, indexed by atomic level -/
  g : levelIndex → ℝ
  /-- shared level energies, indexed by atomic level -/
  E : levelIndex → ℝ
  /-- shared Einstein A-coefficients, indexed by atomic level -/
  A : levelIndex → ℝ

/-- Nondegeneracy / admissibility predicate bundling the positivity hypotheses the
identifiability theorems require: positive temperature, strictly positive density for
every species, strictly positive statistical weights and Einstein coefficients for
every level. (`E` is unconstrained — energies may be any real, and energy
*differences* enter the temperature step.) This is the hypothesis bundle that makes a
`PlasmaParams` a physical LTE state. -/
def PlasmaParams.Admissible (p : PlasmaParams species levelIndex) : Prop :=
  0 < p.T ∧ (∀ s, 0 < p.N s) ∧ (∀ k, 0 < p.g k) ∧ (∀ k, 0 < p.A k)

/-- **Observation / forward map.** The observable attached to species `s` is the
integrated intensity of its single emitting line, whose upper level is `emit s`:
`observe kB Fcal emit p s = lineIntensity kB p.T (p.N s) Fcal p.g p.E p.A (emit s)`.

Reuses `ForwardMap.lineIntensity` verbatim (one line per species, the "at least one
line per species" data). `kB` is Boltzmann's constant and `Fcal` is the shared
instrument/geometry calibration constant. The full observation vector is
`observe kB Fcal emit p`. -/
noncomputable def observe [Fintype levelIndex] (kB Fcal : ℝ) (emit : species → levelIndex)
    (p : PlasmaParams species levelIndex) (s : species) : ℝ :=
  lineIntensity kB p.T (p.N s) Fcal p.g p.E p.A (emit s)

/-- A **composition estimator**: a map from an observation vector `(species → ℝ)`
(the measured line intensities, one per species) to a composition vector `(species →
ℝ)` (estimated number fractions). Plain function type — every concrete extraction
method (classical CF-LIBS, C-sigma, …) is an inhabitant. -/
def CompositionEstimator (species : Type*) : Type _ :=
  (species → ℝ) → (species → ℝ)

variable [Fintype species]

/-- The **true composition** of a parameter set: the closure number fractions
`C s = N s / ∑ₜ N t` of the per-species densities, reusing `Closure.composition`.
This is the ground-truth target every sound estimator must return. -/
noncomputable def trueComposition (p : PlasmaParams species levelIndex) (s : species) : ℝ :=
  composition p.N s

/-- **Soundness** of an estimator: on any observation vector that genuinely arises
from the forward model applied to an *admissible* parameter set `p`, the estimator
returns the true composition `trueComposition p`. This is the correctness contract
shared by all extraction methods; agreement between methods follows from two of them
satisfying it.

Non-tautological: `est` is an *opaque* universally-quantified function, and
`trueComposition` is the estimator-*independent* target — soundness genuinely
constrains `est` rather than being baked into its definition. -/
def Sound [Fintype levelIndex] (kB Fcal : ℝ) (emit : species → levelIndex)
    (est : CompositionEstimator species) : Prop :=
  ∀ p : PlasmaParams species levelIndex, p.Admissible →
    est (observe kB Fcal emit p) = trueComposition p

/-- **General identifiability — the central theorem.**

Under explicit nondegeneracy (positive `T`, `N`, `g`, `A` via `Admissible`; one
emitting line per species via `emit`; an additional assumed two-line Boltzmann ratio
`hTratio` on a distinct-energy pair `(i,j)` that fixes `T`), if two admissible
parameter sets produce **equal observations** `hObs`, share calibration (`hFeq`) and
atomic data (`hgeq`, `hEeq`, `hAeq`), then they have **equal temperature** and
**equal composition**.

*Honest scoping.* The temperature equality is delivered by `hTratio` — an additional
assumed two-line Boltzmann ratio on a distinct-energy pair — **not** by `hObs`. The
one-line-per-species observation map `observe` constrains only the emitting lines
`emit s`; the distinct-energy pair `(i,j)` that pins `T` need not be observed. The
composition equality *is* extracted from `hObs`: equal per-species line intensities
with matched calibration and atomic data force equal `N s` for every species (via the
proven `density_identifiability`), hence equal closure composition.

Assembled strictly from the already-proven `temperature_identifiability` and
`density_identifiability` (neither reproven), plus `Closure.composition`.

Non-vacuous: take `species = Fin 1`, `levelIndex = Fin 2`, `kB = Fcal₁ = Fcal₂ = 1`,
`emit = fun _ => 0`, `p₁ = p₂` with `T = 1`, `N = g = A = fun _ => 1`, `E = ![0,1]`.
Then `E i ≠ E j` (`0 ≠ 1`), `Admissible` holds, the ratio and observation equalities
are reflexive, and the conclusion holds; the content (for differing parameter sets) is
that `hTratio` forces `T₁ = T₂` via `Real.exp` injectivity and `hObs` forces equal
composition via positive-constant cancellation — neither is `rfl`. -/
theorem general_identifiability
    [Fintype levelIndex] [Nonempty levelIndex]
    {kB Fcal₁ Fcal₂ : ℝ} {emit : species → levelIndex}
    {p₁ p₂ : PlasmaParams species levelIndex}
    (s₀ : species)
    (hkB : 0 < kB) (hFcal₁ : 0 < Fcal₁) (hFcal₂ : 0 < Fcal₂)
    (ha₁ : p₁.Admissible) (ha₂ : p₂.Admissible)
    (i j : levelIndex) (hE₁ : p₁.E i ≠ p₁.E j)
    (hEeq : p₁.E = p₂.E) (hgeq : p₁.g = p₂.g) (hAeq : p₁.A = p₂.A)
    (hFeq : Fcal₁ = Fcal₂)
    (hTratio :
      lineIntensity kB p₁.T (p₁.N s₀) Fcal₁ p₁.g p₁.E p₁.A j
          / lineIntensity kB p₁.T (p₁.N s₀) Fcal₁ p₁.g p₁.E p₁.A i
        = lineIntensity kB p₂.T (p₂.N s₀) Fcal₂ p₂.g p₂.E p₂.A j
          / lineIntensity kB p₂.T (p₂.N s₀) Fcal₂ p₂.g p₂.E p₂.A i)
    (hObs : observe kB Fcal₁ emit p₁ = observe kB Fcal₂ emit p₂) :
    p₁.T = p₂.T ∧ (∀ s, trueComposition p₁ s = trueComposition p₂ s) := by
  obtain ⟨hT₁, hN₁, hg₁, hA₁⟩ := ha₁
  obtain ⟨hT₂, hN₂, hg₂, hA₂⟩ := ha₂
  -- (1) Temperature: rewrite the right-hand side of `hTratio` to share p₁'s atomic
  -- data, then apply the proven `temperature_identifiability`.
  rw [← hgeq, ← hEeq, ← hAeq] at hTratio
  have hT : p₁.T = p₂.T :=
    temperature_identifiability hkB hT₁ hT₂ hg₁ (hN₁ s₀) (hN₂ s₀)
      hFcal₁ hFcal₂ hA₁ i j hE₁ hTratio
  refine ⟨hT, ?_⟩
  -- (2) Composition: from `hObs`, every species' emitting-line intensity matches.
  -- Rewrite so both sides share kB T Fcal g E A, then `density_identifiability`
  -- gives equal `N s` for every species.
  have hNeq : ∀ s, p₁.N s = p₂.N s := by
    intro s
    have hObs_s :
        lineIntensity kB p₁.T (p₁.N s) Fcal₁ p₁.g p₁.E p₁.A (emit s)
          = lineIntensity kB p₂.T (p₂.N s) Fcal₂ p₂.g p₂.E p₂.A (emit s) := by
      have := congrFun hObs s
      simpa only [observe] using this
    -- Bring the right side to share p₁'s temperature, calibration and atomic data,
    -- leaving only `N s` to differ.
    rw [← hT, ← hFeq, ← hgeq, ← hEeq, ← hAeq] at hObs_s
    exact density_identifiability hg₁ hFcal₁ (emit s) (hA₁ (emit s)) hObs_s
  -- (3) Equal densities ⇒ equal closure composition.
  have hNfun : p₁.N = p₂.N := funext hNeq
  intro s
  simp only [trueComposition, hNfun]

/-- **Cross-method agreement bridge.** Any two sound estimators return equal
compositions on forward-model observations from an admissible parameter set. A short
`Sound + Sound` consequence: both equal `trueComposition p`. This is the abstract
bridge that makes the classical CF-LIBS and C-sigma method families comparable — the
reliability focus on cross-method agreement.

Non-vacuous: the premise `Sound …` is inhabited by `rawCompositionEstimator` when
`emit` is constant (`rawCompositionEstimator_sound` below), so this is not an
agreement between estimators whose soundness is never met. -/
theorem sound_estimators_agree [Fintype levelIndex]
    {kB Fcal : ℝ} {emit : species → levelIndex}
    {est₁ est₂ : CompositionEstimator species}
    (h₁ : Sound kB Fcal emit est₁) (h₂ : Sound kB Fcal emit est₂)
    {p : PlasmaParams species levelIndex} (ha : p.Admissible) :
    est₁ (observe kB Fcal emit p) = est₂ (observe kB Fcal emit p) := by
  rw [h₁ p ha, h₂ p ha]

/-- A **concrete composition estimator**: normalize the raw observation vector by its
own total, `est obs = composition obs`. This is the simplest genuine extraction method
(it forms number fractions directly from the measured line intensities) and is a real
function of the observations — not the answer baked in. -/
noncomputable def rawCompositionEstimator : CompositionEstimator species :=
  fun obs => composition obs

/-- **Soundness of the raw estimator (constant-`emit` case).** When every species emits
on the *same* atomic level `k₀` (`emit = fun _ => k₀`), the per-species forward
constant `c = Fcal · A k₀ · g k₀ · exp(−E k₀/(k_B T)) / U(T)` is identical across
species, so each observed intensity is `I_s = c · N_s`. Closure number fractions are
scale-invariant (`composition_smul_invariant`), hence normalizing the raw intensities
returns the true composition `N_s / ∑ N_t` exactly, for **every** admissible parameter
set. This inhabits the `Sound` premise of `sound_estimators_agree`, confirming the
agreement bridge is non-vacuous.

(With a *non-constant* `emit`, the per-species constants differ — through `A`, `g`, and
the temperature-dependent Boltzmann factor at distinct upper-level energies — and the
raw estimator is in general *not* sound; recovering composition then requires the
per-line de-normalization of `MultiSpecies.deNormalizedDensity` at a known `T`.) -/
theorem rawCompositionEstimator_sound [Fintype levelIndex] [Nonempty levelIndex]
    {kB Fcal : ℝ} (hFcal : 0 < Fcal) (k₀ : levelIndex) :
    Sound kB Fcal (fun _ => k₀) (rawCompositionEstimator (species := species)) := by
  intro p ha
  obtain ⟨hT, hN, hg, hA⟩ := ha
  -- The shared positive per-species constant `c`, independent of the species `s`.
  set c : ℝ :=
    Fcal * p.A k₀ * (p.g k₀ * boltzmannFactor kB p.T (p.E k₀) / partitionFunction kB p.T p.g p.E)
    with hcdef
  have hc : c ≠ 0 := by
    rw [hcdef]
    have hU : 0 < partitionFunction kB p.T p.g p.E := partitionFunction_pos hg
    exact (mul_pos (mul_pos hFcal (hA k₀))
      (div_pos (mul_pos (hg k₀) (boltzmannFactor_pos _ _ _)) hU)).ne'
  -- Each observed intensity is `c · N s`.
  have hobs : observe kB Fcal (fun _ => k₀) p = fun s => c * p.N s := by
    funext s
    simp only [observe, lineIntensity, population, hcdef]
    ring
  -- Normalize: scale-invariance of `composition` gives the true composition.
  funext s
  simp only [rawCompositionEstimator, trueComposition, hobs]
  exact composition_smul_invariant hc s

end CflibsFormal
