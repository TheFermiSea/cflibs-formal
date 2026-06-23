/-
Copyright (c) 2026 Brian Squires. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Squires
-/
import Mathlib
import CflibsFormal.Closure
import CflibsFormal.ForwardMap
import CflibsFormal.Boltzmann

/-!
# CF-LIBS formalization — Multi-species / multi-stage composition glue

Model a sample with a finite index set `ι` of chemical **elements/species**; element
`s` has number density `N s`. The elemental composition is the number-fraction vector
`C s = N s / (∑_t N t)`, obtained by reusing `CflibsFormal.composition` /
`CflibsFormal.totalDensity` from `Closure.lean` (which is generic in its index `κ`),
instantiated at the species index `ι`.

We prove:

* `speciesComposition_sum_one` / `speciesComposition_mem_stdSimplex` — the
  multi-species closure `∑_s C s = 1` and probability-simplex membership, by **direct
  reuse** of `composition_sum_one` / `composition_mem_stdSimplex`.
* `deNormalized_lineIntensity` — the per-species **inversion identity**: de-normalizing
  the forward `lineIntensity` of species `s` (dividing out the calibration `Fcal`, the
  Einstein coefficient `A s`, degeneracy `g s`, the upper-level Boltzmann factor, and
  multiplying by the partition function `U`) recovers the species number density `N`
  exactly.
* `density_ratio_from_intensities` — the density-from-intensity **bridge**: at a common
  temperature `T` and calibration `Fcal`, with one designated emitting level per species,
  the ratio of two species' de-normalized line intensities equals the ratio `N_s / N_t`
  of their number densities. Hence relative composition is fixed by the measured
  intensities and atomic data at known `T`.

**Single-family scope.** `deNormalizedDensity` shares one `(g, E, A)` family and one
partition-function value across species, because it composes exactly with
`ForwardMap.lineIntensity`, which takes a single `(g, E, A : ι → ℝ)`. This models
"one designated emitting level per species drawn from a common atomic-data family
indexed by species". A genuine multi-element form with per-species partition functions
`U_s` and per-species atomic data is deferred to a follow-up module.
-/

namespace CflibsFormal

open Finset Real
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- Elemental/species composition vector: the number fraction of species `s`,
`C s = N s / (∑_t N t)`. This is `CflibsFormal.composition` from `Closure.lean`
instantiated at the species index type `ι` (Closure is generic in its index `κ`).
Kept as a named alias so the multi-species API reads in species language while all
closure proofs are inherited verbatim. `totalDensity N = ∑ t, N t` is reused directly
from Closure. -/
noncomputable def speciesComposition (N : ι → ℝ) (s : ι) : ℝ :=
  composition N s

/-- Number density of species `s` recovered from its measured designated-line
intensity `I` by dividing out the calibration `Fcal`, Einstein coefficient `A s`,
degeneracy `g s`, Boltzmann factor at the upper-level energy `E s`, and the species
partition function `U_s`. Concretely
`N_s = I · U_s / (Fcal · A s · g s · exp(-E s/(k_B T)))`.
By construction, applying this to the forward `lineIntensity` returns `N` exactly
(`deNormalized_lineIntensity`), so the species-density ratio is fixed by the two
measured intensities at known `T` and atomic data. Here `U_s = partitionFunction kB T g E`
reuses `Boltzmann.partitionFunction`. **Single-family scope:** all species share one
`(g, E, A)` atomic-data family and one partition-function value; per-species partition
functions are deferred (see module docstring).

**Same inverse as `Classic.classicDensity`.** This is definitionally the identical
density-from-intensity inverse used by the classic estimator (`Classic.classicDensity`);
the argument order `(s : ι) (I : ℝ)` here is deliberately the SAME as `classicDensity`'s
`(u : ι) (I : ℝ)`. They are kept as separate named aliases only because the two modules do
not import each other; `MultiSpecies` uses it in species language. -/
noncomputable def deNormalizedDensity (kB T Fcal : ℝ) (g E A : ι → ℝ) (s : ι) (I : ℝ) : ℝ :=
  I * partitionFunction kB T g E / (Fcal * A s * g s * boltzmannFactor kB T (E s))

/-- **Multi-species closure.** The number fractions sum to one: `∑_s C s = 1`, the
CF-LIBS mass/number-fraction normalization, stated in species language and obtained by
direct reuse of `composition_sum_one`. -/
theorem speciesComposition_sum_one {N : ι → ℝ}
    (hN : 0 < totalDensity N) : ∑ s, speciesComposition N s = 1 := by
  unfold speciesComposition
  exact composition_sum_one hN

/-- **Multi-species closure as simplex membership.** The composition vector is
nonnegative and sums to one, i.e. it lies on the standard probability simplex — the
faithful probability-simplex form of the CF-LIBS closure constraint. Direct reuse of
`composition_mem_stdSimplex`. -/
theorem speciesComposition_mem_stdSimplex {N : ι → ℝ} (hn : ∀ s, 0 ≤ N s)
    (hN : 0 < totalDensity N) : speciesComposition N ∈ stdSimplex ℝ ι := by
  unfold speciesComposition
  exact composition_mem_stdSimplex hn hN

/-- **Inversion identity.** De-normalizing the forward line intensity of species `s`
(divide out `Fcal`, `A s`, `g s`, the Boltzmann factor, multiply by `U`) recovers the
species number density `N` exactly. This is the per-species half of the
density-from-intensity bridge and the lemma the ratio theorem rests on. -/
theorem deNormalized_lineIntensity [Nonempty ι] {kB T N Fcal : ℝ} {g E A : ι → ℝ}
    (hg : ∀ k, 0 < g k) (hN : 0 < N) (hFcal : 0 < Fcal) (hA : ∀ k, 0 < A k) (s : ι) :
    deNormalizedDensity kB T Fcal g E A s (lineIntensity kB T N Fcal g E A s) = N := by
  have hU : partitionFunction kB T g E ≠ 0 := (partitionFunction_pos hg).ne'
  have hgs := (hg s).ne'
  have hAs := (hA s).ne'
  have hbf := (boltzmannFactor_pos kB T (E s)).ne'
  unfold deNormalizedDensity lineIntensity population
  field_simp

/-- **Density-from-intensity bridge.** At a common temperature `T` and common
calibration `Fcal`, with one designated emitting level per species, the ratio of two
species' partition-function-and-degeneracy-de-normalized line intensities equals the
ratio `N_s / N_t` of their number densities. Hence relative composition is fixed by the
measured intensities and atomic data at known `T`. The two intensities carry different
densities `Ns`, `Nt` but share `kB, T, Fcal, g, E, A` — two species emitting under the
same plasma conditions and (single-family) atomic data. -/
theorem density_ratio_from_intensities [Nonempty ι] {kB T Ns Nt Fcal : ℝ} {g E A : ι → ℝ}
    (hg : ∀ k, 0 < g k) (hNs : 0 < Ns) (hNt : 0 < Nt) (hFcal : 0 < Fcal) (hA : ∀ k, 0 < A k)
    (s t : ι) :
    deNormalizedDensity kB T Fcal g E A s (lineIntensity kB T Ns Fcal g E A s)
        / deNormalizedDensity kB T Fcal g E A t (lineIntensity kB T Nt Fcal g E A t)
      = Ns / Nt := by
  rw [deNormalized_lineIntensity hg hNs hFcal hA s,
    deNormalized_lineIntensity hg hNt hFcal hA t]

end CflibsFormal
