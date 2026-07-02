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
indexed by species".

**Per-species generalization (gap #7).** The genuine multi-element form with a per-species
partition function `U_s(T)` — a free positive scalar, summed over species `s`'s *own*
internal levels — is provided below via `deNormalizedDensityPerU` / `lineIntensityPerU` and
the theorems `deNormalized_lineIntensity_perU`, `density_ratio_from_intensities_perU`, and
`speciesComposition_ratio_from_intensities_perU`. The single-family `deNormalizedDensity` /
`lineIntensity` are the special case `U_s := partitionFunction kB T g E` (bridged by the
`rfl`-lemmas `deNormalizedDensity_eq_deNormalizedDensityPerU` /
`lineIntensity_eq_lineIntensityPerU`), so the shared-`U` inversion and ratio theorems are
re-derived as specializations (`deNormalized_lineIntensity_ofPerU` /
`density_ratio_from_intensities_ofPerU`). This discharges the shared-`U` reduction flagged
in `docs/SOLVER_FORMALIZATION_GAPS.md` gap #7.
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

/-! ### Per-species partition functions (gap #7)

The declarations below replace the single shared partition-function value of
`deNormalizedDensity` / `lineIntensity` by a **per-species** partition function `U_s`,
carried as an explicit positive scalar. Physically `U_s = U_s(T)` is the internal partition
function of species `s`, summed over *its own* level manifold; here it is decoupled from the
designated-line degeneracies/energies `(g s, E s)` used in the emission factor, which is the
genuine multi-element structure of CF-LIBS. The shared-`U` API is recovered by substituting
`U_s := partitionFunction kB T g E` (the `rfl`-bridges below), making every shared-`U`
statement a special case of the per-species one rather than an independent claim. -/

/-- **Per-species de-normalized density reader.** Number density of species `s` recovered
from its designated-line intensity `I` using species `s`'s *own* partition function `Us`
(an explicit positive scalar):
`N_s = I · U_s / (Fcal · A s · g s · exp(-E s/(k_B T)))`.
Genuine multi-element generalization of `deNormalizedDensity`: `Us` no longer has to be the
shared `partitionFunction kB T g E`; each species carries its own `U_s(T)` while the emitting
line contributes its own `(g s, E s, A s)`. Setting `Us := partitionFunction kB T g E` gives
back `deNormalizedDensity` definitionally (`deNormalizedDensity_eq_deNormalizedDensityPerU`).
Discharges the shared-`U` reduction of `docs/SOLVER_FORMALIZATION_GAPS.md` gap #7.
**Scope EXACT** for the CF-LIBS internal-standard (one designated line per species) reader:
the per-species inverse is written exactly, with `U_s` an unconstrained physical input. -/
noncomputable def deNormalizedDensityPerU (kB T Fcal Us : ℝ) (g E A : ι → ℝ)
    (s : ι) (I : ℝ) : ℝ :=
  I * Us / (Fcal * A s * g s * boltzmannFactor kB T (E s))

/-- **Per-species forward line-emission model.** Integrated optically-thin intensity of
species `s`'s designated line with species `s`'s *own* partition function `Us`:
`I = Fcal · A s · N · g s · exp(-E s/(k_B T)) / U_s`.
This is `ForwardMap.lineIntensity` with the shared partition function replaced by a
per-species scalar; `lineIntensity_eq_lineIntensityPerU` records that the shared-family
forward map is the special case `Us := partitionFunction kB T g E`. **Scope EXACT** (single
designated line per species; `U_s` a free positive input). -/
noncomputable def lineIntensityPerU (kB T N Fcal Us : ℝ) (g E A : ι → ℝ) (s : ι) : ℝ :=
  Fcal * A s * (N * g s * boltzmannFactor kB T (E s) / Us)

/-- **Shared-`U` reader is the per-`U` reader at `Us = partitionFunction kB T g E`.**
Definitional bridge (`rfl`) making `deNormalizedDensity` a special case of
`deNormalizedDensityPerU`. -/
theorem deNormalizedDensity_eq_deNormalizedDensityPerU
    (kB T Fcal : ℝ) (g E A : ι → ℝ) (s : ι) (I : ℝ) :
    deNormalizedDensity kB T Fcal g E A s I
      = deNormalizedDensityPerU kB T Fcal (partitionFunction kB T g E) g E A s I := rfl

/-- **Shared-`U` forward map is the per-`U` forward map at `Us = partitionFunction kB T g E`.**
Definitional bridge (`rfl`) making `lineIntensity` a special case of `lineIntensityPerU`. -/
theorem lineIntensity_eq_lineIntensityPerU
    (kB T N Fcal : ℝ) (g E A : ι → ℝ) (s : ι) :
    lineIntensity kB T N Fcal g E A s
      = lineIntensityPerU kB T N Fcal (partitionFunction kB T g E) g E A s := rfl

omit [Fintype ι] in
/-- **Per-species inversion identity.** De-normalizing species `s`'s per-`U` forward line
intensity recovers its number density `N` exactly, using the species' own partition function
`Us`. Genuine multi-element generalization of `deNormalized_lineIntensity`; note the proof
needs only `0 < Us` (a per-species positivity), and — unlike the shared-`U` version — no
`Nonempty ι` and no `0 < N`. -/
theorem deNormalized_lineIntensity_perU {kB T N Fcal Us : ℝ} {g E A : ι → ℝ}
    (hg : ∀ k, 0 < g k) (hFcal : 0 < Fcal) (hA : ∀ k, 0 < A k) (hUs : 0 < Us) (s : ι) :
    deNormalizedDensityPerU kB T Fcal Us g E A s (lineIntensityPerU kB T N Fcal Us g E A s)
      = N := by
  have hgs := (hg s).ne'
  have hAs := (hA s).ne'
  have hFcal' := hFcal.ne'
  have hUs' := hUs.ne'
  have hbf := (boltzmannFactor_pos kB T (E s)).ne'
  unfold deNormalizedDensityPerU lineIntensityPerU
  field_simp

/-- **Shared-`U` inversion identity as a special case of the per-`U` one.** Re-derives the
`deNormalized_lineIntensity` statement by specializing `deNormalized_lineIntensity_perU` to
`Us = partitionFunction kB T g E` via the `rfl`-bridges — witnessing that the shared-`U`
inversion is not an independent claim. (The original `deNormalized_lineIntensity` above is
retained verbatim for downstream importers.) -/
theorem deNormalized_lineIntensity_ofPerU [Nonempty ι] {kB T N Fcal : ℝ} {g E A : ι → ℝ}
    (hg : ∀ k, 0 < g k) (hFcal : 0 < Fcal) (hA : ∀ k, 0 < A k) (s : ι) :
    deNormalizedDensity kB T Fcal g E A s (lineIntensity kB T N Fcal g E A s) = N := by
  simp only [deNormalizedDensity_eq_deNormalizedDensityPerU, lineIntensity_eq_lineIntensityPerU]
  exact deNormalized_lineIntensity_perU hg hFcal hA (partitionFunction_pos hg) s

omit [Fintype ι] in
/-- **Per-species density-from-intensity bridge.** With *genuinely per-species* partition
functions `Us, Ut` (each summed over its own species' level manifold) and per-species
designated-line data `(g s, E s, A s)` / `(g t, E t, A t)`, at a common temperature `T` and
calibration `Fcal`, the ratio of the two species' `U`-de-normalized line intensities equals
the true density ratio `N_s / N_t`. Hence relative composition is fixed by the measured
intensities and per-species atomic data at known `T`, with no shared-`U` assumption. The
shared-`U` `density_ratio_from_intensities` is the special case `Us = Ut =
partitionFunction kB T g E` (`density_ratio_from_intensities_ofPerU`). -/
theorem density_ratio_from_intensities_perU
    {kB T Ns Nt Fcal Us Ut : ℝ} {g E A : ι → ℝ}
    (hg : ∀ k, 0 < g k) (hFcal : 0 < Fcal) (hA : ∀ k, 0 < A k)
    (hUs : 0 < Us) (hUt : 0 < Ut) (s t : ι) :
    deNormalizedDensityPerU kB T Fcal Us g E A s (lineIntensityPerU kB T Ns Fcal Us g E A s)
        / deNormalizedDensityPerU kB T Fcal Ut g E A t (lineIntensityPerU kB T Nt Fcal Ut g E A t)
      = Ns / Nt := by
  rw [deNormalized_lineIntensity_perU hg hFcal hA hUs s,
    deNormalized_lineIntensity_perU hg hFcal hA hUt t]

/-- **Shared-`U` ratio theorem as a special case of the per-`U` one.** Re-derives
`density_ratio_from_intensities` by specializing `density_ratio_from_intensities_perU` to
`Us = Ut = partitionFunction kB T g E`. Notably it needs neither `0 < Ns` nor `0 < Nt`,
which the per-`U` inversion made unnecessary. -/
theorem density_ratio_from_intensities_ofPerU [Nonempty ι] {kB T Ns Nt Fcal : ℝ}
    {g E A : ι → ℝ}
    (hg : ∀ k, 0 < g k) (hFcal : 0 < Fcal) (hA : ∀ k, 0 < A k) (s t : ι) :
    deNormalizedDensity kB T Fcal g E A s (lineIntensity kB T Ns Fcal g E A s)
        / deNormalizedDensity kB T Fcal g E A t (lineIntensity kB T Nt Fcal g E A t)
      = Ns / Nt := by
  simp only [deNormalizedDensity_eq_deNormalizedDensityPerU, lineIntensity_eq_lineIntensityPerU]
  exact density_ratio_from_intensities_perU hg hFcal hA
    (partitionFunction_pos hg) (partitionFunction_pos hg) s t

/-- **Composition ratio equals density ratio.** `C s / C t = N s / N t` for the multi-species
number-fraction vector, since the shared total density cancels. The closure-side companion of
the intensity bridge. -/
theorem speciesComposition_ratio {N : ι → ℝ} (hD : totalDensity N ≠ 0) (s t : ι) :
    speciesComposition N s / speciesComposition N t = N s / N t := by
  unfold speciesComposition composition
  exact div_div_div_cancel_right₀ hD (N s) (N t)

/-- **Relative composition from intensities (per-species `U`).** The elemental
number-fraction ratio `C_s / C_t` of two species equals the ratio of their per-`U`
de-normalized designated-line intensities — relative composition is fixed by the measured
intensities and per-species atomic data at known `T`, with genuinely per-species partition
functions `Us, Ut`. Combines `density_ratio_from_intensities_perU` with
`speciesComposition_ratio`. -/
theorem speciesComposition_ratio_from_intensities_perU
    {kB T Fcal Us Ut : ℝ} {g E A : ι → ℝ} {N : ι → ℝ}
    (hg : ∀ k, 0 < g k) (hFcal : 0 < Fcal) (hA : ∀ k, 0 < A k)
    (hUs : 0 < Us) (hUt : 0 < Ut) (hD : totalDensity N ≠ 0) (s t : ι) :
    deNormalizedDensityPerU kB T Fcal Us g E A s (lineIntensityPerU kB T (N s) Fcal Us g E A s)
        / deNormalizedDensityPerU kB T Fcal Ut g E A t
            (lineIntensityPerU kB T (N t) Fcal Ut g E A t)
      = speciesComposition N s / speciesComposition N t := by
  rw [density_ratio_from_intensities_perU hg hFcal hA hUs hUt s t,
    speciesComposition_ratio hD s t]

/-! ### Non-vacuity witnesses (per-species `U`) -/

/-- Emitting-level degeneracies of two species: genuinely different, `g 0 = 2 ≠ 5 = g 1`. -/
private def nvPuG : Fin 2 → ℝ := ![2, 5]

/-- Upper-level energies of the two designated lines (arbitrary, distinct). -/
private def nvPuE : Fin 2 → ℝ := ![1, 2]

/-- Einstein coefficients of the two designated lines (positive). -/
private def nvPuA : Fin 2 → ℝ := ![1, 1]

/-- **Non-vacuity of `density_ratio_from_intensities_perU`.** Two species with genuinely
DIFFERENT emitting-level degeneracies (`g 0 = 2 ≠ 5 = g 1`) and genuinely DIFFERENT
per-species partition functions (`U_0 = 3 ≠ 7 = U_1`) recover a non-trivial density ratio
`N_0 / N_1 = 2 / 3` from their per-`U` de-normalized designated-line intensities. This is a
regime the shared-`U` theorem cannot express, since it forces `U_0 = U_1`. -/
example :
    deNormalizedDensityPerU (1 : ℝ) 1 1 3 nvPuG nvPuE nvPuA 0
        (lineIntensityPerU (1 : ℝ) 1 2 1 3 nvPuG nvPuE nvPuA 0)
      / deNormalizedDensityPerU (1 : ℝ) 1 1 7 nvPuG nvPuE nvPuA 1
          (lineIntensityPerU (1 : ℝ) 1 3 1 7 nvPuG nvPuE nvPuA 1)
      = 2 / 3 := by
  have hg : ∀ k : Fin 2, 0 < nvPuG k := fun k => by fin_cases k <;> norm_num [nvPuG]
  have hA : ∀ k : Fin 2, 0 < nvPuA k := fun k => by fin_cases k <;> norm_num [nvPuA]
  exact density_ratio_from_intensities_perU hg (by norm_num) hA (by norm_num) (by norm_num) 0 1

end CflibsFormal
