/-
Copyright (c) 2026 Brian Squires. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Squires
-/
import Mathlib
import CflibsFormal.Boltzmann
import CflibsFormal.ForwardMap
import CflibsFormal.Closure
import CflibsFormal.Saha
import CflibsFormal.Classic

/-!
# CF-LIBS formalization — the C-sigma (Cσ) single-line method (alternative estimator)

The **C-sigma graph** method of Aguilera & Aragón (2007) is an *alternative* CF-LIBS
composition estimator. Instead of one Boltzmann plot per species, it plots a
*normalized* ordinate for ALL lines of ALL species on a SINGLE master line.

For line `k` (upper level `k`) of a species with data `(N, g, E, A)`, define the
C-sigma ordinate
  `Y_{s,k} = log (I_{s,k} / (g_k A_k)) − q_s`,
where `I_{s,k} = lineIntensity …` (from `ForwardMap.lean`) and
`q_s = log (Fcal · N_s / U_s(T))` is the per-species, composition-bearing offset (the
intercept of the species-`s` intensity Boltzmann plot, `boltzmann_plot_intensity`).
After subtracting `q_s`, EVERY line of EVERY species collapses onto ONE straight master
line of slope `−1/(k_B T)`:
  `Y_{s,k} = −E_k / (k_B T)`,   independent of the species `s`.

We prove:

* `csigma_master_line` — the central physics claim: `Y_{s,k} = −E_k/(k_B T)`,
  independent of the species, by reduction to `boltzmann_plot_intensity`.
* `csigma_master_line_indep_species` — two genuinely different species sharing the
  upper-level energy of line `k` produce the same ordinate.
* `csigma_density_offset` — `csigmaDensity` is the exact left-inverse of `csigmaOffset`:
  reading `q_s` off the normalization back-determines the true density `N_s`.
* `csigmaOffset_of_lineIntensity` — the measurement step: the offset read off an OBSERVED
  line intensity (`csigmaOffsetOfIntensity`) recovers the true offset `q_s`.
* `csigma_sound` — soundness of the estimator: run on the genuine forward-model SPECTRUM
  (measured intensities, never `N`), the C-sigma composition returns the TRUE composition
  `C_s = N_s / ∑ N`.
* `sound_agree` / `csigma_agrees_of_sound` — abstract agreement-via-shared-soundness.
* `csigma_agrees_classic` — **the literal cross-method agreement**: fed the SAME measured
  intensities, `csigmaComposition` equals the classic per-species-Boltzmann-plot estimator
  `classicComposition` (from `Classic.lean`) — same observed spectrum, genuinely different
  procedures, coinciding because both are sound.

Two index types appear: `κ` (species/stages, from `Closure.lean`) and `ι` (energy
levels, from `Boltzmann.lean` / `ForwardMap.lean`). This is the ALTERNATIVE method
(namespace `CflibsFormal.Alt`); it reuses the core forward map verbatim.
-/

namespace CflibsFormal.Alt

open CflibsFormal
open Finset Real
open scoped BigOperators

variable {ι : Type*} [Fintype ι]
variable {κ : Type*} [Fintype κ]

/-- Per-species C-sigma offset `q_s = log (Fcal · N_s / U_s(T))`, the
composition-bearing intercept of the species-`s` intensity Boltzmann plot
(`boltzmann_plot_intensity` in `ForwardMap.lean`). It carries the species number
density `N_s` (relative to the partition function `U_s`); subtracting it from every
line ordinate collapses all species onto one master line. -/
noncomputable def csigmaOffset (kB T Fcal N : ℝ) (g E : ι → ℝ) : ℝ :=
  Real.log (Fcal * N / partitionFunction kB T g E)

/-- C-sigma master-line ordinate of line `k` (upper level `k`) of a species with
data `(N, g, E, A)`:
  `Y_{s,k} = log (I_{s,k} / (g_k A_k)) − q_s`,
where `I_{s,k} = lineIntensity …` (from `ForwardMap.lean`) and `q_s = csigmaOffset …`.
The defining feature of the Aguilera–Aragón C-sigma graph: after subtracting the
per-species offset `q_s`, the ordinate of EVERY line of EVERY species depends only on
the upper-level energy `E k` (see `csigma_master_line`). -/
noncomputable def csigmaOrdinate (kB T N Fcal : ℝ) (g E A : ι → ℝ) (k : ι) : ℝ :=
  Real.log (lineIntensity kB T N Fcal g E A k / (g k * A k))
    - csigmaOffset kB T Fcal N g E

/-- Recover the species number density from its C-sigma offset:
  `N_s = exp(q_s) · U_s(T) / Fcal`.
This is the exact inverse of `csigmaOffset` on positive data: reading `q_s` off the
master-line normalization back-determines `N_s` once `U_s` and the common `Fcal` are
known (`csigma_density_offset` certifies it inverts `csigmaOffset`). -/
noncomputable def csigmaDensity (kB T Fcal : ℝ) (g E : ι → ℝ) (q : ℝ) : ℝ :=
  Real.exp q * partitionFunction kB T g E / Fcal

/-- **C-sigma offset read off a measured line.** Given the recovered slope `−1/(k_B T)`,
the per-species offset is read from a single measured line `k = u` by requiring its point
to lie on the master line: from `Y_{s,u} = log(I/(g_u A_u)) − q_s = −E_u/(k_B T)`,
  `q_s = log (I / (g_u A_u)) + E_u / (k_B T)`.
This is the C-sigma measurement step — `q_s` is extracted from the OBSERVED intensity `I`,
not supplied analytically (`csigmaOffset_of_lineIntensity` shows it recovers the true
offset on forward-model data). -/
noncomputable def csigmaOffsetOfIntensity (kB T : ℝ) (g E A : ι → ℝ) (u : ι) (I : ℝ) : ℝ :=
  Real.log (I / (g u * A u)) + E u / (kB * T)

/-- **C-sigma composition estimator.** A pure function of the MEASURED line intensities
`I : κ → ℝ` (one chosen line `u s` per species), matching the input interface of the
classic estimator `Classic.classicComposition`. For each species it reads the offset
`q_s = csigmaOffsetOfIntensity …` off its measured line, recovers the density
`N_s = csigmaDensity … q_s`, and forms the closed composition `C_s = N_s / ∑_t N_t` via
`composition` from `Closure.lean`. This is the ALTERNATIVE (single-line / C-sigma)
estimator: it consumes the SAME observed spectrum as the classic method but via the
single-master-line normalization, and is proven sound and proven to agree with the
classic per-species-Boltzmann-plot estimator below. -/
noncomputable def csigmaComposition (kB T Fcal : ℝ) (g E A : κ → ι → ℝ)
    (u : κ → ι) (I : κ → ℝ) (s : κ) : ℝ :=
  composition (fun t => csigmaDensity kB T Fcal (g t) (E t)
    (csigmaOffsetOfIntensity kB T (g t) (E t) (A t) (u t) (I t))) s

/-- **C-sigma master line.** After subtracting the species offset `q_s`, the ordinate
of every line of every species lies on ONE master line `Y = −E_k/(k_B T)` of slope
`−1/(k_B T)`, independent of the species. Reduces to `boltzmann_plot_intensity`. -/
theorem csigma_master_line [Nonempty ι] {kB T N Fcal : ℝ} {g E A : ι → ℝ}
    (hg : ∀ k, 0 < g k) (hN : 0 < N) (hFcal : 0 < Fcal) (hA : ∀ k, 0 < A k) (k : ι) :
    csigmaOrdinate kB T N Fcal g E A k = - E k / (kB * T) := by
  unfold csigmaOrdinate csigmaOffset
  rw [boltzmann_plot_intensity hg hN hFcal hA k]
  ring

/-- **Species independence, made explicit.** Two DIFFERENT species (different `N, g, E,
A`) whose line `k` shares the same upper-level energy yield the SAME C-sigma ordinate.
This is what "all points collapse onto one line" means operationally. -/
theorem csigma_master_line_indep_species [Nonempty ι]
    {kB T : ℝ} {N₁ N₂ Fcal : ℝ} {g₁ E₁ A₁ g₂ E₂ A₂ : ι → ℝ}
    (hg₁ : ∀ k, 0 < g₁ k) (hN₁ : 0 < N₁) (hg₂ : ∀ k, 0 < g₂ k) (hN₂ : 0 < N₂)
    (hFcal : 0 < Fcal) (hA₁ : ∀ k, 0 < A₁ k) (hA₂ : ∀ k, 0 < A₂ k)
    (k : ι) (hEk : E₁ k = E₂ k) :
    csigmaOrdinate kB T N₁ Fcal g₁ E₁ A₁ k = csigmaOrdinate kB T N₂ Fcal g₂ E₂ A₂ k := by
  rw [csigma_master_line hg₁ hN₁ hFcal hA₁ k, csigma_master_line hg₂ hN₂ hFcal hA₂ k,
    hEk]

/-- **Inverse identity.** `csigmaDensity` is the exact left-inverse of `csigmaOffset`:
reading `q_s` off the normalization and applying `csigmaDensity` returns the true
species density `N_s`. This is the engine of soundness. -/
theorem csigma_density_offset [Nonempty ι] {kB T Fcal N : ℝ} {g E : ι → ℝ}
    (hg : ∀ k, 0 < g k) (hN : 0 < N) (hFcal : 0 < Fcal) :
    csigmaDensity kB T Fcal g E (csigmaOffset kB T Fcal N g E) = N := by
  have hU : 0 < partitionFunction kB T g E := partitionFunction_pos hg
  unfold csigmaDensity csigmaOffset
  rw [Real.exp_log (by positivity)]
  field_simp

/-- **The measurement step recovers the true offset.** Feeding a genuine forward-model
line intensity into the C-sigma offset reader `csigmaOffsetOfIntensity` returns exactly the
analytic offset `q_s = csigmaOffset … = log(Fcal·N_s/U_s)`. This is the non-tautological
link between the OBSERVED spectrum and the composition-bearing offset: it reduces to the
intensity Boltzmann-plot intercept, the `E_u/(k_B T)` terms cancelling. Only positivity at
the single measured line `u` is needed. -/
theorem csigmaOffset_of_lineIntensity [Nonempty ι] {kB T N Fcal : ℝ} {g E A : ι → ℝ}
    (hg : ∀ k, 0 < g k) (hN : 0 < N) (hFcal : 0 < Fcal) (u : ι) (hA : 0 < A u) :
    csigmaOffsetOfIntensity kB T g E A u (lineIntensity kB T N Fcal g E A u)
      = csigmaOffset kB T Fcal N g E := by
  have hU : 0 < partitionFunction kB T g E := partitionFunction_pos hg
  have hgu : g u ≠ 0 := (hg u).ne'
  have hAu : A u ≠ 0 := hA.ne'
  unfold csigmaOffsetOfIntensity csigmaOffset
  have hsplit : lineIntensity kB T N Fcal g E A u / (g u * A u)
      = (Fcal * N / partitionFunction kB T g E) * Real.exp (-E u / (kB * T)) := by
    simp only [lineIntensity, population, boltzmannFactor]
    field_simp
  rw [hsplit, Real.log_mul (div_pos (by positivity) hU).ne' (Real.exp_ne_zero _),
    Real.log_exp]
  ring

/-- **Soundness of the C-sigma estimator.** On the genuine forward-model spectrum
(`I_t = lineIntensity …` at the true densities `N_t`), `csigmaComposition` returns the TRUE
composition `C_s = N_s / ∑ N`. The measurement step recovers each offset
(`csigmaOffset_of_lineIntensity`) and `csigmaDensity` inverts it
(`csigma_density_offset`), so the recovered density vector equals `N` pointwise. The
estimator never sees `N` — only the intensities. -/
theorem csigma_sound [Nonempty ι] [Nonempty κ] {kB T Fcal : ℝ}
    {N : κ → ℝ} {g E A : κ → ι → ℝ} {u : κ → ι}
    (hg : ∀ s k, 0 < g s k) (hN : ∀ s, 0 < N s) (hFcal : 0 < Fcal)
    (hA : ∀ s, 0 < A s (u s)) (s : κ) :
    csigmaComposition kB T Fcal g E A u
        (fun t => lineIntensity kB T (N t) Fcal (g t) (E t) (A t) (u t)) s
      = composition N s := by
  unfold csigmaComposition
  congr 1
  funext t
  rw [csigmaOffset_of_lineIntensity (hg t) (hN t) hFcal (u t) (hA t)]
  exact csigma_density_offset (hg t) (hN t) hFcal

omit [Fintype κ] in
/-- **Abstract agreement bridge.** Any two functions that both equal a common
reference `d` agree with each other. Hoists the trivial transitivity used in
`csigma_agrees_of_sound`; intended to migrate to `Inverse.lean`. -/
theorem sound_agree {f c d : κ → ℝ} (hf : ∀ s, f s = d s) (hg : ∀ s, c s = d s)
    (s : κ) : f s = c s := by
  rw [hf s, hg s]

/-- **Agreement via shared soundness (abstract classic estimator).** Given any
estimator `classicEst` that is sound (`hclassic : ∀ s, classicEst s = composition N s`),
the C-sigma estimator — run on the genuine forward-model spectrum — agrees with it. This
routes agreement through both sides equalling the true composition `composition N`; the
*literal* identity against `CflibsFormal.Classic.classicComposition` on the same observed
spectrum is `csigma_agrees_classic` below. -/
theorem csigma_agrees_of_sound [Nonempty ι] [Nonempty κ] {kB T Fcal : ℝ}
    {N : κ → ℝ} {g E A : κ → ι → ℝ} {u : κ → ι}
    (hg : ∀ s k, 0 < g s k) (hN : ∀ s, 0 < N s) (hFcal : 0 < Fcal)
    (hA : ∀ s, 0 < A s (u s))
    {classicEst : κ → ℝ}
    (hclassic : ∀ s, classicEst s = composition N s) (s : κ) :
    csigmaComposition kB T Fcal g E A u
        (fun t => lineIntensity kB T (N t) Fcal (g t) (E t) (A t) (u t)) s
      = classicEst s :=
  sound_agree (fun s => csigma_sound hg hN hFcal hA s) hclassic s

/-- **CROSS-METHOD AGREEMENT (literal, same observed spectrum).** Fed the SAME measured
line intensities `I_t = lineIntensity …`, the C-sigma single-line estimator
`csigmaComposition` and the classic per-species-Boltzmann-plot estimator
`CflibsFormal.Classic.classicComposition` return the SAME composition. The two consume
identical observations but run genuinely different procedures — C-sigma reads each offset
off the single master-line normalization (`csigmaOffsetOfIntensity`) and inverts it
(`csigmaDensity`), while `classicComposition` inverts each species' line directly
(`classicDensity`) — yet they coincide because BOTH are sound on that spectrum
(`csigma_sound` and `CflibsFormal.Classic.classic_sound` both land on `composition N`).
This is the rigorous statement that the alternative method agrees with the classic one on
real data, not by construction. -/
theorem csigma_agrees_classic [Nonempty ι] [Nonempty κ] {kB T Fcal : ℝ}
    {N : κ → ℝ} {g E A : κ → ι → ℝ} {u : κ → ι}
    (hg : ∀ s k, 0 < g s k) (hN : ∀ s, 0 < N s) (hFcal : 0 < Fcal)
    (hA : ∀ s, 0 < A s (u s)) (hNtot : 0 < totalDensity N) (s : κ) :
    csigmaComposition kB T Fcal g E A u
        (fun t => lineIntensity kB T (N t) Fcal (g t) (E t) (A t) (u t)) s
      = Classic.classicComposition kB T Fcal g E A u
          (fun t => lineIntensity kB T (N t) Fcal (g t) (E t) (A t) (u t)) s :=
  sound_agree (fun s => csigma_sound hg hN hFcal hA s)
    (fun s => Classic.classic_sound hg hFcal hA hNtot s) s

end CflibsFormal.Alt

