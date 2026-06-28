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
import CflibsFormal.Alt.LeastSquares

/-!
# CF-LIBS formalization — the C-sigma (Cσ) single-line method (alternative estimator)

This module formalizes the **multi-element single-master-line normalization plot**: an
*alternative* CF-LIBS composition estimator that, instead of one Boltzmann plot per
species, plots a *normalized* ordinate for ALL lines of ALL species on a SINGLE master
line. This is the multi-element **Boltzmann** master-line construction of Aguilera &
Aragón, "Multi-element Saha–Boltzmann and Boltzmann plots in laser-induced plasmas,"
*Spectrochimica Acta Part B* **62** (2007) 378.

**Two sections.** The FIRST section formalizes the single-stage multi-element **Boltzmann** master
plot (Aguilera & Aragón, *Spectrochim. Acta B* **62** (2007) 378): after subtracting the per-species
offset, all lines of all species collapse onto `Y = −E/(k_B T)` using only `E/(k_B T)`. The SECOND
section adds the defining feature of the **Saha–Boltzmann / Cσ graph** (Aragón & Aguilera,
*J. Quant. Spectrosc. Radiat. Transfer* **149** (2014) 90): the **Saha-coupled cross-stage
collapse**, where
*ionic* (stage `Z+1`) lines also fall on the SAME master line via a Saha ionization-energy abscissa
shift `+χ` and a Saha-bracket ordinate correction (`csigma_saha_master_line`,
`csigma_cross_stage_collapse`) — this genuinely uses `Saha.lean` (`sahaFactor`, `log_sahaFactor`),
and its exact construction was verified against the CF-LIBS literature. The remaining piece of the
full Cσ graph — the σ (cross-section) / concentration normalization that collapses *all elements*
onto ONE universal line of intercept `ln F` — is the multi-element extension (a natural follow-on).

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
* `csigmaDensity_offset_eq_classicDensity` / `csigmaComposition_eq_classicComposition` —
  **the honest content**: the C-sigma offset-inversion is the SAME algebraic left-inverse as
  `Classic.classicDensity`, so `csigmaComposition = classicComposition` as functions of ALL
  positive intensities — an unconditional identity, the two methods are the same inverse in
  `log/exp` vs direct-division packaging.
* `csigma_agrees_classic` — the forward-data instance of that identity (same measured
  spectrum ⇒ same composition); structural, NOT two independent procedures that happen to
  coincide.

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
`csigma_agrees_of_sound`. -/
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

/-- **The C-sigma and classic density inverses are the SAME function (pointwise).** On any
positive measured intensity `I`, reading the offset off the master line and inverting it
(`csigmaDensity ∘ csigmaOffsetOfIntensity`) returns exactly `Classic.classicDensity I`. The
two are the identical algebraic left-inverse of the forward line emission, written two ways:
the C-sigma form `exp(log(I/(g·A)) + E/(kT))·U/Fcal` and the classic form
`I·U/(Fcal·A·g·exp(-E/(kT)))`. The `log`/`exp` cancels (`Real.exp_log`, needs `I>0`), the
Boltzmann factor inverts (`exp(-E/kT) = (exp(E/kT))⁻¹`), and the two collapse to the same
expression. This is the honest content behind the "agreement": it is structural, holding for
ALL positive intensities, not a coincidence on forward-model data. -/
theorem csigmaDensity_offset_eq_classicDensity {kB T Fcal : ℝ} {g E A : ι → ℝ} {u : ι} {I : ℝ}
    (hg : 0 < g u) (hA : 0 < A u) (hI : 0 < I) (hFcal : 0 < Fcal) :
    csigmaDensity kB T Fcal g E (csigmaOffsetOfIntensity kB T g E A u I)
      = Classic.classicDensity kB T Fcal g E A u I := by
  have hpos : 0 < I / (g u * A u) := div_pos hI (mul_pos hg hA)
  have hbf : boltzmannFactor kB T (E u) = (Real.exp (E u / (kB * T)))⁻¹ := by
    unfold boltzmannFactor; rw [← Real.exp_neg]; congr 1; ring
  have hgu := hg.ne'
  have hAu := hA.ne'
  have hFne := hFcal.ne'
  have hexp := (Real.exp_pos (E u / (kB * T))).ne'
  unfold csigmaDensity csigmaOffsetOfIntensity Classic.classicDensity
  rw [hbf, Real.exp_add, Real.exp_log hpos]
  field_simp

/-- **The two estimators are the SAME function of the observations.** For any positive
intensity vector `I`, `csigmaComposition I = Classic.classicComposition I` pointwise — an
UNCONDITIONAL identity (no forward-model / soundness assumption), because the per-species
density inverses coincide (`csigmaDensity_offset_eq_classicDensity`). So the C-sigma
single-master-line estimator and the classic per-species estimator are the same algebraic
left-inverse in two packagings; their "agreement" is structural, not a coincidence. -/
theorem csigmaComposition_eq_classicComposition {kB T Fcal : ℝ}
    {g E A : κ → ι → ℝ} {u : κ → ι} {I : κ → ℝ}
    (hg : ∀ t, 0 < g t (u t)) (hA : ∀ t, 0 < A t (u t)) (hI : ∀ t, 0 < I t)
    (hFcal : 0 < Fcal) (s : κ) :
    csigmaComposition kB T Fcal g E A u I s
      = Classic.classicComposition kB T Fcal g E A u I s := by
  unfold csigmaComposition Classic.classicComposition
  congr 1
  funext t
  exact csigmaDensity_offset_eq_classicDensity (hg t) (hA t) (hI t) hFcal

/-- **Cross-method agreement on a measured spectrum (forward-data instance).** Fed the SAME
measured line intensities `I_t = lineIntensity …`, `csigmaComposition` and
`Classic.classicComposition` return the SAME composition. Honest framing: this is NOT two
independent procedures coinciding "because both are sound" — by
`csigmaComposition_eq_classicComposition` they are the IDENTICAL function on all positive
intensities (the C-sigma offset-inversion is the classic density inverse in `log/exp`
packaging). This theorem is just that unconditional identity applied to the (positive)
forward spectrum. The genuine same-spectrum agreement between *structurally different*
estimators is the OLS-vs-classic one (`Alt.leastSquares_agrees_classic`), where the two
differ off the noise-free fixpoint. -/
theorem csigma_agrees_classic [Nonempty ι] [Nonempty κ] {kB T Fcal : ℝ}
    {N : κ → ℝ} {g E A : κ → ι → ℝ} {u : κ → ι}
    (hg : ∀ s k, 0 < g s k) (hN : ∀ s, 0 < N s) (hFcal : 0 < Fcal)
    (hA : ∀ s, 0 < A s (u s)) (s : κ) :
    csigmaComposition kB T Fcal g E A u
        (fun t => lineIntensity kB T (N t) Fcal (g t) (E t) (A t) (u t)) s
      = Classic.classicComposition kB T Fcal g E A u
          (fun t => lineIntensity kB T (N t) Fcal (g t) (E t) (A t) (u t)) s := by
  refine csigmaComposition_eq_classicComposition (fun t => hg t (u t)) hA (fun t => ?_) hFcal s
  show 0 < lineIntensity kB T (N t) Fcal (g t) (E t) (A t) (u t)
  unfold lineIntensity population
  exact mul_pos (mul_pos hFcal (hA t))
    (div_pos (mul_pos (mul_pos (hN t) (hg t (u t))) (boltzmannFactor_pos _ _ _))
      (partitionFunction_pos (hg t)))

/-! ## Saha-coupled cross-stage collapse (the genuine Cσ feature)

The single-stage master line above is the optically-thin **Boltzmann** master plot. The defining
feature of the real **Saha–Boltzmann / Cσ graph** (Aguilera & Aragón 2007; Aragón & Aguilera 2014)
is that lines of *different ionization stages* also collapse onto ONE line, via the **Saha**
equation: an ionic (stage `Z+1`) line, with its abscissa shifted by the ionization energy `χ` and
its ordinate corrected by the Saha bracket, lands on the SAME master line as the neutral (stage `Z`)
lines. This is the part that genuinely uses `Saha.lean` (`sahaFactor`, `log_sahaFactor`) and that
distinguishes Cσ from a relabelled per-species Boltzmann plot. The exact construction (abscissa
shift `+χ`, ordinate `−` the Saha bracket) is that of the Saha–Boltzmann plot, verified against
the CF-LIBS literature. -/

/-- Log of the **Saha bracket** `2·(2π m_e k_B T / h²)^{3/2} / n_e`. Subtracting this from an
ionic-stage Boltzmann ordinate is exactly the correction that lands it on the neutral master line
(the Saha–Boltzmann plot of Aguilera & Aragón 2007). -/
noncomputable def sahaBracketLog (kB T me h ne : ℝ) : ℝ :=
  Real.log (2 * (thermalBracket kB T me h) ^ (3 / 2 : ℝ) / ne)

/-- **Saha-corrected ionic-stage ordinate.** The ordinate of an ionic (stage `Z+1`) line `k`,
corrected for Saha ionization equilibrium and referenced to the **neutral** stage's offset
`q_I = csigmaOffset` (so both stages share one intercept):
`ln(I/(g_k A_k)) − ln[2·(2π m_e k_B T/h²)^{3/2}/n_e] − q_I`. With the abscissa shifted to `E_k + χ`,
this lies on the SAME master line `Y = −E*/(k_B T)` as the neutral lines — see
`csigma_saha_master_line`. -/
noncomputable def csigmaSahaOrdinate (kB T me h ne NI NII Fcal : ℝ)
    (gI EI : ι → ℝ) (gII EII AII : κ → ℝ) (k : κ) : ℝ :=
  Real.log (lineIntensity kB T NII Fcal gII EII AII k / (gII k * AII k))
    - sahaBracketLog kB T me h ne
    - csigmaOffset kB T Fcal NI gI EI

/-- **Cσ cross-stage master line (the Saha-coupled collapse).** An ionic (stage `Z+1`) line whose
density satisfies Saha ionization equilibrium with the neutral stage
(`hsaha : N_II·n_e = N_I · S(T)`, i.e. `n_{z+1} n_e / n_z = sahaFactor`, the `Saha.saha_relation`)
has Saha-corrected ordinate exactly `−(E_k + χ)/(k_B T)` — the neutral master line
`Y = −E*/(k_B T)` evaluated at the **ionization-shifted** abscissa `E* = E_k + χ`. So neutral and
ionic lines of an element fall on ONE straight line of slope `−1/(k_B T)` and common intercept
`q_I = ln(F·N_I/U_I)`. Reduces the ionic Boltzmann plot (`boltzmann_plot_intensity`) through the
Saha log-identity (`log_sahaFactor`); the partition functions, `n_e`, the `log 2` and the
`(3/2)·log` bracket all cancel, leaving only the ionization shift `χ`. -/
theorem csigma_saha_master_line [Nonempty ι] [Nonempty κ]
    {kB T me h chi ne NI NII Fcal : ℝ} {gI EI : ι → ℝ} {gII EII AII : κ → ℝ}
    (hkB : 0 < kB) (hT : 0 < T) (hme : 0 < me) (hh : 0 < h) (hne : 0 < ne)
    (hgI : ∀ j, 0 < gI j) (hNI : 0 < NI) (hFcal : 0 < Fcal)
    (hgII : ∀ j, 0 < gII j) (hNII : 0 < NII) (hAII : ∀ j, 0 < AII j)
    (hsaha : NII * ne = NI * sahaFactor kB T me h chi gI EI gII EII) (k : κ) :
    csigmaSahaOrdinate kB T me h ne NI NII Fcal gI EI gII EII AII k
      = -(EII k + chi) / (kB * T) := by
  have hUI : 0 < partitionFunction kB T gI EI := partitionFunction_pos hgI
  have hUII : 0 < partitionFunction kB T gII EII := partitionFunction_pos hgII
  have hbr : 0 < thermalBracket kB T me h := thermalBracket_pos hkB hT hme hh
  have hsf : 0 < sahaFactor kB T me h chi gI EI gII EII := sahaFactor_pos hkB hT hme hh hgI hgII
  have hrpow : 0 < (thermalBracket kB T me h) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hbr _
  have hlogNII : Real.log NII
      = Real.log NI + Real.log (sahaFactor kB T me h chi gI EI gII EII) - Real.log ne := by
    have h := congrArg Real.log hsaha
    rw [Real.log_mul hNII.ne' hne.ne', Real.log_mul hNI.ne' hsf.ne'] at h
    linarith
  have hlogsf := log_sahaFactor (chi := chi) (EZ := EI) (EZ1 := EII) hkB hT hme hh hgI hgII
  have e1 : Real.log (Fcal * NII / partitionFunction kB T gII EII)
      = Real.log Fcal + Real.log NII - Real.log (partitionFunction kB T gII EII) := by
    rw [Real.log_div (mul_pos hFcal hNII).ne' hUII.ne', Real.log_mul hFcal.ne' hNII.ne']
  have e2 : sahaBracketLog kB T me h ne
      = Real.log 2 + (3 / 2 : ℝ) * Real.log (thermalBracket kB T me h) - Real.log ne := by
    unfold sahaBracketLog
    rw [Real.log_div (mul_pos (by norm_num) hrpow).ne' hne.ne',
        Real.log_mul (by norm_num) hrpow.ne', Real.log_rpow hbr]
  have e3 : csigmaOffset kB T Fcal NI gI EI
      = Real.log Fcal + Real.log NI - Real.log (partitionFunction kB T gI EI) := by
    unfold csigmaOffset
    rw [Real.log_div (mul_pos hFcal hNI).ne' hUI.ne', Real.log_mul hFcal.ne' hNI.ne']
  unfold csigmaSahaOrdinate
  rw [boltzmann_plot_intensity hgII hNII hFcal hAII k, e1, e2, e3, hlogNII, hlogsf]
  ring

/-- **Neutral and ionic lines share one line.** A neutral line `i` and an ionic line `k` with the
same ionization-shifted abscissa (`E_I i = E_II k + χ`) produce the SAME Cσ ordinate: the neutral
master ordinate (`csigma_master_line`) and the ionic Saha-corrected ordinate
(`csigma_saha_master_line`) coincide. The cross-stage analogue of
`csigma_master_line_indep_species` — "all points, both stages, collapse onto one line." -/
theorem csigma_cross_stage_collapse [Nonempty ι] [Nonempty κ]
    {kB T me h chi ne NI NII Fcal : ℝ} {gI EI AI : ι → ℝ} {gII EII AII : κ → ℝ}
    (hkB : 0 < kB) (hT : 0 < T) (hme : 0 < me) (hh : 0 < h) (hne : 0 < ne)
    (hgI : ∀ j, 0 < gI j) (hNI : 0 < NI) (hFcal : 0 < Fcal) (hAI : ∀ j, 0 < AI j)
    (hgII : ∀ j, 0 < gII j) (hNII : 0 < NII) (hAII : ∀ j, 0 < AII j)
    (hsaha : NII * ne = NI * sahaFactor kB T me h chi gI EI gII EII)
    (i : ι) (k : κ) (hshift : EI i = EII k + chi) :
    csigmaOrdinate kB T NI Fcal gI EI AI i
      = csigmaSahaOrdinate kB T me h ne NI NII Fcal gI EI gII EII AII k := by
  rw [csigma_master_line hgI hNI hFcal hAI i,
      csigma_saha_master_line hkB hT hme hh hne hgI hNI hFcal hgII hNII hAII hsaha k, hshift]

/-! ## Temperature from the Cσ master line (the multi-line regression payoff) -/

/-- **Multi-line temperature from the Cσ master line.** The ordinary-least-squares slope of a
species' Cσ master-line points `(E_k, Y_k)` is exactly `−1/(k_B T)` — so the plasma temperature is
recovered from the *single regression* over all of the species' lines (`olsSlope`,
`Alt.ols_recovers_line`), not from a hand-picked pair. The master-line ordinate is exactly affine in
`E_k` (`csigma_master_line`), so the noise-free OLS slope is exact. (Pooling lines of *different*
stages into one regression is the cross-stage analogue — see `csigma_temperature_cross_stage` for
the two-line cross-stage case.) -/
theorem csigma_master_olsSlope [Nonempty ι] {kB T N Fcal : ℝ} {g E A : ι → ℝ}
    (hg : ∀ k, 0 < g k) (hN : 0 < N) (hFcal : 0 < Fcal) (hA : ∀ k, 0 < A k)
    (hvar : 0 < ∑ k, (E k - mean E) ^ 2) :
    olsSlope E (fun k => csigmaOrdinate kB T N Fcal g E A k) = -1 / (kB * T) := by
  have hcol : ∀ k, csigmaOrdinate kB T N Fcal g E A k = -1 / (kB * T) * E k + 0 := by
    intro k; rw [csigma_master_line hg hN hFcal hA k]; ring
  exact (ols_recovers_line hcol hvar).1

/-- **Cross-stage two-line temperature (the Saha–Boltzmann diagnostic).** A *neutral* line `i` and
an *ionic* line `k` together yield the temperature: the slope of the Cσ master line through the
neutral point `(E_I i, ·)` and the ionization-shifted ionic point `(E_II k + χ, ·)` is exactly
`−1/(k_B T)`. This is the practical value of the Saha-coupled collapse — a single-species Boltzmann
plot **cannot** combine an atomic and an ionic line, but the Saha–Boltzmann / Cσ graph can. Reduces
to
`csigma_master_line` (neutral) and `csigma_saha_master_line` (ionic). -/
theorem csigma_temperature_cross_stage [Nonempty ι] [Nonempty κ]
    {kB T me h chi ne NI NII Fcal : ℝ} {gI EI AI : ι → ℝ} {gII EII AII : κ → ℝ}
    (hkB : 0 < kB) (hT : 0 < T) (hme : 0 < me) (hh : 0 < h) (hne : 0 < ne)
    (hgI : ∀ j, 0 < gI j) (hNI : 0 < NI) (hFcal : 0 < Fcal) (hAI : ∀ j, 0 < AI j)
    (hgII : ∀ j, 0 < gII j) (hNII : 0 < NII) (hAII : ∀ j, 0 < AII j)
    (hsaha : NII * ne = NI * sahaFactor kB T me h chi gI EI gII EII)
    (i : ι) (k : κ) (hx : EI i ≠ EII k + chi) :
    (csigmaOrdinate kB T NI Fcal gI EI AI i
        - csigmaSahaOrdinate kB T me h ne NI NII Fcal gI EI gII EII AII k)
      / (EI i - (EII k + chi)) = -1 / (kB * T) := by
  have hkBT : kB * T ≠ 0 := (mul_pos hkB hT).ne'
  have hxne : EI i - (EII k + chi) ≠ 0 := sub_ne_zero.mpr hx
  rw [csigma_master_line hgI hNI hFcal hAI i,
      csigma_saha_master_line hkB hT hme hh hne hgI hNI hFcal hgII hNII hAII hsaha k]
  field_simp
  ring

/-! ## The Cσ universal line (all ELEMENTS on one line)

The master line above subtracts the *full* per-species offset `q_s = ln(F·N_s/U_s)`, so every
species collapses to `Y = −E/(k_B T)` (intercept `0`). The full **Cσ graph** (Aragón & Aguilera,
2014) instead subtracts only the **concentration/partition** part `ln(N_s/U_s)`, leaving the *common
instrumental intercept* `ln F` — so all lines of all ELEMENTS (and, with the Saha correction, all
STAGES) fall on ONE universal line of slope `−1/(k_B T)` and intercept `ln F`, independent of each
element's concentration and partition function. (Verified against the CF-LIBS literature.) -/

/-- The **concentration/partition normalization** `ln(N_s/U_s(T))` — subtracted from a Boltzmann
ordinate to remove a species' concentration-and-partition dependence, leaving the common `ln F`. -/
noncomputable def csigmaConcentrationLog (kB T N : ℝ) (g E : ι → ℝ) : ℝ :=
  Real.log (N / partitionFunction kB T g E)

/-- **Universal Cσ ordinate (neutral stage).** `ln(I/(g_k A_k)) − ln(N_s/U_s)` — the
concentration-normalized ordinate. Unlike `csigmaOrdinate` (which subtracts the *full* offset
`ln(F·N_s/U_s)`, intercept `0`), this keeps the instrumental intercept `ln F`. -/
noncomputable def csigmaUniversalOrdinate (kB T N Fcal : ℝ) (g E A : ι → ℝ) (k : ι) : ℝ :=
  Real.log (lineIntensity kB T N Fcal g E A k / (g k * A k))
    - csigmaConcentrationLog kB T N g E

/-- **The Cσ universal line.** The concentration-normalized ordinate of *every* line of *every*
species is `ln F − E_k/(k_B T)` — ONE universal line (slope `−1/(k_B T)`, intercept `ln F`),
independent of the species concentration `N_s` and partition function `U_s`. This is the full Cσ
collapse across elements: the concentration normalization `ln(N_s/U_s)` cancels everything but the
instrumental factor `F`. -/
theorem csigma_universal_line [Nonempty ι] {kB T N Fcal : ℝ} {g E A : ι → ℝ}
    (hg : ∀ k, 0 < g k) (hN : 0 < N) (hFcal : 0 < Fcal) (hA : ∀ k, 0 < A k) (k : ι) :
    csigmaUniversalOrdinate kB T N Fcal g E A k = Real.log Fcal - E k / (kB * T) := by
  have hU : 0 < partitionFunction kB T g E := partitionFunction_pos hg
  unfold csigmaUniversalOrdinate csigmaConcentrationLog
  rw [boltzmann_plot_intensity hg hN hFcal hA k,
      Real.log_div (mul_pos hFcal hN).ne' hU.ne', Real.log_mul hFcal.ne' hN.ne',
      Real.log_div hN.ne' hU.ne']
  ring

/-- **Universal-line element independence.** Two genuinely different species (any concentrations,
partition functions, degeneracies) whose line `k` shares the upper-level energy produce the SAME
universal ordinate `ln F − E_k/(k_B T)` — all elements collapse onto one line. -/
theorem csigma_universal_indep_species [Nonempty ι] {kB T Fcal : ℝ}
    {N₁ N₂ : ℝ} {g₁ E₁ A₁ g₂ E₂ A₂ : ι → ℝ}
    (hg₁ : ∀ k, 0 < g₁ k) (hN₁ : 0 < N₁) (hg₂ : ∀ k, 0 < g₂ k) (hN₂ : 0 < N₂)
    (hFcal : 0 < Fcal) (hA₁ : ∀ k, 0 < A₁ k) (hA₂ : ∀ k, 0 < A₂ k)
    (k : ι) (hEk : E₁ k = E₂ k) :
    csigmaUniversalOrdinate kB T N₁ Fcal g₁ E₁ A₁ k
      = csigmaUniversalOrdinate kB T N₂ Fcal g₂ E₂ A₂ k := by
  rw [csigma_universal_line hg₁ hN₁ hFcal hA₁ k, csigma_universal_line hg₂ hN₂ hFcal hA₂ k, hEk]

/-- **Universal Cσ ordinate (ionic stage).** The Saha-corrected ionic ordinate with the *neutral*
concentration normalization — so ionic lines join the SAME universal line as the neutral ones. -/
noncomputable def csigmaSahaUniversalOrdinate (kB T me h ne NI NII Fcal : ℝ)
    (gI EI : ι → ℝ) (gII EII AII : κ → ℝ) (k : κ) : ℝ :=
  Real.log (lineIntensity kB T NII Fcal gII EII AII k / (gII k * AII k))
    - sahaBracketLog kB T me h ne
    - csigmaConcentrationLog kB T NI gI EI

/-- **The universal line spans both stages.** An ionic (stage `Z+1`) line in Saha equilibrium with
the neutral stage has universal ordinate `ln F − (E_k + χ)/(k_B T)` — the SAME universal line
(slope `−1/(k_B T)`, intercept `ln F`) as the neutral lines, at the ionization-shifted abscissa. So
ALL lines of ALL elements and BOTH stages collapse onto one line. (`csigmaSahaUniversalOrdinate`
differs from `csigmaSahaOrdinate` by exactly `ln F`, the offset minus the concentration norm.) -/
theorem csigma_saha_universal_line [Nonempty ι] [Nonempty κ]
    {kB T me h chi ne NI NII Fcal : ℝ} {gI EI : ι → ℝ} {gII EII AII : κ → ℝ}
    (hkB : 0 < kB) (hT : 0 < T) (hme : 0 < me) (hh : 0 < h) (hne : 0 < ne)
    (hgI : ∀ j, 0 < gI j) (hNI : 0 < NI) (hFcal : 0 < Fcal)
    (hgII : ∀ j, 0 < gII j) (hNII : 0 < NII) (hAII : ∀ j, 0 < AII j)
    (hsaha : NII * ne = NI * sahaFactor kB T me h chi gI EI gII EII) (k : κ) :
    csigmaSahaUniversalOrdinate kB T me h ne NI NII Fcal gI EI gII EII AII k
      = Real.log Fcal - (EII k + chi) / (kB * T) := by
  have hU : 0 < partitionFunction kB T gI EI := partitionFunction_pos hgI
  have key : csigmaSahaUniversalOrdinate kB T me h ne NI NII Fcal gI EI gII EII AII k
      = csigmaSahaOrdinate kB T me h ne NI NII Fcal gI EI gII EII AII k + Real.log Fcal := by
    unfold csigmaSahaUniversalOrdinate csigmaSahaOrdinate csigmaOffset csigmaConcentrationLog
    rw [Real.log_div (mul_pos hFcal hNI).ne' hU.ne', Real.log_mul hFcal.ne' hNI.ne',
        Real.log_div hNI.ne' hU.ne']
    ring
  rw [key, csigma_saha_master_line hkB hT hme hh hne hgI hNI hFcal hgII hNII hAII hsaha k]
  ring

end CflibsFormal.Alt

