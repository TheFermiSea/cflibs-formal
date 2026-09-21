# First-principles alternatives for composition from LIBS spectra — exploration memo

*2026-09-21. Status: exploration, not a plan. Companion to `docs/spec/`; nothing here is formalized
or implemented. Citation rule: only items for which a publisher, PubMed, OSTI or ADS page was seen
in this session are cited as literature; everything else is marked UNVERIFIED. The search record is
in the appendix.*

## 0. The frame, stated honestly

An earlier derivation study in this project (recorded in the session memory, 2026-09-02) concluded
that the space of new *physical relations* for an LTE laser plasma is closed: every emission line
couples the emitter density to the observable through one Boltzmann factor, one Einstein
coefficient and one calibration factor, and no algebra removes all three at once. That conclusion
stands. What it does **not** close is the *method* space, which has three independent axes:

1. **Which observable carries the composition.** Excited-line intensities (CF-LIBS, C-sigma), line
   widths, equivalent widths of self-absorbed lines, the saturated cores of optically thick lines,
   temporal or spatial moments of all of these.
2. **Which nuisance is eliminated.** The calibration factor `F`; the excited-state Einstein
   coefficients `A_ki`; the temperature `T` and partition functions `U(T)`; the closure
   `Σ C_s = 1`; the single-temperature assumption itself.
3. **How the inverse problem is posed.** A point estimate under one `(T, n_e)`, or an inversion
   over a *distribution* of plasma states, which is what a time-integrated spectrum actually is.

Every candidate below is a position on these axes. The table in §3 ranks them; §4 says what is
worth formalizing first, because this repository's contribution is a verified identifiability
statement, not a faster fit.

## 1. What each observable is independent of

Under LTE, single zone, for element `s`, stage `z`, line `k` (upper level `E_k`, lower `E_i`):

| observable | needs `F` | needs `A_ki` (excited) | needs `T` | needs `U(T)` | needs closure | note |
|---|---|---|---|---|---|---|
| line intensity `I_k` | yes | yes | yes | yes | yes (for absolute `C`) | CF-LIBS, C-sigma |
| Stark width | no | no | weakly (log) | no | no | gives `n_e` only |
| Doppler width | no | no | gives `T_kin` from `m` | no | no | no atomic data at all; buried under Stark in alloy plasmas |
| equivalent width of a self-absorbed resonance line | no | no (needs `f` of the resonance line) | via ground-state fraction `g_0/U` | weakly | no | column density `N_0 L`; curve of growth |
| saturated line-core radiance | yes (or gives `F`) | no | gives `B_λ(T)` | no | no | Planck ceiling (Kirchhoff) |
| ratio of two lines from one upper level | no | yes | no | no | no | `= A_1 λ_2 / (A_2 λ_1)`; self-absorption test |
| ion/neutral line ratio of one element | no | yes | yes | yes | no | Saha–Boltzmann thermometer |
| continuum spectral shape | no | no | yes | no | no | `T` only |

Reading down the columns: nothing bypasses `T` except widths; nothing bypasses `A_ki` except
widths, equivalent widths (which trade `A_ki` for the far better known resonance `f`) and Planck
cores; nothing bypasses `F` except widths, equivalent widths and ratios. So a composition estimator
that avoids excited-state `A_ki` and `F` altogether has to be built from **widths, equivalent
widths and saturated cores**, with `T` supplied by Planck cores or Doppler widths and `n_e` by
Stark widths. That composite is candidate C1 below; its parts are all published, the assembly and
its identifiability are what is open.

## 2. Candidates

Each entry: principle · observable · what cancels · assumptions · identifiability sketch · failure
modes · literature status · one Lean-formalizable claim · applicability to the project's target
(time-integrated spectra of metal alloys and high-entropy alloys, whose Fe, Cr, Ni, Co, Mn
resonance lines are strongly self-absorbed).

### C1. Widths-and-ceiling estimator: composition from ground-state column densities, with `T` from saturated cores and `n_e` from Stark widths

- **Principle.** At LIBS temperatures the ground state holds almost the whole population of each
  stage (`N_s,z ≈ N_0 · U_z(T)/g_0`, with `U/g_0` close to 1 and slowly varying), so composition is
  *directly* the ratio of ground-state populations. Resonance lines from the ground state are
  exactly the self-absorbed ones; their optical depth gives `N_0 L` through the resonance
  oscillator strength `f`, which for the strong lines of Fe, Cr, Ni, Mn is among the best-known
  atomic data. Excited-line intensities, `A_ki` and `F` are never used; the excited-state tail that
  CF-LIBS *extrapolates* from is exactly the part this estimator ignores.
- **Observable.** Equivalent width `W` (or full profile) of each element's resonance line(s); the
  Stark width of an isolated line for `n_e`; the peak radiance of two or more saturated cores for
  `T` (C2) or a Saha–Boltzmann `T` if C2 is not available.
- **What cancels.** `F` (widths are wavelength-axis quantities), excited-state `A_ki`, and, in the
  ratio of two elements' column densities, the path length `L`.
- **Assumptions.** LTE; a common emitting/absorbing column for the elements compared (single zone,
  or the same two-zone geometry for all resonance lines); the damping (Stark) wing dominates the
  profile when `τ_0 ≫ 1`; ionization balance from Saha with the Stark `n_e`.
- **Identifiability sketch.** Unknowns per element: `N_0` (and `L`, shared). Equations: one curve of
  growth per resonance line, `W = W(N_0 f L, γ_Stark(n_e), Doppler)`. In the flat part of the curve
  (`τ_0 ~ 1–10`) `W` is nearly insensitive to `N_0` and the inversion is ill-conditioned; in the
  damping regime the sharp Ladenburg–Reiche law `W → 2√τ` (this repository's Frontier 07,
  `equivWidth_lorentzian_sqrt_sharp`) makes `W² ∝ N_0 f L γ`, so `N_a/N_b = (W_a/W_b)² · (f_b γ_b)/(f_a γ_a)`
  with `γ ∝ n_e` cancelling if both lines' Stark parameters are known. The price is that a relative
  error `ε` in `W` becomes `2ε` in `N`.
- **Failure modes.** A cool periphery self-reverses resonance lines (two-zone), so `W` mixes core
  emission and peripheral absorption; time integration sums curves of growth over a cooling,
  expanding column; instrument broadening must be deconvolved from `W` when the line core is
  narrower than the slit function; Stark parameters carry 10–30 % uncertainty; elements whose
  resonance lines lie in the VUV are invisible, as in CF-LIBS.
- **Literature status: parts occupied, assembly open.** Column densities from self-absorbed lines
  "as a resource for quantitative analysis": Cristoforetti & Tognoni, Spectrochim. Acta B 79–80
  (2013) 63. The columnar-density Saha–Boltzmann plot for `T`: PubMed 30792922 (2019). Column
  density Saha–Boltzmann (CD-SB) self-absorption correction: Lin et al., Anal. Lett. 58 (2024),
  DOI 10.1080/00032719.2024.2400269. Curve-of-growth plasma characterization: Gornushkin et al.,
  Spectrochim. Acta B 54 (1999) 491; Aguilera & Aragón, Spectrochim. Acta B 62 (2007) 378; the
  C-sigma generalized curves of growth, Aragón & Aguilera, JQSRT 149 (2014) 90, which normalize
  by the Planck function and need one characterization standard. "Exploiting self-absorption" for
  CF-LIBS accuracy: Anal. Chim. Acta (2021), ScienceDirect S0003267021008345. **Not found:** an
  estimator that takes the ground-state column densities as the *primary* composition observable,
  supplies `T` from saturated cores rather than from excited-line plots, and states its
  identifiability and error amplification (the `2ε` above). The damping-wing form is the corner
  this repository is uniquely placed to state exactly. Paper Finder agent (2026-09-21, thread
  `2026-09-21-c1-column-density`, 20 ranked results after a narrowed follow-up; the first, broader
  query exhausted the agent's time budget): "No single paper was found that fully integrates all
  requested aspects (quantification from ground-state column density, Planck-limited temperature,
  and Saha-Boltzmann quantification) in one workflow." Additional prior art it surfaced: Fu, Ni,
  Wang, Jia & Dong, Plasma Sci. Technol. (2018), DOI 10.1088/2058-6272/aaead6, is a *review* of
  CF-LIBS accuracy improvements (full text checked: Boltzmann/Saha–Boltzmann frameworks with
  self-absorption corrections; no Planck-peak thermometry, columnar density not used for composition
  on its own; the agent's summary over-credited it); the 2021 Anal. Chim. Acta paper above is
  "CF-LIBS with columnar density and standard reference line (CD-SRL)", i.e. columnar density
  for quantification *with* a reference line, not strictly standardless; Rezaei, InTech chapter
  (2016), DOI 10.5772/61941, reviews curve-of-growth analysis and a "three lines" optically thick
  method giving temperature and Al density (see C2).
- **Lean-formalizable claim.** In the damping regime, `N_a/N_b` is an explicit function of
  `(W_a, W_b, f_a, f_b, γ_a, γ_b)` (EXACT within the slab model, from Frontier 07 plus
  `CurveOfGrowth`), with a REDUCED bound `|δN/N| ≤ 2|δW/W| + |δγ/γ|` and a stated non-identifiability
  on the flat part of the curve (a `CurveOfGrowth`-style "recover/defeat" boundary).
- **Applicability to time-integrated HEA spectra.** High: the target lines are exactly the strongly
  self-absorbed ones, and `F`-independence removes the largest systematic of hand-held
  instruments. Time integration and self-reversal are the two risks; both are testable on the
  companion's existing alloy spectra by comparing gated and integrated acquisitions.

### C2. Thick-core two-colour pyrometry: `T` from the ratio of two saturated line cores, no atomic data

- **Principle.** The core of an optically thick line radiates at the Planck function of the layer
  where `τ_λ ≈ 1`. Two such cores at different wavelengths give `B_λ1(T)/B_λ2(T)`, a strictly
  monotone function of `T`, so `T` follows with no `A`, no `f`, no `F` and no partition function.
- **Observable.** Peak spectral radiance of two (or more) saturated lines, ideally of different
  elements and widely separated in wavelength.
- **What cancels.** Everything atomic; `F` cancels in the ratio if the relative spectral response is
  known (the same requirement as any Boltzmann plot).
- **Assumptions.** Cores are truly saturated (`τ_0 ≳ 5`) and spectrally resolved; the `τ ≈ 1`
  surfaces of the two lines sit at the same temperature.
- **Identifiability sketch.** One unknown, one equation per pair; over-determined with three or more
  cores, which gives a consistency test of the single-`T` assumption for free.
- **Failure modes, from first principles.** (i) The observed peak is the core radiance *diluted* by
  the instrument profile whenever the core width is below the slit function, so a low-resolution
  spectrometer reads a `T` that is too low by a wavelength-dependent factor; (ii) a cooler periphery
  self-reverses the core, and the reading becomes `T` of the periphery, not the emitting core;
  (iii) a time-integrated peak integrates `B_λ(T(t))` over the cooling history, and because
  `B_λ` is convex in `T` the two-colour ratio of time integrals is not the ratio at any single `T`.
  For the project's time-integrated alloy spectra (ii) and (iii) apply simultaneously.
- **Literature status.** The Planck ceiling as an absolute scale for self-absorption correction is
  occupied: Li et al., Anal. Chim. Acta 1058 (2019) 39 (PubMed 30851852, BRR-SAC); the Planck
  normalization in C-sigma (Aragón & Aguilera 2014); a Planck-function self-absorption method,
  JAAS 2023, DOI 10.1039/d2ja00352j (UNVERIFIED title, from the notebook's source URL). Two-colour
  pyrometry of *line cores* in a laser plasma: no LIBS-specific result surfaced (queries in the
  appendix); the web hits were surface pyrometry. Nearest prior art found by the Paper Finder
  agent (2026-09-21): the "three lines method" reviewed in Rezaei, InTech chapter (2016), DOI
  10.5772/61941, attributed there to Rezaei & Tavassoli, J. Anal. At. Spectrom. (2014; UNVERIFIED
  beyond the chapter's citation): ratios of the peak intensities of three optically thick lines,
  with the plasma length from shadowgraphy and a measured electron density, solved on contour
  plots for `T`, the Al density and the instrument factor. That is a saturated-line *ratio*
  method with atomic data, not atomic-data-free two-colour pyrometry, and the chapter (full text
  checked) does not use the Planck ceiling as a thermometer. Treat C2 as open but low value for
  this target.
- **Lean-formalizable claim.** `T ↦ B_λ1(T)/B_λ2(T)` is strictly monotone for `λ1 ≠ λ2`
  (PURE-MATH), hence two saturated cores identify `T`; plus the dilution statement: convolution with
  a unit-area kernel lowers a peak, so the pyrometric `T` is a *lower bound* (EXACT within the
  model).
- **Applicability.** Low for time-integrated data; worth a gated, high-resolution test only.

### C3. Charge-neutrality normalization instead of closure: absolute densities from the Stark `n_e`, and a missing element as a *deficit*

- **Principle.** CF-LIBS fixes the absolute scale by `Σ C_s = 1`, which silently redistributes
  any undetected element (H, O, N, C, halogens with VUV resonance lines) over the detected ones.
  Charge neutrality, `n_e = Σ_s Σ_z z N_s,z`, is a second absolute equation whose right-hand side
  the Saha–Boltzmann analysis already produces up to the scale `F`, and whose left-hand side the
  Stark width measures independently of `F`. Using neutrality as the normalization gives
  absolute densities without closure; closure then becomes a *test*, and `1 − Σ C_s` is an
  estimate of the undetected mass fraction, with a sign.
- **Observable.** The usual line intensities plus one Stark width.
- **What cancels.** The closure assumption. `F` is *solved for* rather than eliminated.
- **Assumptions.** LTE; the Stark `n_e` and the Saha ionization balance refer to the same plasma
  volume; ionization stages beyond the first are negligible or included.
- **Identifiability sketch.** Unknowns: `C_s` for `S` elements, `F`, `T`, `n_e` (`S + 3`).
  Equations: `S` Boltzmann intercepts, `S` Saha relations, one Stark width, one neutrality, one
  closure (`2S + 3`). With closure dropped the system is still determined; with closure kept it is
  over-determined by one, and the residual is the deficit. Leverage is poor for elements with a
  small ionization fraction (high ionization energy at low `T`), because their ion densities
  barely enter the neutrality sum; leverage is good for the alloy metals, which are mostly singly
  ionized at typical LIBS delays.
- **Failure modes.** Stark `n_e` accuracy of 10–20 % propagates directly into the absolute scale;
  neutral and ion lines sampling different zones (Tognoni et al. 2010 name the Saha-versus-Stark
  `n_e` mismatch as a diagnostic of exactly this); time integration averages `n_e(t)` and the
  Saha balance differently.
- **Literature status: core occupied, the residual is open (revised 2026-09-21 after the Asta
  Paper Finder agent run).** Abbass, Ahmed, Ahmed & Baig, Plasma Chem. Plasma Process. 36 (2016)
  1287, DOI 10.1007/s11090-016-9729-y, compare a Boltzmann-intercept CF-LIBS with an "electron
  density conservation" CF-LIBS on Pb–Sn alloys, in which "elemental compositions are determined
  by comparing the experimentally measured number density with the theoretical results obtained by
  CF-LIBS", and find the conservation method "more appropriate"; their `n_e` comes from the
  Saha–Boltzmann equation, not from a Stark width, and the sample is a binary alloy where neutrality
  and closure are two equations for two unknowns. Wala, Polek, Harilal, Jones & Phillips,
  Spectrochim. Acta B (2025), DOI 10.1016/j.sab.2025.107142 (arXiv 2503.01185), use neutrality to
  bound `n_e` from ion column densities measured by laser *absorption* and compare with Stark values.
  The Paper Finder agent's narrative: "No papers were found that fully implement ... using the
  discrepancy between closure-normalized and neutrality-normalized results ... to detect or quantify
  missing elements", five candidates, top relevance 0.78 (Wala), the Abbass paper at 0.48. So what
  remains open is narrower than first stated: neutrality with a *Stark* `n_e` as the absolute scale
  for a multi-element sample, the closure residual as a signed missing-element estimate, and the
  identifiability statement. The 75-source notebook, restricted to peer-reviewed sources, likewise
  returns no paper that reports a missing-element deficit;
  Tognoni, Cristoforetti, Legnaioli & Palleschi, Spectrochim. Acta B 65 (2010) 1 use the
  Saha/Stark `n_e` consistency only as a diagnostic and state that closure fails when elements are
  missing. Forward simulators impose neutrality (a 2023 RSC Adv. forward model was named by the
  notebook; UNVERIFIED), inverse solvers do not. Web queries on this vocabulary returned nothing
  relevant. Still the cleanest open candidate found, with the 2016 paper as the required prior-art citation.
- **Lean-formalizable claim.** In the existing `Inverse`/`CompositionIdentifiability` setting: the
  composition and `F` are identifiable from `(intensities, Stark n_e)` *without* the closure
  hypothesis (EXACT), and with an undetected species the closure-normalized estimate is biased by
  an explicit factor `1/(1 − C_missing)` while the neutrality-normalized estimate is unbiased and the
  closure residual equals `C_missing` (EXACT). This slots into the certificate ledger
  (`EvaluatorSoundness`) as a runtime-checkable missing-element certificate.
- **Applicability.** High for alloys (all constituents visible, singly ionized); doubles as the
  consistency certificate the algorithm-search campaign lacks.

### C4. Temperature-distribution inversion for time-integrated spectra: composition jointly with a measure over `T`

- **Principle.** A time-integrated (and spatially integrated) spectrum is not an LTE spectrum at any
  `T`; it is `I_k = F N_s ∫ w(T) e^{−E_k/kT} / U_s(T) dT` for an emission-measure-like weight
  `w(T)` shared by all lines of all elements. CF-LIBS fits a single `T` to a curved Boltzmann plot
  and absorbs the curvature into `A_ki` "errors". The alternative is to invert for `w(T)` and the
  `N_s` jointly.
- **Observable.** Many lines per element spanning a wide `E_k` range, across elements.
- **What cancels.** The single-temperature assumption; `F` and closure as in CF-LIBS.
- **Assumptions.** LTE at each instant; the same `w(T)` for every species (same plume, same
  integration), which is the one strong physical assumption and is exactly what fails when
  neutrals and ions occupy different zones.
- **Identifiability sketch.** Recovering `w(T)` from `E_k`-sampled moments is a Laplace-type
  inversion and is ill-posed; but the composition ratio `N_a/N_b` between elements whose lines cover
  the same `E_k` range is insensitive to `w` at first order (the same weight multiplies both), which
  is the useful statement. Two testable necessary conditions follow with no fit at all: every
  Boltzmann plot of a mixture is *convex* (log-sum-exp of a positive mixture), and the single-`T`
  slope fitted to a convex plot is bracketed by the local slopes at the lowest and highest `E_k`.
- **Failure modes.** Line selection over a wide `E_k` range reintroduces self-absorption at the low
  end and weak lines at the high end; `U_s(T)` differs between elements so the weight does not
  cancel exactly; the shared-`w` assumption.
- **Literature status: adjacent-field template, LIBS assembly open.** Time-integrated x-ray
  spectra inverted for electron-temperature distributions: OSTI 1889537 / PubMed 36182496 (2022).
  Curved Boltzmann plots fitted as two Boltzmann components appear in plasma spectroscopy (web
  hits, not LIBS-specific, UNVERIFIED as LIBS). A 2025 Plasma Sources Sci. Technol. paper inverts
  a time-integrated Hα profile for `n_e(t)` (named by the notebook; UNVERIFIED). The notebook,
  restricted to peer-reviewed sources, finds no joint composition + `T`-distribution fit to a
  time-integrated LIBS spectrum. Paper Finder agent (2026-09-21, 38 ranked results, thread
  `2026-09-21-c4-temperature-distribution`): "No papers were found that jointly fit both composition
  and temperature distribution from time-integrated LIBS spectra, which likely reflects a gap in the
  LIBS literature rather than a search failure"; the top matches are solar/x-ray differential
  emission measure inversions (e.g. corpus 119301790, 252762450, 247839410) and one LIBS-adjacent
  precedent, a 2023 Eur. Phys. J. Appl. Phys. study interpreting Boltzmann-plot temperatures from
  spatially integrated oxygen lines of a non-uniform plasma (corpus 264392447; UNVERIFIED beyond the
  agent's summary). Frame any work here as transfer from the DEM/x-ray results, not invention.
- **Lean-formalizable claim.** Convexity of the mixture Boltzmann plot (PURE-MATH, Jensen on
  log-sum-exp) and the slope bracket (EXACT); first-order insensitivity of `N_a/N_b` to `w` when
  `E_k` coverage matches (REDUCED, with the mismatch term explicit). The convexity test is a
  falsifiable check of the single-zone assumption that costs nothing at runtime.
- **Applicability.** Direct: the project's spectra are time-integrated and the Pisa group's
  objection to time-integrated CF-LIBS is precisely the superposition this candidate models.

### C5. Cooling-trajectory forward model (adiabatic expansion) for time-integrated spectra

- **Principle.** Replace the free weight `w(T)` of C4 by a physical trajectory: impulsive heating,
  then adiabatic expansion `T ∝ V^{−(γ−1)}`, `n_e ∝ V^{−1}`, LTE along the path, integrated over the
  gate. Two or three trajectory parameters instead of a function.
- **Status.** Not found as a composition method (appendix); adjacent physics is standard plume
  hydrodynamics. **Identifiability is the open question:** the trajectory parameters and `w(T)`
  moments are confounded with composition unless the gate is wide and the `E_k` coverage large.
  Rank medium-low; it is C4 with a prior, and only worth doing after C4's necessary conditions are
  tested on real gated-versus-integrated pairs.

### C6. Doppler-width kinetic thermometer

- **Principle.** `T_kin` from the Doppler width of a light element's line using only its mass.
- **Status.** Established in plume time-of-flight work (UNVERIFIED for LIBS quantification). In
  alloy plasmas the Doppler width is buried under Stark and instrument broadening at the delays
  where lines are bright. Low applicability; listed for completeness of the elimination table.

### C7. Full-spectrum radiative-transfer likelihood as the vehicle

- Not a method but the container in which C1–C4 become constraints: a forward model of lines,
  continuum, self-absorption and instrument response fitted to the raw spectrum. Occupied
  (Monte-Carlo CF-LIBS, spectral-synthesis fitting; the notebook names several, UNVERIFIED as a
  set). The project's stance stands: any such fit is only as good as the identifiability of the
  constraints inside it, which is what C1–C4 supply.

## 3. Ranking

| candidate | novelty (literature) | physical justification | applicability to time-integrated alloy spectra | Lean target cost |
|---|---|---|---|---|
| C3 neutrality normalization / missing-element deficit | core occupied (Abbass 2016); residual, Stark scale and identifiability open | strong (an exact conservation law replacing an assumption) | high | low: extends `CompositionIdentifiability` |
| C1 widths-and-ceiling column-density estimator | parts occupied, assembly open | strong; error doubling is explicit | high, two known risks | medium: Frontier 07 + `CurveOfGrowth` |
| C4 `T`-distribution inversion | adjacent template | strong for the necessary conditions; weak for the full inversion | direct | low for the convexity test; high for the inversion |
| C5 cooling-trajectory model | open | plausible | unknown identifiability | high |
| C2 thick-core two-colour pyrometry | open, LIBS-specific | strong in principle; fails on this data | low | low |
| C6 Doppler thermometer | established elsewhere | exact | low | trivial |
| C7 full-spectrum likelihood | occupied | container | — | — |

## 4. What to do with this

1. **Formalize C3 first.** It is one theorem pair on existing definitions, it produces a
   runtime certificate the algorithm-search evaluator can use today, and it converts the closure
   assumption from an axiom into a measured residual. Statement drafts belong in `docs/spec/03`
   as a new dossier once the owner agrees.
2. **State C1 exactly, then test it.** The damping-wing composition identity is a two-line
   corollary of Frontier 07; the value is the honest error statement next to it. Experimentally,
   the test is cheap: gated versus integrated spectra of one alloy, equivalent widths of the
   Fe/Cr/Ni/Mn resonance lines, compared with the certified composition.
3. **Add C4's convexity test to the reviewer's checklist** for any time-integrated dataset before
   anyone fits a single-`T` CF-LIBS to it. If the Boltzmann plots are not convex within noise,
   the mixture model is falsified and the data are not a superposition of LTE states.
4. **Do not pursue C2 or C5 on the current data.** Both need gated, high-resolution acquisitions
   the project does not have; both are recorded so nobody re-derives them.

None of this changes the project's rule that accuracy claims are made only against certified
compositions on held-out spectra with the boring baseline run first.

## 5. What the Asta agents added (2026-09-21)

Three Asta tools were run after the memo's first version; each is a different kind of evidence.

### 5.1 Paper Finder agent (novelty negatives)

Per-candidate verdicts are folded into §2 above. Net effect on the ranking: C3's core is occupied
(Abbass et al. 2016), C4's LIBS gap is confirmed with the DEM literature as template, C1's assembly
remains unpublished with the 2013/2019/2021/2024 column-density papers as prior art, and C2's nearest
neighbour is a three-line saturated-ratio method, not pyrometry.

### 5.2 Theorizer (literature-grounded theories with novelty scores)

`asta generate-theories literature-theory-generation`, novelty-focused, 40 papers requested, 36
retrieved, eight theories with sixteen "laws" (falsifiable if-then predictions), each scored on six
novelty dimensions. Two caveats before any of it is used. First, the mission statement named C1–C4,
and all eight theories are restatements of those four, so the run cannot be read as independent
confirmation that they are the right candidates. Second, the 36-paper set does not contain the
prior art the Paper Finder found (Abbass 2016; Cristoforetti & Tognoni 2013; the CD-SB papers), so
its "Genuinely New" labels on the neutrality and column-density laws are not reliable; they are
"new relative to a corpus that missed the relevant papers". What survives is three predictions
with concrete, testable thresholds that the memo did not contain:

- **A density window for neutrality closure.** Neutrality with a Stark `n_e` should beat
  sum-to-unity only when `n_e` lies in roughly `3×10^16`–`3×10^17 cm⁻³` (Stark measurable, ions
  present, LTE plausible); below it the Saha leverage vanishes, above it opacity dominates. The
  numbers are the model's, not derived, but the window is the right shape for the identifiability
  statement in C3 and gives the certificate a runtime precondition.
- **Narrow-window equivalent-width ratios.** Taking the two resonance lines of C1 within the same
  few-nanometre window makes their equivalent-width ratio insensitive to the *relative* spectral
  response as well as to `F`, which even ratio methods otherwise need. That is a genuine refinement
  of C1's line-selection rule.
- **A wing-dominance classifier.** `W / Δλ_FWHM ≥ 2` as the operational test that a self-absorbed
  line is in the damping-wing regime where C1's √τ law applies and the ratio is temperature-
  insensitive; `< 1` as the flat-curve regime where it is not. The thresholds are unverified, but
  the classifier is exactly the "recover/defeat" boundary the Lean statement needs, and it is a
  measurable quantity.

The full export (theories, novelty assessments, extraction tables, `citations.bib`) is under
`.asta/theories/export/` (gitignored).

### 5.3 AutoDiscovery (data-driven, Bayesian surprise) on the SuperCam calibration library

Run `8e781522-ba41-4a80-aa84-02edff0dd9dc`, 20 experiments (20 credits), on a table derived from the
NASA PDS SuperCam laboratory LIBS library (Anderson et al. 2022): 1,193 base spectra of 334 certified
geological standards, 37 strong lines, per-line continuum, net peak, net area, FWHM, shape factor
`area/(peak·FWHM)` and peak-over-continuum, plus per-spectrometer sums (`docs/research/supercam_features.py`
and `supercam_autodiscovery_metadata.json`, run from the companion repo root; the SuperCam channel spacing of ~0.05 nm and instrument FWHM of ~0.15–0.3 nm
bound what widths can show). Thirteen experiments were "surprising", all in the negative direction
(the prior that a calibration-free observable tracks composition fell), and five confirmed their
hypothesis. The results that bear on the candidates:

| finding | evidence (AutoDiscovery's own analysis, reviewed as faithfully executed) | bears on |
|---|---|---|
| Resonance-line **width keeps tracking concentration where intensity saturates** | K I 766.49: above 4 wt% K2O, FWHM `r = 0.82` vs net peak `0.66` (Steiger `Z = 4.0`); Na I 589.00 above 5 wt% Na2O: peak slope collapses to 1.5 %/wt%, FWHM keeps 8.6 %/wt%; Ca I 422.67 above 15 wt% CaO: peak `ρ = −0.20` (turnover), FWHM `ρ = +0.59` | C1's width channel is real on this data |
| **Doublet ratio as a calibration-free optical-depth observable** | Ca II 393.37/396.85 falls from 1.71 (<2 wt% CaO) to 1.39 (>10 wt%), `ρ = −0.78`, distance-invariant; Mg II 279.55/280.27 saturates already below 2 wt% MgO | the self-absorption gate every candidate needs; matches `CurveOfGrowth`'s source-free ratio |
| **Dimensionless observables are distance-invariant**, raw intensities are not | decay exponent with standoff `−0.01` for shape/width features vs `−0.53` for spectrometer sums; zero-shot transfer 1.5 m → 4.25 m: FeOT `R²` from `−7.05` (raw) to `+0.29` (dimensionless) | the `F`-independence claim of §1, measured |
| **Shape factor is not a generic self-absorption classifier** | works for Mg I 285.21 (ROC-AUC 0.89) but inverts for Ca II 393.37 (0.14); Fe lines show mixed signs | C1's "shape" proxy is line-specific; use widths and doublet ratios, not shape |
| **Instrument broadening dominates widths** for Si I 288, Fe I 404 at geological concentrations | width flat across bulk oxide levels; net area still shows saturating-plateau behaviour (ΔBIC +74 Si, +362 Ca) | C1 needs resolved lines: alkalis and Ca yes, Si/Fe no at this resolution |
| **Peak-over-continuum is worse than net area** | continuum scaling differs between the three spectrometers; `log(area ratio)` Na/K predicts `log(Na2O/K2O)` with `r = 0.89`, peak/continuum ratio `r = −0.46` | continuum-normalized observables are not a free lunch |

Two cautions. The table was built for exploration, not measurement: line windows are fixed, blends
are not handled, and widths at the instrument limit are noisy. And AutoDiscovery's hypotheses are
generated and judged by a model; the code was reviewed as faithful to each plan, but no result here
has been reproduced independently. The three confirmations are consistent with each other and with
the physics in C1, which is why they are worth a proper test on the companion's certified alloy
spectra, where the resonance lines are far thicker than in geological standards.

### 5.4 Net change to the recommendation

C3 stays first, now explicitly as "the residual and the identifiability of Abbass-style neutrality
closure with a Stark density", with the density window as its precondition. C1 gains an empirical
leg: on real calibrated data the width channel works where intensities fail, the doublet ratio
supplies the gate, and dimensionless observables transfer across geometry. Its first test should be
widths and equivalent widths of the alkali and Ca resonance lines against certified values, with
the wing-dominance classifier computed alongside, before any alloy work.

## Appendix A. Search record (so the negatives are auditable)

Update 2026-09-21 (after `asta login`): the Asta Paper Finder agent (`asta literature interactive`,
criteria extraction + verification loop) was run on C3, C1 and C4 with thread directories under
`.asta/literature/threads/2026-09-21-*` (gitignored; per-criterion relevance judgements kept there);
three `asta literature find --mode diligent` one-shot searches returned only generic CF-LIBS
application papers (max relevance 0.64, no criterion satisfied). The Theorizer
(`asta generate-theories literature-theory-generation`, novelty-focused, 40 papers) and an
AutoDiscovery run on a reduced SuperCam calibration table were launched the same day; their
outputs are reported in §5 once complete.

Tools that worked (2026-09-20 sweep): NotebookLM notebook "CF-LIBS: Calibration-Free LIBS" (75 sources), three
queries, the third restricted to peer-reviewed sources; web search (nine queries); publisher /
PubMed / OSTI / ADS pages for the citations above. Tools that did not: the Asta CLI (`asta papers
snippet-search`) failed with `Token refresh failed: invalid_grant` and needs `asta login`; the
anonymous Semantic Scholar snippet API returned HTTP 429 on all ten queries. The notebook's
answers cite the owner's own generated notes ("Advanced Computational Techniques Literature Review
(2025)", "ALIAS Performance Diagnostic", "Asta Research: ChemCam…") alongside papers; those were
excluded from the citations above.

Queries (verbatim, minus tool syntax): equivalent width / curve of growth composition LIBS;
Ladenburg–Reiche damping wing LIBS quantification; calibration-free LIBS without transition
probabilities; Kirchhoff law emission/absorption temperature laser plasma; column density
resonance lines composition; time-resolved cooling composition; continuum-normalized absolute
density; collisional-radiative CF-LIBS; Bayesian full-spectrum inversion; molecular dissociation
equilibrium stoichiometry; blackbody-radiation-referenced self-absorption (Li 2019); column-density
Saha–Boltzmann (Lin 2024); Cristoforetti & Tognoni 2013 columnar density; two-colour pyrometry of
optically thick line cores; closure versus charge neutrality / undetected element; time-integrated
cooling model / temperature-distribution / Boltzmann-plot curvature. Notebook queries: methods
without Boltzmann `T` and without excited-state `A`; `F`- and `T`-independent observables and the
limits of curves of growth, time-integrated spectra and single-zone plasmas; neutrality versus
closure, Tognoni 2010 on `n_e` consistency, joint `T`-distribution fits (peer-reviewed only).

Scratch copies of the raw answers: session scratchpad `novel/nlm1.json`, `nlm2.json`, `nlm3.json`.
