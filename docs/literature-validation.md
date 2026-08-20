# Full-codebase literature validation — 2026-07-09

> **FROZEN SNAPSHOT (2026-07-09).** This audit covers the then-48-module corpus (412 named
> results); it is NOT updated to the current 64-module state. Modules added since are covered by
> per-result author-plus-independent-audit review (see `CONTEXT.md` Status), not by this one-time
> audit.

*Machine-assisted audit of all 48 modules (412 named results) against the published CF-LIBS
literature. Eight domain validators (independent LLM agents, read-only) each deep-checked every
physics-bearing (EXACT / REDUCED / APPROXIMATION) result in their module group — statement
fidelity, attribution, scope-tag grade, sign/exponent/functional form — grounded in the
NotebookLM source notebooks (the repo-citation collection and the 75-source CF-LIBS corpus) and
targeted literature search. Every critical/major finding was slated for independent adversarial
verification; **none was needed — zero critical, zero major findings across the entire
codebase.** 21 minor/info observations were triaged by the lead; the accepted fixes are listed
below and landed in the same commit as this report.*

## Verdict summary

| Group | Modules | Deep-checked | Verdict |
|---|---|---|---|
| L1 Core CF-LIBS (forward model, Boltzmann plot, closure, classic inversion) | 8 | 31 | **FAITHFUL** |
| L2 Saha equilibrium (ionization balance, T/n_e coupling, LTE) | 6 | 24 | **FAITHFUL** |
| L3 OLS statistics & error budgets | 7 | 32 | **FAITHFUL** |
| L4 Alternative estimators (Cσ / Saha–Boltzmann master line, GLS) | 5 | 34 | **FAITHFUL** |
| L5 Self-absorption & curve of growth | 6 | 34 | **FAITHFUL** |
| L6 Line broadening, Stark, continuum | 6 | 13 | **FAITHFUL** |
| L7 Perturbations, matrix effects, dynamics, outer loop | 7 | 36 | **FAITHFUL** |
| L8 Pure-math substrate + repo-wide citation/tag hygiene | 3 + full TSV | 50 + 399 rows | ISSUES-FOUND (hygiene only) |

**Findings: 0 critical · 0 major · 7 minor · 14 info.** No formalized statement was found to
contradict the physics it cites. No sign, exponent, or functional-form error was found anywhere.

## Strongest explicit confirmations (statement ↔ published equation)

- **Saha–Eggert** (`Saha.lean`): leading factor 2 (electron spin degeneracy), thermal bracket
  `(2π mₑ k_B T/h²)^{3/2}`, ratio orientation `U_{z+1}/U_z`, `exp(−χ/k_B T)` — exact match to
  the Griem form; `log_sahaFactor` affine in `1/(k_B T)` with slope `−χ`.
- **Boltzmann plot** (`ForwardMap`/`Boltzmann`): ordinate `ln(I/(g A))`, slope `−1/(k_B T)`,
  two-line temperature — verbatim Ciucci 1999 (photon-rate convention confirmed against the
  founding paper); the wavelength ordinate `ln(Iλ/(gA))` bridge matches Aragón & Aguilera 2008
  with the `hc/4πλ` factors cancelling exactly.
- **Cσ master line** (`Alt/CSigma`): ionic-stage abscissa shift `+χ` (ADDED) and Saha-bracket
  ordinate correction (SUBTRACTED), both stages on slope `−1/(k_B T)` — exactly the verified
  Aguilera & Aragón 2007 / Aragón & Aguilera 2014 construction; `sahaBracketLog` is the
  canonical bracket `ln(2(2π mₑ k_B T/h²)^{3/2}/n_e)`.
- **Self-absorption** (`SelfAbsorption`): `SA(τ) = (1−e^{−τ})/τ`, slab solution `S·(1−e^{−τ})`,
  strict downward bias — match the literature escape-factor formalism (Aberkane 2020 review
  quoting the canonical equations; Gornushkin 1999; Bulajic 2002).
- **McWhirter** (`PartialLTE`): prefactor 1.6·10¹² and the `√T·(ΔE)³` shape — verbatim.
- **Voigt FWHM** (`VoigtWidth`): Olivero–Longbothum 1977 coefficients 0.5346 / 0.2166 — exact.
- **Stark** (`StarkBroadening`/`StarkShift`): width `Δλ = 2w·(n_e/n_ref)` vs *unfactored* signed
  shift `d = d_ref·(n_e/n_ref)` — the width/shift factor-of-2 distinction correctly maintained.
- **Gauss–Markov** (`Alt/OLSVariance`/`Alt/GaussMarkov`): `Var(β̂) = σ²/SS_E` and BLUE
  optimality — the classical laws, with the deterministic/statistical layers correctly
  separated.
- **Dimensions.lean**: every rational-exponent dimension vector hand-verified against SI;
  SI→CGS conversion factors exact (1 J = 10⁷ erg, m⁻³ = 10⁻⁶ cm⁻³).

## Accepted fixes (landed with this report)

1. **`SahaStability` header staleness** (minor, L2): the "T-channel monotonicity — STILL OPEN"
   bullet predated the Phase-2 landing of `sahaFactor_strictMonoOn_temp`; rewritten to state
   the closure under the disclosed level-ceiling hypothesis `∀ k, EZ k ≤ χ`.
2. **`Alt/CSigma` intro staleness** (minor, L4): the intro called the universal-line collapse
   an unproved follow-on, but the module proves it (`csigma_universal_line` et al.); also
   dropped the "σ (cross-section)" conflation the sibling module explicitly disclaims.
3. **`Inverse.rawCompositionEstimator_sound`** (minor, L1): retagged APPROXIMATION → REDUCED —
   it is an exact conditional identity under a disclosed model restriction, which is what
   REDUCED denotes; APPROXIMATION denotes inequality/asymptotic stand-ins.
4. **`NonlinearLeastSquares.profiledResidual_not_injective_m3`** (minor, L8): retagged
   EXACT/Ciucci 1999 → PURE-MATH/— — a constructed counterexample makes no positive physics
   claim attributable to Ciucci.
5. **`EquivalentWidth.equivWidth_lorentzian_sqrt_sharp`** (minor, L5): citation
   Gornushkin 1999 → **Ladenburg–Reiche 1913** — the sharp `W/√τ → 2` constant is the classical
   absorption-theory result; Gornushkin 1999 remains the citation for the LIBS
   intensity-curve-of-growth results it actually covers.
6. **`OuterLoopModelB` naming** (minor, L7): docstring now states "Model B" is the repo's own
   Frontier-04 designation (defined by contrast with the refuted degenerate Model A), not a
   name used by Aguilera & Aragón 2007; noted the spine is agnostic to the `n_e` source
   (Saha ratio here; a Stark leg would instantiate equally well).
7. **`SelfAbsorption` bias bullet** (info, L5): qualified — the downward composition bias is
   for *differentially* self-absorbed species; a factor common to all species cancels in the
   scale-invariant closure (see `SelfAbsorptionInverse`).
8. **VARPRO attribution** (minor, L8): the `NonlinearLeastSquares` section header now names
   Golub & Pereyra 1973 as the origin of variable projection.

## Noted, no change required (convention-consistent or already disclosed)

- **EXACT on rigorous inequalities** (e.g. `relDensity_le`, `equivWidth_le_thin`,
  `stark_saha_lte_consistent`): repo-wide, EXACT denotes *model faithfulness* (no physical
  approximation), not "is an equality" — the established vocabulary, applied consistently.
- **Photon-rate (REDUCED) vs wavelength (EXACT) forward-model twins**: deliberate and
  documented (per-line λ folded into scalar `Fcal` is a genuine reduction).
- **Sign-normalized slope hypotheses** (`olsSlope = 1/(k_B T)` with the physical slope
  negative): disclosed in the docstrings and immaterial (only `|Δβ|` enters the bounds).
- **Aitken 1935 vs Gauss–Markov granularity** on the variance rows: module docstrings already
  carry the fuller attribution.
- **`deconvolveGaussian_quadrature` → Aragón & Aguilera 2008**: attribution to the LIBS
  deconvolution *practice* is defensible as framed.

## Citation-whitelist clarification (L8)

Five citation strings in `docs/scope-tags.tsv` fall outside the 16-source core whitelist but
are **real, topically-correct, previously-vetted sources** (documented in
`reviews/literature-validity-audit.md`): Aitchison 1986 (compositional data / log-ratio
invariance), Cowan–Dieke 1948 (self-reversal), Parigger 2016 (spatial/Abel inversion),
Gigosos 2003 (hydrogen Stark simulations), Cremers & Radziemski 2013 (LIBS handbook).
Ladenburg–Reiche 1913 (fix 5 above) joins this vetted extension set. These are
whitelist-*documentation* gaps, not misattributions; the sanctioned set is: the 16-source core
+ these six vetted extensions.

---

*Method note: validators were instructed with explicit false-positive discipline — the repo's
dimensionless conventions, scope-tag vocabulary, and disclosed REDUCED simplifications are
correct behavior, not defects — and each ran against the primary sources, not from memory.
The zero-critical/zero-major outcome means the adversarial-verification stage (independent
refutation of each serious finding) had no work to do.*
