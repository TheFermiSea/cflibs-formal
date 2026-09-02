# CONTEXT — cflibs-formal

A machine-checked **specification** of calibration-free Laser-Induced Breakdown
Spectroscopy (CF-LIBS) in Lean 4 + mathlib: the forward model (LTE plasma line
emission), the inverse problem (composition recovery), and the identifiability /
reliability theorems that say *when and why* the inversion is well-posed.

The goal is **rigor, not numerical accuracy.** This is a verified companion to a numerical
CF-LIBS pipeline: it establishes which guarantees hold under explicit hypotheses. Real-data
accuracy is limited by atomic data and plasma modeling, not by this spec — so we invest in
provable structure (soundness, identifiability, error bounds), not curve-fitting.

## Domain language

- **LTE plasma** — local thermodynamic equilibrium; level populations follow a Boltzmann
  distribution at a single temperature `T`, ionization follows Saha.
- **Boltzmann factor / partition function** — `boltzmannFactor kB T E = exp(-E/(kB·T))`;
  `partitionFunction = Σ_k g_k · boltzmannFactor` (a finite sum over levels).
- **Saha factor** — the ionization-equilibrium ratio `n_{z+1}·n_e/n_z = S(T)` with the
  3/2 thermal-de-Broglie power and `exp(-χ/(kB·T))`.
- **Forward map (`lineIntensity`)** — optically-thin emission `I = Fcal · A_k · population`,
  with a **per-line** Einstein coefficient `A : ι → ℝ`.
- **Boltzmann plot** — `log(I/(g_k A_k)) = log(Fcal·N/U) − E_k/(kB·T)`; slope → `T`,
  intercept → species concentration. The workhorse identity everything rests on. Two equivalent
  conventions are formalized and proven to share the slope `−1/(kB·T)`: the photon-rate /
  `Fcal`-absorbed ordinate `log(I/(gA))` (Ciucci 1999; canonical `ForwardMap`) and the
  energy/wavelength ordinate `log(I·λ/(gA))` (Thouin et al. 2023; `ForwardMapEnergy`), where the
  per-line `hc/4πλ_k` is made explicit (closes a literature-review false-positive that the
  reduced ordinate "omits λ").
- **Composition / closure** — `C_s = N_s / Σ_t N_t`; `Σ C_s = 1`; the vector lies in the
  probability simplex. Closure fixes the absolute scale (the *calibration-free* property).
- **Self-absorption / optical depth / curve of growth** — `I_meas = I_thin · SA(τ)`,
  `SA(τ) = (1−e^{−τ})/τ ∈ (0,1]`; derived from a radiative-transfer slab `S·(1−e^{−τ})`.
- **Identifiability** — injectivity of the forward map: equal observations (under explicit
  nondegeneracy) force equal `(T, n_e, composition)`.

## Architecture — two tracks over a shared core

Import DAG is **acyclic** (Lean-guaranteed); `Boltzmann` is the base of the forward/inverse chain,
with `SpatialForward` and `Dimensions` as independent `Mathlib`-only modules. Every core
definition is defined once and reused verbatim, and every module imports only `Mathlib` /
`CflibsFormal` (checked by `scripts/stats.sh`).

- **Shared core** (`namespace CflibsFormal`): `Boltzmann`, `Saha`, `Closure`, `ForwardMap`,
  `ForwardMapEnergy` (energy/wavelength forward sibling: explicit `hc/4πλ`, proven to reduce to
  the photon-rate `ForwardMap` and to share the Boltzmann-plot slope),
  `OLS` (the pure-algebra ordinary-least-squares foundation — `mean`, `olsSlope`, the centering
  identities, and the noise gain `∑wₖ²=1/SS_E` — the single core home reused by `Alt/LeastSquares`,
  `ErrorBudget`, and `Alt/OLSVariance`/`Alt/GaussMarkov`; a `Mathlib`-only base module),
  `LeastSquaresFit` (the least-squares/projection inverse for **noisy off-manifold** data on top
  of `OLS`: the normal equations, the projection identity `rss_decomposition`, global minimality
  `ols_minimizes_rss`, a residual feasibility predicate `LeastSquaresFeasible`, and the
  on-manifold bridge `ols_minimizer_eq_inverse` where the projection inverse meets the exact-fit
  inverse — a `Mathlib`-only base module),
  `Identifiability`, `MultiSpecies`, `SelfAbsorption`, `Robustness`, `Inverse`
  (algorithm-agnostic estimator framework), `CompositionRobustness`,
  `CompositionIdentifiability`, `SelfAbsorptionInverse`, `SahaInverse`, `CurveOfGrowth`,
  `JointIdentifiability` (two-line observation map — `(T, composition)` jointly identifiable
  from the observations alone, discharging `general_identifiability`'s assumed-ratio caveat),
  `SahaStability` (Lipschitz/relative-error transfer of the Saha n_e diagnostic),
  `SahaEquilibrium` (the reduced Saha–closure–charge self-consistency core: unique existence
  of the coupled `(n_e, N₀, N₁)` state at fixed T),
  `AtomicDataPerturbation` (the wrong-atomic-data aliasing identity + relative-error bounds
  through to composition — the accuracy-floor channel),
  `PartitionLipschitz` (the `U_s(T)` temperature-sensitivity leg: two-point and Lipschitz
  partition-function bounds with explicit constants),
  `NonlinearLeastSquares` (the nonlinear joint `(T, N)` fit: EVT existence of a minimizer on a
  compact physical box for any off-manifold observation, plus the VARPRO structure — the
  N-section is exactly quadratic with a unique profiled-density minimizer, so the 2-D fit is
  provably 1-D in `T` — the nonlinear sibling of `LeastSquaresFit`),
  `NoiseToComposition` (the composed end-to-end error chain: per-line ordinate noise ⇒
  temperature gap ⇒ recovered-density error ⇒ composition error, assembled from `ErrorBudget`,
  `AtomicDataPerturbation`, and `CompositionRobustness`),
  `EquivalentWidth` (the *integrated* curve of growth — equivalent width `W(τ)=∫(1−e^{−τφ})`:
  the slope-1 saturation bound `W ≤ τ·∫φ`, monotonicity, and the flat-profile slab identity
  `W = 1−e^{−τ}`; the slope-½ damping wing is honestly out of scope),
  `StarkBroadening` (independent electron-density diagnostic + McWhirter LTE bound),
  `SpatialForward` (discrete onion-peeling Abel inversion — relaxes single-zone homogeneity),
  `LineBroadening` (toward real line profiles: thermal Doppler width + the Gaussian-quadrature
  width budget / deconvolution that feeds the Stark diagnostic),
  `VoigtWidth` (the Olivero–Longbothum Voigt FWHM combination of the Gaussian and Lorentzian widths
  — the piece LineBroadening left out; honest exact-Gaussian-limit vs approximate-Lorentzian-limit),
  `SelfReversal` (the two-zone hot-core/cool-shell model and the central-dip mechanism — the
  non-isothermal effect single-zone `SelfAbsorption` cannot produce),
  `StarkShift` (the Stark line-SHIFT density diagnostic — signed companion to the Stark width, with
  honest sign-conditional monotonicity and the n_e-cancelling shift/width ratio),
  `HydrogenStark` (the hydrogen Balmer-line n_e diagnostic — the *most common* LIBS technique:
  linear Stark effect, `Δλ ∝ n_e^(2/3)` / `n_e ∝ Δλ^(3/2)`, distinct from the non-hydrogenic
  *linear-in-n_e* `StarkBroadening`),
  `PartialLTE` (relaxes LTE: the McWhirter density bound inverted to the thermalization-limit energy
  `E*`, with `mcWhirter ⟺ thermalized` — which levels are collisionally thermalized),
  `Continuum` (the free-free + free-bound background: emissivity scaling, exact baseline-subtraction
  recovery, and the line-to-continuum thermometer — monotone only in the `E_k ≥ hc/λ` regime),
  `Dimensions` (additive dimensional-analysis layer: machine-checks homogeneity of the forward
  relations; does not touch the dimensionless core),
  `ErrorBudget` (the deterministic error-propagation chain — ε → OLS slope → temperature →
  composition — that turns the pipeline's empirical reliability thresholds, `min_energy_spread`
  and `min_snr`, into proven *sufficient-condition* corollaries; builds on the core `OLS`
  foundation, honest that the line-count law is statistical, not deterministic),
  `MatrixEffects` (matrix effects as explicit parameters: the recovered SUBcomposition — pairwise
  ratios among the detected species `D` — is matrix-INDEPENDENT (`recoveredComposition_ratio_`
  `matrix_invariant`, Aitchison coherence) while absolute fractions inflate by `1/(1−m)` ≥ 1
  (`composition_le_recoveredComposition`); plus an intensity bridge from the forward map and the
  Saha ionization-suppression channel (`sahaIonDensity_antitone`); honest that this is the
  completeness/ablation channels with `n`/`T` fixed, NOT unconditional matrix-independence),
  `TemporalEvolution` (time-resolved / gate-delayed recovery: the plasma state `(T(t), n_e(t), ρ(t))`
  drifts between gates, yet the recovery is SOUND at each gate — `gateSahaTotalDensity_eq` shows the
  electron density `n_e(t)` cancels via the two-stage Saha sum, and the shared dilution `ρ(t)` cancels
  in closure; honest that the cross-gate invariance is a thin corollary of the stoichiometric-ablation
  `hDilute`, a COMPLEMENTARY temporal analogue of — not stronger than — `classic_calibration_free`,
  with a compiling non-vacuity witness and the McWhirter LTE window as the applicability bound).
- **Classic algorithm** (`namespace CflibsFormal.Classic`): `Classic` — the textbook
  calibration-free algorithm, `classic_sound` (composition leg given `T`).
- **Alternative estimators** (`namespace CflibsFormal.Alt`): `Alt/CSigma` (single
  master-line normalization plot), `Alt/CSigmaCurveOfGrowth` (the self-absorption DROOP on the
  Cσ graph: optically-thick lines sit below the universal line by `ln SA(τ)`, strictly monotone
  in the optical depth `τ = N·σ_ℓ·ℓ` — the cross-section `σ` weighting; the genuinely-new analytic
  piece is `selfAbsorptionFactor_strictAntiOn`; honest REDUCED flat-profile/escape-factor scope, the
  profile-integrated slope-½ wing out), `Alt/SelfAbsorbed` (self-absorption-corrected),
  `Alt/LeastSquares` (multi-line OLS Boltzmann plot). Each is proven sound and related back
  to the classic estimator. `Alt/OLSVariance` closes the **statistical** layer the deterministic
  `ErrorBudget` chain deferred: on `Mathlib`'s probability stack (a zero-mean, homoscedastic,
  independent noise model) it proves OLS-slope unbiasedness `𝔼[β̂]=β` and the Gauss–Markov variance
  law `Var(β̂)=σ²/SS_E` (`olsSlope_variance_eq`, via `OLS.olsSlope_noise_gain`), hence the
  `card`-free "more lines / more spread ⇒ less variance" statement (`olsSlope_variance_antitone`)
  the deterministic worst case could not give. `Alt/GaussMarkov` then proves the **optimality**
  layer — OLS is the Best Linear Unbiased Estimator of the slope (`ols_is_blue : Var(β̂) ≤ Var(Tₐ)`
  for any linear unbiased `Tₐ`), via the unbiasedness `iff` (`linEstimator_unbiased_iff`) and the
  deterministic Pythagorean core `∑wₖ² ≤ ∑aₖ²` (`weight_sq_ge_noiseGain`). Honest scope: independence
  is a reduction from the classical uncorrelatedness hypothesis (mathlib's `IndepFun.variance_sum`),
  and optimality is "minimum-variance among linear unbiased estimators" only (not Cramér–Rao).

New alternative methods go under `CflibsFormal.Alt`; shared physics/inverse machinery in
`CflibsFormal`. Literature-facing modules carry a `## Literature` docstring paragraph citing
the peer-reviewed primary sources.

## Design decisions

1. **Dimensionless (bare `ℝ`) core + an additive dimensional layer.** Energies, temperatures,
   densities, intensities are all `ℝ`; dimensional consistency in the inverse-problem core is
   *human discipline*, not type-enforced, because those theorems are dimensionally trivial and a
   unit-carrying type would obstruct `field_simp`/`ring`/`log`/`exp` for no diagnostic gain. To
   close the discipline gap *without* paying that cost, `Dimensions.lean` adds an **additive**
   dimensional-analysis layer (a `Dimension` exponent-vector group over `ℚ`) that machine-checks
   the **homogeneity** of the forward relations — `E/(k_B T)` dimensionless, the thermal bracket
   `L⁻²`, the Saha factor `L⁻³` = number density, the Saha law homogeneous — leaving the
   dimensionless core untouched. (Cued by physlib's `Units`/`Dimension` and Lean4PHYS; see #2.)

2. **mathlib-only; physlib is an upstream target, not a dependency (re-confirmed 2026-06-23).**
   Current `gh`-verified state of `leanprover-community/physlib` (renamed PhysLean + Lean-QuantumInfo):
   actively maintained but pinned to Lean **v4.30.0** (we were v4.31.0 — depending would have
   forced a downgrade; as of 2026-09-02 physlib is on v4.33.0 and we are on v4.33.1, see
   `docs/upstream-physlib-plan.md`); its statistical mechanics is **measure-theoretic and unit-aware** (even
   `CanonicalEnsemble/Finite` carries `MeasurableSpace` + a `Temperature` units type), heavier than
   our needs for the dimensionally-trivial inverse-problem layer; and it has `StatisticalMechanics` /
   `Thermodynamics` / `Units` / `translational` physics **but still no Saha/ionization** (0 code
   hits). The relationship is therefore *inverted*: physlib has Boltzmann/canonical-ensemble but no
   ionization equilibrium, so our Saha–Boltzmann layer is a clean *additive* contribution to
   upstream — **eventually, not now**. The deliberate plan (scope, form, governance under physlib's
   AI policy, triggers, steps) is `docs/upstream-physlib-plan.md`. The one genuine *cue* taken from
   physlib/Lean4PHYS — units/dimensional rigor — is implemented as the additive `Dimensions.lean`
   layer (see #1), without the dependency.

3. **Axiom-cleanliness is a hard invariant.** Every declaration must depend only on
   `{propext, Classical.choice, Quot.sound}`. Enforced automatically by `tools/` (vendored
   `leanprover-community/axiom-audit`): `lake exe axiom-audit --root CflibsFormal`, wired into
   CI. This catches `sorry`/`admit` (`sorryAx`), `native_decide`, and home-rolled axioms
   reaching in through imports — which `grep` cannot.

4. **Honest scoping.** A docstring must not claim more than its theorem proves. (An
   adversarial validation pass found and fixed several over-claims — e.g. a "cross-method
   agreement" that was really a shared-soundness corollary, a soundness theorem branded
   "end-to-end" when temperature was assumed.) A green proof of the wrong statement is
   worthless; statements are audited, not just compiled.

5. **Modeling scope.** Baseline assumptions are LTE, a single-zone homogeneous plasma, and
   optically-thin emission — all explicit, and progressively relaxed: self-absorption is
   modeled separately (`SelfAbsorption`, `SelfAbsorptionInverse`, `CurveOfGrowth`, with the
   precise recover/defeat boundary characterized, plus the non-isothermal two-zone **self-reversal**
   dip in `SelfReversal`); spatial inhomogeneity is modeled via the
   **discrete onion-peeling Abel inversion** (`SpatialForward`, single-zone = the N=1 case;
   the continuous Abel integral inverse is explicitly out of scope); the LTE assumption
   itself gets independent electron-density checks (`StarkBroadening`: non-hydrogenic Stark width,
   linear in nₑ, vs. Saha nₑ, McWhirter bound; `HydrogenStark`: the common hydrogen Balmer-line
   diagnostic, nₑ ∝ Δλ^(3/2)) and a principled relaxation (`PartialLTE`: the McWhirter density bound
   inverted to the thermalization-limit energy `E*` — which levels collisionally thermalize);
   the point-line / known-width idealization is relaxed toward real
   **line profiles** (`LineBroadening`: thermal Doppler width + the exact Gaussian-quadrature
   width budget and deconvolution that exposes the Stark Lorentzian; `VoigtWidth`: the
   Olivero–Longbothum Voigt FWHM combination of those Gaussian and Lorentzian widths — the full
   Voigt convolution *profile* stays out of scope); and the optically-thin *line-only* forward
   model is extended with the
   **continuum background** (`Continuum`: free-free + free-bound emissivity scaling, exact
   baseline-subtraction recovery, and the line-to-continuum thermometer).

## Verification discipline

Gates, all required before trusting a result:
1. **Green build** — `lake build` (clean re-elaboration from source).
2. **Axiom-clean** — `lake exe axiom-audit --root CflibsFormal` (exit 0).
3. **Style/structure lint** — `lake exe runLinter CflibsFormal` (mathlib/batteries env linters:
   docBlame, simpNF, unusedArguments, …) — catches missing docstrings, unused hypotheses, etc.
4. **Import hygiene** — `scripts/stats.sh` (every module imports only `Mathlib` / `CflibsFormal`,
   no surprise external deps; acyclicity is guaranteed by the build). Also prints the base modules
   and derived declaration counts.
5. **Statement audit** — adversarial review that the *statement* faithfully encodes the
   intended physics (non-vacuous, non-trivial, non-tautological, honestly scoped).

Gates 1–4 are automated in CI (`.github/workflows/lean_action_ci.yml`).

## Status

72 modules, 641 axiom-clean named results (theorem/lemma) + 200 defs (counts via `scripts/stats.sh`).
CI gates: axiom-cleanliness (`tools/`), style/structure lint (`runLinter`), docs-sync + scope-tag
completeness (`scripts/gen-docs.sh`), import-hygiene (`scripts/stats.sh`), and the epistemic-drift
scope-consistency guard (`scripts/check-scope-consistency.sh`).
The original **~186-result corpus** was adversarially validated (verdict: sound-with-minor-fixes,
zero blockers; all findings fixed) and given a whole-corpus **literature-validity audit**
(`reviews/literature-validity-audit.md`): 69 faithful / 33 reduced / 5 idealized / 78 pure-math,
**0 divergent, 0 unverified citations, 1 minor docstring over-reach (fixed)**. Subsequent additions
to the current 641-result corpus (the frontier and architectural-review deepening sweeps) are
individually author-plus-independent-audit reviewed rather than re-covered by that one-time audit.
A numerical regression oracle (`oracle/`) bridges the verified spec to the numerical pipeline
(CF-LIBS-improved) — multi-element + the alternative estimators (OLS, self-absorption, Saha
nₑ) + the derived error-budget thresholds, each fixture instantiating a proven theorem.

## Metrology & traceability

"Calibration-free" is a *metrological traceability claim*. Convention lock: `docs/conventions.md`.

**The measurand, per module.** The VIM (JCGM 200) wants the quantity *intended* to be measured,
specified finely enough that its value is unique to the required uncertainty. "Composition" is not a
measurand.

| module | measurand |
| --- | --- |
| `Classic`, `CompositionIdentifiability` | number fraction `C_s = N_s/∑_t N_t` of species `s` in the single homogeneous emitting zone, at the state `(T, n_e)` the gate samples |
| `Boltzmann`, `ForwardMap` | the *excitation* temperature of one species' LTE level distribution over the fitted line set — not a kinetic or ionization temperature |
| `Saha`, `StarkBroadening`, `HydrogenStark` | `n_e` in that zone, from a stage ratio (Saha) or a line width (Stark) — two different measurands, coinciding only under LTE |
| `TemporalEvolution` | `C_s` **at gate delay `t`**, of the diluted state `ρ(t)·N₀`; soundness is per-gate, cross-gate invariance a corollary of `hDilute`, not evidence for it |
| `SpatialForward` | the per-shell emissivity `ε(r_j)` of `N` shells; single-zone is the `N = 1` case |
| `MatrixEffects` | the **sub**composition over the detected set `D`; absolute fractions inflate by `1/(1−m)` |

The last three rows carry the content: the single-zone measurand is a spatial *and* temporal average
over a plasma that is neither homogeneous nor stationary. That averaging is definitional, not
instrumental.

**Where the chain terminates: atomic data, not SI.** `Classic.classic_calibration_free` proves the
instrument constant `Fcal` cancels under closure, for *all* data — so no matrix-matched standard and
no SI-traceable radiometric scale enters. What replaces them is the tabulated `(g_k, A_ki, E_k)` and
`U_s(T)`, reaching every recovered density through `AtomicDataPerturbation.responseFactor`
`ρ = g_u·A_u·exp(−E_u/k_BT)/U(T)` — literature values with their own (often unstated) uncertainty
and no unbroken chain of calibrations to the SI. Plainly: **results here are traceable to
atomic-data tabulations, not to the SI.** "Calibration-free" means free of a calibration *standard*,
not free of external reference data.

**Identifiability = absence of definitional uncertainty.** The VIM's *definitional uncertainty* —
the component due to the finite detail of the measurand's definition — is a floor: an ambiguous
measurand specification cannot be rescued by better instrumentation alone. The identifiability
theorems say that floor is zero under stated nondegeneracy:
`Identifiability.temperature_identifiability` (distinct upper-level energies ⇒ `T` unique),
`JointIdentifiability.joint_identifiability` and
`CompositionIdentifiability.compositionIdentifiable` (equal observations force equal `(T, C)`, no
assumed ratio — the state-to-data map is injective). The converses are the *positive* case:
`temperature_degeneracy` / `temperature_not_identifiable_of_degenerate` exhibit two positive
temperatures with identical observations, and `temperature_ratio_near_degenerate` bounds the
approach (signal `O(ΔE)`), making the runtime "small `ΔE` ⇒ refuse" gate metrologically correct
rather than merely cautious. Caveat: these are *conditional* zero-floor results, for the measurand
as the model defines it. Real definitional uncertainty lives in the gap between that measurand and
the plasma — the last rows above — and no injectivity theorem touches it.

**The bubble under the carpet.** Closure does not eliminate the calibration constant's uncertainty;
it **relocates** it. `classic_calibration_free` is the elimination; `classicDensity_aliasing` is
where it reappears — inverting with wrong atomic data returns *exactly* `N̂ = N·ρ_true/ρ_wrong`. The
budget line that read `Fcal` now reads `(g, A, E, U)`, sized by `classicDensity_aliasing_error`
(`|N̂−N| ≤ N·δ/(1−δ)`), `..._error_channels`, `..._error_energy`, and carried to composition by
`classicComposition_atomicData_error`; `classicDensity_temperature_aliasing` is the same shape for a
wrong recovered `T`. `AtomicDataPerturbation` proves this relocation but never names it: **closure
buys standard-independence at the price of an atomic-data-dominated budget, and
`classicDensity_aliasing` is the exchange rate.** Hence the already-enforced hard refusal on missing
atomic data — the bias is finite, plausible, and has no self-diagnosing signature.

**Deterministic worst-case, not linearized GUM propagation — deliberate.** JCGM 100 (GUM)
propagates `u_c² = ∑(∂f/∂x_i)²u_i²`; JCGM 101 directs abandoning that when the model is
significantly non-linear or the output far from normal. CF-LIBS is the textbook instance — `T`
enters as `exp(−E/k_BT)`, the inverse is a log-slope, Saha carries `T^{3/2}·exp(−χ/k_BT)`, and
composition is a ratio of those; a sensitivity-coefficient table would approximate an approximation.
`ErrorBudget` instead propagates deterministic worst-case envelopes — `olsSlope_stable_l1` (sharp
ℓ¹), `olsSlope_stable_l2_sq` (Cauchy–Schwarz), the exact `temp_rel_error_eq`, and the inverted
thresholds `requiredEnergySpread_sufficient` / `maxPerLineError_sufficient`. No linearization is
taken anywhere: the reductions live in the hypotheses (lumped `δ`), never in the algebra. **This is
a strength and should be presented as one.** The statistical layer stays separate —
`Alt/OLSVariance` (`Var β̂ = σ²/SS_E`), `Alt/GaussMarkov` (BLUE), `Alt/StochasticBudget`
(Chebyshev, sub-Gaussian tails) — and `olsSlope_chebyshev` is distribution-free, so it is *not* a
coverage factor: a GUM expanded uncertainty `U = k·u_c` with `k = 2` presumes approximate normality.
Do not print a `k` beside it. **Rule: never mix worst-case and RSS philosophies in one table.** An
ℓ¹ envelope from `olsSlope_stable_l1` and a `σ/√SS_E` from `olsSlope_variance_eq` answer different
questions (guaranteed bound vs. standard deviation); summing or row-comparing them yields a number
that is neither. One philosophy per table, labelled.
