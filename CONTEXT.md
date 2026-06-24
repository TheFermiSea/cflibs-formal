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
  energy/wavelength ordinate `log(I·λ/(gA))` (Khelladi 2023; `ForwardMapEnergy`), where the
  per-line `hc/4πλ_k` is made explicit (closes a literature-review false-positive that the
  reduced ordinate "omits λ").
- **Composition / closure** — `C_s = N_s / Σ_t N_t`; `Σ C_s = 1`; the vector lies in the
  probability simplex. Closure fixes the absolute scale (the *calibration-free* property).
- **Self-absorption / optical depth / curve of growth** — `I_meas = I_thin · SA(τ)`,
  `SA(τ) = (1−e^{−τ})/τ ∈ (0,1]`; derived from a radiative-transfer slab `S·(1−e^{−τ})`.
- **Identifiability** — injectivity of the forward map: equal observations (under explicit
  nondegeneracy) force equal `(T, n_e, composition)`.

## Architecture — two tracks over a shared core

Import DAG is **acyclic with `Boltzmann` as the sole root**; every core definition is
defined once and reused verbatim.

- **Shared core** (`namespace CflibsFormal`): `Boltzmann`, `Saha`, `Closure`, `ForwardMap`,
  `ForwardMapEnergy` (energy/wavelength forward sibling: explicit `hc/4πλ`, proven to reduce to
  the photon-rate `ForwardMap` and to share the Boltzmann-plot slope),
  `Identifiability`, `MultiSpecies`, `SelfAbsorption`, `Robustness`, `Inverse`
  (algorithm-agnostic estimator framework), `CompositionRobustness`,
  `CompositionIdentifiability`, `SelfAbsorptionInverse`, `SahaInverse`, `CurveOfGrowth`,
  `StarkBroadening` (independent electron-density diagnostic + McWhirter LTE bound),
  `SpatialForward` (discrete onion-peeling Abel inversion — relaxes single-zone homogeneity),
  `Dimensions` (additive dimensional-analysis layer: machine-checks homogeneity of the forward
  relations; does not touch the dimensionless core),
  `ErrorBudget` (the deterministic error-propagation chain — ε → OLS slope → temperature →
  composition — that turns the pipeline's empirical reliability thresholds, `min_energy_spread`
  and `min_snr`, into proven *sufficient-condition* corollaries; imports `Alt/LeastSquares` for
  the OLS slope, honest that the line-count law is statistical, not deterministic).
- **Classic algorithm** (`namespace CflibsFormal.Classic`): `Classic` — the textbook
  calibration-free algorithm, `classic_sound` (composition leg given `T`).
- **Alternative estimators** (`namespace CflibsFormal.Alt`): `Alt/CSigma` (single
  master-line normalization plot), `Alt/SelfAbsorbed` (self-absorption-corrected),
  `Alt/LeastSquares` (multi-line OLS Boltzmann plot). Each is proven sound and related back
  to the classic estimator.

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
   actively maintained but pinned to Lean **v4.30.0** (we are v4.31.0 — depending forces a
   downgrade); its statistical mechanics is **measure-theoretic and unit-aware** (even
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
   precise recover/defeat boundary characterized); spatial inhomogeneity is modeled via the
   **discrete onion-peeling Abel inversion** (`SpatialForward`, single-zone = the N=1 case;
   the continuous Abel integral inverse is explicitly out of scope); and the LTE assumption
   itself gets an independent electron-density check (`StarkBroadening`: Stark width vs. Saha
   nₑ, McWhirter bound).

## Verification discipline

Gates, all required before trusting a result:
1. **Green build** — `lake build` (clean re-elaboration from source).
2. **Axiom-clean** — `lake exe axiom-audit --root CflibsFormal` (exit 0).
3. **Style/structure lint** — `lake exe runLinter CflibsFormal` (mathlib/batteries env linters:
   docBlame, simpNF, unusedArguments, …) — catches missing docstrings, unused hypotheses, etc.
4. **Import-DAG-root invariant** — `scripts/stats.sh` (the root `Boltzmann` imports no CflibsFormal
   module; acyclicity is guaranteed by the build). Also prints derived declaration counts.
5. **Statement audit** — adversarial review that the *statement* faithfully encodes the
   intended physics (non-vacuous, non-trivial, non-tautological, honestly scoped).

Gates 1–4 are automated in CI (`.github/workflows/lean_action_ci.yml`).

## Status

23 modules, 138 axiom-clean named results (theorem/lemma) + 65 defs (counts via `scripts/stats.sh`).
Three automated CI gates: axiom-cleanliness (`tools/`), style/structure lint (`runLinter`), and the
import-DAG-root invariant (`scripts/stats.sh`).
Adversarially validated (verdict: sound-with-minor-fixes, zero blockers; all findings fixed).
A whole-corpus **literature-validity audit** (`reviews/literature-validity-audit.md`) classified all
186 defs+theorems against the peer-reviewed CF-LIBS literature: 69 faithful / 33 reduced / 5 idealized
/ 78 pure-math, **0 divergent, 0 unverified citations, 1 minor docstring over-reach (fixed)**.
A numerical regression oracle (`oracle/`) bridges the verified spec to the numerical pipeline
(CF-LIBS-improved) — multi-element + the alternative estimators (OLS, self-absorption, Saha
nₑ) + the derived error-budget thresholds, each fixture instantiating a proven theorem.
