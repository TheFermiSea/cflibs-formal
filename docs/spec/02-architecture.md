# 02 — Architecture: as-is and target

## 1. As-is (verified against the tree at `5daee7c`)

**Scale.** 81 modules (73 core + 8 `Alt/`), 751 axiom-clean named results, 217 defs; 12 runtime
certificates; 6 oracle scenarios; 751 scope-tag rows.

**Layers (bottom to top).** Every arrow is an import; the DAG is acyclic by construction.

```
mathlib
  └─ Analysis, OLS, Aitchison, Dimensions, SpatialForward, ConformalCoverage …   (Mathlib-only base modules)
       └─ Boltzmann ── Saha ── Closure ── ForwardMap / ForwardMapEnergy            (forward model)
            └─ Identifiability, JointIdentifiability, CompositionIdentifiability     (injectivity)
            └─ Inverse (algorithm-agnostic) ── Classic ── Alt/* (CSigma, LeastSquares, SelfAbsorbed…)
            └─ LeastSquaresFit, NonlinearLeastSquares, ProfiledTUniqueness           (noisy inverse)
            └─ Robustness, CompositionRobustness, ErrorBudget, ConditionNumber,
               AtomicDataPerturbation, NoiseToComposition, Alt/OLSVariance, Alt/GaussMarkov  (error layer)
            └─ SahaEquilibrium, SahaContraction, MatrixIonizationCoupling, OuterLoopModelB,
               JointConvergence, SahaStability, PartitionLipschitz                    (self-consistency)
            └─ SelfAbsorption, CurveOfGrowth, EquivalentWidth, LadenburgReiche, OpticalDepth*,
               SelfReversal, RadiativeTransferDepth, DoubletChannel                  (opacity)
            └─ LineBroadening, VoigtWidth, VoigtErrorEnclosure, StarkBroadening, StarkShift,
               HydrogenStark, StarkOpacityGuard, PartialLTE, NonLTEKinetics, Continuum (plasma diagnostics)
            └─ MatrixEffects, TemporalEvolution, InhomogeneityBias, DifferentialEstimator,
               FisherLineSelection, LineSelection, EvaluatorSoundness, ConformalCoverage (reliability)
            └─ Certificates ── OracleAnchors ── oracle/Generate.lean → fixtures.json → companion tests
```

**Invariants that shape every new module.**
1. One definition per concept, reused verbatim (`partitionFunction`, `composition`, `lorentzian`,
   `multiElementIonized`, `mean`/`olsSlope`, `sahaFactor`).
2. Index types `ι` (levels), `κ`/`σ` (species), `Ω` (sample space), `[Fintype]` as needed,
   `[Nonempty]` only where a proof uses it.
3. Dimensionless `ℝ`; `Dimensions.lean` proves homogeneity separately and is never imported by the core.
4. Every physics module has a `## Literature` docstring drawing only on `docs/citation-whitelist.tsv`.
5. Every hypothesis that encodes physics (LTE, optically thin, stoichiometric ablation,
   exchangeability) is a **named carried predicate** or an explicit hypothesis; none is discharged
   silently.
6. A result is done only with: green `lake build`, axiom-audit, runLinter, stats, oracle un-drifted,
   scope-tag row, docs regenerated, and a statement audit.

**The two bridges to the numerical pipeline** (`../CF-LIBS-improved`):
- *Oracle:* `oracle/Generate.lean` mirrors Lean ℝ definitions in `Float`, emits `fixtures.json`;
  `check_fixtures.py` re-checks it; the companion vendors the certificates scenario byte-for-byte.
- *Certificates:* `Certificates.lean` defines `…Cert : Prop` as pure float arithmetic plus a
  soundness theorem `cert → guarantee`; the companion's `certificate_gate.py` evaluates them as hard
  in-loop rejects during algorithm search.

## 2. Target architecture (this spec)

Four additions, placed where the import DAG says they belong. Names are proposals; the pre-registration
fixes them.

```
                     Boltzmann ── Saha ──────────────┐
                                                     ▼
   SahaEquilibrium (Z=1, DONE) ◄── reduces from ── SahaCascade.lean        [new, P0]
        │                                            │ per-species totals N_s = Σ_z N_{s,z}
        ▼                                            ▼
   MatrixEffects / TemporalEvolution ◄── two stoichiometry corollaries      [new theorems, P3]
        │                                            │
        ▼                                            ▼
   Closure.composition ──────────────────► CompositionIdentifiability, NoiseToComposition (unchanged)

   EquivalentWidth.lorentzian, LadenburgReiche.lorentzianG (DONE)
        │
        ▼
   ContinuousProfile.lean  [new, P1]  — shifted/scaled Lorentzian = mathlib Cauchy PDF,
        │                              Gaussian = mathlib Gaussian PDF, Voigt := convolution
        ├──► EquivalentWidth (equivWidth of a real profile), VoigtWidth (what O–L approximates)
        ▼
   SpectrometerForward.lean [new, P2] — pixel kernel K p l = ∫ φ_l · R_p ; y = K.mulVec I ;
        │                                identifiability of I ; first instance = companion Gaussian IRF
        ▼
   ForwardMap (line intensities I) ── existing inverse chain

   Certificates.lean  + C15 (cascade residual enclosure) + C16 (kernel rank gate)
   oracle/Generate.lean + Scenario 7 (cascade fixed point; pixel-integrated lines)
```

**Data flow, stated once so the blueprint's diagram error does not recur.** Photons: plasma state
`(T, n_e, N_{s,z})` → line emissivities (Boltzmann + cascade) → continuous profiles → instrument
kernel → pixel sums `y`. Inference runs the other way: `y` → line intensities `I` (SpectrometerForward,
needs kernel rank) → Boltzmann/Saha inverse → per-species totals → closure → composition. Stoichiometry
is a hypothesis about the plasma-to-target map that sits *beside* closure, not downstream of the
instrument.

## 3. Namespace and file placement

| Addition | File | Namespace | Base module? |
|---|---|---|---|
| Z-stage cascade | `CflibsFormal/SahaCascade.lean` | `CflibsFormal` | No: imports `Saha`, `SahaEquilibrium` |
| Continuous profiles | `CflibsFormal/ContinuousProfile.lean` | `CflibsFormal` | Imports `EquivalentWidth`, `LadenburgReiche`; mathlib `Probability.Distributions.{Cauchy,Gaussian.Real}`, `Analysis.Convolution` |
| Instrument kernel | `CflibsFormal/SpectrometerForward.lean` | `CflibsFormal` | Imports `ContinuousProfile`, `ForwardMap`, `OLSIdentifiability` |
| Stoichiometry corollaries | append to `CflibsFormal/MatrixEffects.lean` | `CflibsFormal` | — |
| Certificates C15/C16 | `CflibsFormal/Certificates.lean` | `CflibsFormal` | — |
| Oracle scenario 7 | `oracle/Generate.lean`, `oracle/fixtures.json`, `oracle/check_fixtures.py` | — | — |
| Dimensional homogeneity of emission/radiance | `CflibsFormal/Dimensions.lean` (additive) | `CflibsFormal.Dimension` | Stays Mathlib-only |

## 4. Placement relative to the frontier dossiers

| Dossier | Relation to this spec |
|---|---|
| 02 Saha monotonicity (closed) | `sahaFactor_strictMonoOn_temp` gives the T-dependence of every stage factor `S_z(T)`; the cascade is stated at fixed T and inherits it |
| 03 Multi-element iteration (closed) | The cascade's Z = 1 reduction target; its damped-iteration convergence is the template for a cascade iteration (deferred, 06) |
| 04 Outer T-iteration (closed, one witness deferred) | Unchanged; the cascade replaces `legNe` only if a cascade n_e leg is proven Lipschitz (deferred) |
| 07 Ladenburg–Reiche (closed) | Supplies `lorentzianG`; ContinuousProfile reuses it |
| 09 Radiative transfer depth (open) | Profiles feed the depth-structured source integral; not attempted here |
| 10 Spatial Abel (out of scope) | Untouched |
| 12 Runtime certificates (landed) | C15/C16 follow its certificate map format |

## 5. What is explicitly not in the target

- Unit-carrying types in the core (blueprint §1 anti-pattern 1). Confirmed policy.
- The full Voigt FWHM as a theorem about the convolution (the Olivero–Longbothum formula is an
  APPROXIMATION and stays one).
- Bessel-function Ladenburg–Reiche (refused, ROADMAP §5).
- A single "everything" well-posedness theorem before its parts exist (blueprint Milestone 4). It
  becomes a Phase-5 integration target with its own pre-registration.
