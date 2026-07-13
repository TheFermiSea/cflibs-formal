# Module reference

> **AUTO-GENERATED** by `scripts/gen-docs.sh` — do not hand-edit; regenerate after
> adding/removing modules or results. The docs-sync CI gate diffs this against source.

One row per module under `CflibsFormal/`. *Base* = imports no `CflibsFormal` module.
*Lit* = carries a `## Literature` citation paragraph.

| Module | Namespace | Results | Defs | Base | Lit | Role |
|---|---|--:|--:|:--:|:--:|---|
| `Aitchison.lean` | `CflibsFormal` | 4 | 3 | ✓ | ✓ | 2DCOS-LIBS formalization — Aitchison compositional identities |
| `AitchisonIsometry.lean` | `CflibsFormal` | 3 | 6 | – | ✓ | Aitchison compositional data — a genuine isometric log-ratio (ilr) transform |
| `Alt/CSigma.lean` | `CflibsFormal.Alt` | 17 | 10 | – | – | the C-sigma (Cσ) single-line method (alternative estimator) |
| `Alt/CSigmaCurveOfGrowth.lean` | `CflibsFormal.Alt` | 7 | 2 | – | ✓ | The Cσ curve of growth — self-absorption droop below the universal line |
| `Alt/GaussMarkov.lean` | `CflibsFormal.Alt` | 7 | 1 | – | ✓ | Gauss–Markov optimality (BLUE) for the OLS Boltzmann-plot slope |
| `Alt/LeastSquares.lean` | `CflibsFormal.Alt` | 6 | 3 | – | ✓ | the multi-line ordinary-least-squares Boltzmann-plot estimator |
| `Alt/OLSAtomicDataPerturbation.lean` | `CflibsFormal.Alt` | 6 | 2 | – | ✓ | per-line atomic-data error in the OLS density reader |
| `Alt/OLSVariance.lean` | `CflibsFormal.Alt` | 7 | 1 | – | ✓ | the Gauss–Markov variance law for the OLS Boltzmann-plot slope |
| `Alt/SelfAbsorbed.lean` | `CflibsFormal.Alt` | 5 | 1 | – | – | the self-absorption-corrected composition estimator (alternative) |
| `Alt/StochasticBudget.lean` | `CflibsFormal.Alt` | 13 | 4 | – | ✓ | Chebyshev tail (concentration) bounds for the OLS slope and intercept |
| `Analysis.lean` | `CflibsFormal` | 7 | 0 | ✓ | – | Shared analysis scaffolding |
| `AtomicDataPerturbation.lean` | `CflibsFormal` | 8 | 4 | – | ✓ | the atomic-data perturbation channel |
| `Boltzmann.lean` | `CflibsFormal` | 5 | 3 | ✓ | – | Part 1: the Boltzmann distribution |
| `Certificates.lean` | `CflibsFormal` | 12 | 12 | – | ✓ | runtime certificates (the typed bridge) |
| `Classic.lean` | `CflibsFormal.Classic` | 5 | 2 | – | – | the classic calibration-free algorithm, assembled and sound |
| `Closure.lean` | `CflibsFormal` | 6 | 2 | – | – | Closure of species composition |
| `CompositionIdentifiability.lean` | `CflibsFormal` | 3 | 1 | – | – | multi-line / many-element composition identifiability |
| `CompositionRobustness.lean` | `CflibsFormal` | 5 | 1 | – | – | Whole-composition-vector error propagation |
| `Continuum.lean` | `CflibsFormal` | 6 | 5 | ✓ | ✓ | the continuum background |
| `CurveOfGrowth.lean` | `CflibsFormal` | 10 | 2 | – | ✓ | the curve of growth and multi-line self-absorption |
| `Dimensions.lean` | `CflibsFormal` | 16 | 15 | ✓ | – | a dimensional-analysis layer |
| `EquivalentWidth.lean` | `CflibsFormal` | 20 | 2 | ✓ | ✓ | the equivalent-width curve of growth |
| `ErrorBudget.lean` | `CflibsFormal` | 19 | 2 | – | – | the error-propagation chain and DERIVED reliability thresholds |
| `ForwardMap.lean` | `CflibsFormal` | 3 | 1 | – | – | Part 4: the optically-thin forward map |
| `ForwardMapEnergy.lean` | `CflibsFormal` | 5 | 1 | – | ✓ | the energy-intensity forward map and convention equivalence |
| `HydrogenStark.lean` | `CflibsFormal` | 4 | 2 | ✓ | ✓ | the hydrogen-line (Balmer) Stark electron-density diagnostic |
| `Identifiability.lean` | `CflibsFormal` | 7 | 0 | – | – | Part 5: identifiability of the inverse problem |
| `IntervalEnclosure.lean` | `CflibsFormal` | 7 | 2 | – | ✓ | a verified ε-ball enclosure for the OLS forward map |
| `Inverse.lean` | `CflibsFormal` | 3 | 6 | – | – | Part 6: the algorithm-agnostic inverse-problem framework |
| `JointIdentifiability.lean` | `CflibsFormal` | 1 | 1 | – | – | Part 7: joint (temperature, composition) identifiability |
| `LadenburgReiche.lean` | `CflibsFormal` | 6 | 1 | – | ✓ | the sharp Ladenburg–Reiche asymptotic equivalent |
| `LeastSquaresFit.lean` | `CflibsFormal` | 9 | 3 | – | – | the ordinary-least-squares projection / feasibility inverse |
| `LineBroadening.lean` | `CflibsFormal` | 5 | 4 | ✓ | ✓ | line broadening (Doppler width + the Voigt Gaussian budget) |
| `MatrixEffects.lean` | `CflibsFormal` | 22 | 7 | – | ✓ | matrix effects (completeness, ablation, ionization suppression) |
| `MatrixIonizationCoupling.lean` | `CflibsFormal` | 12 | 0 | – | ✓ | Coupling the ionization-suppression channel with the multi-element fixed point |
| `MultiSpecies.lean` | `CflibsFormal` | 12 | 4 | – | – | Multi-species / multi-stage composition glue |
| `NoiseToComposition.lean` | `CflibsFormal` | 5 | 2 | – | ✓ | the end-to-end noise → composition chain (gap #5, the composed bound) |
| `NonLTEKinetics.lean` | `CflibsFormal` | 15 | 2 | – | ✓ | non-LTE departure coefficients and the departure error budget |
| `NonlinearLeastSquares.lean` | `CflibsFormal` | 31 | 3 | – | ✓ | the nonlinear joint `(T, N)` least-squares inverse (existence leg) |
| `OLS.lean` | `CflibsFormal` | 17 | 9 | ✓ | – | the ordinary-least-squares algebraic foundation |
| `OLSConditioning.lean` | `CflibsFormal` | 5 | 0 | – | ✓ | quantitative conditioning of the Boltzmann-plot normal matrix |
| `OLSIdentifiability.lean` | `CflibsFormal` | 11 | 1 | – | ✓ | n-line Boltzmann-plot identifiability (design-map injectivity) |
| `OuterLoopModelB.lean` | `CflibsFormal` | 1 | 0 | – | – | the outer temperature iteration, Model B headline (Frontier 04) |
| `PartialLTE.lean` | `CflibsFormal` | 6 | 2 | – | ✓ | the partial-LTE thermalization limit |
| `PartitionLipschitz.lean` | `CflibsFormal` | 3 | 0 | – | ✓ | the `U_s(T)` partition-function Lipschitz leg (gap #5) |
| `ProfiledUnimodality.lean` | `CflibsFormal` | 3 | 0 | – | ✓ | strict unimodality of the profiled temperature objective |
| `RadiativeTransferDepth.lean` | `CflibsFormal` | 7 | 3 | – | ✓ | depth-structured radiative transfer (the N-zone stack) |
| `Robustness.lean` | `CflibsFormal` | 5 | 2 | – | – | Robustness / error-propagation bounds |
| `Saha.lean` | `CflibsFormal` | 6 | 4 | – | – | Part 2: the Saha ionization equilibrium |
| `SahaContraction.lean` | `CflibsFormal` | 2 | 0 | – | ✓ | Damped Saha closure iteration converges to the *unique* equilibrium |
| `SahaEquilibrium.lean` | `CflibsFormal` | 34 | 6 | – | ✓ | Coupled Saha–closure–charge self-consistency (reduced core) |
| `SahaInverse.lean` | `CflibsFormal` | 3 | 2 | – | ✓ | Part 6: coupling Saha into the inverse problem |
| `SahaStability.lean` | `CflibsFormal` | 11 | 1 | – | ✓ | Part 2b: stability of the `n_e` diagnostic |
| `SelfAbsorption.lean` | `CflibsFormal` | 10 | 3 | – | – | self-absorption / optical-thickness-aware forward map |
| `SelfAbsorptionInverse.lean` | `CflibsFormal` | 5 | 1 | – | – | Self-absorption coupled into the inverse problem — identifiability preserved vs. lost |
| `SelfReversal.lean` | `CflibsFormal` | 4 | 1 | ✓ | ✓ | self-reversal (the two-zone line dip) |
| `SpatialForward.lean` | `CflibsFormal` | 11 | 4 | ✓ | ✓ | spatially-resolved (discrete Abel / onion-peeling) forward model |
| `StarkBroadening.lean` | `CflibsFormal` | 7 | 4 | – | ✓ | Stark broadening + the McWhirter LTE criterion |
| `StarkShift.lean` | `CflibsFormal` | 9 | 3 | ✓ | ✓ | the Stark line-shift electron-density diagnostic |
| `TemporalEvolution.lean` | `CflibsFormal` | 8 | 7 | – | ✓ | time-resolved (gate-delayed) recovery |
| `TwoDCOS.lean` | `CflibsFormal` | 8 | 3 | ✓ | ✓ | 2DCOS-LIBS formalization — Noda two-dimensional correlation algebra |
| `TwoDCOSOrder.lean` | `CflibsFormal` | 11 | 1 | – | ✓ | 2DCOS-LIBS formalization — the sequential-order (lead/lag) sign algebra |
| `VoigtErrorEnclosure.lean` | `CflibsFormal` | 5 | 0 | – | ✓ | a non-circular error enclosure for the Voigt FWHM |
| `VoigtWidth.lean` | `CflibsFormal` | 7 | 1 | ✓ | ✓ | the Voigt FWHM combination (Olivero–Longbothum) |
| **64 modules** | | **543** | **181** | | | |

