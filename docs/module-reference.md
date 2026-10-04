# Module reference

> **AUTO-GENERATED** by `scripts/gen-docs.sh` — do not hand-edit; regenerate after
> adding/removing modules or results. The docs-sync CI gate diffs this against source.

One row per module under `CflibsFormal/`. *Base* = imports no `CflibsFormal` module.
*Lit* = carries a `## Literature` citation paragraph.

| Module | Namespace | Results | Defs | Base | Lit | Role |
|---|---|--:|--:|:--:|:--:|---|
| `Aitchison.lean` | `CflibsFormal` | 4 | 3 | ✓ | ✓ | 2DCOS-LIBS formalization — Aitchison compositional identities |
| `AitchisonIsometry.lean` | `CflibsFormal` | 4 | 6 | – | ✓ | Aitchison compositional data — a genuine isometric log-ratio (ilr) transform |
| `Alt/CSigma.lean` | `CflibsFormal.Alt` | 17 | 10 | – | ✓ | the C-sigma (Cσ) single-line method (alternative estimator) |
| `Alt/CSigmaCurveOfGrowth.lean` | `CflibsFormal.Alt` | 7 | 2 | – | ✓ | The Cσ curve of growth — self-absorption droop below the universal line |
| `Alt/GaussMarkov.lean` | `CflibsFormal.Alt` | 7 | 1 | – | ✓ | Gauss–Markov optimality (BLUE) for the OLS Boltzmann-plot slope |
| `Alt/LeastSquares.lean` | `CflibsFormal.Alt` | 6 | 3 | – | ✓ | the multi-line ordinary-least-squares Boltzmann-plot estimator |
| `Alt/NeutralityScale.lean` | `CflibsFormal.Alt` | 6 | 2 | – | ✓ | Neutrality scale — the calibration factor from charge neutrality instead of closure |
| `Alt/OLSAtomicDataPerturbation.lean` | `CflibsFormal.Alt` | 6 | 2 | – | ✓ | per-line atomic-data error in the OLS density reader |
| `Alt/OLSVariance.lean` | `CflibsFormal.Alt` | 7 | 1 | – | ✓ | the Gauss–Markov variance law for the OLS Boltzmann-plot slope |
| `Alt/SelfAbsorbed.lean` | `CflibsFormal.Alt` | 5 | 1 | – | ✓ | the self-absorption-corrected composition estimator (alternative) |
| `Alt/StochasticBudget.lean` | `CflibsFormal.Alt` | 14 | 4 | – | ✓ | Chebyshev tail (concentration) bounds for the OLS slope and intercept |
| `Analysis.lean` | `CflibsFormal` | 13 | 0 | ✓ | – | Shared analysis scaffolding |
| `AtomicDataPerturbation.lean` | `CflibsFormal` | 9 | 4 | – | ✓ | the atomic-data perturbation channel |
| `Boltzmann.lean` | `CflibsFormal` | 8 | 4 | ✓ | ✓ | Part 1: the Boltzmann distribution |
| `Certificates.lean` | `CflibsFormal` | 12 | 12 | – | ✓ | runtime certificates (the typed bridge) |
| `Classic.lean` | `CflibsFormal.Classic` | 5 | 2 | – | ✓ | the classic calibration-free algorithm, assembled and sound |
| `Closure.lean` | `CflibsFormal` | 7 | 2 | – | ✓ | Closure of species composition |
| `CompositionIdentifiability.lean` | `CflibsFormal` | 3 | 1 | – | ✓ | multi-line / many-element composition identifiability |
| `CompositionRobustness.lean` | `CflibsFormal` | 5 | 1 | – | – | Whole-composition-vector error propagation |
| `ConditionNumber.lean` | `CflibsFormal` | 15 | 0 | – | ✓ | the condition number as an ERROR-AMPLIFICATION factor |
| `ConformalCoverage.lean` | `CflibsFormal` | 3 | 1 | ✓ | ✓ | the rank-counting step behind split-conformal coverage |
| `Continuum.lean` | `CflibsFormal` | 6 | 5 | ✓ | ✓ | the continuum background |
| `CurveOfGrowth.lean` | `CflibsFormal` | 10 | 2 | – | ✓ | the curve of growth and multi-line self-absorption |
| `DifferentialEstimator.lean` | `CflibsFormal` | 11 | 2 | – | ✓ | the reference-differenced (line-by-line) estimator |
| `Dimensions.lean` | `CflibsFormal` | 16 | 15 | ✓ | – | a dimensional-analysis layer |
| `DoubletChannel.lean` | `CflibsFormal` | 22 | 1 | – | ✓ | The doublet channel — the second observable that breaks the `N`–`τ` alias |
| `EquivalentWidth.lean` | `CflibsFormal` | 25 | 4 | ✓ | ✓ | the equivalent-width curve of growth |
| `ErrorBudget.lean` | `CflibsFormal` | 19 | 2 | – | ✓ | the error-propagation chain and DERIVED reliability thresholds |
| `EscapeFactor.lean` | `CflibsFormal` | 2 | 0 | – | ✓ | Profile escape factor versus the flat-slab self-absorption factor |
| `EvaluatorSoundness.lean` | `CflibsFormal` | 6 | 5 | – | ✓ | evaluator soundness (which hard-gate clauses feed which theorem) |
| `FisherLineSelection.lean` | `CflibsFormal` | 19 | 1 | – | ✓ | Fisher information, the Cramér–Rao bound, and "adding a line never hurts" |
| `FixedEffectsDesign.lean` | `CflibsFormal` | 3 | 4 | ✓ | ✓ | the fixed-effects (element-dummy) weighted Boltzmann design |
| `ForwardMap.lean` | `CflibsFormal` | 3 | 1 | – | ✓ | Part 4: the optically-thin forward map |
| `ForwardMapEnergy.lean` | `CflibsFormal` | 5 | 1 | – | ✓ | the energy-intensity forward map and convention equivalence |
| `HeteroAtomicData.lean` | `CflibsFormal` | 11 | 2 | – | ✓ | PER-LINE heterogeneous atomic-data error in the Boltzmann-plot SLOPE |
| `HydrogenStark.lean` | `CflibsFormal` | 4 | 2 | ✓ | ✓ | the hydrogen-line (Balmer) Stark electron-density diagnostic |
| `Identifiability.lean` | `CflibsFormal` | 7 | 0 | – | ✓ | Part 5: identifiability of the inverse problem |
| `InhomogeneityBias.lean` | `CflibsFormal` | 28 | 9 | – | ✓ | Inhomogeneity bias: the sign of the Boltzmann-plot error is a theorem |
| `IntervalEnclosure.lean` | `CflibsFormal` | 7 | 2 | – | ✓ | a Lipschitz bound on the OLS design normal matrix |
| `Inverse.lean` | `CflibsFormal` | 3 | 6 | – | ✓ | Part 6: the algorithm-agnostic inverse-problem framework |
| `IonApparentTemperature.lean` | `CflibsFormal` | 2 | 0 | – | ✓ | Ion and neutral apparent temperatures in a line-of-sight mixture |
| `IpdSahaInverse.lean` | `CflibsFormal` | 3 | 1 | ✓ | ✓ | the IPD-aware Saha inverse in log coordinates (frontier FT-02) |
| `JointConvergence.lean` | `CflibsFormal` | 5 | 1 | – | ✓ | the joint `(T, n_e)` outer-loop contraction (Frontier) |
| `JointIdentifiability.lean` | `CflibsFormal` | 1 | 1 | – | ✓ | Part 7: joint (temperature, composition) identifiability |
| `KernelLineExtraction.lean` | `CflibsFormal` | 1 | 0 | ✓ | ✓ | kernel least-squares line extraction under profile misspecification |
| `KirchhoffSource.lean` | `CflibsFormal` | 1 | 2 | ✓ | ✓ | Kirchhoff-consistent line opacity and the Planck source function |
| `LadenburgReiche.lean` | `CflibsFormal` | 6 | 1 | – | ✓ | the sharp Ladenburg–Reiche asymptotic equivalent |
| `LeastSquaresFit.lean` | `CflibsFormal` | 9 | 3 | – | – | the ordinary-least-squares projection / feasibility inverse |
| `LineBroadening.lean` | `CflibsFormal` | 5 | 4 | ✓ | ✓ | line broadening (Doppler width + the Voigt Gaussian budget) |
| `LineEvidence.lean` | `CflibsFormal.LineEvidence` | 9 | 3 | ✓ | ✓ | when is a missing line evidence of absence? (two gates) |
| `LineExtraction.lean` | `CflibsFormal.LineExtraction` | 18 | 2 | ✓ | ✓ | a metamorphic specification of line extraction |
| `LineSelection.lean` | `CflibsFormal` | 19 | 4 | – | ✓ | slope-variance-optimal (D_s) line selection |
| `MatrixEffects.lean` | `CflibsFormal` | 23 | 7 | – | ✓ | matrix effects (completeness, ablation, ionization suppression) |
| `MatrixIonizationCoupling.lean` | `CflibsFormal` | 10 | 0 | – | ✓ | Coupling the ionization-suppression channel with the multi-element fixed point |
| `MultiSpecies.lean` | `CflibsFormal` | 12 | 4 | – | ✓ | Multi-species / multi-stage composition glue |
| `NoiseGainFloor.lean` | `CflibsFormal` | 3 | 8 | – | ✓ | noise-gain floors for the Boltzmann slope and intercept difference |
| `NoiseToComposition.lean` | `CflibsFormal` | 5 | 2 | – | ✓ | the end-to-end noise → composition chain (gap #5, the composed bound) |
| `NonLTEKinetics.lean` | `CflibsFormal` | 15 | 2 | – | ✓ | non-LTE departure coefficients and the departure error budget |
| `NonlinearLeastSquares.lean` | `CflibsFormal` | 32 | 3 | – | ✓ | the nonlinear joint `(T, N)` least-squares inverse (existence leg) |
| `OLS.lean` | `CflibsFormal` | 17 | 9 | ✓ | ✓ | the ordinary-least-squares algebraic foundation |
| `OLSConditioning.lean` | `CflibsFormal` | 1 | 0 | – | ✓ | quantitative conditioning of the Boltzmann-plot normal matrix |
| `OLSIdentifiability.lean` | `CflibsFormal` | 11 | 1 | – | ✓ | n-line Boltzmann-plot identifiability (design-map injectivity) |
| `OpacityBroadening.lean` | `CflibsFormal` | 27 | 5 | – | ✓ | opacity broadening: a DERIVED budget for the Stark opacity guard |
| `OpticalDepth.lean` | `CflibsFormal` | 18 | 4 | – | ✓ | Optical depth bound to the plasma state — closing the free-`τ` gap |
| `OpticalDepthBridge.lean` | `CflibsFormal` | 10 | 0 | – | ✓ | Wiring the state-bound optical depth into the free-`τ` corpus |
| `OracleAnchors.lean` | `CflibsFormal` | 0 | 0 | – | ✓ | oracle fixture anchors (machine-checked spec ↔ fixtures link) |
| `OuterLoopModelB.lean` | `CflibsFormal` | 1 | 0 | – | ✓ | the outer temperature iteration, Model B headline (Frontier 04) |
| `PartialLTE.lean` | `CflibsFormal` | 6 | 2 | – | ✓ | the partial-LTE thermalization limit |
| `PartitionLipschitz.lean` | `CflibsFormal` | 3 | 0 | – | ✓ | the `U_s(T)` partition-function Lipschitz leg (gap #5) |
| `ProfiledTUniqueness.lean` | `CflibsFormal` | 10 | 1 | – | ✓ | `T`-uniqueness of the profiled fit, and the joint `(T, N)` corollary |
| `ProfiledUnimodality.lean` | `CflibsFormal` | 3 | 0 | – | ✓ | strict unimodality of the profiled temperature objective |
| `RadiativeTransferDepth.lean` | `CflibsFormal` | 7 | 3 | – | ✓ | depth-structured radiative transfer (the N-zone stack) |
| `RatioModeSensitivity.lean` | `CflibsFormal` | 1 | 0 | ✓ | ✓ | Ratio-mode sensitivity to the assumed temperature |
| `RefuseToReport.lean` | `CflibsFormal` | 1 | 1 | ✓ | ✓ | the refuse-to-report policy (certified abstention) |
| `Robustness.lean` | `CflibsFormal` | 5 | 2 | – | – | Robustness / error-propagation bounds |
| `Saha.lean` | `CflibsFormal` | 6 | 4 | – | ✓ | Part 2: the Saha ionization equilibrium |
| `SahaContraction.lean` | `CflibsFormal` | 2 | 0 | – | ✓ | Damped Saha closure iteration converges to the *unique* equilibrium |
| `SahaEquilibrium.lean` | `CflibsFormal` | 41 | 7 | – | ✓ | Coupled Saha–closure–charge self-consistency (reduced core) |
| `SahaInverse.lean` | `CflibsFormal` | 3 | 2 | – | ✓ | Part 6: coupling Saha into the inverse problem |
| `SahaRangeEnclosure.lean` | `CflibsFormal` | 3 | 0 | – | ✓ | an a-priori Saha `S(T)`-range enclosure (Frontier 04) |
| `SahaStability.lean` | `CflibsFormal` | 17 | 3 | – | ✓ | Part 2b: stability of the `n_e` diagnostic |
| `SelfAbsorption.lean` | `CflibsFormal` | 11 | 3 | – | ✓ | self-absorption / optical-thickness-aware forward map |
| `SelfAbsorptionInverse.lean` | `CflibsFormal` | 5 | 1 | – | ✓ | Self-absorption coupled into the inverse problem — identifiability preserved vs. lost |
| `SelfReversal.lean` | `CflibsFormal` | 4 | 1 | ✓ | ✓ | self-reversal (the two-zone line dip) |
| `SharedUpperLevel.lean` | `CflibsFormal` | 6 | 1 | – | ✓ | lines from a shared upper level: an atomic-data consistency gate |
| `SpatialForward.lean` | `CflibsFormal` | 11 | 4 | ✓ | ✓ | spatially-resolved (discrete Abel / onion-peeling) forward model |
| `StarkBroadening.lean` | `CflibsFormal` | 7 | 4 | – | ✓ | Stark broadening + the McWhirter LTE criterion |
| `StarkOpacityGuard.lean` | `CflibsFormal` | 9 | 1 | – | ✓ | opacity guard for the Stark electron-density diagnostic |
| `StarkShift.lean` | `CflibsFormal` | 9 | 3 | ✓ | ✓ | the Stark line-shift electron-density diagnostic |
| `TemporalEvolution.lean` | `CflibsFormal` | 8 | 7 | – | ✓ | time-resolved (gate-delayed) recovery |
| `TwoDCOS.lean` | `CflibsFormal` | 8 | 3 | ✓ | ✓ | 2DCOS-LIBS formalization — Noda two-dimensional correlation algebra |
| `TwoDCOSOrder.lean` | `CflibsFormal` | 11 | 1 | – | ✓ | 2DCOS-LIBS formalization — the sequential-order (lead/lag) sign algebra |
| `VoigtErrorEnclosure.lean` | `CflibsFormal` | 5 | 0 | – | ✓ | a non-circular error enclosure for the Voigt FWHM |
| `VoigtWidth.lean` | `CflibsFormal` | 7 | 1 | ✓ | ✓ | the Voigt FWHM combination (Olivero–Longbothum) |
| **94 modules** | | **843** | **248** | | | |

