# 05 — Complete module disposition

[Plan index](README.md)

Baseline: `5daee7c41b3c10e96cff982041a0020dc162a2cf`. All **81** source modules are
accounted for below. Counts follow the existing documentation parser (751 named results), not the
line-regex stats total or an environment census. Targets name proposed responsibility groups;
individual sections may need different destinations after declaration-level dependency analysis.

**Default disposition is preserve and reorganize.** No module is approved for deletion by this
inventory. A leaf in the module import graph is not unused: the root exposes it, external Lean
clients may use its constants, and the Python/documentation correspondence may depend on it.

| Current module | Named results | Proposed primary responsibility | Action / caution |
|---|---:|---|---|
| [Aitchison](../../CflibsFormal/Aitchison.lean) | 4 | `Math/Composition` | Retain model-specific results and public names; move after consumer and assumption review. |
| [AitchisonIsometry](../../CflibsFormal/AitchisonIsometry.lean) | 3 | `Math/Composition` | Retain model-specific results and public names; move after consumer and assumption review. |
| [Alt/CSigma](../../CflibsFormal/Alt/CSigma.lean) | 17 | `Inference/Estimators` | Retain model-specific results and public names; move after consumer and assumption review. |
| [Alt/CSigmaCurveOfGrowth](../../CflibsFormal/Alt/CSigmaCurveOfGrowth.lean) | 7 | `Inference/Estimators` | Retain model-specific results and public names; move after consumer and assumption review. |
| [Alt/GaussMarkov](../../CflibsFormal/Alt/GaussMarkov.lean) | 7 | `Inference/Statistics` | Move with probability/noise assumptions, preserving Alt namespace initially. |
| [Alt/LeastSquares](../../CflibsFormal/Alt/LeastSquares.lean) | 6 | `Inference/Estimators` | Retain model-specific results and public names; move after consumer and assumption review. |
| [Alt/OLSAtomicDataPerturbation](../../CflibsFormal/Alt/OLSAtomicDataPerturbation.lean) | 6 | `Inference/Stability` | Retain model-specific results and public names; move after consumer and assumption review. |
| [Alt/OLSVariance](../../CflibsFormal/Alt/OLSVariance.lean) | 7 | `Inference/Statistics` | Preserve stochastic assumptions; share only deterministic regression algebra. |
| [Alt/SelfAbsorbed](../../CflibsFormal/Alt/SelfAbsorbed.lean) | 5 | `Inference/Estimators` | Retain model-specific results and public names; move after consumer and assumption review. |
| [Alt/StochasticBudget](../../CflibsFormal/Alt/StochasticBudget.lean) | 13 | `Inference/Statistics` | Keep RSS/probability bounds separate from deterministic worst-case budgets. |
| [Analysis](../../CflibsFormal/Analysis.lean) | 13 | `Math/Bounds` | Split exponential/reciprocal bounds, derivative adapters, and quadratic/fixed-point support; retain short physics-facing adapters. |
| [AtomicDataPerturbation](../../CflibsFormal/AtomicDataPerturbation.lean) | 8 | `Inference/Stability` | Retain model-specific results and public names; move after consumer and assumption review. |
| [Boltzmann](../../CflibsFormal/Boltzmann.lean) | 5 | `Physics/Atomic` | Preserve weighted finite-level API; compare physlib representations before any replacement. |
| [Certificates](../../CflibsFormal/Certificates.lean) | 12 | `Applications/CFLIBS` | Retain model-specific results and public names; move after consumer and assumption review. |
| [Classic](../../CflibsFormal/Classic.lean) | 5 | `Applications/CFLIBS` | Retain model-specific results and public names; move after consumer and assumption review. |
| [Closure](../../CflibsFormal/Closure.lean) | 6 | `Math/Composition` | Retain model-specific results and public names; move after consumer and assumption review. |
| [CompositionIdentifiability](../../CflibsFormal/CompositionIdentifiability.lean) | 3 | `Inference/Identifiability` | Retain model-specific results and public names; move after consumer and assumption review. |
| [CompositionRobustness](../../CflibsFormal/CompositionRobustness.lean) | 5 | `Inference/Stability` | Retain model-specific results and public names; move after consumer and assumption review. |
| [ConditionNumber](../../CflibsFormal/ConditionNumber.lean) | 15 | `Math/Regression` | Retain model-specific results and public names; move after consumer and assumption review. |
| [ConformalCoverage](../../CflibsFormal/ConformalCoverage.lean) | 3 | `Inference/Statistics` | Preserve counting result; GAP-03 probability bridge remains assumed. |
| [Continuum](../../CflibsFormal/Continuum.lean) | 6 | `Physics/Radiation` | Retain model-specific results and public names; move after consumer and assumption review. |
| [CurveOfGrowth](../../CflibsFormal/CurveOfGrowth.lean) | 10 | `Physics/Radiation` | Retain model-specific results and public names; move after consumer and assumption review. |
| [DifferentialEstimator](../../CflibsFormal/DifferentialEstimator.lean) | 11 | `Inference/Estimators` | Retain model-specific results and public names; move after consumer and assumption review. |
| [Dimensions](../../CflibsFormal/Dimensions.lean) | 16 | `Physics/Dimensions` | Separate audit layer; evaluate standard exponent algebra without changing inverse types. |
| [DoubletChannel](../../CflibsFormal/DoubletChannel.lean) | 22 | `Physics/Diagnostics` | Retain model-specific results and public names; move after consumer and assumption review. |
| [EquivalentWidth](../../CflibsFormal/EquivalentWidth.lean) | 20 | `Physics/Radiation` | Separate profile-independent integral properties from profile-specific models. |
| [ErrorBudget](../../CflibsFormal/ErrorBudget.lean) | 19 | `Inference/Stability` | Retain model-specific results and public names; move after consumer and assumption review. |
| [EvaluatorSoundness](../../CflibsFormal/EvaluatorSoundness.lean) | 6 | `Applications/CFLIBS` | Retain model-specific results and public names; move after consumer and assumption review. |
| [FisherLineSelection](../../CflibsFormal/FisherLineSelection.lean) | 19 | `Physics/Diagnostics` | Keep physical design criterion; do not imply a proved general Cramer-Rao bound. |
| [ForwardMap](../../CflibsFormal/ForwardMap.lean) | 3 | `Physics/Radiation` | Retain model-specific results and public names; move after consumer and assumption review. |
| [ForwardMapEnergy](../../CflibsFormal/ForwardMapEnergy.lean) | 5 | `Physics/Radiation` | Retain model-specific results and public names; move after consumer and assumption review. |
| [HeteroAtomicData](../../CflibsFormal/HeteroAtomicData.lean) | 10 | `Inference/Stability` | Retain model-specific results and public names; move after consumer and assumption review. |
| [HydrogenStark](../../CflibsFormal/HydrogenStark.lean) | 4 | `Physics/Diagnostics` | Retain model-specific results and public names; move after consumer and assumption review. |
| [Identifiability](../../CflibsFormal/Identifiability.lean) | 7 | `Inference/Identifiability` | Retain model-specific results and public names; move after consumer and assumption review. |
| [InhomogeneityBias](../../CflibsFormal/InhomogeneityBias.lean) | 27 | `Inference/Stability` | Retain model-specific results and public names; move after consumer and assumption review. |
| [IntervalEnclosure](../../CflibsFormal/IntervalEnclosure.lean) | 7 | `Inference/Stability` | Retain model-specific results and public names; move after consumer and assumption review. |
| [Inverse](../../CflibsFormal/Inverse.lean) | 3 | `Inference/Estimators` | Retain model-specific results and public names; move after consumer and assumption review. |
| [JointConvergence](../../CflibsFormal/JointConvergence.lean) | 1 | `Inference/Algorithms` | Retain model-specific results and public names; move after consumer and assumption review. |
| [JointIdentifiability](../../CflibsFormal/JointIdentifiability.lean) | 1 | `Inference/Identifiability` | Retain model-specific results and public names; move after consumer and assumption review. |
| [LadenburgReiche](../../CflibsFormal/LadenburgReiche.lean) | 6 | `Physics/Radiation` | Retain model-specific results and public names; move after consumer and assumption review. |
| [LeastSquaresFit](../../CflibsFormal/LeastSquaresFit.lean) | 9 | `Math/Regression` | Retain model-specific results and public names; move after consumer and assumption review. |
| [LineBroadening](../../CflibsFormal/LineBroadening.lean) | 5 | `Physics/Radiation` | Separate supplied width algebra from future convolution derivation; GAP-01. |
| [LineSelection](../../CflibsFormal/LineSelection.lean) | 19 | `Physics/Diagnostics` | Retain model-specific results and public names; move after consumer and assumption review. |
| [MatrixEffects](../../CflibsFormal/MatrixEffects.lean) | 22 | `Inference/Stability` | Retain model-specific results and public names; move after consumer and assumption review. |
| [MatrixIonizationCoupling](../../CflibsFormal/MatrixIonizationCoupling.lean) | 10 | `Physics/Plasma` | Retain model-specific results and public names; move after consumer and assumption review. |
| [MultiSpecies](../../CflibsFormal/MultiSpecies.lean) | 12 | `Applications/CFLIBS` | Retain model-specific results and public names; move after consumer and assumption review. |
| [NoiseToComposition](../../CflibsFormal/NoiseToComposition.lean) | 5 | `Inference/Stability` | Retain model-specific results and public names; move after consumer and assumption review. |
| [NonLTEKinetics](../../CflibsFormal/NonLTEKinetics.lean) | 15 | `Physics/Plasma` | Preserve reduced steady state; GAP-04 is new dynamics work. |
| [NonlinearLeastSquares](../../CflibsFormal/NonlinearLeastSquares.lean) | 32 | `Inference/Algorithms` | Split residual/objective, normal equations, and algorithmic convergence; no generic solver framework without a consumer. |
| [OLS](../../CflibsFormal/OLS.lean) | 17 | `Math/Regression` | Retain model-specific results and public names; move after consumer and assumption review. |
| [OLSConditioning](../../CflibsFormal/OLSConditioning.lean) | 1 | `Math/Regression` | Retain model-specific results and public names; move after consumer and assumption review. |
| [OLSIdentifiability](../../CflibsFormal/OLSIdentifiability.lean) | 11 | `Inference/Identifiability` | Retain model-specific results and public names; move after consumer and assumption review. |
| [OpacityBroadening](../../CflibsFormal/OpacityBroadening.lean) | 27 | `Physics/Radiation` | Retain model-specific results and public names; move after consumer and assumption review. |
| [OpticalDepth](../../CflibsFormal/OpticalDepth.lean) | 17 | `Physics/Radiation` | Retain model-specific results and public names; move after consumer and assumption review. |
| [OpticalDepthBridge](../../CflibsFormal/OpticalDepthBridge.lean) | 9 | `Physics/Radiation` | Retain model-specific results and public names; move after consumer and assumption review. |
| [OracleAnchors](../../CflibsFormal/OracleAnchors.lean) | 0 | `Applications/CFLIBS` | Retain fixture anchors; no claim of verified floating-point execution. |
| [OuterLoopModelB](../../CflibsFormal/OuterLoopModelB.lean) | 1 | `Inference/Algorithms` | Review actual modeled iteration, not historical naming; preserve mathematical scope. |
| [PartialLTE](../../CflibsFormal/PartialLTE.lean) | 6 | `Physics/Plasma` | Retain model-specific results and public names; move after consumer and assumption review. |
| [PartitionLipschitz](../../CflibsFormal/PartitionLipschitz.lean) | 3 | `Physics/Atomic` | Keep partition-specific constants here; extract only domain-independent inequalities. |
| [ProfiledTUniqueness](../../CflibsFormal/ProfiledTUniqueness.lean) | 10 | `Inference/Identifiability` | Split parameter elimination from injectivity/uniqueness; preserve nondegeneracy hypotheses. |
| [ProfiledUnimodality](../../CflibsFormal/ProfiledUnimodality.lean) | 3 | `Inference/Identifiability` | Retain model-specific results and public names; move after consumer and assumption review. |
| [RadiativeTransferDepth](../../CflibsFormal/RadiativeTransferDepth.lean) | 7 | `Physics/Radiation` | Retain model-specific results and public names; move after consumer and assumption review. |
| [Robustness](../../CflibsFormal/Robustness.lean) | 5 | `Inference/Stability` | Retain model-specific results and public names; move after consumer and assumption review. |
| [Saha](../../CflibsFormal/Saha.lean) | 6 | `Physics/Plasma` | Retain supplied law and conventions; GAP-02 is optional deeper derivation. |
| [SahaContraction](../../CflibsFormal/SahaContraction.lean) | 2 | `Inference/Algorithms` | Retain model-specific results and public names; move after consumer and assumption review. |
| [SahaEquilibrium](../../CflibsFormal/SahaEquilibrium.lean) | 34 | `Physics/Plasma` | Split two-stage single/multi-species balance, existence/uniqueness, and iteration estimates; iteration portions go to Algorithms. |
| [SahaInverse](../../CflibsFormal/SahaInverse.lean) | 3 | `Inference/Estimators` | Retain model-specific results and public names; move after consumer and assumption review. |
| [SahaRangeEnclosure](../../CflibsFormal/SahaRangeEnclosure.lean) | 3 | `Inference/Stability` | Retain model-specific results and public names; move after consumer and assumption review. |
| [SahaStability](../../CflibsFormal/SahaStability.lean) | 11 | `Physics/Plasma` | Keep equilibrium sensitivities near their physical definitions; move generic bounds down. |
| [SelfAbsorption](../../CflibsFormal/SelfAbsorption.lean) | 10 | `Physics/Radiation` | Retain model-specific results and public names; move after consumer and assumption review. |
| [SelfAbsorptionInverse](../../CflibsFormal/SelfAbsorptionInverse.lean) | 5 | `Inference/Estimators` | Retain model-specific results and public names; move after consumer and assumption review. |
| [SelfReversal](../../CflibsFormal/SelfReversal.lean) | 4 | `Physics/Radiation` | Retain model-specific results and public names; move after consumer and assumption review. |
| [SpatialForward](../../CflibsFormal/SpatialForward.lean) | 11 | `Physics/Radiation` | Retain model-specific results and public names; move after consumer and assumption review. |
| [StarkBroadening](../../CflibsFormal/StarkBroadening.lean) | 7 | `Physics/Diagnostics` | Retain model-specific results and public names; move after consumer and assumption review. |
| [StarkOpacityGuard](../../CflibsFormal/StarkOpacityGuard.lean) | 8 | `Physics/Diagnostics` | Retain model-specific results and public names; move after consumer and assumption review. |
| [StarkShift](../../CflibsFormal/StarkShift.lean) | 9 | `Physics/Diagnostics` | Retain model-specific results and public names; move after consumer and assumption review. |
| [TemporalEvolution](../../CflibsFormal/TemporalEvolution.lean) | 8 | `Applications/TimeResolved` | Keep per-gate soundness and common-dilution assumptions explicit. |
| [TwoDCOS](../../CflibsFormal/TwoDCOS.lean) | 8 | `Applications/Correlation` | Retain proven correlation identities independently of invalid historical monograph. |
| [TwoDCOSOrder](../../CflibsFormal/TwoDCOSOrder.lean) | 11 | `Applications/Correlation` | Retain precise ordering assumptions; do not infer temperature-free composition. |
| [VoigtErrorEnclosure](../../CflibsFormal/VoigtErrorEnclosure.lean) | 5 | `Physics/Radiation` | Retain model-specific results and public names; move after consumer and assumption review. |
| [VoigtWidth](../../CflibsFormal/VoigtWidth.lean) | 7 | `Physics/Radiation` | Retain model-specific results and public names; move after consumer and assumption review. |

## Non-library artifacts

| Current area | Proposed disposition and safeguard |
|---|---|
| `CflibsFormal.lean` | Preserve compatibility aggregator; add topic entry points in a later implementation phase; validate root coverage independently |
| `upstream/SahaUpstream.lean` | Keep separately built/audited seed; track correspondence to core, avoid a divergent second physics definition |
| `oracle/` | Keep fixture generation and Python regression; record which scalar definitions each fixture covers |
| `docs/integration/cflibs_certificates.py` | Treat as a numerical mirror with explicit hypothesis/rounding boundaries; review consumers before any relocation |
| `tools/AxiomAudit*`, `tools/ScopeCheck.lean` | Verification infrastructure, not physics boilerplate; preserve full namespace/root coverage |
| `scripts/gen_docs.py`, `stats.sh`, `kernel-replay.sh` | Update path/parser coverage when moving files; reconcile census discrepancy before using counts for migration acceptance |
| `docs/scope-tags.tsv` | Preserve curated classification; update module keys atomically with moves; no bulk scope promotions |
| `docs/citation-whitelist.tsv` | Preserve epistemic status and evidence; UNVERIFIED remains unresolved, not silently sanctioned |
| `docs/module-reference.md`, `theorem-catalog.md` | Generated only; never hand-edit around failed metadata checks |
| `docs/conventions.md`, `CONTEXT.md`, root README | Preserve conventions; later replace stale counts with one generated/snapshot source |
| `docs/frontiers/`, `SOLVER_FORMALIZATION_GAPS.md` | Reconcile with accepted physics priorities; classify proposals as active, deferred, or superseded with reason |
| `docs/2dcos/` | Keep original/corrected work and ERRATA linked; separate historical defective engines from maintained experiments before any deletion |
| `reviews/` | Retain immutable historical evidence with audited revision/date; do not imply newer modules were audited |
| Tracked caches / generated bytecode | Candidate cleanup only after tracked-file and consumer review; they are not formal evidence |
| `.github/workflows/` | Preserve build/audit/scope/docs/oracle/kernel gates and private publication boundary |

## Required deletion receipt

For any future retired implementation, record old path and declarations, replacement declarations
and equality/signature evidence, all known consumers, reference-search results, changed root/audit
coverage, metadata changes, and last recoverable commit. If no replacement is required, state why
the scientific capability is intentionally dropped and who accepted that scope decision. Moving an
old engine to an archive preserves provenance; it is not proof that a replacement exists.
