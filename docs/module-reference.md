# Module reference

> **AUTO-GENERATED** by `scripts/gen-docs.sh` — do not hand-edit; regenerate after
> adding/removing modules or results. The docs-sync CI gate diffs this against source.

One row per module under `CflibsFormal/`. *Base* = imports no `CflibsFormal` module.
*Lit* = carries a `## Literature` citation paragraph.

| Module | Namespace | Results | Defs | Base | Lit | Role |
|---|---|--:|--:|:--:|:--:|---|
| `Alt/CSigma.lean` | `CflibsFormal.Alt` | 17 | 10 | – | – | the C-sigma (Cσ) single-line method (alternative estimator) |
| `Alt/CSigmaCurveOfGrowth.lean` | `CflibsFormal.Alt` | 7 | 2 | – | ✓ | The Cσ curve of growth — self-absorption droop below the universal line |
| `Alt/GaussMarkov.lean` | `CflibsFormal.Alt` | 7 | 1 | – | ✓ | Gauss–Markov optimality (BLUE) for the OLS Boltzmann-plot slope |
| `Alt/LeastSquares.lean` | `CflibsFormal.Alt` | 4 | 3 | – | ✓ | the multi-line ordinary-least-squares Boltzmann-plot estimator |
| `Alt/OLSVariance.lean` | `CflibsFormal.Alt` | 7 | 1 | – | ✓ | the Gauss–Markov variance law for the OLS Boltzmann-plot slope |
| `Alt/SelfAbsorbed.lean` | `CflibsFormal.Alt` | 5 | 1 | – | – | the self-absorption-corrected composition estimator (alternative) |
| `Analysis.lean` | `CflibsFormal` | 1 | 0 | ✓ | – | Shared analysis scaffolding |
| `Boltzmann.lean` | `CflibsFormal` | 5 | 3 | ✓ | – | Part 1: the Boltzmann distribution |
| `Classic.lean` | `CflibsFormal.Classic` | 5 | 2 | – | – | the classic calibration-free algorithm, assembled and sound |
| `Closure.lean` | `CflibsFormal` | 6 | 2 | – | – | Closure of species composition |
| `CompositionIdentifiability.lean` | `CflibsFormal` | 3 | 1 | – | – | multi-line / many-element composition identifiability |
| `CompositionRobustness.lean` | `CflibsFormal` | 5 | 1 | – | – | Whole-composition-vector error propagation |
| `Continuum.lean` | `CflibsFormal` | 6 | 5 | ✓ | ✓ | the continuum background |
| `CurveOfGrowth.lean` | `CflibsFormal` | 10 | 2 | – | ✓ | the curve of growth and multi-line self-absorption |
| `Dimensions.lean` | `CflibsFormal` | 16 | 15 | ✓ | – | a dimensional-analysis layer |
| `ErrorBudget.lean` | `CflibsFormal` | 14 | 0 | – | – | the error-propagation chain and DERIVED reliability thresholds |
| `ForwardMap.lean` | `CflibsFormal` | 3 | 1 | – | – | Part 4: the optically-thin forward map |
| `ForwardMapEnergy.lean` | `CflibsFormal` | 5 | 1 | – | ✓ | the energy-intensity forward map and convention equivalence |
| `HydrogenStark.lean` | `CflibsFormal` | 4 | 2 | ✓ | ✓ | the hydrogen-line (Balmer) Stark electron-density diagnostic |
| `Identifiability.lean` | `CflibsFormal` | 3 | 0 | – | – | Part 5: identifiability of the inverse problem |
| `Inverse.lean` | `CflibsFormal` | 3 | 6 | – | – | Part 6: the algorithm-agnostic inverse-problem framework |
| `LineBroadening.lean` | `CflibsFormal` | 5 | 4 | ✓ | ✓ | line broadening (Doppler width + the Voigt Gaussian budget) |
| `MatrixEffects.lean` | `CflibsFormal` | 17 | 7 | – | ✓ | matrix effects (completeness, ablation, ionization suppression) |
| `MultiSpecies.lean` | `CflibsFormal` | 4 | 2 | – | – | Multi-species / multi-stage composition glue |
| `OLS.lean` | `CflibsFormal` | 7 | 4 | ✓ | – | the ordinary-least-squares algebraic foundation |
| `PartialLTE.lean` | `CflibsFormal` | 6 | 2 | – | ✓ | the partial-LTE thermalization limit |
| `Robustness.lean` | `CflibsFormal` | 5 | 2 | – | – | Robustness / error-propagation bounds |
| `Saha.lean` | `CflibsFormal` | 6 | 4 | – | – | Part 2: the Saha ionization equilibrium |
| `SahaInverse.lean` | `CflibsFormal` | 3 | 2 | – | ✓ | Part 6: coupling Saha into the inverse problem |
| `SelfAbsorption.lean` | `CflibsFormal` | 10 | 3 | – | – | self-absorption / optical-thickness-aware forward map |
| `SelfAbsorptionInverse.lean` | `CflibsFormal` | 4 | 1 | – | – | Self-absorption coupled into the inverse problem — identifiability preserved vs. lost |
| `SelfReversal.lean` | `CflibsFormal` | 4 | 1 | ✓ | ✓ | self-reversal (the two-zone line dip) |
| `SpatialForward.lean` | `CflibsFormal` | 4 | 1 | ✓ | ✓ | spatially-resolved (discrete Abel / onion-peeling) forward model |
| `StarkBroadening.lean` | `CflibsFormal` | 7 | 4 | – | ✓ | Stark broadening + the McWhirter LTE criterion |
| `StarkShift.lean` | `CflibsFormal` | 9 | 3 | ✓ | ✓ | the Stark line-shift electron-density diagnostic |
| `TemporalEvolution.lean` | `CflibsFormal` | 8 | 7 | – | ✓ | time-resolved (gate-delayed) recovery |
| `VoigtWidth.lean` | `CflibsFormal` | 7 | 1 | ✓ | ✓ | the Voigt FWHM combination (Olivero–Longbothum) |
| **37 modules** | | **242** | **107** | | | |

