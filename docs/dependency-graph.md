# Dependency graph (reading guide)

The import DAG is **acyclic by construction** — Lean rejects cyclic imports, so a green `lake build`
is itself the acyclicity proof. Every module imports only `Mathlib` and other `CflibsFormal`
modules (enforced by `scripts/stats.sh`). This page is a reading guide; for the per-module import
data see the *Base* column of [`module-reference.md`](module-reference.md).

## Two tracks over a shared core

```
                         Mathlib
                            │
          ┌─────────────────┴───────────────────┐
   shared core  (namespace CflibsFormal)     independent Mathlib-only layers
   Boltzmann → Saha → Closure → ForwardMap …  Dimensions, SpatialForward,
        │  (forward model → inverse problem)   LineBroadening, Continuum, …
        ▼
   Classic (namespace CflibsFormal.Classic)    Alt/* (namespace CflibsFormal.Alt)
   the textbook estimator                      alternative estimators (CSigma,
                                               LeastSquares, OLSVariance, GaussMarkov, …)
```

- **`Boltzmann`** is the base of the forward/inverse chain (Boltzmann factor + partition function),
  on which `Saha`, `Closure`, `ForwardMap`, identifiability, robustness, and the estimators build.
- **Base modules** (import no `CflibsFormal` module — the leaves of the internal DAG) are the
  rows marked *Base ✓* in [`module-reference.md`](module-reference.md): the additive `Dimensions`
  layer, the discrete-onion-peeling `SpatialForward`, and several self-contained modeling-fidelity
  modules (`Continuum`, `LineBroadening`, `StarkShift`, `VoigtWidth`, `SelfReversal`, `HydrogenStark`).
- **Layering rule:** shared physics / inverse machinery lives in `CflibsFormal`; new *alternative*
  estimators go under `CflibsFormal.Alt`. See `CONTEXT.md` for the full architecture and the design
  decisions behind this split.
- **Frontier landings (2026-09-27).** Eight shared-core modules came from the 2026-09-24 audit's
  frontier theorems. Six are *Base* (Mathlib only): `IpdSahaInverse` (the IPD-aware Saha
  inverse), `FixedEffectsDesign` (the element-dummy Saha–Boltzmann design), `KernelLineExtraction`
  (line extraction under profile misspecification), `RefuseToReport` (the certified-abstention
  policy), `RatioModeSensitivity` (the ratio-mode log-ratio derivative) and `KirchhoffSource`
  (Kirchhoff's law for the opacity with stimulated emission). Two build on the core:
  `NoiseGainFloor` (imports `OLS`, `FixedEffectsDesign`) and `EscapeFactor` (imports
  `SelfAbsorption`, `EquivalentWidth`, `CurveOfGrowth`). The other landings extend existing
  modules; `SahaStability` now also imports `InhomogeneityBias` and `SahaEquilibrium`,
  `SelfAbsorption` imports `OLS`, and `Alt/NeutralityScale` imports `MultiSpecies`.
- **Frontier landings (2026-09-28).** `IonApparentTemperature` (ion versus neutral apparent
  temperature in a line-of-sight mixture) imports `InhomogeneityBias` and `SahaStability`. The
  other items of that landing extend `SahaStability`, `InhomogeneityBias` and `EquivalentWidth`.

## Rendering the full graph

`lake exe graph` (the mathlib `importGraph` tool) renders the DAG, treating `Mathlib` as a single
boundary node:

```bash
lake exe graph --to CflibsFormal docs/assets/import-dag.svg   # full upstream graph
lake exe graph cflibs-imports.dot                             # GraphViz .dot of the default target
```

(A committed, transitively-reduced internal-only SVG is a planned addition; until then, generate it
on demand with the commands above.)
