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

## Rendering the full graph

`lake exe graph` (the mathlib `importGraph` tool) renders the DAG, treating `Mathlib` as a single
boundary node:

```bash
lake exe graph --to CflibsFormal docs/assets/import-dag.svg   # full upstream graph
lake exe graph cflibs-imports.dot                             # GraphViz .dot of the default target
```

(A committed, transitively-reduced internal-only SVG is a planned addition; until then, generate it
on demand with the commands above.)
