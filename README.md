# cflibs-formal

A **machine-verified Lean 4 + mathlib specification** of calibration-free Laser-Induced Breakdown
Spectroscopy (CF-LIBS): the forward plasma-emission model, the inverse composition-recovery
problem, and the identifiability / reliability theorems that establish *when and why* the inversion
is well-posed. It is the verified companion to the numerical pipeline `CF-LIBS-improved`.

**The goal is rigor, not numerical accuracy.** Real-data CF-LIBS accuracy is limited by atomic data
and plasma modeling, not by this spec — so the investment is in *provable structure* (soundness,
identifiability, error bounds, honestly-scoped modeling fidelity), each result grounded in the
peer-reviewed literature and audited so that the *statement* faithfully encodes the intended
physics. Everything is dimensionless (bare `ℝ`); a separate additive layer machine-checks
dimensional homogeneity.

## Status

35 modules · 241 axiom-clean theorems/lemmas · 107 defs (run `scripts/stats.sh` for live counts).
Axiom-clean invariant: every declaration depends only on `{propext, Classical.choice, Quot.sound}`.

## Layout

| Path | Contents |
|---|---|
| `CflibsFormal/` | The spec: shared core (`namespace CflibsFormal`) + alternative estimators (`CflibsFormal/Alt/`, `namespace CflibsFormal.Alt`) |
| `CONTEXT.md` | Architecture, domain glossary, design decisions, modeling scope, verification discipline |
| `AGENTS.md` | Operational brief for coding agents (gates, conventions, non-negotiables) |
| `docs/` | Module reference, theorem catalog (scope-tagged + cited), glossary, architecture, ADRs, dependency graph |
| `oracle/` | Float-mirror regression oracle bridging the spec to the Python pipeline |
| `tools/`, `upstream/`, `scripts/`, `reviews/` | Vendored axiom-audit; physlib upstream seed; stats/CI helpers; audit archive |

## Build & verify

Requires the pinned toolchain (`lean-toolchain`: `leanprover/lean4:v4.31.0`) and mathlib `v4.31.0`,
fetched by `lake`:

```bash
lake exe cache get        # fetch the mathlib build cache (first time)
lake build                # build the spec
```

The full verification gate suite (all run in CI, `.github/workflows/lean_action_ci.yml`):

```bash
lake build                                          # green build
lake exe axiom-audit --root CflibsFormal            # axiom-cleanliness
lake exe runLinter CflibsFormal                     # style/structure lint
./scripts/stats.sh                                  # import hygiene + counts
lake exe oracle-fixtures > /tmp/f.json && diff -u oracle/fixtures.json /tmp/f.json && python3 oracle/check_fixtures.py
```

## License

Apache-2.0 (see `LICENSE`). Vendored components retain their own licenses (`tools/` — axiom-audit,
Apache-2.0).
