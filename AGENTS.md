# AGENTS.md — operational brief for coding agents

> Vendor-neutral entry point (read by most coding agents). For the full narrative — architecture,
> domain glossary, design decisions, modeling scope — read **`CONTEXT.md`**. This file is the
> *how to work here* brief: what the repo is, the gates you must pass, where things live, and the
> non-negotiables you must not break.

## What this is

`cflibs-formal` is a **machine-verified Lean 4 + mathlib specification** of calibration-free
Laser-Induced Breakdown Spectroscopy (CF-LIBS): the forward plasma-emission model, the inverse
(composition-recovery) problem, and the identifiability / reliability theorems that say *when and
why* the inversion is well-posed. It is the verified companion to the Python pipeline
`../CF-LIBS-improved`.

**The value of this repo is RIGOR, not numerical accuracy.** Real-data CF-LIBS accuracy is limited
by atomic data and plasma modeling, not by this spec. So we invest in *provable structure* —
soundness, identifiability, error bounds, honest scope — never in curve-fitting. Do not pitch
changes here as improving measurement accuracy.

- **Toolchain:** Lean `v4.31.0` + mathlib `v4.31.0` (`lake`). Pinned — do not `lake update`.
- **Everything is dimensionless** (bare `ℝ`); an additive `Dimensions.lean` layer machine-checks
  homogeneity separately.
- 35 modules under `CflibsFormal/` (+ `Alt/`); see `docs/module-reference.md` for the index and
  `docs/theorem-catalog.md` for every result with its scope tag + citation.

## The four non-negotiables (a change that breaks any of these is wrong)

1. **Axiom-clean.** Every declaration depends only on `{propext, Classical.choice, Quot.sound}`.
   No `sorry`/`admit`/`native_decide`. Enforced by `lake exe axiom-audit --root CflibsFormal`.
2. **mathlib-only imports.** Every module imports only `Mathlib` and `CflibsFormal.*`. No new
   external deps. (physlib is an *upstream target*, not a dependency — see
   `docs/upstream-physlib-plan.md`.)
3. **Dimensionless `ℝ` core.** The inverse-problem layer is bare `ℝ`; dimensional rigor lives in
   the additive `Dimensions.lean` layer, which must not be wired into the core.
4. **Honest scoping is the cardinal rule.** A docstring must not claim more than its theorem
   proves. Mark **EXACT** vs **REDUCED** vs **APPROXIMATION** vs **OUT-OF-SCOPE** honestly. A green
   proof of a vacuous, tautological, or physically-wrong statement is *worthless* — the whole point
   of this repo. Audit the *statement*, not just the compile. Every physics module carries a
   `## Literature` docstring with **verified** citations; verify constants, signs, and inequality
   directions against the literature *before* formalizing — never guess.

## Verification gates — run ALL before trusting or committing any result

```bash
lake build                                          # 1. green build (clean re-elaboration)
lake exe axiom-audit --root CflibsFormal            # 2. axiom-clean (exit 0)
lake exe runLinter CflibsFormal                     # 3. style/structure lint ("Linting passed")
./scripts/stats.sh                                  # 4. import hygiene + counts (exit 0)
lake exe oracle-fixtures > /tmp/f.json \
  && diff -u oracle/fixtures.json /tmp/f.json \
  && python3 oracle/check_fixtures.py               # 5. numerical-oracle regression (no drift)
# upstream seed (separate lean_lib, not in defaultTargets):
lake build SahaUpstream && lake exe axiom-audit --root SahaUpstream
```
Gates 1–4 (+ oracle + upstream) are the CI in `.github/workflows/lean_action_ci.yml`. Gate 5 of
the *discipline* — a faithfulness/statement audit — is human/agent judgment, not automated.

**Trust nothing self-reported.** If a subagent/tool says "green + axiom-clean," re-run the gates
yourself (`#print axioms <thm>` reports the axiom set of a single result). Never trust truncated
tool output.

## Where things live

| Path | What |
|---|---|
| `CONTEXT.md` | The narrative root: architecture, domain glossary, design decisions, modeling scope, verification discipline |
| `docs/module-reference.md` | **Auto-generated** module index: namespace, role, #results/#defs, base?, citation, imports |
| `docs/theorem-catalog.md` | **Auto-generated** catalog of every result with its **scope tag** (EXACT/REDUCED/APPROXIMATION/PURE-MATH) + citation + one-line summary — the integrity spine |
| `docs/scope-tags.tsv` | Curated authoritative scope classification (one row per result). The docs-sync CI gate **fails if any result is untagged** — a new theorem must declare its epistemic status here |
| `docs/dependency-graph.md` | The internal import DAG (reading guide) |
| `scripts/gen-docs.sh` | Regenerates the two auto docs from source + checks scope-tag completeness (run after adding/removing results) |
| `CflibsFormal/` | The spec. Core (`namespace CflibsFormal`) + `Alt/` (alternative estimators, `namespace CflibsFormal.Alt`) |
| `oracle/` | Float-mirror regression oracle bridging the spec to the Python pipeline |
| `tools/` | Vendored `axiom-audit` |
| `upstream/` | `SahaUpstream.lean` — mathlib-only Saha seed staged for an eventual physlib PR |
| `reviews/` | Audit archive (literature-validity, foundation) |

## Conventions

- **Namespacing:** shared physics/inverse machinery → `CflibsFormal`; new *alternative* estimators
  → `CflibsFormal.Alt`. Index types: `ι` levels, `κ` species, `σ` species (probability layer),
  `Ω` sample space — all with `[Fintype …]` as needed.
- **Reuse core defs verbatim;** define each concept once. Import DAG is acyclic (Lean-guaranteed).
- **Docstrings:** every `def`/`theorem` needs one (`runLinter docBlame`). Lines ≤ 100 chars.
  Literature-facing modules carry a `## Literature` paragraph with real citations.
- **Git:** branch is `main` with a real remote (`origin`); the repo is the backup. Commit each
  coherent unit and **push**. End commit messages with the `Claude-Session:` trailer (see history).

## A new theorem is "done" only when

green build · axiom-clean (`#print axioms`) · no `sorry` · runLinter clean · import-hygiene clean ·
oracle un-drifted · **and the statement is audited for non-vacuity + faithful physics + honest
scope** · classified in `docs/scope-tags.tsv` (EXACT/REDUCED/APPROXIMATION/PURE-MATH + citation) ·
the auto docs regenerated (`./scripts/gen-docs.sh`).
