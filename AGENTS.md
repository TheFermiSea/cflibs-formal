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

- **Toolchain:** Lean `v4.33.1` + mathlib `v4.33.1` (`lake`). Pinned — do not `lake update`.
- **Everything is dimensionless** (bare `ℝ`); an additive `Dimensions.lean` layer machine-checks
  homogeneity separately.
- 82 modules under `CflibsFormal/` (73 top level + 9 in `Alt/`, 2026-09-25) — recount via
  `scripts/stats.sh`; see `docs/module-reference.md` for the index and `docs/theorem-catalog.md`
  for every result with its scope tags + citation.

## The four non-negotiables (a change that breaks any of these is wrong)

1. **Axiom-clean.** Every declaration depends only on `{propext, Classical.choice, Quot.sound}`.
   No `sorry`/`admit`/`native_decide`. Enforced by `lake exe axiom-audit --root CflibsFormal`.
2. **mathlib-only imports.** Every module imports only `Mathlib` and `CflibsFormal.*`. No new
   external deps. (physlib is an *upstream target*, not a dependency — see
   `docs/upstream-physlib-plan.md`.)
3. **Dimensionless `ℝ` core.** The inverse-problem layer is bare `ℝ`; dimensional rigor lives in
   the additive `Dimensions.lean` layer, which must not be wired into the core.
4. **Honest scoping is the cardinal rule.** A docstring must not claim more than its theorem
   proves. Mark **EXACT** vs **REDUCED** vs **APPROXIMATION** vs **PURE-MATH** honestly (the scope
   tags in `docs/scope-tags.tsv`; "out of scope" stays a prose docstring caveat, not a scope tag).
   Tags have two axes (`docs/conventions.md` §8): a definition that encodes a physical model
   carries a *model* tag, a theorem a *relation* tag, and the *published* tag (the weaker of the
   relation tag and the model tags in the statement; PURE-MATH exempt) is the one to quote. A
   green proof of a vacuous, tautological, or physically-wrong statement is *worthless* — the whole
   point
   of this repo. Audit the *statement*, not just the compile. Every physics module carries a
   `## Literature` docstring with **verified** citations; verify constants, signs, and inequality
   directions against the literature *before* formalizing — never guess.

## Verification gates — run ALL before trusting or committing any result

```bash
lake build                                          # 1. green build (clean re-elaboration)
lake exe axiom-audit --root CflibsFormal            # 2. axiom-clean (exit 0)
lake exe scope-check                                # 2b. scope gate + docs/scope-published.tsv current
lake exe runLinter CflibsFormal                     # 3. style/structure lint ("Linting passed")
scripts/kernel-replay.sh --changed origin/main      # 3b. independent kernel replay (leanchecker) of changed modules
./scripts/stats.sh                                  # 4. import hygiene + counts (exit 0)
lake exe oracle-fixtures > /tmp/f.json \
  && diff -u oracle/fixtures.json /tmp/f.json \
  && python3 oracle/check_fixtures.py               # 5. numerical-oracle regression (no drift)
# upstream seed (separate lean_lib, not in defaultTargets):
lake build SahaUpstream && lake exe axiom-audit --root SahaUpstream
```
Gates 1–4 (+ oracle + upstream + kernel replay of changed modules; weekly full sweep) are the CI in `.github/workflows/lean_action_ci.yml`. Gate 5 of
the *discipline* — a faithfulness/statement audit — is human/agent judgment, not automated.

**Trust nothing self-reported.** If a subagent/tool says "green + axiom-clean," re-run the gates
yourself (`#print axioms <thm>` reports the axiom set of a single result). Never trust truncated
tool output.

## Where things live

| Path | What |
|---|---|
| `CONTEXT.md` | The narrative root: architecture, domain glossary, design decisions, modeling scope, verification discipline |
| `docs/module-reference.md` | **Auto-generated** module index: namespace, role, #results/#defs, base?, citation, imports |
| `docs/theorem-catalog.md` | **Auto-generated** catalog of every result with its **scope tags** (EXACT/REDUCED/APPROXIMATION/PURE-MATH; `own → published` when they differ) + citation + one-line summary — the integrity spine |
| `docs/scope-tags.tsv` | Curated authoritative scope classification: one row per result (its *relation* tag) plus one row per definition that encodes a physical model (its *model* tag, e.g. `lineIntensity` REDUCED); an untagged definition inherits the weakest model tag it uses (`docs/conventions.md` §8), so a definition that restates a model without using a tagged definition inherits nothing and needs its own row. The docs-sync CI gate **fails if any result is untagged** — a new theorem must declare its epistemic status here |
| `docs/scope-published.tsv` | **Auto-generated, committed** by `lake exe scope-check --write`: each theorem's relation tag, its *published* tag (the weaker of the relation tag and the model tags of the definitions in its statement; PURE-MATH exempt) and the model rows that weakened it. `scope-check` fails if it is stale and `gen-docs.sh` fails if it is missing |
| `docs/dependency-graph.md` | The internal import DAG (reading guide) |
| `scripts/gen-docs.sh` | Regenerates the two auto docs from source + checks scope-tag completeness (run after adding/removing results). It renders published tags from `docs/scope-published.tsv`, so after changing `docs/scope-tags.tsv` run `lake exe scope-check --write` first |
| `CflibsFormal/` | The spec. Core (`namespace CflibsFormal`) + `Alt/` (alternative estimators, `namespace CflibsFormal.Alt`) |
| `oracle/` | Float-mirror regression oracle bridging the spec to the Python pipeline |
| `tools/` | Vendored `axiom-audit`, and the `scope-check` executable (`ScopeCheck.lean`) |
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
scope** · classified in `docs/scope-tags.tsv` (relation tag EXACT/REDUCED/APPROXIMATION/PURE-MATH
and citation; a new definition that encodes a physical model gets a model row) · published tags
recomputed and committed (`lake exe scope-check --write`, which rewrites
`docs/scope-published.tsv`) · then the auto docs regenerated (`./scripts/gen-docs.sh`, which reads
that file and fails if it is missing or out of step).
