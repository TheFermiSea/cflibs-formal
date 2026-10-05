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
- **Everything is dimensionless** (bare `ℝ`); an additive `Dimensions.lean` layer checks the
  exponent arithmetic of hand-assigned dimension vectors separately (it is not linked to the
  definitions, so it does not catch a wrong exponent in one).
- Size (kept current by `scripts/gen-docs.sh`; the docs-sync gate fails if it drifts):
  <!-- stats:begin -->
  94 modules · 848 named results (theorem/lemma) · 248 defs
  <!-- stats:end -->
  See `docs/module-reference.md` for the index and `docs/theorem-catalog.md` for every result
  with its scope tags + citation.

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
   point of this repo. Audit the *statement*, not just the compile. Every physics module carries a
   `## Literature` docstring with **verified** citations; verify constants, signs, and inequality
   directions against the literature *before* formalizing — never guess.

## Verification gates — run ALL before trusting or committing any result

```bash
lake build --wfail                                  # 1. green build, no warnings
lake exe axiom-audit --root CflibsFormal            # 2. axiom-clean (exit 0)
lake exe scope-check                                # 2b. scope gate + docs/scope-published.tsv current
lake exe export-catalog > /tmp/c.jsonl \
  && diff -u docs/catalog.jsonl /tmp/c.jsonl        # 2c. kernel-exported catalog current
lake exe runLinter CflibsFormal                     # 3. style/structure lint ("Linting passed")
scripts/kernel-replay.sh --changed origin/main      # 3b. independent kernel replay (leanchecker) of changed modules
./scripts/stats.sh                                  # 4. source hygiene (imports, orphans, sorry/axiom tokens) + counts
lake exe oracle-fixtures > /tmp/f.json \
  && diff -u oracle/fixtures.json /tmp/f.json \
  && python3 oracle/check_fixtures.py               # 5. numerical-oracle regression (no drift)
python3 oracle/line_extraction/check_fixtures.py \
  && python3 oracle/tier2/check_fixtures.py         # 5b. companion-facing fixture sets (need numpy)
./scripts/gen-docs.sh --check                       # 6. auto docs + size lines in sync, every
                                                    #    catalog theorem tagged, Literature present
./scripts/check-citations.sh                        # 7. every scope-tag citation is whitelisted
python3 scripts/check_cards.py --selftest \
  && python3 scripts/gen_cards.py \
  && git diff --exit-code -- docs/theorems/         # 8. theorem cards (needs pyyaml)
# upstream seed (separate lean_lib, not in defaultTargets):
lake build SahaUpstream && lake exe axiom-audit --root SahaUpstream
```
All of the above run in CI (`.github/workflows/lean_action_ci.yml`; the kernel replay covers the
changed modules there, and a weekly workflow sweeps every module). The statement audit —
is the *statement* faithful, non-vacuous and honestly scoped — is human/agent judgment, not
automated (`.claude/agents/lean-statement-audit.md` is the procedure).

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
| `oracle/` | Float-mirror regression oracle bridging the spec to the Python pipeline; `oracle/line_extraction/` and `oracle/tier2/` hold the fixture sets and reference predicates the companion pins for its line-extraction and physical-validity gates |
| `tools/` | Vendored `axiom-audit`, and this repo's `scope-check` (`ScopeCheck.lean`) and `export-catalog` (`ExportCatalog.lean`) executables |
| `docs/catalog.jsonl` | **Auto-generated, committed** by `lake exe export-catalog`: one JSON line per documented declaration (printed statement, file:line, binders, used constants, axioms); the theorem cards hash their reviewed statements against it |
| `docs/theorems/` | Theorem cards (D21, D24): curated per-family pages with a generated Facts block; `SCHEMA.md` is the contract, `scripts/check_cards.py` the gate, `scripts/gen_cards.py` the generator |
| `docs/conventions.md` | The convention lock (log base, partition-function normalization, units, scope-tag semantics §8) |
| `docs/citation-whitelist.tsv`, `docs/citations.md` | Per-citation verification status and the guide to it |
| `upstream/` | `SahaUpstream.lean` — mathlib-only Saha seed staged for an eventual physlib PR |
| `reviews/` | Audit archive (literature-validity, foundation) |
| `docs/decisions.md` | The owner's decision ledger (D1–D24); cite decisions as `D<n>` |
| `docs/research/`, `docs/integration/` | Dated research memos and audits; the M4 population-layer integration contract with CF-LIBS-improved |
| `docs/archive/openprover/` | Scrubbed snapshot of the proof-queue records (dossiers, verdicts, parked targets) behind PRs #8/#9; a log, not a source of truth |

## Conventions

- **Namespacing:** shared physics/inverse machinery → `CflibsFormal`; new *alternative* estimators
  → `CflibsFormal.Alt`. Index types: `ι` levels, `κ` species, `σ` species (probability layer),
  `Ω` sample space — all with `[Fintype …]` as needed.
- **Reuse core defs verbatim;** define each concept once. Import DAG is acyclic (Lean-guaranteed).
- **Docstrings:** every `def`/`theorem` needs one (`runLinter docBlame` covers definitions;
  for theorems the docs gate fails when a result is missing from the kernel-derived catalog,
  which lists only documented declarations). Lines ≤ 100 chars.
  Literature-facing modules carry a `## Literature` paragraph with real citations.
- **Git:** the default branch is `main` on a real remote (`origin`); the repo is the backup and it
  is **public** (D23: name companion paths and symbols only; no private code, backlog ids, host
  names or absolute paths). Work on a feature branch, commit each coherent unit, **push**, and
  land it by pull request once CI is green. End commit messages with the `Claude-Session:`
  trailer (see history).

## A new theorem is "done" only when

green build · axiom-clean (`#print axioms`) · no `sorry` · runLinter clean · import-hygiene clean ·
oracle un-drifted · **and the statement is audited for non-vacuity + faithful physics + honest
scope** · classified in `docs/scope-tags.tsv` (relation tag EXACT/REDUCED/APPROXIMATION/PURE-MATH
and citation; a new definition that encodes a physical model gets a model row) · published tags
recomputed and committed (`lake exe scope-check --write`, which rewrites
`docs/scope-published.tsv`) · then the auto docs regenerated (`./scripts/gen-docs.sh`, which reads
that file and fails if it is missing or out of step).
