# 08 — Validation of this planning change

[Plan index](README.md)

**Date:** 2026-09-15. **Baseline:** `5daee7c41b3c10e96cff982041a0020dc162a2cf`.
**Branch:** `docs/physics-formalization-plan`.

## Scope of changes

- Added the planning collection and root README navigation.
- Added ordinary gap comments in `LineBroadening`, `Saha`, `ConformalCoverage`, `NonLTEKinetics`,
  `tools/ScopeCheck.lean`, and `scripts/stats.sh` at the user's request.
- No Lean declaration, proof, statement, import, scope row, citation row, fixture, checking logic,
  dependency pin, or numerical implementation changed.
- Removing the added comment blocks reproduces the six baseline source files exactly.
- Original `main` checkout remained clean; work was performed in a separate planning worktree.

## Actual local verification

The baseline and annotated branch used the existing Lean/mathlib 4.33.1 dependency cache. The
planning worktree used a separate copy of the project's build outputs and rebuilt changed sources
and affected consumers. This was **not** a clean full rebuild of mathlib or an external-library trial.

| Check | Result and boundary |
|---|---|
| `lake build` | Passed on baseline and annotated branch; final build completed with 8,788 jobs reported |
| `lake exe axiom-audit --root CflibsFormal` | Passed: 2,092 declarations within `{propext, Classical.choice, Quot.sound}` |
| `lake exe scope-check` | Exit 0, but only 133 EXACT declarations checked; confirmed coverage defect GAP-05 remains intentionally unfixed |
| `lake exe runLinter CflibsFormal` | Passed |
| Explicit kernel replay of four annotated physics/probability modules | Passed for `LineBroadening`, `Saha`, `ConformalCoverage`, `NonLTEKinetics`; two workers, one Lean thread each |
| Rebuilt `scope-check` and independent `ScopeCheck` kernel replay | Passed after tooling comment; one replay worker; checking logic unchanged |
| `lake build SahaUpstream` and upstream axiom audit | Passed; 12 upstream-seed declarations within allowlist |
| `scripts/stats.sh` | Passed import hygiene; reports 752 results/217 defs; known prose-count discrepancy GAP-06 |
| `scripts/gen-docs.sh` | Passed: 81 modules, 751 results, 217 defs, all catalog results tagged; no generated-file diff |
| `lake exe oracle-fixtures`, exact fixture diff | Passed; committed fixtures unchanged |
| `python3 oracle/check_fixtures.py` | Passed; float-mirror regression only |
| `scripts/check-scope-consistency.sh` | Exit 0 with 7 mixed-approximation and 80 reduced-dependency advisory warnings; not a clean scientific-scope audit |
| `scripts/check-citations.sh` | Advisory completed; unverified entries and three unacknowledged prose years remain; no primary-source-validation verdict |
| Documentation paths and links | Checked against the worktree; full 81-module inventory reconciled |
| `git diff --check` and shell syntax | Checked; comment-only source comparison performed |

Baseline `--changed origin/main` replay selected no modules, as expected for the unchanged baseline.
It was not counted as proof replay. The annotated branch was instead replayed using an explicit
module list. No claim is made that all 81 modules received a fresh independent replay in this pass.

## Scope-check coverage investigation

A temporary read-only Lean program loaded the actual `CflibsFormal` environment through the existing
`AxiomAudit.withImportedEnv` helper and applied the checker's current short-name resolution to every
EXACT and APPROXIMATION row. It confirmed:

| Unresolved metadata | Count | Location |
|---|---:|---|
| EXACT | 3 | `Classic.lean`: `classicDensity_recovers`, `classic_sound`, `classic_calibration_free` |
| EXACT | 22 | `Alt/CSigma`, `Alt/OLSAtomicDataPerturbation`, `Alt/SelfAbsorbed`, `Alt/OLSVariance`, `Alt/GaussMarkov`, `Alt/StochasticBudget` |
| APPROXIMATION | 7 | `Alt/CSigmaCurveOfGrowth` |

The current checker prepends `CflibsFormal` to short names, ignoring the nested namespaces, and
silently filters names absent from the environment. Its approximation tag lookup has the same key
mismatch. This establishes incomplete coverage, **not** that any skipped theorem actually violates
the scope rule. F0 must repair resolution and inspect the newly covered dependencies before using
the check as evidence of complete scope consistency. This planning change documents the defect only.

## Research confidence

The four requested library repositories, plus crnt-lean and Clawristotle, were inspected at the
revisions in [the reuse matrix](02-library-reuse.md). No external source was executed or certified.
Additional astronomy/materials projects were web discovery leads with explicitly lower confidence.
Exact imported replacements and ports still require adapter proofs, build/axiom checks, license
review, and physical assumption review. No blanket boilerplate-reduction percentage is claimed.

## Outstanding work

The F0–F6 migration and all six gap resolutions are future work. Citation verification and the
existing advisory warnings remain open; this pass does not relabel or waive them. The accompanying
source comments preserve these boundaries without introducing unfinished theorem declarations.
