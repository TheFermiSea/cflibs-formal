# 01 — Current-state audit

[Plan index](README.md)

## Evidence and limits

The baseline is `5daee7c41b3c10e96cff982041a0020dc162a2cf`. The audit enumerated all tracked
Lean modules and their imports, read the project directive, CI/tooling, generated catalogs,
upstream proposal, and representative load-bearing definitions and statements. It is an
architecture and statement-boundary review, **not a renewed literature audit of every theorem**.
The [validation record](08-validation-record.md) distinguishes source inspection, build checks,
and independent proof replay. Historical audits cannot establish correctness of later additions.

| Observation | Evidence and interpretation |
|---|---|
| 81 source modules; root imports all 81 | `CflibsFormal.lean`; complete inventory in document 05 |
| 28,474 physical lines | Source snapshot; line counts include comments and proofs |
| Generated catalog: 751 results, 217 definitions | `scripts/gen-docs.sh`; private declarations, examples, and other declaration forms are outside this count |
| `stats.sh` reports 752 results | Its line regex also counts prose in `ConformalCoverage.lean`; do not use this number as an environment census |
| 358 PURE-MATH, 221 REDUCED, 158 EXACT, 14 APPROXIMATION rows | `docs/scope-tags.tsv`; tags describe statements, not whole-model truth |
| All 81 files import umbrella `Mathlib` | Convenient but hides actual dependencies; reducing imports is a separate, measured maintenance task |
| README says 64 modules; AGENTS says 72 | Hand-maintained metadata has drifted; neither is an authoritative coverage record |
| 46 citation-whitelist rows | 28 AUDIT-VETTED, 15 UNVERIFIED, 2 CONVENTION, 1 CORRECTED; whitelist membership is not primary-source verification |

Source paths below are relative to the repository root. The inventory links each module.

## Preserve these achievements

- `Boltzmann`, `ForwardMap`, `Classic`, and `Closure` connect a finite-level model to
  conditional calibration-free recovery. They provide the main narrative spine.
- `SahaEquilibrium` and `SahaContraction` distinguish existence, uniqueness, and convergence.
  The latter's `dampedMultiElementIter_converges_to_equilibrium` supplies a limit and proves it
  is the unique positive equilibrium under its fixed-temperature, two-stage assumptions.
- `RadiativeTransferDepth` contains both finite zone composition and a continuous formal-solution
  integral. It is more than an attenuation-factor stub.
- Self-absorption, line-selection, Stark, noise propagation, and composition results encode real
  diagnostic restrictions. Their domain-specific inequalities should survive organizational moves.
- `Analysis` already consolidates helpers formerly repeated across several modules. It is a useful
  adapter layer, although its current name conceals several distinct mathematical subjects.
- Axiom auditing, declaration-level scope checking, kernel replay, fixture comparison, and curated
  scope metadata are valuable safeguards. Refactoring must preserve their coverage.

## Problems, ordered by effect on understanding

### 1. There is no single physical-model entry point

Population laws and source functions sit next to optimizer convergence, stochastic bounds, and
application gate predicates. `import CflibsFormal` exposes everything. Readers must reconstruct the
physical dependency chain from implementation imports. Introduce small topic entry points while
keeping the umbrella import compatible until its retirement is explicitly reviewed.

### 2. Statement strength and physical derivation are easy to confuse

| Concrete case | Current mathematical content | Required presentation |
|---|---|---|
| `Saha.sahaFactor` | Defines the standard expression; proves positivity and rearrangements | State that the equilibrium law is supplied; do not imply a chemical-potential derivation |
| `LineBroadening` | Defines width formulas and proves properties/inverses; quadrature is an operational rule | Separate Gaussian convolution derivation from width algebra and Voigt approximation |
| `NonLTEKinetics` | Reduced two-level steady-state departure factor | Do not advertise a multilevel time-dependent collisional-radiative solver |
| `TemporalEvolution` | Per-gate soundness under common stoichiometric dilution | Composition invariance depends on supplied non-fractionating ablation; no hydrodynamics derived |
| `ConformalCoverage.ExchangeableRank` | Predicate equating supplied `p` to a covered fraction | Counting theorem plus assumed probability bridge, not a formal proof from exchangeable random variables |
| `Certificates`, `EvaluatorSoundness` | Conditional predicates and implication chains | A runtime Boolean or float mirror is not a proof that all physical hypotheses hold |

Several source docstrings already explain these limitations well. The architecture should expose
those explanations centrally rather than bury them inside individual files.

### 3. Large files mix independently reusable subjects

`SahaEquilibrium` (1,693 lines), `NonlinearLeastSquares` (1,487), `ProfiledTUniqueness` (943),
`EquivalentWidth` (941), and `SahaStability` (882) deserve section-level decomposition. Split by
model/equation/proof responsibility, not an arbitrary line limit. Re-run declaration consumers
before deciding where each section belongs.

### 4. Algebraic generality leaks into the physical narrative

Lean's real division and logarithm are total. An algebraic identity can be valid at zero or with
negative inputs where the intended physical interpretation fails. Keep useful general lemmas;
provide explicit positive-temperature, density, wavelength, partition, and normalization
hypotheses at physical entry points. Do not silently strengthen existing exported signatures.

### 5. Historical and executable material share a documentation surface

`docs/2dcos/README.md` explicitly labels a source monograph unsound and preserves defective code,
while also describing a corrected engine. Keep original, correction, and audit together with
status and provenance. The verified `TwoDCOS` modules must be assessed independently; sharing a
name with an abandoned attempt is not evidence they are invalid. Archive only after consumer and
provenance checks. Generated Python bytecode is a future cleanup candidate, not scientific evidence.

### 6. Existing checks have distinct blind spots

`gen_docs.py` is a source parser, not the Lean environment. `scope-check` checks particular
transitive EXACT→APPROXIMATION edges and reports only 133 of 158 EXACT metadata rows resolved;
its short-name lookup silently filters missing declarations (GAP-05). It cannot certify equation faithfulness or completeness of
all metadata. Changed-module replay compares committed HEAD to a base, excludes deleted files,
and does not include uncommitted edits. A green no-op replay is not a fresh corpus proof audit.

## What this audit does not establish

It does not prove most local mathematics is redundant, that any external repository is axiom-clean,
that all physical citations have been verified, or that the Python companion is verified end to end.
Those claims require the acceptance procedures in the execution handbook.
