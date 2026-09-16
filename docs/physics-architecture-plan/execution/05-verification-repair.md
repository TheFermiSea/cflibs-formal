# F0 repair specification — scope coverage and declaration accounting

[Handbook](README.md) · [Gap register](../09-gap-register.md)

This is a future implementation specification for GAP-05/06. No checker logic, metadata format,
or proof changes are part of the current planning review.

## Repair GAP-05 before relying on a green scope gate

### Contract

Each curated row must identify exactly one current, intended declaration. The checker must reject
malformed rows, unknown tags, unresolved names, duplicate/conflicting assignments, and a claimed
defining module that does not match the resolved source ownership. Missing data must not disappear
through filtering or map insertion. Diagnostic output must name the row and reason.

Use fully qualified Lean names as the internal key for **both** starting declarations and dependency
lookups. Keep traversal through definitions and theorem types as well as proof bodies. Do not infer
namespace from a file path: `Classic` and `Alt` already demonstrate why that is unsafe.

### Recommended migration

1. Capture the current rows and the built declaration inventory. Preserve the original TSV for the
   comparison; do not fix missing names by deleting rows.
2. Resolve existing `(module, short name)` entries against declaration ownership in the environment.
   Require a unique match; explicitly record unresolved or ambiguous cases for review.
3. In one tool/metadata change, make the declaration-name field in `scope-tags.tsv` fully qualified,
   retaining module, tag, and citation fields. Update `gen_docs.py`, scope checking, and all other
   consumers together. Preserve the assigned scope and citation of every result.
4. Make document generation consume the same canonical name mapping. Do not maintain two independent
   namespace-guessing implementations or silently treat the first namespace in a file as universal.
5. Reject duplicate keys even if their tags agree; normalize only documented whitespace/comment
   conventions. A partial parse is a failure, not a successful smaller dataset.
6. Resolve all tags, not just EXACT. Verify the APPROXIMATION set can be found on dependency paths.
7. Compare curated named results against the intended source/environment result set. Definitions,
   generated helpers, private witnesses, and explicit compatibility aliases require documented
   treatment; they must neither inflate scientific counts nor conceal omitted public results.
8. Run the dependency check on the full resolved set. Newly found violations require statement or
   classification review; preserving the previous green outcome is not an acceptance requirement.
9. Regenerate catalogs, run axiom/scope/linter/oracle gates, and replay changed verification modules
   as well as any changed library modules. This repair must not alter physics proofs to pass.

The exact representation may be refined during implementation, but full-name identity, complete
resolution, and rejection of invalid input are required. Do not add a second authoritative scope
ledger. Existing module fields describe ownership; old import shims do not own imported declarations.

### Required regression cases

Use isolated miniature inputs and declarations, not corrupted production scope data or disallowed
axioms. A mathematical theorem can be tagged APPROXIMATION solely in a test fixture to exercise
the checker without asserting a new physical law.

| Case | Required result |
|---|---|
| Root, `CflibsFormal.Classic`, and `CflibsFormal.Alt` names | Resolve correctly and participate in checks |
| Same short name in two namespaces | Qualified rows remain distinct; ambiguous legacy row rejected |
| Misspelled/missing theorem; renamed source with stale module field | Nonzero exit with named row |
| Invalid tag, missing field, duplicate row, conflicting duplicate | Nonzero exit; no silently discarded row |
| EXACT directly or transitively uses APPROXIMATION | Nonzero exit with a dependency path |
| Path crosses a definition or includes a type-level dependency | Same failure; wrappers cannot hide the approximate dependency |
| EXACT imports a mixed module but does not use its approximate declaration | Pass; avoid reverting to module-level false positives |
| APPROXIMATION declaration in `Alt` | Recognized as a dependency target as well as a resolved row |
| Declared result omitted from its intended build/audit root | Coverage reconciliation fails, even if the remaining root builds |
| Added private/generated helper | Accounted for in axiom audit without inventing another scientific result |

At the unchanged baseline, resolution should account for **all 158 EXACT and 14 APPROXIMATION
rows**, including the previously missed 25 and 7 respectively. All 751 curated rows must resolve
under their own tags. These are baseline expectations, not permanent magic constants: future
accepted additions/removals change expected sets through a reviewed inventory diff.

## Repair GAP-06 without confusing counts

The stats regex counts the prose line beginning `theorem says` in `ConformalCoverage`; the existing
doc parser skips it. A quick repair can share a single comment-aware source census with documented
declaration forms, but that is not a substitute for the environment inventory used for trust.

Acceptance cases: nested Lean comments; docstrings containing `theorem`/`def`; attributes split over
lines; namespaces; multiline declarations; private/protected declarations; examples; and new nested
source directories. Decide and document which forms belong to the public result census. Do not
relabel or edit valid Lean declarations to accommodate a weak parser.

At the current baseline, retain the explained 751/217 catalog totals and separately report the full
audit set. Compare actual names, not only the integer total. The repair is complete when stats,
generated references, curated scope, and audit coverage have compatible, explicit meanings.

## Deliverable and stop condition

Deliver one reviewable tooling/metadata change with unchanged scientific content, positive and
negative regression evidence, complete resolution, and a list of any newly exposed scope violations.
If it exposes such violations, stop the structural migration until their dispositions are reviewed;
do not suppress the test, weaken the rule, or silently retag the results.
