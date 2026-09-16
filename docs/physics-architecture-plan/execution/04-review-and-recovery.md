# Review receipts, failure handling, and external-library trials

[Handbook](README.md)

## Per-change review receipt

Attach this information to each implementation change, scaled to its size:

```text
Intent / phase:
Base revision and final revision:
Changed modules and declarations:
Old and new public theorem types / attributes:
Physical equations and conventions affected:
Supplied assumptions / derived conclusions:
Consumers migrated and compatibility paths retained:
Scope rows / citations / generated references:
Non-vacuity witness and excluded case:
Build, audit, linter, scope and replay commands + results:
Actual replayed module list:
Oracle and companion correspondence result:
Unresolved limitations:
Retirement evidence, if applicable:
Rollback commit or bounded inverse change:
```

“No theorem statement changed” must be supported by source/type comparison. “Axiom-clean” must
name the audited roots/revision and report the actual audit result. “Physically faithful” needs
statement/source review, not just a build log.

## Failure response table

| Failure | Immediate action | Diagnosis | Recovery / acceptance condition |
|---|---|---|---|
| Import fails after move | Stop the family migration | Canonical path, shim direction, root coverage, untracked file | Fix dependency direction and rebuild consumers; no copied definitions |
| Build passes only with old cache | Reject apparent success | Missing target/source, stale `.olean`, omitted aggregator import | Fresh-output build under same pins; complete module census |
| New theorem changes inferred arguments | Treat as API change | Namespace, section variables, typeclass/implicit parameters | Preserve signature or review explicit API migration separately |
| Simplifier regression | Isolate changed attributes | `[simp]` duplication, orientation, reducibility, instance priorities | Restore stable attribute set; add focused caller evidence |
| Axiom audit fails | Stop acceptance | Complete selected constant closure, external imports, placeholders | Remove disallowed dependency; never extend allowlist to fit the proof |
| Scope check fails | Inspect dependency and scientific claim | EXACT uses approximation; stale metadata; hidden stronger model | Correct statement/architecture or honest classification with review |
| Catalog loses results | Block retirement | Parser limitations, renamed module keys, visibility changes | Reconcile source and environment; restore coverage |
| Oracle changes | Stop structural refactor | Convention/definition/order/rounding differences | Explain and separate science fix; do not bless new fixtures blindly |
| Kernel replay reports no modules | Check selection | Working tree uncommitted or wrong base | Replay explicit built modules; record actual selection |
| Replay is killed / times out | Record incomplete gate | Worker count, memory, environment size | Reduce bounded concurrency; retry same target; no pass inferred |
| Statement has no physical witness | Stop theorem work | Contradictory premises, zero-rank case, conclusion assumed | Repair statement before proof automation |
| External package fails pins/trust | Keep existing implementation | Version, assumptions, license, transitive axioms | Defer candidate or approve a bounded port; no surprise upgrade |

## Safe rollback

1. Identify the smallest coherent failed change and its consumers.
2. Preserve failure evidence and unrelated/user changes.
3. Revert that change's source, metadata, generated references, and fixtures together if they were
   legitimately part of it. Never use a broad hard reset as routine recovery.
4. Rebuild the restored targets and rerun the relevant gates; reverting text alone may leave stale
   build artifacts or broken callers.
5. Record the failed assumption and revised smaller next step. Do not repeatedly attempt the same
   incompatible abstraction without new evidence.

## External-library experiment protocol

This is a future, isolated experiment; this planning pass only inspected public source.

1. Name one local declaration or missing scientific bridge and its consumer. A broad desire to
   “use physlib” is not a testable experiment.
2. Create an isolated candidate checkout with explicit Lean, mathlib, and external revisions.
   Preserve the production pins. Compare every dependency, not just the top-level toolchain string.
3. Inspect repository and file-level licenses and notices before porting. physlib/DynamicalSystems/
   SciLean sources inspected here use Apache-style notices; crnt-lean uses MIT. Recheck the selected
   files and transitive copied material rather than assuming one repository license covers all.
4. Inspect the external theorem type, imported definitions, and all axioms in its closure. A README
   “no sorry” claim or source-text scan does not discharge this.
5. State the adapter equalities and restrictions. Examples: integer versus real degeneracy weights,
   positive versus nonnegative temperature, fixed versus parametric constants, closed versus open
   invariant domain, supplied versus proved solution existence.
6. Build and audit the candidate plus adapter under a mutually compatible pin set. Replay selected
   imported/ported and adapter declarations; retain the evidence and limitations.
7. Compare the old API, sharpness of bounds, build/runtime footprint, maintainability, and physical
   readability. A larger dependency for a three-line adapter may not be worthwhile.
8. Choose: keep local proof; reuse existing mathlib; port a small attributed result; propose upstream
   work; or propose an optional adapter target. Present any dependency-policy change as a separate
   reviewable decision. Do not silently connect the external target to the dimensionless inverse core.
9. Only after acceptance migrate consumers and retire the superseded implementation. Upstream
   publication, issue filing, or maintainer messages require the project's separate authorization.

## Final architecture review

Ask a reviewer to trace one equation chain without the migration author:

- Where are the state, supplied laws, observables, and validity assumptions defined?
- Which theorem connects the observable to a diagnostic or inferred composition?
- Which effects are approximated, excluded, or represented only by input parameters?
- Which mathematical helper is reused from mathlib, and why does its domain apply?
- What remains unproved, and where is the corresponding source annotation?
- Can old imports and numerical mirrors still be accounted for, or is retirement documented?

A successful review should answer these from the code and docs, without relying on the author's
memory. That is the practical test of the refactor's readability.
