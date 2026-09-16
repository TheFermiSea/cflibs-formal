# 07 — Migration roadmap

[Plan index](README.md)

Do not implement this entire plan as one change. The first migration should be small enough to
review theorem types and assumptions individually. No phase requires adding an external dependency.

| Phase | Deliverable | Prerequisite | Exit condition |
|---|---|---|---|
| F0 — Baseline and decisions | Revision/pins, environment census, assumption ledger, consumer map | Accepted planning scope | Existing gates characterized; GAP-05/06 reconciled before claiming full coverage; no unexplained missing declaration |
| F1 — Physics reading slice | Atomic populations → emission → diagnostic → composition navigation | F0 | One end-to-end chain readable with explicit supplied laws and preserved public API |
| F2 — Reusable mathematics | Small audited mathlib substitutions/adapters | F1, exact candidate matches | Old statements preserved; selected duplicate proofs retired; no lost domain constants |
| F3 — Physics modules | Domain folders and narrowly scoped topic imports | F1; F2 only for touched helpers | Physics no longer depends on estimator/application wrappers; metadata and roots complete |
| F4 — Inference and bridges | Estimators, stability, statistics, algorithms, application contracts separated | F3 | Each capstone names its physical model; deterministic/statistical bounds and runtime assumptions distinct |
| F5 — Retire and document | Approved shim removal, historical research separation, consistent catalogs | F4 and consumer migration | No duplicate active implementations; old paths removed only with retirement evidence |
| F6 — Extend the science | One prioritized missing equation/bridge per work package | Relevant physical slice stable | Statement review, non-vacuity, proof, scope/citation review, correspondence gates all pass |

F6 is deliberately not a prerequisite for a useful organizational refactor. The source gap comments
remain useful even if a deeper derivation is deferred. An external-library trial is an independent
experiment after F0, never a reason to block all mathlib-only cleanup.

## Suggested reviewable change sequence

1. Baseline records and a physics reading guide; repair inventory tooling in its own change if needed.
2. One finite-population/emission slice moved with import shims, existing names, and unchanged proofs.
3. One mathlib adapter replacement with an exact old/new statement comparison.
4. Plasma closure split into physical equilibrium and algorithmic convergence.
5. Radiation/profile/diagnostic split; preserve supplied versus derived boundaries.
6. Inference/application split and companion correspondence review.
7. Research/archive cleanup with provenance and consumer checks.
8. Remove eligible shims; retain any externally required compatibility explicitly.
9. Select GAP-01 or another P1 scientific bridge as a separately reviewed theorem task.

These are proposed change boundaries, not completed work. Parallel implementation is safe only
where declaration ownership and imports are disjoint; shared public definitions have one owner.

## Completion criteria

The refactor is complete when a physicist can locate each prioritized law, its assumptions, its
proven consequences, and its diagnostic consumers; mathematical helpers have justified homes;
public compatibility and retirement decisions are explicit; and the complete verification surface
still covers all shipped declarations. A smaller theorem count is neither required nor sufficient.

The [execution handbook](execution/README.md) provides concrete procedures and recovery rules.
