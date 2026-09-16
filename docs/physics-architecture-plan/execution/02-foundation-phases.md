# F0–F2 — Establish evidence and prove the migration pattern

[Handbook](README.md)

## F0 — Baseline, consumers, and model decisions

**Entry:** accepted organizational scope; unchanged pinned toolchain; known starting revision.

### Steps

1. Capture repository state and run the core gates in [working rules](01-working-rules.md). Record
   failures as baseline findings, including environment/resource causes; do not call them passes.
2. Enumerate every tracked module, root import, named declaration, scope row, and generated reference.
   Reconcile `stats.sh`'s prose-count discrepancy with `gen_docs.py` and the Lean environment.
3. Resolve GAP-05: scope rows must map to fully qualified declarations, including `Classic` and
   `Alt`; unknown/ambiguous names must fail closed. Check approximation lookup coverage as well as
   the EXACT starting set. Keep this tooling correction separate from physics moves.
4. Establish a public API set: exported names/types, implicit parameters, attributes, and import paths.
   Include the `Alt` namespace and separate `SahaUpstream` target.
5. Map direct and transitive consumers of the first physical slice. Source search gives candidates;
   inspect elaborated constant dependencies where a retirement decision depends on actual use.
6. Fill the assumption ledger for `Boltzmann`, `ForwardMap`, `ForwardMapEnergy`, `Classic`, and Saha
   closure. Identify supplied equations, photon/energy conventions, and normalization domains.
7. Compare existing frontiers/gap documents to the new priorities. Record disagreements and their
   dispositions; preserve history rather than silently rewriting old decisions.
8. Define a bounded first change and its rollback boundary. Keep scientific derivation gaps separate.

**Checks:** every module accounted for; no supposedly unused declaration classified solely by import
fan-in; all public claims tied to a statement; pinned lockfile unchanged; failing gates explained.

**Stop:** missing root coverage, unresolved meaning of an observable, or unexplained API/census
mismatch. Repair that evidence first in a separate change.

**Exit:** a reproducible baseline and approved first-slice declaration list. **Recovery:** discard
only this phase's experimental files; retain baseline logs and unresolved findings.

## F1 — Finite populations to observed lines: first vertical slice

**Entry:** F0; exact ownership list and consumer map for the slice.

### Steps

1. Draw the actual chain from finite weighted levels through partition/population to line intensity,
   temperature diagnostic, and composition closure. Mark each supplied physical relation.
2. Propose file boundaries for definitions, physical properties, and diagnostic consumers. Avoid
   simultaneous public-namespace changes or new state-record abstractions.
3. Move the smallest leaf definitions/proofs first, preserving bodies and declaration types.
4. Make old module paths import-only shims. Change new internal consumers to canonical new paths;
   prevent reverse dependencies through shims.
5. Add a small topic aggregator and update umbrella coverage. Keep the legacy umbrella compatible.
6. Update scope-tag module keys, generated references, and source links atomically.
7. Build the slice and actual consumers; run full required gates before acceptance. Exercise a
   representative old import and new topic import with existing public statements.
8. Review the physical reading sequence with the ledger in front of the code. If it requires opening
   optimizer or correlation files to understand the emission model, the boundary is not ready.

**Checks:** theorem types/attributes unchanged; one definition per physical quantity; old import
clients still compile; photon/energy variants distinct; witnesses and fixtures unchanged.

**Stop:** an equivalence proof is suddenly needed for a purported move, scope rows disappear, or a
physics module must import application gates. Split representation changes out and fix the boundary.

**Exit:** a reusable migration example, not a skeleton of empty folders. **Recovery:** revert the
coherent move and metadata changes together; rebuild old targets, never just restore a shim.

## F2 — Replace proven mathematical duplication

**Entry:** F1 pattern established; one candidate from the reuse matrix with exact source revision.

### Steps

1. State the local theorem and all its consumers. Identify whether the proof is generic or encodes
   a physical constant/domain that must remain local.
2. Locate the candidate in pinned mathlib and inspect its complete type. Record any stronger
   assumptions, nonempty/complete-domain conditions, norm conventions, and type conversions.
3. Write a small adapter preserving the old theorem type. Prove needed domain invariance or
   completeness explicitly. An open positive interval is not a complete domain by default.
4. Compare the new proof dependency/axiom closure and compilation behavior. Keep a direct proof if
   the adapter is substantially harder to read and provides no maintenance benefit.
5. Change one consumer family, then the rest. Keep a compatibility theorem only when public callers
   need it; do not leave two independent active implementations.
6. Remove the replaced proof body only after all callers pass. Preserve useful domain-facing names,
   docstrings, and sharp constants even if their implementation is now a short `exact`/`simpa`.
7. Run the full protocol and changed-module replay. Review non-vacuity and generated scope metadata.
8. Record a replacement receipt: old statement, imported result, adapter, consumers, and deletion.

**Checks:** old statement still available; no weakened bound or strengthened premise; no new axioms,
external import, or implicit toolchain update; actual simplification measured rather than assumed.

**Stop:** the only available theorem is on a newer toolchain, an external assumption is unproved,
or proof size falls only because a physical premise was assumed. Defer the reuse trial; keep local
correct code.

**Exit:** one justified replacement, then repeat. **Recovery:** restore the old proof and its consumers
as a unit; retain the failed match record so the same incompatibility is not repeatedly rediscovered.
