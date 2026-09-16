# F3–F6 — Migrate domains, retire safely, extend the science

[Handbook](README.md)

## F3 — Make physical models the primary library surface

**Entry:** F1 migration pattern accepted; F2 complete for any helpers this move actually touches.

### Steps

1. Split `SahaEquilibrium` by conserved populations, charge-balance map, equilibrium existence and
   uniqueness, and iteration estimates. Keep the latter with algorithms; physical definitions must
   not import iteration convergence merely to expose charge balance.
2. Organize radiation by emitted observable, opacity, transfer, and profile/width model. Preserve
   `RadiativeTransferDepth`'s discrete and continuous content; mark source functions that are supplied.
3. Organize diagnostics around what a measured quantity identifies: temperature, electron density,
   optical depth, or a model-validity restriction. Preserve rank and positivity preconditions.
4. Keep `Dimensions` independently auditable. If changing its representation, first prove the
   four-field/exponent-function equivalence as a separate F2-style change.
5. Migrate one family at a time with shims. Update tags, aggregators, documentation, and consumers
   for each family before starting the next.
6. Produce physical entry-point pages with equation, domain, scope, source, and theorem links.
7. Run the protocol and an import-boundary review. Build each topic independently in addition to
   the umbrella, then replay affected modules and key consumers.

**Checks:** no estimator/application dependency from physics; all conserved quantities and stage
truncations visible; no duplicated source function or width convention; every old result accounted
for in the inventory; no claim that GAP-01/02/04 was solved by moving files.

**Stop:** a proposed split needs a changed equation, or a dependency cycle is resolved by copying a
physical definition. Review shared ownership instead.

**Exit:** coherent plasma, radiation, and diagnostics reading paths. **Recovery:** revert one family
and its metadata atomically; retain already accepted independent families.

## F4 — Separate inference, algorithms, statistics, and runtime correspondence

**Entry:** physical definitions stable; mapped consumers for the affected capstones.

### Steps

1. Separate generic finite-data OLS from physical Boltzmann-plot inputs and their validity conditions.
2. Group identifiability results by forward model. Separate existence of an inverse, uniqueness,
   conditioning, and algorithmic convergence; none implies all the others.
3. Move deterministic perturbation bounds together while preserving per-source constants and
   correlated/systematic error handling. Keep stochastic variance/coverage in a distinct layer.
4. Preserve `Alt` declaration names initially, but organize files by estimator or statistical
   responsibility. Alternative methods reuse the same physical laws.
5. Review `Certificates` and `EvaluatorSoundness` clause by clause. Label each hypothesis as supplied
   by the physical model, checked by an exact predicate, approximated in floats, or unverified.
6. Check Python mirror and oracle correspondence by definition, not filename. Record both repository
   revisions; do not change the companion code as a side effect of this project’s reorganization.
7. Run old-client imports, representative theorem applications, fixtures, and the full gate protocol.
8. Review the resulting application capstone against its physical assumptions and numerical limits.

**Checks:** no deterministic/RSS mixing; no coverage claim from assumed `ExchangeableRank` alone;
no Boolean accepted as a proof of LTE or a strict numerical inequality; all profile approximations
still exposed to diagnostics.

**Stop:** fixture drift, a changed error budget, a newly assumed rank bound, or an API change hidden
inside a move. Split scientific corrections from organization.

**Exit:** each inference chain identifies its physical model and trust boundary. **Recovery:** restore
consumer and metadata changes with the affected model interface; do not overwrite oracle expectations.

## F5 — Retire duplicate surfaces and separate historical attempts

**Entry:** migrated consumers, replacement receipts, and an explicit compatibility decision for each
old import path. A lack of internal references alone is not sufficient.

### Steps

1. Re-run declaration and path consumer searches across source, tools, tests/examples, upstream seed,
   generated references, documentation, and known companion integrations.
2. Classify remaining shims: still required public compatibility, eligible for retirement, or blocked
   by an unknown external consumer. Record the policy rather than leaving unexplained temporary files.
3. For eligible shims, remove the old path, migrate its remaining clients, and verify the new topic
   aggregator and root still expose the intended declaration set.
4. Classify each research artifact. Keep known-invalid originals with ERRATA and corrected versions;
   do not present them as current executable examples. Archive paths need reciprocal provenance links.
5. Review tracked generated caches separately. Remove only artifacts proven unnecessary; do not
   delete scientific inputs, audit evidence, or historical source merely to shrink the tree.
6. Regenerate references and reconcile front pages/roadmaps. Every missing API or dropped capability
   needs a retirement receipt, not just a smaller diffstat.
7. Build in a fresh output directory/worktree with pinned dependencies. Run all targets and the
   broader kernel sweep appropriate to the migration; deleted modules cannot be replayed directly.
8. Verify public import behavior, gates, fixtures, and the physics reading map. Land the bounded
   retirement change with a recoverable commit and updated compatibility record.

**Checks:** no stale `.olean` masking removed source; no duplicate active law definitions; no lost
scope/citation row without a corresponding retirement; no archive imported by the shipped library.

**Stop:** an old engine is still a consumer's only implementation, provenance would be lost, or the
new root misses declarations. Preserve it until the missing decision or replacement is supplied.

**Exit:** justified retirement and navigable history. **Recovery:** restore the specific retirement
commit and metadata; never reset unrelated accepted work or the user's branch.

## F6 — Fill one physical proof gap at a time

**Entry:** relevant architecture stable; a gap-register ID or approved physical work package.

### Steps

1. State the intended equation and observable. Verify the primary-source equation and its assumptions;
   preserve existing citation status until this is done.
2. Write the Lean target signature before the proof. List supplied physical laws separately from the
   mathematical conclusions. Review it for circular assumptions and totalized-operation edge cases.
3. Build a jointly satisfiable non-vacuity example and a diagnostic failure case before pursuing a
   large automated proof. Revise the model if the intended examples cannot satisfy its premises.
4. Search pinned mathlib, then source-pinned external candidates. Follow F2 for reuse; do not add an
   external package without the independent trial described in review/recovery.
5. Prove the mathematical foundation and the equality/correspondence to existing scalar definitions.
   Example: GAP-01 closes only after profile convolution and FWHM connect to `gaussQuadrature`.
6. Add the capstone, its proper scope row, verified citation, and generated documentation. Check
   transitive scope; a supplied empirical fit does not become exact because subsequent algebra is.
7. Run the complete protocol and independent replay. Update fixtures only for separately justified
   new behavior, never as an unexplained baseline rewrite.
8. Replace the gap annotation with the completed theorem reference. Record residual assumptions and
   resolving revision; update scientific priorities to reflect actual new capability.

**Checks:** new physical conclusion clearly identified; no proof placeholder; no claim of numerical
accuracy; hypothesis audit and kernel audit both complete; existing clients and conventions preserved.

**Stop:** statement is vacuous, requires an unsupported physical assumption, or the library candidate
has an incompatible trust base. Leave the gap open with a precise reason.

**Exit:** one completed equation/bridge, not just more helper lemmas. **Recovery:** keep accepted
independent mathematics only if useful and honestly scoped; revert unaccepted model changes together.
