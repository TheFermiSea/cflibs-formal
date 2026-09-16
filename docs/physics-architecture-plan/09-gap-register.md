# 09 — Confirmed gaps annotated in source

[Plan index](README.md)

The user requested comments or stubs at gaps identified by this review. Five ordinary Lean block
comments and one shell comment block were added near the relevant definitions and checks. There are
no placeholder declarations, new axioms, changed proofs, or asserted resolutions. These are documented mathematical boundaries;
none is evidence that the existing conditional theorems are invalid.

| ID and source anchor | Existing result | Missing obligation | Priority and completion evidence |
|---|---|---|---|
| GAP-01: [LineBroadening](../../CflibsFormal/LineBroadening.lean), before `gaussQuadrature` | Algebra of a supplied Gaussian width rule | Normalized profile convolution, variance addition, half-maximum/FWHM bridge | P1: positive-width profile theorem reduces to existing rule; separate degenerate limit and Voigt scope |
| GAP-02: [Saha](../../CflibsFormal/Saha.lean), before `sahaFactor` | Defined Saha expression and its algebraic consequences | Statistical-mechanics derivation with translational partition, chemical equilibrium, electron spin, and matching energy conventions | P3: derive the same factor under explicit ideal-gas/LTE assumptions; no assumed Saha relation disguised as derivation |
| GAP-03: [ConformalCoverage](../../CflibsFormal/ConformalCoverage.lean), before `ExchangeableRank` | Finite counting bound plus assumed probability/count equality | Probability-space theorem from exchangeability, measurable scores, test/calibration split, ties, endpoint handling | Downstream optional: actual marginal coverage theorem; do not equate a random realized fraction to a fixed marginal probability without justification |
| GAP-04: [NonLTEKinetics](../../CflibsFormal/NonLTEKinetics.lean), before the two-level section | Reduced steady-state departure coefficient | Specified rate dynamics, positivity, conservation, trajectories, equilibrium and relaxation bridge | P2: a non-vacuous finite-network result with detailed-balance and rate hypotheses; no claim that McWhirter suffices |
| GAP-05: [ScopeCheck](../../tools/ScopeCheck.lean), before `parseTags` | Checks dependencies of names it resolves | Fully qualified scope-row resolution; missing rows currently filtered silently | F0 blocker for claims of complete scope coverage: every row resolves uniquely; unresolved/ambiguous rows fail closed; namespace cases verified |
| GAP-06: [stats.sh](../../scripts/stats.sh), before the counting regex | Counts declaration-like source lines | Comment-aware count / environment reconciliation | F0: explain and remove the 752-versus-751 discrepancy without changing proof content; counters must document their coverage |

GAP-05 is a verification-coverage defect, not a missing physics theorem. The baseline check reports
133 checked EXACT declarations against 158 EXACT metadata rows. The current lookup prepends only
`CflibsFormal` to short names and ignores unresolved entries. Environment inspection confirmed
25 unresolved EXACT rows (3 in `Classic`, 22 in `Alt`) and 7 unresolved APPROXIMATION rows
(in `Alt/CSigmaCurveOfGrowth`). Approximation lookups also need fully qualified keys. Axiom auditing still reports 2,092
project declarations within its allowlist; incomplete scope resolution does not imply new axioms.

## Scope of this register

This is not an exhaustive missing-theorem list. Potential improvements such as more ion stages,
profile truncation bounds, units conversions, and material mass fractions are proposed work in
[physics priorities](04-physics-priorities.md); they have not all been verified absent throughout the
entire environment. Keep that distinction when adding more source annotations.

## Closing a gap

1. Inspect current mathlib and the pinned candidates in [library reuse](02-library-reuse.md).
2. Write the exact target statement and separately list supplied model assumptions.
3. Review a non-vacuity witness and an excluded boundary case before investing in proof automation.
4. Prove the bridge and its correspondence to the existing public definition; preserve callers.
5. Run the proof and metadata gates in the [handbook](execution/README.md).
6. Replace the gap comment with a reference to the completed declaration and update this register
   with the resolving revision. Keep any remaining modeling limitation explicit.

A phase can finish with a deferred research gap if its claims remain conditional and accurately
scoped. No gap should be silently converted into an implementation promise or a required dependency.
