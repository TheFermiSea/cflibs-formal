# 10 — Implementation decisions and dependency cuts

[Plan index](README.md)

This final review refines the proposal at `d91cd3e`; it does not implement the migration.
It resolves planning ambiguities using current imports and statements. Where this document
refines a primary home in the inventory, the section-level split below controls the move.

## Decisions for the first implementation cycle

| Question | Decision | Reconsider only when |
|---|---|---|
| What must precede moving files? | F0 repairs scope-name resolution and establishes a reconciled declaration inventory | A narrower change has an independently complete coverage argument; documentation alone can proceed |
| Must an external library be adopted? | No. Use the pinned mathlib first; external trials are optional and isolated | A concrete missing theorem has a better compatible, audited implementation |
| Must public namespaces match new directories? | No. Preserve `CflibsFormal`, `CflibsFormal.Classic`, and `CflibsFormal.Alt` | A separate public API migration is justified |
| Does every proposed folder need to exist? | No. Create a folder only when moving a coherent existing responsibility into it | A second responsibility needs a distinct home |
| Must generic mathematics be removed? | No. Retain readable adapters and domain-specific bounds | An exact replacement reduces maintenance without strengthening premises or weakening conclusions |
| Does reorganization require closing physics gaps? | No. F6 is separate theorem development | An existing advertised claim cannot remain honest without a correction |
| When may an old module path disappear? | After named consumers migrate and the compatibility decision is recorded | Unknown external clients require a documented compatibility window |
| Is dependency-policy review needed for every move? | No. Ordinary mathlib-only moves follow the accepted plan | External imports, toolchain changes, dimensional core types, or scientific scope changes are proposed |

Do not invent a calendar deadline or request a fresh approval for every routine move. The current
user task remains planning only; this document is not authorization to begin implementation.

## Dependency cuts required by the actual source

These are **module-level observed edges**, not proof that every declaration uses each import.
Confirm constant-level consumers before extracting or removing an edge.

| Current dependency | Why a whole-file move is insufficient | Required split and acceptance |
|---|---|---|
| `LineSelection` imports `Certificates` and `Alt.OLSVariance` | Moving it intact under Physics imports application gates and probability machinery | Put `energySpread`, `spreadOn`, and generic finite-data facts with Math/Regression; variance comparisons and their probability witnesses with Inference/Statistics; `energySpreadCert_iff` with Applications/CFLIBS |
| `FisherLineSelection` imports `LineSelection` | Inherits its application/statistics closure | Put spread-update identities with Math/Regression and information/variance results with Inference/Statistics; keep physical interpretation in the diagnostic guide |
| `StarkOpacityGuard` imports `Certificates` | A physical opacity diagnostic would depend on application policy | Extract width/density inequalities that do not mention certificates into Physics/Diagnostics; retain certificate predicates, implication chains, and counterexamples about those gates in Applications/CFLIBS |
| `Identifiability` imports Boltzmann, Saha, ForwardMap, Analysis | `Classic` currently imports the whole mixed module | Separate line-temperature/density and ionization-specific results when F3 reaches them; F1 does not move this entire transitive closure |
| `SahaEquilibrium` contains balance and iteration material | Moving the whole file to Plasma leaves numerical algorithm results mixed with the physical state | Keep balance, existence, uniqueness in Plasma; iteration maps/estimates and `SahaContraction` capstones in Algorithms, depending downward on equilibrium |
| `Closure` imports `Boltzmann` | Its proposed Math/Composition home forbids a physics import | Inspect declaration dependencies; remove a genuinely unused import or split any physical statements upward before accepting the Math boundary |
| `Analysis` serves many physical models | A single large replacement risks several independent proof chains | Extract one mathematical family per change; keep domain-specific constants at their consumers |

For `LineSelection`, do not relabel the slope-variance ranking theorem as joint D-optimality when
candidate cardinalities vary: the source distinguishes slope variance from the determinant
`n * SS_E` and intercept uncertainty. Preserve its actual statement and assumptions when writing
new module summaries. A physics-facing name does not change a PURE-MATH theorem's scope.

**Acceptance:** the final Physics import closure contains no Applications or Inference modules;
Math imports only Math and mathlib. Temporary legacy shims may retain their original broad closure,
but canonical new topic imports must satisfy their promised boundary. Document that difference.

## Define the public surface before counting changes

Maintain one generated declaration inventory for the migration, derived from the built Lean
environment and associated source/module metadata. It should record fully qualified name,
declaration kind, defining module, public/private status where recoverable, elaborated type,
relevant attributes, and whether the declaration has a curated scope row. Store comparisons in
review artifacts rather than creating another hand-maintained theorem catalog.

Use three sets with different meanings:

- **Public contracts:** supported user-facing definitions, theorem constants, instances, notation,
  and import paths. These require preservation or an explicit compatibility/retirement decision.
- **Curated scientific results:** current scope rows and the public named results they cover. These
  require complete resolution and honest scope, including definitions traversed by their proofs.
- **Full audit environment:** all project-prefixed declarations, including generated/private helpers.
  These require axiom coverage; they are not all stable APIs or separate scientific results.

The baseline 751 catalog results, 217 catalog definitions, and 2,092 audited declarations count
different sets. Do not force them to agree. Module moves may rename private auxiliary constants;
account for them without treating that as an undocumented public theorem removal.

For each change, compare sets as well as totals: unchanged public names and types, explicit additions,
explicit retirements, and accounted-for private/generated differences. Equal counts can hide one
missing theorem replaced by another. Exact-byte pretty-printed type comparison is evidence, not
an infallible equality test: investigate differences in binder naming or elaboration separately.

## Boundary and convention checks to keep concrete

| Check | Expected outcome |
|---|---|
| Import new atomic/radiation topic without the root umbrella | Builds without application certificates, statistical estimators, or compatibility-shim imports |
| Import old `CflibsFormal.Boltzmann` or `CflibsFormal.ForwardMap` | Existing public names/types remain available during compatibility period |
| Distinct-energy line pair | Existing reciprocal-temperature identity retains its denominator orientation and assumptions |
| Equal-energy line pair | The distinct-energy theorem cannot be applied; do not let totalized division certify thermometry |
| Positive versus zero temperature | Physical-facing interpretation requires the recorded valid domain; existing general algebra is not silently strengthened |
| Photon-like versus energy observable | Existing conversion is explicit; wavelength-dependent factors cannot be folded into a common scalar without a proved restriction |
| Common calibration versus species-dependent scale | Preserve the common-scale invariance theorem; do not generalize it to independent species scales |
| Fixed-noise slope ranking versus varying line noise | Apply the variance comparison only with its common-noise hypotheses; no claim of universal best line set |
| Closed-loop numerical convergence versus plasma relaxation | Keep distinct targets and separate assumptions; neither theorem substitutes for the other |

These are review cases for future changes, not new tests added by this planning pass. Use existing
witnesses where they establish the intended condition; add focused tests only for an uncovered
regression risk. The [first-change recipe](execution/06-first-migration.md) gives a bounded start.
