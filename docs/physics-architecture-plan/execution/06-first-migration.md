# First migration — a bounded finite-population and emission slice

[Handbook](README.md) · [Architecture decisions](../10-implementation-decisions.md)

**Future work only.** This recipe starts after F0 coverage repair. It fixes the size and evidence of
the first move so that “refactor the physics” does not become a simultaneous rewrite of all models.

## Move A: two modules, unchanged public declarations

| Current module | Proposed canonical module | Compatibility path |
|---|---|---|
| `CflibsFormal.Boltzmann` | `CflibsFormal.Physics.Atomic.FiniteLevels` | Old module becomes an import-only shim |
| `CflibsFormal.ForwardMap` | `CflibsFormal.Physics.Radiation.IntegratedLine` | Old module becomes an import-only shim |

Preserve the `CflibsFormal` declaration namespace, theorem bodies, assumptions, and attributes.
The existing small modules include some diagnostic consequences; retaining those during Move A is
an intentional intermediate state. F3 can separate responsibilities later. No new physical record,
unit type, partition formula, or logarithm convention is introduced here.

### Procedure

1. Save the exact public declaration/type set of these modules and their current consumers. Include
   at least `partitionFunction`, `population`, `population_sum`, `lineIntensity`,
   `boltzmann_plot_intensity`, and `temperature_from_two_lines` in the compatibility review.
2. Move Boltzmann's source to its proposed path without changing its contents; leave the old import
   shim. Update the defining-module field of its scope rows using the repaired canonical-name map.
3. Move ForwardMap similarly, changing its internal import to the canonical FiniteLevels path.
   No canonical new module may import an old shim.
4. Add only the topic entry point needed for this slice. Keep `CflibsFormal.lean` and old import paths
   compatible; compare the intended root declaration set before and after.
5. Build both new canonical modules, both old paths, the root, and actual downstream consumers.
   Regenerate catalogs and review ownership changes. Preserve the original gaps and scope labels.
6. Run the full protocol, with explicit kernel-replay targets for new modules, changed shims/root,
   and changed consumers. The pre-commit `--changed` selector alone is insufficient.
7. Inspect the new topic's transitive imports. It must not import `Classic`, `Certificates`, `Alt`,
   or the root umbrella to make proof names resolve.
8. Compare fixtures and public signatures; commit the coherent move only after evidence is complete.

**Acceptance:** old and new imports expose the same supported constants; no statement or fixture
change; all scope rows resolve to new ownership; no duplicate definition; no change in physical
claims. Use a fresh project output build before declaring old artifact independence.

## Move B: demonstrate the consumer chain without broadening Move A

After Move A is accepted, migrate a selected consumer to the canonical imports and document this
existing path:

`population_sum` → `lineIntensity` → `boltzmann_plot_intensity` →
`temperature_from_two_lines` → `Classic.classicDensity_recovers` → `Classic.classic_sound`.

This is a **reading path**, not a claim that the final theorem automatically composes all preceding
results. `Classic.classic_sound` takes temperature as an argument; its temperature-recovery theorem
is a separate leg. Do not advertise fused end-to-end estimated-temperature soundness without a
statement that actually connects the recovered temperature to the composition estimator.

Select the required `Classic` declarations and imports by actual use. Do not relocate all of
`Identifiability`, Saha, or error budgets merely because they appear in its current transitive
module closure. Keep source-wide statement decomposition for F3/F4.

## Evidence to review

| Contract | Evidence |
|---|---|
| Public API preservation | Compare qualified names, elaborated types, and attributes; compile representative old and new imports |
| Nontrivial populations | Existing finite weighted normalization statement and a jointly valid positive-state witness |
| Thermometry | Distinct energies and unchanged reciprocal-temperature sign; degenerate pair cannot satisfy its hypothesis |
| Composition | Existing unequal-density two-species witness remains valid; temperature is still explicitly supplied |
| Calibration cancellation | `Classic.classic_calibration_free` retains a common nonzero scale; no species-dependent generalization |
| Scope preservation | Same tags/citations attached to the same qualified declarations; new module ownership resolves |
| Dependency boundary | New physics imports have no path through the legacy root, inference, or application gates |
| Retirement honesty | Shims remain declared compatibility surfaces; no claim of retired public paths yet |

If Move A cannot meet its boundary without changing theorem types or pulling in application code,
stop and revise the split. Do not hide the issue by adding an umbrella import, copying a physical
definition, or introducing an external dependency. Rollback restores both sources, shims, scope
ownership, and generated references as one unit.
