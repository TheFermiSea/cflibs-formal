# Physics-first formalization and refactoring plan

**Status: proposal only.** Prepared 2026-09-15 against
`5daee7c41b3c10e96cff982041a0020dc162a2cf`. Source changes are limited to comment-only
gap annotations requested during review (four physics/probability boundaries and two tooling gaps). No definitions, proofs, theorem statements, imports, dependencies, toolchain, oracle,
or scope classifications change.

## Recommendation

Organize the project around the equations that connect **atomic populations → plasma
composition → emitted radiation → transport → measured spectra → conditional inference**.
Keep mathematical support small and reusable. Preserve the existing proofs of spectroscopy
and inverse-problem guarantees; make their assumptions and limitations visible at the physical
model boundary. Move exploratory methods and historical attempts out of the primary reading path.

The project has substantial domain mathematics already. Its problem is not simply too many
lemmas: a flat 81-module surface mixes physical laws, model assumptions, generic inequalities,
application certificates, and research experiments. Deleting short proofs by size would erase
useful contracts. Reuse must be demonstrated theorem by theorem.

**First choice: the pinned mathlib.** physlib is the strongest external alignment target for
statistical mechanics and dimensions; DynamicalSystems and chemical-reaction libraries may help
future kinetics. SciLean and LML address different needs and are not immediate replacements for
this project's physics. All external adoption requires a separate compatibility and policy decision.
See the source-pinned [reuse assessment](02-library-reuse.md).

## Read in this order

| Document | Purpose |
|---|---|
| [01 — Current-state audit](01-current-state.md) | Evidence, trust boundaries, gaps, and what to preserve |
| [02 — Library reuse](02-library-reuse.md) | Source-pinned ecosystem research and concrete reuse candidates |
| [03 — Target architecture](03-target-architecture.md) | Responsibilities, dependency rules, and readable physical APIs |
| [04 — Physics priorities](04-physics-priorities.md) | Equation chains, acceptance criteria, astronomy/materials overlap |
| [05 — Module disposition](05-module-disposition.md) | Every current Lean module accounted for; supporting artifacts |
| [06 — Proof and physics contracts](06-proof-and-physics-contracts.md) | Statement review, conventions, non-vacuity, trust, and oracle limits |
| [07 — Migration roadmap](07-migration-roadmap.md) | Ordered, bounded changes and completion criteria |
| [Execution handbook](execution/README.md) | Step-by-step procedures, checks, stop conditions, recovery |
| [09 — Source gap register](09-gap-register.md) | Comment anchors and missing proof obligations |
| [Validation record](08-validation-record.md) | What this planning pass actually checked |

## Decisions carried forward

The [existing directive](../../AGENTS.md) remains authoritative: rigor over numerical accuracy;
only `propext`, `Classical.choice`, and `Quot.sound`; mathlib-only imports; a bare-`ℝ` inverse core;
an additive, separately checked dimensional layer; honest scope tags and source verification.
The user-requested broader physics emphasis is reflected in the proposed domain architecture and
research priorities. It does not authorize silently changing these implementation constraints.

This is a specification, not an assertion that the migration or external proof audits have run.
Milestones are dependency ordered, not calendar estimates. Preserve the private repository's
publication boundary: this work does not deploy documentation or submit upstream contributions.
