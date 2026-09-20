# cflibs-formal — Development Specification (v0.1, 2026-09-20)

This directory is the **working specification** for the next phase of `cflibs-formal`. It replaces the
two Google-Docs drafts ("Lean 4 Scientific Autoformalization", "Revised Architectural Blueprint:
Formalizing CF-LIBS in Lean 4") as the canonical plan; those drafts were audited and their
verified content is folded in here. The repo is the system of record; a Google-Docs copy of this
spec is published for reading only.

## How to read this

| File | Answers | Read when |
|---|---|---|
| `01-blueprint-audit.md` | What in the Revised Blueprint is true, false, already done, or unverifiable | Before touching any module the blueprint proposes |
| `02-architecture.md` | What the repo is today (layers, invariants, namespaces) and the target architecture with the proposed modules placed in it | Before designing a new module |
| `03-module-specs.md` | Per-module dossiers: obstacle, statement, scope tag, literature, mathlib prerequisites, milestone A, acceptance criteria, pre-registration drafts | When starting a module |
| `04-autoformalization-framework.md` | The agent harness this repo will run: roles, tools, gates, the red-team protocol, budgets, and the boundary-pushing proposals | Before running any agent on this repo |
| `05-verification-governance.md` | Gates, CI, scope tags, citation policy, agent policy, review checklists | Before accepting any result |
| `06-milestones.md` | Phased plan with entry/exit criteria, budgets, and what is deferred or refused | For planning and status |

## Status vocabulary (used throughout)

- **VERIFIED** — a primary source was opened (Lean source in this repo, the pinned mathlib checkout,
  an arXiv abstract/HTML page, a GitHub README) and it supports the claim.
- **CORRECTED** — a primary source contradicts the claim as written; the corrected form is given.
- **UNVERIFIED** — only a secondary summary was seen, or nothing was opened. Treat as a lead, not a fact.
- **DONE** — the declaration exists in `CflibsFormal/` today (checked by grep on 2026-09-20).
- Scope tags keep the repo meaning: **EXACT / REDUCED / APPROXIMATION / PURE-MATH** (`docs/scope-tags.tsv`).
- Tractability grades keep the frontier-dossier meaning: **A** (no unmet dependency, mostly
  bookkeeping), **B** (new glue, all mathlib present), **C** (needs absent infrastructure or is refused).

## Non-negotiables (unchanged; restated so this spec cannot drift from AGENTS.md)

1. Axiom-clean: every declaration depends only on `propext`, `Classical.choice`, `Quot.sound`.
2. mathlib-only imports. physlib is an upstream target, not a dependency.
3. Dimensionless `ℝ` core; `Dimensions.lean` is additive and never wired into the core.
4. Honest scoping: the statement is audited, not just the compile. A green proof of the wrong
   statement is worthless.

## One-paragraph summary of the plan

The physics roadmap adds four capabilities the current spec lacks: a **Z-stage ionization cascade**
with a unique charge-neutral electron density (the one genuinely new piece of the blueprint), **continuous
line profiles** (Lorentzian, Gaussian, Voigt-as-convolution) built by reuse of mathlib's Cauchy and
Gaussian densities and this repo's existing `lorentzian`, a **spectrometer kernel** that maps continuous
line emission to pixel sums and certifies when line intensities are recoverable, and two **stoichiometry
corollaries** that fall out of `Closure` and `MatrixEffects` in a few lines. Each lands with a certificate
in `Certificates.lean`, an oracle scenario, and a scope-tag row. The development method is an
**autoformalization harness** rather than an external framework: a general coding agent with Lean LSP
tools, a read-only adversarial statement reviewer that must first pass a seeded-drift red team, preregistered
statements, isolated workers that never run `lake build`, and the existing gates run by the lead. The
boundary-pushing part is the faithfulness tooling: a CF-LIBS drift benchmark derived from
`docs/conventions.md`, oracle fixtures as shadow theorems, blueprint-attribute parity between
`## Literature` prose and declarations, a vendored vacuity checker, a disprove-first step, and an
agent-driven upstream path into PhyslibAlpha.
