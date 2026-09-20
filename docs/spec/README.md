# cflibs-formal — Development Specification (v0.2, 2026-09-20)

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

## How this spec is maintained (it is a living document)

- **Where it lives.** `docs/spec/` on branch `docs/formalization-spec`, tracked by a **draft PR** that
  stays open as the mutable guide. Discussion happens in PR review comments; agreed changes land as
  commits on the branch. The PR is never merged as-is; when a phase completes, the durable parts
  (module docstrings, `docs/frontiers/*` dossiers, `docs/conventions.md`, `CONTEXT.md`) are updated on
  `main` through their own PRs, and the spec's status table is updated here.
- **Versioning.** Bump the version in this file's title and add a line to the change log below whenever
  a statement, tag prediction, budget, or decision changes. Never edit a frozen pre-registration; write a
  deviation note instead (`scripts/prereg.sh` header explains why).
- **Drive copies.** The Google-Docs copies ("cflibs-formal spec 00..06") are read-only snapshots and go
  stale; the branch is canonical. Re-export after a version bump if the Docs copies are being read.
- **What may not change without a decision by the repo owner:** the four non-negotiables; a scope tag
  from REDUCED/APPROXIMATION up to EXACT; adding any dependency; the refusals list in `06-milestones.md`.

### Decisions pending (owner's call; the spec proceeds under the stated default)

| # | Decision | Default assumed here | Where it matters |
|---|---|---|---|
| D1 | Instrument model: abstract kernel with the companion's Gaussian IRF as first instance, vs. Gaussian-only | abstract kernel | `03` §3.2 |
| D2 | Where the stoichiometry corollaries live: `MatrixEffects.lean` vs. `TemporalEvolution.lean` | `MatrixEffects.lean` | `03` §4 |
| D3 | Whether to run the Frontier 02/07 dry run (costs a budget, has ground truth) before the cascade | yes | `04` §8, `06` Phase 0 |
| D4 | Budget ceilings per phase | as listed in `06` | `06` |
| D5 | Whether to submit the Saha seed to PhyslibAlpha in this cycle or defer | defer to Phase 5 | `04` §7.8, `docs/upstream-physlib-plan.md` |

### Change log

| Version | Date | Change |
|---|---|---|
| v0.1 | 2026-09-20 | Initial seven-file spec; blueprint audit; harness design |
| v0.1.1 | 2026-09-20 | S7 reduction statement: added `0 < ne` (load-bearing); acceptance wording for reductions corrected. (The `0 < S s 0` added at the same time was found unnecessary in v0.2 and removed.) |
| v0.2 | 2026-09-20 | Deep review pass: mathlib lemma names verified and pinned (`LinearMap.ker_eq_bot`, `integral_sub_right_eq_self` via `to_additive`, Chebyshev lemma names), S4 hypotheses stated, S5/S6/S8 binders (incl. `[Nonempty κ]`) and S9 index-type design corrected, S7's unnecessary `S`-positivity removed, `λ` identifiers renamed `lam`, Gershgorin cited for K4, K3 injectivity dropped, L1 weakened to `0 ≤ γ`, G4 Doppler binding added, third stoichiometry theorem dropped, worktree/olean and reviewer-vocabulary/tooling facts corrected, prereg audit scoping and runLinter invocation corrected, red-team blinding and dry-run contamination control added, maintenance and decisions sections added; independently audited (21 findings, all applied); the draft PR that carries this spec was opened with this version |
| v0.2.1 | 2026-09-20 | Consistency: G3/G4 rows in the scope-tag table (05 §3) aligned with 03; S9 grade B in the prereg draft; reviewer-agent row in 04 §2 no longer calls it read-only before the Phase-0 change |

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
