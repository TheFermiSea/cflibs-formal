# Copilot instructions — cflibs-formal

`cflibs-formal` is a **machine-verified Lean 4 + mathlib `v4.31.0`** specification of
calibration-free LIBS (CF-LIBS): the forward plasma-emission model, the inverse
composition-recovery problem, and the identifiability/reliability theorems that say *when and why*
the inversion is well-posed. When reviewing, judge changes as a **formal-methods reviewer**, not a
general software reviewer — "correct" here means *the proof is sound and the statement faithfully
says what it claims*, not that code runs fast or reads idiomatically.

## The cardinal rule: rigor, not accuracy

**The value of this repo is provable rigor, never numerical accuracy.** A green proof of a vacuous,
tautological, or physically-wrong statement is worthless. So:

- **Audit the statement, not just the compile.** Ask: is this theorem non-vacuous? Do its
  hypotheses secretly make the conclusion trivial (e.g. an empty domain, `0 = 0`, a hypothesis that
  already implies the goal)? Does the *docstring claim more than the theorem proves*? Overclaiming a
  docstring is a real defect worth a comment.
- **Do not suggest "accuracy" improvements**, curve-fitting, tuning, or better numerics. That is
  explicitly out of scope; such suggestions are noise here.

## The four non-negotiables — flag any change that breaks one

1. **Axiom-clean.** Every declaration may depend only on `{propext, Classical.choice, Quot.sound}`.
   Flag any new `sorry`, `admit`, `native_decide`, `axiom`, or `@[implemented_by]`/`unsafe` that
   could introduce trust. New `axiom` declarations are almost always wrong here.
2. **mathlib-only imports.** Every module imports only `Mathlib` and `CflibsFormal.*`. Flag any
   new external dependency or non-`Mathlib`/non-`CflibsFormal` import.
3. **Dimensionless `ℝ` core.** The inverse-problem core is bare `ℝ`. The `Dimensions.lean` layer is
   additive and must **not** be wired into the core — flag core modules that start importing/using
   the dimensional layer.
4. **Honest scoping.** Every result is classified **EXACT / REDUCED / APPROXIMATION / PURE-MATH**.
   The docstring's claim must match the classification. Flag a docstring that describes an
   approximation as exact, or a reduced/idealized model as the full physics.

## Two-track architecture — never let these mix

- Core physics/inverse machinery lives in `namespace CflibsFormal`. Alternative estimators live in
  `namespace CflibsFormal.Alt` under `CflibsFormal/Alt/`.
- **Core must never import `CflibsFormal.Alt`.** A core→Alt import is a hard architectural
  violation — flag it.
- **Define each concept once and reuse it verbatim.** If a change re-implements a def/lemma that
  already exists (common targets: shared analysis helpers in `Analysis.lean`, Boltzmann/Saha
  factors, partition functions), flag the duplication and name the existing declaration to reuse.

## Scope tags and citations — the integrity spine

- Every new non-`private` `theorem`/`lemma` must have a row in `docs/scope-tags.tsv`
  (`module <TAB> name <TAB> SCOPE <TAB> citation`). A new public result **without** a tsv row will
  fail CI — flag it. `def`s, `private`, and `example`s are exempt. A tsv row whose theorem was
  renamed/removed is stale and also fails — flag orphaned rows.
- **Citations must be real and verifiable — never invented.** The repo uses a curated set of
  verified references (e.g. *Tognoni 2010*, *Ciucci 1999*, *Saha–Eggert (Griem)*, *Gornushkin
  1999*, *Aguilera & Aragón 2007/2008*, *Aragón & Aguilera 2014*, *Bulajic 2002*, *Yalcin 1999*,
  *Aitken 1935*, *Olivero–Longbothum 1977*, *Griem 1974/1997*, *Cristoforetti 2010 / –Tognoni
  2013*, *Boltzmann*, *McWhirter 1965*; `—` for pure math). Treat any **new** citation string not
  already present in `docs/scope-tags.tsv` as unverified — flag it for verification against the
  actual paper (correct authors, year, and that it supports the constant/sign/inequality used).
- Before formalizing physics, constants, signs, and **inequality directions** must be checked
  against the cited literature. If a change flips an inequality or a sign, that is a high-value
  thing to question.

## Lean / mathlib style (the `runLinter` gate enforces these)

- Every `def` and `theorem` needs a docstring. Lines ≤ 100 characters.
- **Goal-changing `show` is forbidden — use `change`.** Flag `show <newgoal>` used to restate a
  goal into a defeq form; the linter rejects it.
- Flag unused non-underscore hypothesis binders (prefix with `_` or drop them) and unused `simp`
  lemma arguments. Removing a *genuinely* unused hypothesis is a valid strengthening; removing one
  that is actually used is a correctness bug — check the proof body before endorsing either.

## What NOT to comment on

- Proof-term "performance", micro-optimizations, or golfing that doesn't change the statement.
- Naming/idiom suggestions that would break the "define once, reuse verbatim" rule.
- Anything framed as improving measurement accuracy or adding a runtime feature.
- The pinned toolchain: do **not** suggest `lake update` or bumping Lean/mathlib versions.

## When in doubt

Prefer fewer, higher-signal comments aimed at the invariants above (soundness, non-vacuity, honest
scope, missing scope-tag row, core→Alt import, invented citation, flipped sign/inequality) over
broad stylistic feedback. The authoritative brief is `AGENTS.md`; the full narrative is
`CONTEXT.md`.
