# 05 — Verification and governance

## 1. Gates (unchanged, listed once with what each one cannot see)

| # | Gate | Command | Catches | Blind to |
|---|---|---|---|---|
| 1 | Green build | `lake build` (lead only) | type errors | everything about meaning |
| 2 | Axiom-clean | `lake exe axiom-audit --root CflibsFormal` | `sorryAx`, `native_decide`, home-rolled axioms through imports | vacuous statements |
| 2b | Kernel replay | `scripts/kernel-replay.sh --changed origin/main` | elaborator bugs | same |
| 3 | Lint | `lake exe runLinter CflibsFormal` | missing docstrings, unused hypotheses, simp-normal form | over-claiming docstrings |
| 4 | Import hygiene / counts | `scripts/stats.sh` | non-mathlib imports | — |
| 5 | Oracle | `lake exe oracle-fixtures` + diff + `check_fixtures.py` | numeric drift in mirrored defs | statements with no fixture |
| 6 | Scope tags + docs | `scripts/gen-docs.sh`, `lake exe scope-check`, `scripts/check-scope-consistency.sh` | untagged results, tag/statement inconsistency | wrong tag that is self-consistent |
| 7 | Mutation kill | `scripts/mutate-check.sh` | statements that survive flipped inequalities / deleted hypotheses | mutants nobody seeded |
| 8 | Pre-registration | `scripts/prereg.sh freeze / audit` | statement retreat after the fact | statements never registered |
| 9 | Statement audit | `lean-statement-audit` agent + human read | vacuity, degeneracy, narrower-than-name, mis-tag | its own blind spots until red-teamed (04 §5) |
| 10 | Citations | `citation-integrity` skill, `scripts/check-citations.sh`, whitelist | invented or mis-attributed references | equations transcribed with the wrong sign from a real source (needs 04 §7.6) |

**Rule:** gates are executed by the lead and their output pasted, never summarized. Truncated tool output
is treated as no output.

## 2. Proposed additions to CI (each is a script, no new dependency)

| Addition | Trigger | Fails when |
|---|---|---|
| `scripts/vacuity-check.sh` (04 §7.4) | every PR touching `CflibsFormal/` | a probe derives `False` from a new theorem's hypotheses alone, or a hazard pattern is unguarded |
| `scripts/check-literature-parity.sh` (04 §7.3) | every PR touching a physics module | a headline theorem's docstring names no whitelisted equation, or cites outside the whitelist |
| Pre-registration presence | every PR adding a new module | no `docs/preregistrations/*.md` with `PASS FROZEN` references the module (statements are then labelled exploratory in the tag column) |
| Red-team record | every change to `.claude/agents/lean-statement-audit.md` | no `docs/spec/redteam/<date>.md` newer than the change |

## 3. Scope-tag rules for the new module classes

| Result type | Tag | Reason |
|---|---|---|
| PDF normalization, integrability, symmetry (ContinuousProfile) | PURE-MATH | no physical constant enters |
| Profile ↔ FWHM parameter binding (G3) | EXACT | encodes the cited definition of Doppler width |
| Voigt := convolution | PURE-MATH definition; docstring caveat that O–L is APPROXIMATION | no FWHM equality is claimed |
| Cascade fraction identities, antitonicity, fixed point | PURE-MATH | algebra over `S`, `Ntot` |
| Cascade with `S` bound to `sahaFactor` (S9) | EXACT (Saha–Eggert, Griem 1997) | faithful to the cited law |
| Kernel linearity and identifiability | PURE-MATH / EXACT (definitional) | — |
| Gaussian-IRF instance, thin-plasma additivity | REDUCED | optically thin, additive lines, known profiles |
| Stoichiometry corollaries | EXACT (Tognoni 2010 stoichiometric ablation) | the hypothesis is the physics; the theorem is algebra |
| Certificates C15/C16 soundness | same tag as the wrapped theorem | follows the "Honest scope" rule in the `Certificates.lean` header docstring |

## 4. Agent policy additions to `AGENTS.md` (proposed text)

- Workers run `lake env lean <absolute path>` from the repo root only; `lake build` is the lead's.
- No `set_option maxHeartbeats` above the default without a comment stating why and a Refiner note.
- No hypothesis may be added to a frozen statement; Refiner deviations are written to the
  pre-registration file and re-trigger the statement review.
- Output of an external closer (Aristotle, SorryDB, any API prover) is accepted only after local
  `axiom-audit` and kernel replay; its provenance is recorded in the commit message.
- Every new headline theorem ships with a `nonvacuity_*` instance and an oracle row (04 §7.2).
- A `sorry`-bearing statement file may exist only in a worktree, never on a branch pushed to `origin`.

## 5. Review checklist for the lead (per new module)

1. Pre-registration is `PASS FROZEN` and predates the Lean file (`prereg.sh audit`).
2. The Target-Reviewer verdict on the frozen statement is recorded and FAITHFUL.
3. Reduction theorems (S7, E1) close by unfolding plus their stated lemma route, with no hypotheses
   beyond those in the frozen statement; they must not re-prove the theorem they reduce to.
4. Mutants listed in the acceptance section are all killed; the run log is attached.
5. `#print axioms` on each headline theorem, pasted.
6. Docstring claims ≤ theorem; scope tag matches the table in §3; `## Literature` uses the whitelist.
7. The `nonvacuity_*` witness exercises the load-bearing hypothesis (non-zero where a bound is in
   that variable).
8. Oracle scenario regenerates and diffs clean; the companion vendoring step is noted as manual.
9. Convention lock (`docs/conventions.md`) updated first if any convention is touched.
10. CONTEXT.md counts and the module list updated; `gen-docs.sh` run.

## 6. Provenance rules for this spec itself
- Lemma names marked "grep at implementation" are not to be cited in docstrings until grepped.
- Literature numbers quoted from the autoformalization review came through fetch-and-extract tools;
  re-open the source before any enters a docstring.
- Two items remain UNVERIFIED from the earlier drafts and must not be repeated as fact: LeanMarathon's
  "Slurm scheduling"; the "RL-Theory" repository claim.
