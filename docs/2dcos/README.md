# Gated-Delay 2DCOS for LIBS — working area (MUTABLE)

**Status: living drafts. Audited 2026-07-10 against the primary literature — the source
monograph is scientifically unsound (AI-generated). See `ERRATA.md`. Correct in place.**

This directory holds a research idea for applying **time-resolved, gated-delay Two-Dimensional
Correlation Spectroscopy (2DCOS)** to standardless quantitative LIBS. These are *working
documents*, deliberately kept editable — not vetted like `docs/frontiers/01..12`, and not (and,
on the current audit, not to be) reflected in the verified Lean spec. Nothing here is imported
by the build, oracle, or CI.

## Audit verdict (2026-07-10)

A literature-grounded audit (8 agents; Asta/Semantic Scholar, NotebookLM, DOI resolution)
found the monograph's central method does **not survive contact with the literature**:

- **Model B is not a valid n_e elimination and is neither standardless nor temperature-free.**
  The Mean-Value-Theorem step only *relabels* the transient n_e as an undetermined constant
  (existence-only theorem, misused); the loop closes only by tautologically inverting an
  invented "Noda = Wronskian flux" identity; and all the temperature dependence is buried in
  the lumped parameter ξ(T), which the engine must receive precomputed. (ERRATA C1, C2, C5.)
- **Two FATAL code/label errors:** the syntax-invalid `2DCOSMetrics` class, and `softmax(log x)`
  mislabeled as an ILR transform when it is plain Aitchison closure `x/Σx`. (C3, C19.)
- **Two apparently fabricated citations** (the "Corsi et al. 2000" Cσ paper — title lifted from
  Aragón & Aguilera 2014; and "Moon et al. 2020"), plus **9 of 23 references defective** (DOIs
  resolving to different papers, wrong titles/years). (C4, C10, C11–C17.)
- Several MAJOR reasoning defects (strawman "Model C" via a universal zero-diagonal property;
  a fabricated "ΔE" foil; unvalidated "butterfly" self-absorption signature). (C6–C9, C20–C22.)
- **What survives:** the zero-diagonal proof (correct but standard/misapplied), the LTE/Saha/
  Stewart–Pyatt prose framing, and the mechanical 2DCOS matrix math (the Hilbert–Noda kernel is
  exactly Noda's published form). Fixing these does *not* rescue Model B.

`gated_delay_2dcos_engine.corrected.py` applies only the **mechanical** fixes (parse error, the
ILR→closure relabel, robustness guards) and explicitly leaves the invalid Model-B computation
in place with an ERRATA note — it is not a working method.

## Rebuild (2026-07-11) — the correct version

A second workflow (8 Opus/Sonnet agents; 5 literature-grounded foundations → coherent
monograph + engine → **independent adversarial re-audit**) rebuilt this correctly. The re-audit
graded it **SOUND** (0 must-fix): no resurrected overclaims, standard/correct equations, verified
citations, a real ILR. The refuted Model B is **removed, not reformulated.**

| File | What it is |
|---|---|
| `monograph.corrected.md` | The correct, honestly-scoped monograph — *Time-Resolved 2D Correlation Spectroscopy for LIBS: A Literature-Grounded Formulation*. Real Noda 2DCOS, the cooling-plasma trajectory physics, what time-resolved 2DCOS genuinely offers LIBS (established uses + clearly-labelled testable hypotheses + an explicit "what it does NOT do"), closure vs. a correct ILR, and a fully DOI-verified bibliography (2 fabricated refs struck, 7 defective ones fixed). |
| `twodcos_engine.py` + `test_twodcos_engine.py` | The correct engine (NumPy, float64): correct synchronous/asynchronous 2DCOS + Hilbert–Noda kernel, Noda sequential-order extraction, an S/N-style diagnostic, and a **genuine ILR** (orthonormal SBP basis, isometry) alongside `closure`. No Model B / no standardless inversion. **9/9 tests pass** (zero-diagonal, antisymmetry, ILR round-trip + isometry, closure=1, sequential-order recovery). |

**Honest scope of the rebuild:** it does not invent a working standardless method (none exists via
2DCOS). "Correct" here means standard sourced equations, real citations, honest scope, and a
runnable toolkit for what time-resolved 2DCOS *actually* does — denoising, sequential-order of
species emergence/decay, and correlation structure — not n_e-free / temperature-free
quantification. The equations lost from the original (`⟦MATH⟧` gaps in `monograph.md`) are
supplied correctly here from the primary literature; the novel-but-unsound derivation is not.

## Contents

| File | What it is |
|---|---|
| `monograph.md` | The theoretical monograph (kinetic–thermodynamic formulation, Model B electron-density elimination, asynchronous zero-diagonal proof, self-absorption phase-lag, JAX architecture). |
| `gated_delay_2dcos_engine.py` | Draft JAX engine (`process_gated_delay_2dcos` + self-absorption wing coupling). Saved **verbatim**, including known defects. |
| `ERRATA.md` | Living error/correction log. Add every issue we find here before/while fixing. |

## Capture caveats (read before trusting these files)

1. **The monograph's mathematics did not survive the paste.** Every equation and most inline
   math symbols came through as the object-replacement glyph `￼` (U+FFFC). In `monograph.md`
   these have been made greppable as `⟦MATH⟧` (display equations, on their own line) and
   `⟦?⟧` (inline symbols). **The actual formulas must be re-supplied** — the prose is intact,
   the math is a gap. Search `⟦` to find every hole.
2. **`gated_delay_2dcos_engine.py` is saved exactly as written and does not currently parse**
   (`2DCOSMetrics` is not a valid Python identifier). Kept verbatim on purpose; see ERRATA.

## Working discipline

- These are the *source of record* for the idea. When correcting, edit in place and log the
  change in `ERRATA.md` (what was wrong, what it's now, why).
- If/when the math stabilizes and a claim becomes a candidate for machine verification, it
  graduates to a proper `docs/frontiers/NN-*.md` dossier (obstacle → formalizable route →
  milestone ladder) and only then toward the Lean spec — same pipeline as frontiers 08–10.
- Not committed automatically; commit when Brian says so.
