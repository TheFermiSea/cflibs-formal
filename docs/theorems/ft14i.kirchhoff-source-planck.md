---
schema: card/v1
id: ft14i.kirchhoff-source-planck
title: "Kirchhoff-consistent line source function is Planck's law"
kind: result
depth: full
summary: >
  For one bound-bound transition with LTE level populations and emission/absorption coefficients
  linked by the Einstein-Milne relation, the emissivity divided by the opacity that includes the
  stimulated-emission factor equals the Planck function, independent of density, partition
  function, transition probability and path length. The identity is algebra once the two physics
  hypotheses are granted; the module keeps every coefficient abstract.
lean:
  decl: CflibsFormal.source_eq_planck
  reviewed:
    commit: "d070a4bebd02ab3a00bc3e0ad37250b9e3be3df8"
    statement_hash: "95f4804c43b8f95473202574fdb90fe6331657a28c03ab26e3412f98e87440cd"
    by: "draft sonnet; adversarial review opus (independent, D24); fixes sonnet; lead spot-check"
    method: "binder-by-binder LaTeX vs catalog statement; physics reading; honest scope; CF-LIBS-improved anchors; citation roles; check_cards.py"
  not_to_confuse_with:
    - CflibsFormal.lteSourceStrength
frontier:
  ids:
    - FT-14
  part: "(i)"
  pr:
    - 8
  landing_commits:
    - {sha: 3c10eeed6f15e5a92c9333c27e843549a8a9685e, what: "landed at the end of OpticalDepth.lean in the group-III landing commit, with FT-06, FT-08, FT-13, FT-18 and FT-20"}
    - {sha: 1021a0219e28c25eea430cbe6e4bc7e2544c0702, what: "moved verbatim into its own Mathlib-only module, KirchhoffSource.lean, so the scope-consistency check would not flag an EXACT result in a module also importing an APPROXIMATION-tagged one"}
    - {sha: ec8c56c7269774164399f9b23ab5845ecf4866f3, what: "added the module's copyright header (style-linter follow-up)"}
  verification:
    - {decl: CflibsFormal.source_eq_planck, route: hand-land, record: docs/archive/openprover/staging/2026-09-27/FOLLOWUPS.md}
citations:
  - {key: "Griem 1997", role: model-source, supports: "LTE line emission and absorption with the stimulated-emission factor, and Kirchhoff's law, as cited by KirchhoffSource.lean (context for H4 and the conclusion; not a source for H5's constants)"}
  - {key: "Aragón & Aguilera 2014", role: corroborating, supports: "the LIBS line absorption coefficient carries the stimulated-emission factor", locator: "Eq. (4), accepted-manuscript numbering"}
pipeline:
  - repo: CF-LIBS-improved
    ref: "main@b142ae25"
    path: cflibs/radiation/kernels.py
    symbol: _apply_self_absorption
    anchor_text: "Optical-slab self-absorption"
    relation: assumes
    note: >
      Builds the wavelength-form Planck function and sets the opacity to emissivity over it
      directly, without deriving it from a lower-level cross-section; this theorem gives
      sufficient conditions (H4, H5) under which that step is exact. Works per unit wavelength;
      the corresponding bridge is the D19 gap (open item below).
  - repo: CF-LIBS-improved
    ref: "main@b142ae25"
    path: cflibs/radiation/two_zone.py
    symbol: TwoZoneSpectrumModel.compute_spectrum
    anchor_text: "LTE (Kirchhoff) absorption coefficient"
    relation: assumes
    note: "Peripheral-zone opacity and source function built the same way; same reliance."
  - repo: CF-LIBS-improved
    ref: "main@b142ae25"
    path: cflibs/inversion/physics/self_absorption_observable.py
    symbol: planck_ceiling_optical_depth
    anchor_text: "Line-center optical depth from the measured peak"
    relation: assumes
    note: >
      Inverts I = B(1 - e^-tau) for tau from a measured peak and B(T); presumes the source
      function equals the Planck function. Cites Völker & Gornushkin 2023, not on the
      cflibs-formal whitelist and not opened by the card author.
  - repo: CF-LIBS-improved
    ref: "main@b142ae25"
    path: cflibs/radiation/kernels.py
    symbol: _forward_emissivity
    anchor_text: "Per-line instrument sigma from resolving power"
    relation: tension
    note: >
      Not previously traced: one broadening mode always builds the per-line profile from
      instrument resolving power, on a path whose instrument-folding flag
      `SpectrumModel._run_forward_kernel` sets to correlate with, but not gate, that mode; the
      Bayesian forward path (`cflibs/inversion/solve/bayesian/forward.py`,
      `BayesianForwardModel`) also always folds instrument sigma in PHYSICAL_DOPPLER mode, so
      with its opt-in self-absorption an instrument width likewise reaches ε before the
      Kirchhoff division. [traced by reading, main@b142ae25]
decisions:
  - D15
  - D19
status:
  lean: proved
  pipeline: none
  pipeline_reliance: implicit
open_items:
  - kind: citation
    text: >
      D19 requires constants checked against standard references before FT-14 is stated; no
      record shows Griem 1997 (or another source) was opened for B0 = 2hν³/c², and the D19
      wavelength-form bridge lemma is not formalized. The landed statement sidesteps the first
      gap by keeping κ0, ε0, B0 abstract.
    ref: D19
  - kind: model-row
    text: >
      lineOpacity carries no model row although its stimulated-emission factor already
      presupposes LTE populations; PR #8 recorded this as an open owner decision, still pending.
  - kind: lean
    text: >
      source_eq_planck/lineOpacity are not wired into OpticalDepth.opticalDepth, which remains
      Wien-limit; every result that instantiates τ with opticalDepth (e.g.
      opticalDepth_knownTauCert, the OpticalDepthBridge τ-ratio results, thickLineIntensity)
      inherits that gap. C12/C13 (knownTau_certificate_sound, saDistinct_certificate_sound /
      cogRatio_injOn) are stated over an abstract τ / opacity coefficient and do not, though a
      binding of their τ to opticalDepth would.
  - kind: docstring
    text: >
      KirchhoffSource.lean's docstring attributes the n_l = 0 vanishing to a/0 = 0; scratch
      evidence shows the right side actually vanishes because hpop/hein force B0 = 0. The
      guard-keeping conclusion is unaffected; the stated mechanism is imprecise.
  - kind: pipeline
    text: >
      No pipeline test checks the pipeline's coefficients against hpop/hein (round-trip test
      proposed in section 5, not implemented), and whether the NIST_PARITY instrument-width path
      is reachable in practice is untraced.
  - kind: lean
    text: >
      FT-14 part (v) (transfer before instrument) remains parked as FT14-conv-absorptance-le,
      Fubini step unstaged — a sibling result, not this card's declaration.
    ref: FT-14
  - kind: owner-decision
    text: "Owner spot-check of this EXACT card (D24) pending; required before merge to main."
provenance:
  - docs/archive/openprover/staging/2026-09-27/FT14-source-eq-planck/dossier.md
  - docs/archive/openprover/staging/2026-09-27/FT14-source-eq-planck/statement.lean
  - docs/archive/openprover/staging/2026-09-27/_hand-land/FT14-source-eq-planck.proof.lean
  - docs/archive/openprover/staging/2026-09-27/FOLLOWUPS.md
  - docs/research/audit-2026-09-24/REPORT.md
  - docs/research/audit-2026-09-24/frontier.json
  - docs/research/audit-2026-09-24/evidence/adv-verifier-2/Refute.lean
  - https://github.com/TheFermiSea/cflibs-formal/pull/8
  - https://github.com/TheFermiSea/cflibs-formal/pull/9
evidence:
  - file: docs/theorems/evidence/ft14i.kirchhoff-source-planck/check.lean
    sha256: d0883a650731ee332f022ec5c16aed6d685a357cfdbfffed71e6d2b2a1a51a85
    command: "lake env lean docs/theorems/evidence/ft14i.kirchhoff-source-planck/check.lean"
    result: >
      Prints source_eq_planck's type and both definitions verbatim (matching docs/catalog.jsonl);
      #print axioms reports [propext, Classical.choice, Quot.sound] only; exit 0.
  - file: docs/theorems/evidence/ft14i.kirchhoff-source-planck/sharpness.lean
    sha256: 613bf7cf339d9b93d9dd107d519a0c4e498f3327f8ae387df105dfa512a3ff33
    command: "lake env lean docs/theorems/evidence/ft14i.kirchhoff-source-planck/sharpness.lean"
    result: >
      The hκ counterexample and the non-vacuity witness type-check; source_eq_planck_noGuards
      (the statement without hx and hnl) is proved on standard axioms only; exit 0.
updated: 2026-09-28
---

# Kirchhoff-consistent line source function is Planck's law

<!-- BEGIN GENERATED facts -->

**Facts** — generated by `scripts/gen_cards.py`; hand edits inside this block are overwritten on the next run.

### Headline — `CflibsFormal.source_eq_planck` (theorem)

- Lean: [`CflibsFormal/KirchhoffSource.lean:61`](../../CflibsFormal/KirchhoffSource.lean#L61)
- Scope: `EXACT`
- Citation: `Griem 1997` 🟡 AUDIT-VETTED
- Axioms: `Classical.choice`, `Quot.sound`, `propext`
- Used by: 0 declaration(s) in `CflibsFormal`

```lean
∀ {κ0 ε0 B0 nl nu x gu gl : ℝ},
  (0 : ℝ) < x →
    (0 : ℝ) < κ0 →
      (0 : ℝ) < nl →
        nu / nl = gu / gl * Real.exp (-x) →
          ε0 * gu / gl = κ0 * B0 →
            CflibsFormal.lineEmissivity ε0 nu / CflibsFormal.lineOpacity κ0 nl x =
              B0 / (Real.exp x - (1 : ℝ))
```

Statement hash: `95f4804c43b8f95473202574fdb90fe6331657a28c03ab26e3412f98e87440cd` — **MATCH** vs `lean.reviewed.statement_hash` (reviewed at commit `d070a4bebd02ab3a00bc3e0ad37250b9e3be3df8`).

<!-- END GENERATED facts -->

## 1. Statement

### 1.1 Symbols

One bound-bound transition, frequency form (D19). All quantities are dimensionless reals; the
"meaning" column is the physics reading the Lean statement itself keeps abstract.

| Symbol | Lean name | Meaning |
|---|---|---|
| $n_l$ | `nl` | lower-level population |
| $n_u$ | `nu` | upper-level population |
| $g_l$ | `gl` | lower-level degeneracy |
| $g_u$ | `gu` | upper-level degeneracy |
| $x$ | `x` | $h\nu/(k_BT)$ |
| $\kappa_0$ | `κ0` | absorption coefficient per lower-level particle ($\propto h\nu\,B_{lu}\,\phi$) |
| $\varepsilon_0$ | `ε0` | emission coefficient per upper-level particle ($\propto h\nu\,A_{ul}\,\phi$) |
| $B_0$ | `B0` | $2h\nu^3/c^2$ in the frequency form |

### 1.2 Definitions used

- `lineOpacity κ0 nl x := κ0 * nl * (1 - Real.exp (-x))` — the opacity with the stimulated-emission
  factor $1-e^{-x}$.
- `lineEmissivity ε0 nu := ε0 * nu` — the emissivity.

### 1.3 Hypotheses

- **H1** (`hx` binder) — $x>0$.
- **H2** (`hκ` binder) — $\kappa_0>0$.
- **H3** (`hnl` binder) — $n_l>0$.
- **H4** (`hpop` binder), LTE population ratio — $\dfrac{n_u}{n_l}=\dfrac{g_u}{g_l}\,e^{-x}$.
- **H5** (`hein` binder), Einstein-Milne relation — $\dfrac{\varepsilon_0\,g_u}{g_l}=\kappa_0\,B_0$.

`gu`, `gl`, `ε0`, `B0` and `nu` are otherwise unconstrained reals.

### 1.4 Conclusion

$$
\frac{\varepsilon}{\kappa}=\frac{\varepsilon_0\,n_u}{\kappa_0\,n_l\,(1-e^{-x})}=\frac{B_0}{e^{x}-1}.
$$

### 1.5 Lean correspondence

| Binder | Label | Note |
|---|---|---|
| `κ0`, `ε0`, `B0`, `nl`, `nu`, `x`, `gu`, `gl` | — | implicit reals, no side conditions beyond H1–H5 |
| `hx` | H1 | — |
| `hκ` | H2 | — |
| `hnl` | H3 | — |
| `hpop` | H4 | parses as $(g_u/g_l)\,e^{-x}$ |
| `hein` | H5 | parses as $(\varepsilon_0 g_u)/g_l$, i.e. `ε0 * gu / gl` |

Lean division is total (`a / 0 = 0`); no `rpow` occurs anywhere in the statement or proof (only
`Real.exp`). `nu / nl` and `lineEmissivity … / lineOpacity …` would both silently read `0` if
their denominators vanished — why `hκ` is needed (κ0 ≠ 0 would suffice) and `hnl` is kept as a
regime guard although (§3) it is not needed; `gu / gl` in H4/H5 also reads 0 at $g_l=0$, which
forces $n_u=0$, $B_0=0$ and a 0 = 0 instance — no positivity of $g_u,g_l$ is assumed.

## 2. Physical meaning

**What the hypotheses encode.** Take one line $u\to l$ at frequency $\nu$ in a plasma at
temperature $T$, so $x=h\nu/(k_BT)>0$. In the usual frequency form, emissivity
$\varepsilon_\nu=\tfrac{h\nu}{4\pi}A_{ul}n_u\phi(\nu)$ and absorption coefficient
$\kappa_\nu=\tfrac{h\nu}{4\pi}B_{lu}n_l\phi(\nu)\big(1-\tfrac{g_l n_u}{g_u n_l}\big)$, where the
bracket is the stimulated-emission correction. Under the LTE ratio H4 the bracket equals
$1-e^{-x}$, giving `lineOpacity` with $\kappa_0=\tfrac{h\nu}{4\pi}B_{lu}\phi$; the Einstein
relations $g_lB_{lu}=g_uB_{ul}$, $A_{ul}=\tfrac{2h\nu^3}{c^2}B_{ul}$ give
$\varepsilon_0 g_u/g_l=\kappa_0\cdot 2h\nu^3/c^2$, i.e. H5 with $B_0=2h\nu^3/c^2$.
[derivation, unchecked] — the card author's algebra from the standard Einstein relations; the
constants are not in the Lean statement and no source was opened for them (§6, D19).

**What the conclusion says.** $B_0/(e^x-1)=\tfrac{2h\nu^3}{c^2}\tfrac{1}{e^{h\nu/k_BT}-1}=B_\nu(T)$,
the Planck function: the line source function $S_\nu=\varepsilon_\nu/\kappa_\nu$ equals $B_\nu(T)$,
with density, partition function, $A_{ul}$, profile and path length all cancelled.

**Why the stimulated-emission factor matters.** Drop it and the ratio becomes $B_0e^{-x}$ — the
Wien-limit form behind `lteSourceStrength`, which also carries $F_{\rm cal}$, $\sigma_0$ and
$\ell$ ("Stimulated emission is NOT modelled",
`OpticalDepth.lean`'s scope block). Wien over Planck is $1-e^{-x}$: about $0.92$ at $x\approx2.5$
(visible lines, per that docstring) and about $0.79$ at $x\approx1.55$ (the audit's figure).

**Why it matters for CF-LIBS.** Homogeneous-slab self-absorption writes $I=S(1-e^{-\tau})$. With
$S=B_\nu(T)$ the saturated plateau depends on $T$ and $\nu$ only, and licenses computing opacity
from emissivity as $\kappa=\varepsilon/B$, which the pipeline's forward model does.
`source_eq_planck` gives sufficient conditions for that step to be exact — H4 and H5, with
$x,\kappa_0,n_l \gt 0$ — and needs nothing about mixtures, instrument response or path length; it
does not show they are necessary.

## 3. Scope and validity

Own relation tag EXACT; published tag EXACT (`docs/scope-tags.tsv`, `docs/scope-published.tsv`),
since `lineOpacity`/`lineEmissivity` carry no model row that would weaken it under D15's two-axis
rule — whether they should is itself an open owner decision (below).

**Idealizations encoded:** one transition, one frequency, with emission and absorption sharing the
line profile implicitly; LTE population ratio at one temperature (H4); the Einstein-Milne relation
imposed directly as a hypothesis (H5), not derived from primitive Einstein $A$/$B$ coefficients;
frequency form (D19); no continuum, scattering, or non-LTE.

**What it does NOT claim:**
- **No converse.** It does not show that $\varepsilon/\kappa=B_0/(e^x-1)$ forces H4 or H5 (LTE
  populations or the Einstein–Milne relation).
- **No numerical constants.** $2h\nu^3/c^2$ and $h\nu/4\pi$ stay abstract; no numeric Planck
  constant enters the statement.
- **No wavelength form.** The D19 bridge to the $\lambda$-form identity the pipeline computes
  with is not formalized.
- **Nothing about `OpticalDepth.opticalDepth`.** The two are not wired together; `opticalDepth`
  remains the Wien-limit definition (§6).
- **Nothing about emergent intensity, path length, or the instrument.** Those are FT-14 part
  (ii), not landed (its building block `equivWidth_strictMonoOn` has card ft14v), and part (v),
  parked as `FT14-conv-absorptance-le`.
- **Nothing about mixtures.** A sightline crossing several temperatures has no single Planck
  source function; this is stated for one temperature.
- **Not full LTE.** H4 fixes only the $u/l$ population ratio; the result holds for any two-level
  Boltzmann ratio at the $x$ in the opacity, and claims nothing about whether the plasma is in
  LTE.
- **Not a measurement-accuracy claim.** Per `AGENTS.md`'s cardinal rule, this is algebraic
  structure given H4/H5, not a claim that any composition estimate becomes more accurate.

**Hypothesis sharpness and non-vacuity**
([scratch: evidence/ft14i.kirchhoff-source-planck/sharpness.lean], card author, exit 0):
- **`hκ` is load-bearing.** At $\kappa_0=0$, $g_u=0$, $g_l=1$, $n_u=0$, $n_l=1$, $x=1$,
  $B_0=\varepsilon_0=1$, H4/H5 both hold, the left side is $0$ and the right side is
  $1/(e-1)\ne0$.
- **`hx` and `hnl` are not needed.** The statement without them (`source_eq_planck_noGuards`) is a
  theorem for every real $x$ and $n_l$, given only `hκ`, H4, H5.
- **The docstring's stated reason is imprecise.** It attributes both sides vanishing at $n_l=0$ to
  `a / 0 = 0`; the left side does, but the right vanishes because H4/H5 force $B_0=0$ there
  (via $g_u/g_l=0$, $\kappa_0>0$) — a different mechanism. The guard-keeping conclusion stands.
- **Non-vacuity.** At $x=\kappa_0=n_l=g_u=g_l=\varepsilon_0=B_0=1$, $n_u=e^{-1}$, every hypothesis
  holds and the conclusion is the nonzero $1/(e-1)$.

## 4. Proof idea

`div_eq_iff` turns H4 into $n_u=(g_u/g_l)e^{-x}n_l$; `linear_combination` (scaled by $n_l e^{-x}$
against H5) gives $\varepsilon_0 n_u=\kappa_0 B_0 n_l e^{-x}$; `Real.add_one_lt_exp` gives
$e^x-1\ne0$; unfolding both definitions, rewriting $e^{-x}$ via `Real.exp_neg`, and closing with
`field_simp` finishes it — four steps, about ten lines. The audit's adversarial verifier found an
equivalent route independently (`Real.one_lt_exp_iff` in place of `Real.add_one_lt_exp`, the same
`field_simp` close), corroborating the proof without sharing code with the landed one
(`docs/research/audit-2026-09-24/evidence/adv-verifier-2/Refute.lean`).

## 5. Role in the composition-extraction pipeline

**Current state** (CF-LIBS-improved `main@b142ae25`). No pipeline code or document names this
theorem or its module; the positive control for that search, `cflibs-formal`, matches 34 files
under `cflibs/` and `docs/`, and the Lean identifier `sahaBoltzmann_shift_eq_log_saha` matches
`iterative.py`, confirming the search works. Three sites compute consistently with
the conclusion without naming it (`pipeline_reliance: implicit`): the `kernels.py`, `two_zone.py`
and `self_absorption_observable.py` entries above, all Kirchhoff's relation $\kappa=\varepsilon/B$
or $S=B$. A fourth entry (`tension`) records a finding not present in earlier drafts of this card:
one broadening mode's per-line profile reaches the emissivity through the instrument's resolving
power on a path the wrapper's own instrument-folding flag does not gate, so in that mode an
instrument width can already sit inside $\varepsilon$ before the Kirchhoff division — related to,
but not identical with, FT-14 part (v)'s parked "transfer before instrument" step.

**Proposed use (not implemented).**
- **Cross-reference.** Name `source_eq_planck` at the three `assumes` sites so the implicit
  modelling step is attached to its hypotheses.
- **Einstein-Milne round-trip test (new).** Compute the wavelength-form absorption coefficient
  independently from the pipeline's own atomic data ($B_{lu}$ from $A_{ul}$, times the
  lower-level population and $1-e^{-x}$), and assert it equals $\varepsilon_\lambda/B_\lambda$ to
  about $10^{-10}$ relative on a $(\lambda,T)$ grid. **Falsification arm:** dropping $1-e^{-x}$, or
  evaluating a Wien $B$ instead of a Planck one, must fail by exactly that factor — a test that
  cannot fail this way is not testing H4/H5.
- **Formal follow-up.** Land the D19 wavelength bridge, then wire `lineOpacity` into a
  Kirchhoff-consistent optical-depth variant so the spec's $\tau$ and the pipeline's $\tau$
  describe the same object.

**What it would change.** The evidence status of an existing, previously unattached modelling
step, plus a new regression test — this is rigor, not accuracy (`AGENTS.md`); no composition
change is expected unless the test finds a genuine constant or convention error.

**How it would be validated.** By the round-trip test above, including its falsification arm. An
existing pipeline test (`tests/inversion/physics/test_self_absorption_observable.py`,
`TestPlanckRung`) round-trips $\tau$ through $I=B(1-e^{-\tau})$ on both sides, using $S=B$ on both
the forward and inverse side, so it cannot independently test H4/H5 and is not a substitute.

## 6. Status and remaining work

**Done.** Proved and landed (hand-land, not queued — `FOLLOWUPS.md` records a `verify.py` pass);
axiom-clean on the standard three axioms, independently re-checked by the card author
(`evidence/check.lean`); the sharpness and non-vacuity claims independently executed
(`evidence/sharpness.lean`).

**Open** (mirrors `open_items[]`):
1. D19's constants check (a standard reference opened for $B_0=2h\nu^3/c^2$) has no record; the
   wavelength-form bridge lemma is not formalized.
2. `lineOpacity`'s model-row question is an open owner decision (PR #8).
3. Not wired into `OpticalDepth.opticalDepth`, still Wien-limit; every result that instantiates
   $\tau$ with `opticalDepth` (e.g. `opticalDepth_knownTauCert`, the `OpticalDepthBridge`
   $\tau$-ratio results, `thickLineIntensity`) inherits that gap. C12/C13 are stated over an
   abstract $\tau$ / opacity coefficient and do not, though a binding of their $\tau$ to
   `opticalDepth` would.
4. The docstring's stated reason for the $n_l=0$ case is imprecise (§3).
5. No pipeline regression test exists for H4/H5, and the NIST_PARITY instrument-width path's
   practical reachability is untraced.
6. FT-14 part (v) (transfer before instrument) remains parked as `FT14-conv-absorptance-le`, its
   Fubini step unstaged — a sibling result, not this declaration.
7. **Owner spot-check (D24):** this card publishes EXACT and is not done until the owner has
   spot-checked it.

## 7. Literature

Griem 1997 is the model source for LTE line emission and absorption with the stimulated-emission
factor and Kirchhoff's law: it supports the physical reading of H4 and the conclusion, not H5's
constants or the algebra connecting them, and — since the module takes no numerical constant from
it — does not by itself discharge open item 1 (a citation attesting the physics is not one
attesting a numeric constant). Aragón & Aguilera 2014 is cited only as corroborating, off-module
evidence that a real LIBS absorption coefficient carries the stimulated-emission factor this
theorem's opacity includes; it is not cited by `KirchhoffSource.lean` itself. The Einstein
relations and the constants $h\nu/4\pi$, $2h\nu^3/c^2$ used in §2 have no opened whitelist source
(Griem 1997 is cited by the module only for LTE emission/absorption and Kirchhoff's law, and the
module takes no constant from it); §2's derivation of H5 is the card author's own algebra
[derivation, unchecked] and is not attributed to any source.

## 8. Provenance

The audit that raised this result is `docs/research/audit-2026-09-24/REPORT.md`'s FT-14 section
(verdict revise overall, part (i) graded A), with its machine-readable twin
`docs/research/audit-2026-09-24/frontier.json` and the independent adversarial-verifier proof at
`docs/research/audit-2026-09-24/evidence/adv-verifier-2/Refute.lean`. Staged as a hand-land target
in `docs/archive/openprover/staging/2026-09-27/FT14-source-eq-planck/` (dossier and frozen
statement) and `.../_hand-land/`'s proof file, with the pass recorded in that round's
`FOLLOWUPS.md`. Landed in commit `3c10eee` (pull request #8), moved to its own module in `1021a02`
(same PR), copyright header in `ec8c56c` (pull request #9). Governing decisions: D15 (scope-tag
semantics), D19 (radiation conventions, including the constants-check obligation of open item 1).
Card evidence: `docs/theorems/evidence/ft14i.kirchhoff-source-planck/check.lean` and
`.../sharpness.lean` (hashes in the front matter).
