# CF-LIBS spec — literature-validity audit (all 22 modules)

A per-theorem audit of `CflibsFormal` against the peer-reviewed CF-LIBS literature, answering:
**are the definitions faithful encodings of the published physics, and are the docstrings honestly
scoped?** It extends the deeper four-formula `boltzmann-convention-verdict.md` (forward map, Saha,
self-absorption, Boltzmann ordinate) to the whole corpus.

## Bottom line

**Validated.** Every physics-bearing definition is a faithful, valid-reduced, or documented-idealized
encoding of its cited source. **No definition is divergent** (contradicting the literature) and **no
citation is unverifiable**. Across 186 audited entries (defs + theorems), the only issue found was a
single **minor docstring over-claim**, which is now fixed.

This is consistent with the project thesis: the theorems are *machine-checked deductions*, so they
cannot be wrong as logic; their scientific validity reduces to (a) faithful definitions and (b) honest
scoping — both confirmed here.

## Method

A workflow ran **one independent auditor per module** (22 in parallel), each classifying every
`theorem`/`lemma`/`def` and cross-checking it against the module's `## Literature` docstring, the
verified citation baseline, the convention verdict, and web search. Every entry flagged as
`over-reach` / `divergent` / `unverified-citation` was then **independently re-checked by a second
agent** (refute-or-confirm) so that nothing is acted on without adversarial verification — the same
discipline that classified the reviewer's original "fundamental error" as a false positive.

Verdict categories (the first four are *valid*; only the last three are issues):
`faithful` (matches the cited equation) · `reduced` (valid dimensionless / lumped-factor form,
intentional) · `idealized` (documented physical idealization — LTE, single-zone, uniform-slab) ·
`pure-math` (infrastructure lemma, no physical claim) · `over-reach` (docstring claims more than
proven) · `divergent` (definition contradicts literature) · `unverified-citation`.

## Result

| Verdict | Count | Meaning |
| --- | --- | --- |
| `faithful` | 69 | Definition/claim matches the cited literature equation directly |
| `reduced` | 33 | Valid unit-reduced / dimensionless / lumped-factor form (intentional) |
| `idealized` | 5 | Documented idealization (LTE, single-zone, uniform-slab escape factor) |
| `pure-math` | 78 | Infrastructure lemma (positivity, Finset/Lipschitz/Cauchy–Schwarz), no physical claim |
| `over-reach` | 1 | Docstring claimed more than the theorem proves → **fixed** |
| `divergent` | 0 | — |
| `unverified-citation` | 0 | — |

After adversarial verification: **1 confirmed issue** out of 186 entries.

## Per-module verdict

| Module | Role | Entries | Verdict mix | Primary source |
| --- | --- | --- | --- | --- |
| `Boltzmann` | physics | 8 | 6 faithful, 2 pure-math | LTE Boltzmann distribution |
| `Saha` | physics | 10 | 3 faithful, 1 reduced, 6 pure-math | Griem, *Principles of Plasma Spectroscopy* (Saha–Eggert) |
| `Closure` | physics | 8 | 4 faithful, 4 pure-math | Ciucci et al., *Appl. Spectrosc.* 53 (1999) 960 |
| `ForwardMap` | physics | 4 | 3 reduced, 1 pure-math | Tognoni et al., *Spectrochim. Acta B* 65 (2010) 1 |
| `ForwardMapEnergy` | physics | 6 | 3 faithful, 2 reduced, 1 pure-math | Khelladi et al., *EPJ Appl. Phys.* 101 (2023) ap230072 |
| `Classic` | inverse fwk | 7 | 4 faithful, 1 reduced, 2 pure-math | Ciucci et al. 1999 |
| `MultiSpecies` | physics | 6 | 5 faithful, 1 reduced | Ciucci et al. 1999 |
| `Identifiability` | inverse fwk | 3 | 3 faithful | Ciucci et al. 1999 |
| `Inverse` | inverse fwk | 10 | 1 faithful, 1 reduced, 2 idealized, 6 pure-math | Ciucci et al. 1999 (lumped-F convention) |
| `Robustness` | inverse fwk | 7 | 2 reduced, 5 pure-math | Ciucci et al. 1999 |
| `CompositionRobustness` | inverse fwk | 6 | 6 pure-math | (pure math) |
| `CompositionIdentifiability` | inverse fwk | 6 | 2 faithful, 1 reduced, 3 pure-math | Ciucci et al. 1999 |
| `SelfAbsorption` | physics | 12 | 5 faithful, 1 reduced, 2 idealized, 4 pure-math | Gornushkin et al., *Spectrochim. Acta B* 54 (1999) 491 |
| `SelfAbsorptionInverse` | inverse fwk | 5 | 3 faithful, 1 idealized, 1 pure-math | Gornushkin et al. 1999 |
| `SahaInverse` | physics | 5 | 3 faithful, 2 reduced | Yalcin et al., *Appl. Phys. B* 68 (1999) 121 |
| `CurveOfGrowth` | physics | 12 | 6 faithful, 5 pure-math, 1 over-reach → fixed | Gornushkin et al. 1999; Bulajic et al. 2002 |
| `StarkBroadening` | physics | 11 | 3 faithful, 2 reduced, 6 pure-math | Griem, *Spectral Line Broadening by Plasmas* (1974) |
| `SpatialForward` | physics | 8 | 4 faithful, 4 pure-math | Parigger et al. (onion-peeling Abel inversion) |
| `ErrorBudget` | inverse fwk | 18 | 4 faithful, 7 reduced, 7 pure-math | Tognoni et al. 2010 (multi-line OLS) |
| `Alt/CSigma` | inverse fwk | 16 | 8 faithful, 1 reduced, 7 pure-math | Aguilera & Aragón, *Spectrochim. Acta B* 62 (2007) 378 |
| `Alt/LeastSquares` | inverse fwk | 12 | 6 reduced, 6 pure-math | Ciucci et al. 1999 |
| `Alt/SelfAbsorbed` | physics | 6 | 2 faithful, 2 reduced, 2 pure-math | Gornushkin et al. 1999 |

## The one confirmed issue (fixed)

**`CurveOfGrowth.cogRatio_strictAntiOn`** — over-reach (minor). The docstring stated the source-free
opacity ratio "decreases monotonically *from the `n → 0⁺` limit `w₁/w₂` toward `1` as `n → ∞`*",
asserting endpoint **limit values** as if proved. The theorem proves only `StrictAntiOn … (Set.Ioi 0)`
(strict monotonicity ⇒ injectivity ⇒ identifiability) — the limit values are correct curve-of-growth
facts but are not part of what is proven. **Fix:** the docstring now marks those limits as descriptive
context, "not proved by this theorem."

Two analogous wording tightenings were applied to `ErrorBudget` (the audit's first pass also noted
them, though they were not adversarially confirmed): `olsSlope_stable_l1` no longer asserts the worst
case "attains it" as a proven sharpness result (no attainment lemma exists, unlike
`Robustness.twoLineBeta_stable_sharp`), and `olsSlope_stable_l2`'s docstring no longer calls the
deterministic `ε√N/√SS_E` bound "the form quoted in textbook error budgets" without distinguishing it
from the statistical Gauss–Markov `σ/√SS_E` law.

Findings that were examined and **not** changed: `Robustness`'s sharpness claims (true and proven by
the `_sharp` sibling theorems in-module) and `SelfAbsorption`'s "derived from first principles" framing
(already precise — it states the slab solution is "defined independently of `SA`" — and explicitly
endorsed by the convention verdict as "derived, not presupposed").

## Honest scope — what "valid" does and does not mean here

- **Not measurement accuracy.** Real-data CF-LIBS accuracy is atomic-data-limited; this spec gives
  provable well-posedness and error structure, not better numbers on a real spectrum.
- **Dimensionless.** Units are human discipline, not type-enforced; many `reduced` verdicts are exactly
  this (a lumped/dimensionless form of a dimensional literature equation).
- **Idealized plasma model.** LTE, equilibrium Saha/Boltzmann, optically-thin (relaxed via
  self-absorption / curve-of-growth), single-zone (relaxed via onion-peeling Abel). Real deviations —
  non-LTE, gradients, continuum, self-reversal, Stark *shift*, matrix effects, full line profiles — are
  not modeled and not claimed. The `idealized` entries are valid *within* their stated scope.
- **Deep-dived separately:** the forward map, Saha factor, and self-absorption escape factor received a
  dedicated factor-by-factor audit in `boltzmann-convention-verdict.md` (all correct/reduced); this
  pass confirms and extends that across the remaining modules.

## Conclusion

To the question *"are they all scientifically valid?"* — **yes, within the layered sense above:** the
definitions faithfully encode the cited peer-reviewed physics (or valid reduced/idealized forms of it),
the proofs are machine-checked and axiom-clean, and after this audit the docstrings are honestly scoped.
The corpus is a faithful, well-cited formalization of the *idealized* CF-LIBS model — not a claim that
any real LIBS spectrum obeys it.
