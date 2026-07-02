# Solver-Driven Formalization Gaps

Generated 2026-06-30 from the formal-leverage review that mapped the CF-LIBS
no-fallback ("strict mode") solver work onto this verified spec.

**Verification status (authoritative):** `cflibs-formal` is **axiom-clean** — 692
declarations, `lake env axiom-audit` exit 0, foundation-audit 0/0/0. The only axioms
are the three standard mathlib foundations (`propext`, `Classical.choice`, `Quot.sound`).
The "2 sorry / 2 admit / 11 axiom" sometimes quoted are **phantom textual counts**
(docstrings + the vendored `tools/AxiomAudit.lean`), not proof obligations.

So everything below is a **MISSING property the solvers rely on** — not a broken proof.
51 runtime solver checks were derived from *proven* theorems; these gaps are where the
strict solver would step outside the verified envelope.

---

## Tier 1 — load-bearing (strict-mode trust gates depend on these; prove first)

1. **Existence / least-squares inverse.** ✅ **Addressed (linear/Boltzmann-plot case)** in
   `LeastSquaresFit.lean` (2026-07-02). Every *other* inverse theorem (`Inverse.lean`,
   `SahaInverse.lean`, `Identifiability.lean`) is *exact-fit injectivity*: equal
   observations ⇒ equal parameters, with no existence/feasibility statement for **noisy,
   off-manifold** data — which is every real spectrum. `LeastSquaresFit.lean` now supplies,
   for the log-linearized Boltzmann-plot fit CF-LIBS actually uses:
   * **existence of the minimizer** — `ols_minimizes_rss`: the closed-form OLS estimate
     globally minimizes the residual sum of squares `rss` over all `(m,b)` for *arbitrary*
     off-manifold `y` (constructive, via the projection identity `rss_decomposition` +
     normal equations `residual_sum_zero` / `residual_dot_energy_zero`);
   * a **residual-based feasibility predicate** — `LeastSquaresFeasible` +
     `leastSquaresFeasible_iff_exists` (feasible at `ε` ⟺ some line fits within `ε`);
   * **minimizer = identifiable inverse on-manifold** — `ols_minimizer_eq_inverse` +
     `leastSquaresResidual_eq_zero_iff` (zero minimal residual ⟺ on-manifold), and
     `Alt.olsBoltzmann_forward_feasible` shows the noise-free forward spectrum has zero
     residual, i.e. the projection inverse coincides with the identifiable inverse there —
     which is *why* `leastSquares_sound` holds on the fixpoint (`Sound` discharged
     on-manifold; off-manifold there is no ground-truth `(T,N)` to be `Sound` against).

   **Residual (still open):** the *fully nonlinear joint* least-squares inverse over the
   coupled multi-species forward map (fit `(T, n_e, composition)` simultaneously from raw
   intensities, not the per-species log-linearized line) — this overlaps gaps #6 and #8 and
   is a separate, larger effort.

2. **Atomic-data perturbation channel.** Identifiability assumes the two parameter
   sets share *identical, correct* `g, A, E, U(T)` (`CompositionIdentifiability.lean:132`,
   `Identifiability.lean`). But the documented real-data accuracy floor *is* atomic-data
   mismatch (~0.171 RMSEP), NULL-A_ki, incomplete stages. → Prove a perturbation theorem
   bounding composition error by Δ(g·A), ΔE_k, ΔU_s. **Highest physics impact.**
   Runtime corollary: hard-FAIL on missing/zero/NULL atomic data instead of the
   `IP=15.0 eV` / crude-`U` fallbacks.

3. **n_e / Saha stability + multi-line conditioning.** `electronDensity_antitone`
   (`Saha.lean:120`) proves only exact injectivity — no Lipschitz/condition-number bound
   for `n_e` vs (ΔR, ΔT) (gap #2), and `Robustness.lean` conditions only the 2-line slope,
   with no rank/condition theorem for the multi-element design matrix (gap #11).
   → Prove `electronDensityFromRatio` sensitivity constants + the design-matrix
   rank/condition requirement.

4. **Degeneracy converse.** ✅ **Addressed (exact-degenerate case)** in
   `Identifiability.lean` (2026-07-02). `lineIntensity_ratio_closed_form` names the shared
   two-line ratio engine `I_j/I_i = ((g_j·A_j)/(g_i·A_i))·exp((E_i−E_j)/(k_B T))`;
   `temperature_degeneracy` proves `E_i = E_j` ⇒ the ratio collapses to the `T`-independent
   constant `(g_j·A_j)/(g_i·A_i)` (for *any* `T₁, T₂, N, Fcal` — no positivity needed);
   `temperature_not_identifiable_of_degenerate` exhibits the non-injectivity (`T₁ = 1 ≠ 2 = T₂`
   with identical ratio observations). So `temperature_identifiability`'s `E_i ≠ E_j`
   hypothesis is provably *necessary*, and the "ΔE = 0 → refuse" decision is a theorem.

   **Residual (still open):** the *near-degenerate quantitative* version — a bound
   `|∂(ratio)/∂T| ≲ ΔE/(k_B T²)` making "small ΔE ⇒ ill-conditioned" (not just "zero ΔE ⇒
   lost") rigorous; the `ss_e > 0` OLS energy-spread gate has its deterministic counterpart in
   `ErrorBudget.requiredEnergySpread_sufficient`, but the two-line conditioning constant is
   not yet formalized (overlaps gap #3).

5. **End-to-end noise → composition propagation.** Error bounds take the per-species
   density error δ as a *given hypothesis* (`CompositionRobustness.lean:98,147`); the
   chain raw-noise ε → intensity error → slope/intercept error → δ → ΔC is not closed
   (gaps #10, #14), there is no `U_s(T)` Lipschitz lemma, and the deterministic slope
   bound assumes a single global ε (no per-line heteroscedastic variant, gap #19).
   → Prove the composed bound `|ΔC_s| ≤ f(ε, SS_E, T-sensitivity of U_s)` + a per-line
   `olsSlope_stable` variant.

6. **Coupled Saha–closure–charge fixed point.** The iterative CF-LIBS loop couples
   Saha(n_e) ↔ closure(∑C=1) ↔ charge neutrality; only static facts are proven
   (`Saha.lean:84`, `Closure.lean`). No existence/uniqueness/convergence of the
   self-consistent (T, n_e, composition). → Formalize the loop as a fixed-point operator
   and prove contraction/convergence — this is what licenses trusting the iterative
   solver's convergence flag.

7. **Multi-species per-U generalization.** `deNormalizedDensity` /
   `density_ratio_from_intensities` (`MultiSpecies.lean:38-41,77`) assume one shared U
   and atomic-data family across species; real multi-element CF-LIBS uses per-species
   `U_s(T)`. → Generalize the ratio/relative-composition theorems to per-species U and
   atomic data.

8. **Joint (T, composition) from ≥2 lines/species.** `general_identifiability`
   (`Inverse.lean:173`) pins T only by *assuming* an external two-line ratio (`hTratio`)
   on a one-line-per-species map. The solver fits T and composition simultaneously from
   multi-line data. → Extend the observation map to ≥2 distinct-energy lines/species and
   prove (T, composition) jointly identifiable from `hObs` alone.

## Tier 2 — self-absorption / regime coverage

9. **Self-absorption composition-level non-identifiability** (`SelfAbsorptionInverse.lean`,
   gap #1): a per-line density LOST theorem exists but no *composition-level* one
   (two compositions → equal thick observations). Dominant failure mode for concentrated
   / high-entropy alloys. → Prove it to justify refuse-to-report under unknown τ.
10. **Thick-regime curve of growth** (`EquivalentWidth.lean`, `Alt/CSigmaCurveOfGrowth.lean`,
    gap #18): only the optically-thin / saturation-onset branch is formalized. → Add the
    thick (√τ) asymptotic + a Lipschitz/conditioning bound for the COG inverse.
11. **Matrix-effect invariance under per-shot (T, n_e) variation** (`MatrixEffects.lean`,
    gap #12): invariance proven only at fixed T, n_e. → Bound composition error vs
    per-shot plasma variation (or add a runtime T/n_e stability monitor).
12. **Continuous spatial (Abel) inverse + full-Voigt regime** (`SpatialForward.lean`,
    gap #27): only discrete onion-peeling / single-zone is covered. → Add regime
    detection (τ, spatial-gradient magnitude, Voigt mixing) that triggers refuse-to-report
    outside the verified envelope.

## Tier 3 — the hypothesis *is* the runtime check (wire it; no Lean fix required)

- **LTE validity** (gap #24): a hypothesis in every Boltzmann/Saha theorem (correctly —
  it is measurement-dependent). The spec *provides* `mcWhirterBound` (`StarkBroadening.lean`).
  → Strict mode must evaluate McWhirter on the measured n_e + cross-check Stark/Saha n_e
  agreement, and refuse when LTE is unsupported.
- **Unobserved ionization stage** (gap #25): `saha_joint_identifiability` *requires* both
  a neutral and an observed ion line. Any single-stage n_e inference (the pressure-balance
  fallback) is outside the envelope. → The hypothesis is the gate: refuse n_e when no ion
  line is observed; do not impute a stage ratio.
- **Completeness / missing-mass m** (gap #13): absolute composition is provably inflated
  by 1/(1−m), but m depends on undetected sub-threshold species. → Runtime policy:
  report absolute fractions as upper bounds, flag non-reliable unless completeness is
  externally certified (prefer ratios/deltas — `recoveredComposition_ratio_matrix_invariant`).
- **Float vs ℝ** (gap #22): the spec is over exact ℝ; near a threshold the Float pipeline
  may disagree. → Add an interval margin to threshold gates, or document the caveat.
- **Dimensional/unit safety** (gap #26): the inverse core uses bare ℝ. → Keep unit/scale
  validation in the solver input layer (`Dimensions.lean` is an additive checker).

## Not gaps (record, do not chase)

- The three standard mathlib axioms (gap #20) are the trust base — no fix possible/needed.
- The "2 sorry / 11 axiom" premise (gap #21) is phantom textual counts; the spec is
  axiom-clean.
- `oracle/Generate.lean` (gap #28) is a *Float bridge / test artifact*, not verified
  ground truth — trust the ℝ theorems, not `fixtures.json`.

---

## How the solver consumes this

Strict mode (`CFLIBS_NO_FALLBACK`) gates each solve on the **proven** preconditions
(positivity, distinct-energy lever arm, observed ion stage, simplex closure, conditioning
/ error-budget bounds) and **refuses** (typed failure + diagnostics) rather than
substituting a fallback. The Tier-1/2 gaps mark where a *refuse* today is a heuristic that
a future theorem would make rigorous; the Tier-3 items are already-provided criteria that
just need wiring. See the companion strict-mode work on `feat/no-fallback-exploratory` in
the cflibs repo.
