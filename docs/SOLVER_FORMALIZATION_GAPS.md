# Solver-Driven Formalization Gaps

Generated 2026-06-30 from the formal-leverage review that mapped the CF-LIBS
no-fallback ("strict mode") solver work onto this verified spec.

**Verification status (authoritative):** `cflibs-formal` is **axiom-clean** — 851
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

2. **Atomic-data perturbation channel.** ✅ **Addressed** in `AtomicDataPerturbation.lean`
   (2026-07-02). `classicDensity_aliasing` (EXACT): inverting the true spectrum with wrong
   atomic data returns `N̂ = N·ρ_true/ρ_wrong` — finite, arbitrarily biased, with no
   self-diagnosing signature, which is *why* the only sound runtime response to
   missing/NULL data is refusal. `classicDensity_aliasing_error` (lumped relative response
   error δ ⇒ `|N̂−N| ≤ N·δ/(1−δ)`), `classicDensity_aliasing_error_channels` (split
   `δ_gA`/`δ_U` channels), and `classicComposition_atomicData_error` (composed through the
   verbatim `CompositionRobustness` bound to `|Ĉ_s − C_s|`). **Residual:** per-line
   heterogeneous δ across a multi-line fit, and the `ΔE ≠ 0` channel split out of the
   lumped ρ (currently absorbed exactly, not isolated).

3. **n_e / Saha stability + multi-line conditioning.** ✅ **Partially addressed** in
   `SahaStability.lean` (2026-07-02): `electronDensity_relativeError` (EXACT — the
   diagnostic's log-derivative is exactly −1, so relative stage-ratio error transfers
   one-to-one to relative n_e error) and `electronDensity_lipschitz` (the explicit
   sensitivity constant `S/R₀²` on `R ≥ R₀`). **Residual:** the T-channel (`∂n_e/∂T`) is
   honestly open — `dS/dT` mixes the thermal bracket, `exp(−χ/kT)`, and the
   partition-ratio `U_{z+1}/U_z`, whose sign is not definite without extra hypotheses; and
   the multi-element design-matrix rank/condition theorem remains open.

4. **Degeneracy converse.** ✅ **Addressed (exact-degenerate case)** in
   `Identifiability.lean` (2026-07-02). `lineIntensity_ratio_closed_form` names the shared
   two-line ratio engine `I_j/I_i = ((g_j·A_j)/(g_i·A_i))·exp((E_i−E_j)/(k_B T))`;
   `temperature_degeneracy` proves `E_i = E_j` ⇒ the ratio collapses to the `T`-independent
   constant `(g_j·A_j)/(g_i·A_i)` (for *any* `T₁, T₂, N, Fcal` — no positivity needed);
   `temperature_not_identifiable_of_degenerate` exhibits the non-injectivity (`T₁ = 1 ≠ 2 = T₂`
   with identical ratio observations). So `temperature_identifiability`'s `E_i ≠ E_j`
   hypothesis is provably *necessary*, and the "ΔE = 0 → refuse" decision is a theorem.

   **Residual:** ✅ also closed (2026-07-02) — `temperature_ratio_near_degenerate`
   (`Identifiability.lean`) bounds the two-temperature ratio difference LINEARLY in
   `|E_i − E_j|` with an explicit constant, so "small ΔE ⇒ ill-conditioned" is quantitative
   (not just "zero ΔE ⇒ lost"), and its `ΔE = 0` limit recovers `temperature_degeneracy`
   exactly.

5. **End-to-end noise → composition propagation.** Error bounds take the per-species
   density error δ as a *given hypothesis* (`CompositionRobustness.lean:98,147`); the
   chain raw-noise ε → intensity error → slope/intercept error → δ → ΔC is not closed
   (gaps #10, #14), there is no `U_s(T)` Lipschitz lemma, and the deterministic slope
   bound assumes a single global ε (no per-line heteroscedastic variant, gap #19).
   ✅ **Partially addressed** in `ErrorBudget.lean` (2026-07-02):
   `olsSlope_stable_hetero` (per-line heteroscedastic budgets `ε_k` — exploits noiseless
   lines no global-ε bound can), `olsSlope_stable_l1_of_hetero` (recovers the global bound
   as the constant special case), `temp_rel_error_hetero` (composed per-line noise ⇒
   relative temperature error). **Residual:** the `U_s(T)` Lipschitz leg and the final
   δ→ΔC cross-channel coupling (recovered-T error through `U_s(T̂)` into the density
   channel) — recorded in-file; the temperature and composition budgets remain independent
   until then.

6. **Coupled Saha–closure–charge fixed point.** ✅ **Addressed (reduced core)** in
   `SahaEquilibrium.lean` (2026-07-02): the single-element, two-stage, fixed-T system
   (charge neutrality `n_e = N₁` via `chargeNeutrality_two_stage`, Saha `R·n_e = S`,
   closure `N₀+N₁ = Ntot`) reduces to `n_e² = S(Ntot − n_e)` with closed form
   `sahaEquilibriumNe`; existence (`0 < n_e < Ntot`, self-consistency), uniqueness of the
   positive root, the bundled `∃!` for the full `(n_e, N₀, N₁)` state
   (`sahaEquilibrium_unique_state`), and strict monotonicity in S. **Residual:** the
   multi-element loop coupled through shared n_e, the outer T-iteration, and — crucially —
   *convergence of the iterative map* (the fixed point exists and is unique; the solver's
   convergence flag is licensed for the reduced core's *target*, not yet its iteration).

7. **Multi-species per-U generalization.** ✅ **Addressed** in `MultiSpecies.lean`
   (2026-07-02): `deNormalizedDensityPerU` / `lineIntensityPerU` with genuinely
   per-species `U_s`; `density_ratio_from_intensities_perU` and
   `speciesComposition_ratio_from_intensities_perU` prove ratio/relative-composition
   recovery with `U_s ≠ U_t`; `rfl` bridges + `_ofPerU` corollaries re-derive the old
   shared-U theorems as literal `Us := partitionFunction` specializations (the shared-U
   reduction is fully discharged, not siblinged).

8. **Joint (T, composition) from ≥2 lines/species.** ✅ **Addressed (two-line case)** in
   `JointIdentifiability.lean` (2026-07-02): `observe₂` (two emitting levels per species)
   and `joint_identifiability` — equal two-line observations + one distinct-energy pair on
   some species ⇒ equal T AND equal composition, with NO assumed ratio hypothesis: the
   temperature is extracted from `hObs` itself, discharging `general_identifiability`'s
   `hTratio` caveat. **Residual:** full n-line OLS-fit identifiability (the
   `Alt/LeastSquares` layer's concern) and the nonlinear joint least-squares inverse
   (gap #1 residual).

## Tier 2 — self-absorption / regime coverage

9. **Self-absorption composition-level non-identifiability.** ✅ **Addressed** in
   `SelfAbsorptionInverse.lean` (2026-07-02):
   `selfAbsorption_breaks_composition_identifiability` — an explicit two-species
   construction with per-species τ's whose thick observation vectors are IDENTICAL while
   the closure compositions DIFFER (species 0 reuses the per-line aliasing verbatim,
   species 1 fixed). Honest contrast retained: composition *survives* under matched/known
   τ (`thick_density_identifiability`); the LOST/PRESERVED boundary is exactly per-species
   vs common/known optical depth. Justifies refuse-to-report under unknown per-species τ.
10. **Thick-regime curve of growth.** ✅ **Partially addressed** in `EquivalentWidth.lean`
    (2026-07-02): `slabCurve_forward_lipschitz` (saturation kills forward sensitivity —
    response decays like `e^{−τ}`), `slabCurve_inverse_lipschitz` (the COG-inverse
    condition number `1/(1−Wmax)` blowing up at saturation — the explicit bound licensing
    the runtime saturation gate), `slabCurve_roundTrip_lipschitz` (the same blow-up as
    `e^{τmax}` phrased in τ). **Residual:** the thick-regime √τ (Ladenburg–Reiche /
    damping-wing) asymptotic stays honestly OUT of scope — it needs Voigt wings.
11. **Matrix-effect invariance under per-shot (T, n_e) variation.** ✅ **Partially
    addressed** in `MatrixEffects.lean` (2026-07-02): `homologousPair_ratio_closed_form` +
    `homologousPair_ratio_temperature_invariant` — energy-matched (homologous) cross-species
    line pairs have EXACTLY T-invariant intensity ratios (the shared `U(T)` cancels, no
    matched-U assumption smuggled); `nonHomologousPair_ratio_temperature_dependent` proves
    the invariance hinges on the energy match; per-species-U variants state the `U_t/U_s`
    residual explicitly. **Residual:** the quantitative `|ΔE| ≠ 0` per-shot drift bound
    (its same-species engine is `temperature_ratio_near_degenerate`); per-shot n_e enters
    only through Saha stage shuffling, outside this module's Boltzmann-only encoding.
12. **Continuous spatial (Abel) inverse + full-Voigt regime** (`SpatialForward.lean`,
    gap #27): only discrete onion-peeling / single-zone is covered. **Honest scoping
    (2026-07-02): no Lean fix this pass.** The continuous Abel integral-equation inverse
    and full-Voigt mixing are genuinely research-scale formalization efforts; the
    actionable content is RUNTIME regime detection (τ, spatial-gradient magnitude, Voigt
    mixing → refuse-to-report), which is a Tier-3-style wiring item, not a theorem. The
    discrete onion-peeling envelope remains the verified boundary.

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
