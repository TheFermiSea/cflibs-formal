# Outer T-Iteration of the Full CF-LIBS Loop

Planning dossier. Not Lean code. Every current-state claim is anchored to a real
declaration in `CflibsFormal/*.lean`; every mathlib claim is grepped and marked
VERIFIED / ABSENT against mathlib v4.31.0 (`.lake/packages/mathlib`).

---

## 1. The formal obstacle

CF-LIBS runs an **outer loop**: guess `T` → read composition / `n_e` at that `T`
→ re-estimate `T` → repeat. Every *ingredient* sensitivity bound now exists, but
the loop **as a self-map with a fixed point** does not. The module header of
`SahaEquilibrium.lean` (lines 69–71) states this in the repo's own words:

> "What remains open is the outer temperature iteration and the convergence of
> the *multi-element* coupled iteration."

What we HAVE (anchored):

* **Inner `n_e` iteration — fully closed (template).** `sahaIter`
  (`SahaEquilibrium.lean:450`), with the complete Banach-style chain
  `sahaIter_fixedPoint` (:455), `sahaIter_contraction` (:485),
  `sahaIter_mapsTo` (:542, interval invariance), `sahaIter_geometric_error`
  (:558), `sahaIter_tendsto` (:593). This is a **hand-rolled** contraction on a
  box `[0,b]` in `|·|` — it does *not* use mathlib's `ContractingWith`. It is the
  exact structural template for the outer loop.
* **Coupled `n_e` at fixed `T` — existence + uniqueness only.**
  `multiElement_exists_pos_fixedPoint` (`SahaEquilibrium.lean:314`, IVT),
  `multiElement_pos_fixedPoint_unique` (:363). No iteration convergence.
* **`T → n_e` Lipschitz leg.** `electronDensityFromRatio_lipschitz_temp`
  (`SahaStability.lean:660`): `|n_e(T₁)−n_e(T₂)| ≤ (sahaFactorLipConst …/R₀)·|T₁−T₂|`
  on `[Tmin,Tmax]`, constant from `sahaFactorLipConst` (`SahaStability.lean:542`)
  via `sahaFactor_lipschitz_temp` (:570).
* **slope → `T` legs.** `temp_rel_error_le/eq/hetero` (`ErrorBudget.lean:214/198/401`),
  `olsSlope_stable_l1/l2/hetero` (`ErrorBudget.lean:84/137/365`).
* **`T` → density → composition leg.** `tempResponseErrorBound`
  (`AtomicDataPerturbation.lean:513`), `classicDensity_temperature_aliasing_error`
  (:530), assembled end-to-end in `noise_to_composition`
  (`NoiseToComposition.lean:281`) via `noise_to_temperatureGap` (:191),
  `noise_to_density` (:235), `tempResponseErrorBoundOfGap_mono` (:149).
* **The physical coupling.** `sahaBoltzmann_plot` (`SahaInverse.lean:95`) and
  `sahaBoltzmann_shift_eq_log_saha` (:134): the inter-stage ordinate offset equals
  `log S(T) − log n_e + (log U_z − log U_{z+1})`, and `saha_joint_identifiability`
  (:183) recovers `(T, n_e)` jointly — but as *identifiability* (unique preimage),
  **not** as an iteration map.

The gap: there is **no `Φ`** — no self-map on `T` (or on `(T,n_e)`) whose fixed
point *is* the self-consistent CF-LIBS solution, and no theorem that its iteration
converges. All the Lipschitz constants that would bound such a `Φ` exist as
separate lemmas; nothing composes them into a contraction.

**Precise statement we cannot yet prove.** For a temperature box `[Tmin,Tmax]`,
a self-map `Φ : [Tmin,Tmax] → [Tmin,Tmax]` modelling one outer sweep, there is a
unique `T⋆` with `Φ T⋆ = T⋆`, and `Φ^[n] T₀ → T⋆` for every `T₀ ∈ [Tmin,Tmax]` —
gated by an explicit, runtime-checkable condition on the published sensitivity
constants.

---

## 2. Mathematical landscape

### Literature

* Banach fixed-point / contraction mapping — standard; the repo already applies
  the geometric-series form by hand in the `sahaIter` block.
  [VERIFIED: mathlib `ContractingWith`, see §3.]
* **Aguilera & Aragón 2007**, *Multi-element Saha–Boltzmann and Boltzmann plots*,
  Spectrochim. Acta B 62:378 — the multi-stage plot whose common slope fixes `T`
  and whose inter-stage offset encodes `n_e`; **this is the coupling that makes
  the outer loop non-trivial.** [VERIFIED: on the repo's approved-citation list;
  cited already at `SahaInverse.lean:52`.]
* **Yalcin 1999**, Appl. Phys. B 68:121 — joint `(T,n_e)` from a Saha–Boltzmann
  plot. [VERIFIED: approved list; `SahaInverse.lean:48`.]
* **Tognoni 2010 / Ciucci 1999** — the CF-LIBS algorithm and its iterative `T`
  refinement. [VERIFIED: approved list.]
* Cristoforetti & Tognoni 2013 — convergence behaviour of the CF-LIBS iteration in
  practice (damping / under-relaxation frequently used). [UNVERIFIED — must check
  the exact convergence claim before citing in a Lean docstring.]

### The crux modelling decision: what IS `Φ`? (seeded direction b)

The whole dossier turns on one fact: **the per-stage two-line temperature is
composition-independent.** `temperature_from_two_lines` (`ForwardMap.lean:107`)
proves the Boltzmann-plot slope equals `1/(k_B T)` *exactly*, with `Fcal, N, U, g,
A` all cancelling. So any `Φ` built from a single-stage slope **ignores its
input** → constant map → the "outer loop" converges in one step and the theorem is
vacuous. This trap must be dodged. Three candidate loop models:

**Model A — two-line `Φ_T` (degenerate).** `Φ(T) := 1/(k_B · slope)` with
`slope = temperature_from_two_lines`. Since `slope` is independent of `T`, `Φ` is
**constant**; fixed point trivial, contraction constant `L = 0`.
*Fidelity:* low (not the real loop). *Tractability:* A but not worth stating as a
headline. *Verdict:* REFUTED as the frontier's target; keep only as a one-line
sanity remark ("the `T`-subproblem closes in one step; the loop's non-triviality
lives entirely in the `n_e` feedback").

**Model B — combined Saha–Boltzmann slope (the physical CF-LIBS loop).** Put
*all* stages on one plot. To place the ion-stage points on the shared line, their
ordinates are shifted by the Saha offset `c(n_e,T) = log S(T) − log n_e + Δlog U`
(exactly `sahaBoltzmann_shift_eq_log_saha`, `SahaInverse.lean:134`). This offset is
the **same constant** for every ion line (independent of that line's `E`), so it
does **not** change the within-stage slope — but a vertical shift of the ion
*cluster* relative to the neutral cluster **does** change the *combined* OLS slope
whenever the two clusters occupy different energy ranges. Concretely, for the
merged fit `slope = Cov(E,Y)/Var(E)`, adding `c` to the ion subset moves the slope
linearly in `c`:
`Δslope = c · (mean_ion E − mean_all E) · (n_ion/N) / Var(E)`.
Then `Φ(T) := 1/(k_B · slope(n_e(T)))` with `n_e(T)` the Saha-equilibrium density
(`sahaEquilibriumNe` / `electronDensityFromRatio`). Now `Φ` is **genuinely
`T`-dependent** — the loop is real. Its Lipschitz constant is the product
`L_Φ = L_{ne}·L_{log}·L_{off→slope}·L_{slope→T}`, i.e. **literally the product of
published sensitivity constants** (direction a). *Fidelity:* high (this is
Aguilera–Aragón). *Tractability:* B — needs one NEW def (`combinedSahaBoltzmannSlope`)
and one NEW OLS lemma (slope-vs-subset-offset). *Verdict:* CONFIRMED as the target.

**Model C — joint `(T,n_e)` self-map on a 2-D box.** `Φ(T,n_e) =
(T-from-slope-given-n_e, n_e-from-Saha-given-T)` on `[Tmin,Tmax]×[ne_min,ne_max]`
with the sup metric. The `n_e`-leg Lipschitz-in-`T` exists
(`electronDensityFromRatio_lipschitz_temp`); the `T`-leg Lipschitz-in-`n_e` is the
same new content as Model B. *Fidelity:* highest (matches
`saha_joint_identifiability`'s two unknowns). *Tractability:* B–C — needs product-
metric contraction (mathlib has `Prod` EMetric) and the same new `T`-leg. *Verdict:*
CONFIRMED but DEFER — do the 1-D Model B first; C is a lift of it.

### Direction (a) — "product of constants < 1" as the headline (CONFIRM)

`Φ = legT ∘ legNe` where `legNe : Tbox → neBox` is `L₁`-Lipschitz and
`legT : neBox → Tbox` is `L₂`-Lipschitz. If both map their box into the next box
and `L₁·L₂ < 1`, `Φ` contracts `Tbox` with factor `L₁·L₂`. This is a **runtime-
checkable gate**: the solver already computes `sahaFactorLipConst/R₀` (= `L₁`) and
the slope→T constants (`L₂` factors); the flag is `L₁·L₂ < 1`. CONFIRMED and
provable now, abstractly, before any physics is plugged in (Milestone 1).

### Direction (c) — interval invariance is a genuine prerequisite (CONFIRM/REFINE)

`Φ([Tmin,Tmax]) ⊆ [Tmin,Tmax]` is **not** automatic. The template makes this an
explicit hypothesis: `sahaIter_mapsTo` (`SahaEquilibrium.lean:542`) assumes
`√(S·Ntot) ≤ b`. For the `T`-box the analogous side-condition is that the recovered
`T′ = 1/(k_B·slope)` stays in `[Tmin,Tmax]`, i.e. `slope ∈ [1/(k_B Tmax),
1/(k_B Tmin)]` — an explicit, checkable bound on the combined slope over the box.
REFINED: invariance must be carried as a hypothesis (`hmaps`), exactly as the inner
loop does; it cannot be derived for free.

---

## 3. mathlib inventory (v4.31.0)

Needed vs available:

* **Contraction / Banach fixed point.**
  VERIFIED: `ContractingWith` = `K < 1 ∧ LipschitzWith K f`
  (`Mathlib/Topology/MetricSpace/Contracting.lean:40`).
  VERIFIED: set-restricted Banach — `efixedPoint'` (:170),
  `efixedPoint_isFixedPt'` (:180), `tendsto_iterate_efixedPoint'` (:185),
  `apriori_edist_iterate_efixedPoint_le'` (:190), for `IsComplete s` +
  `MapsTo f s s` + `ContractingWith K (hsf.restrict …)`.
  *Caveat:* these are stated in `edist` (`EMetricSpace`), and `ContractingWith`
  needs a **global** `LipschitzWith` on the subtype — so using them means porting
  the repo's `|·|`-on-box bounds through `edist`. This is precisely why the
  `sahaIter` block hand-rolled its contraction instead. Both routes are open; see
  Risks.
* **Lipschitz composition (product constant).**
  VERIFIED: `LipschitzOnWith` (`Mathlib/Topology/EMetricSpace/Lipschitz.lean:62`);
  `LipschitzOnWith.comp` (:328): `LipschitzOnWith Kg g t → LipschitzOnWith K f s →
  MapsTo f s t → LipschitzOnWith (Kg*K) (g∘f) s` — the product constant, exactly
  direction (a).
  VERIFIED: `lipschitzOnWith_iff_restrict` (:97) bridges box `|·|` bounds to
  `LipschitzWith` on the `Icc` subtype.
* **Completeness of the box.**
  VERIFIED: `IsClosed.isComplete` (`Mathlib/Topology/UniformSpace/Cauchy.lean:447`)
  and `IsCompact.isComplete` (:736). `isClosed_Icc` is standard (order-topology);
  gives `IsComplete (Set.Icc Tmin Tmax)` in `ℝ`.
* **Convergence machinery (hand-rolled route).**
  VERIFIED: `tendsto_pow_atTop_nhds_zero_of_lt_one`
  (`Mathlib/Analysis/SpecificLimits/Basic.lean:188`).
  Present-by-use (already invoked in `sahaIter_tendsto`): `squeeze_zero`,
  `Function.iterate_succ_apply'`, `tendsto_iff_dist_tendsto_zero`,
  `intermediate_value_Icc`.
* **2-D (Model C).** VERIFIED: `Prod` is an `EMetricSpace` (product sup metric),
  so `ContractingWith` applies to `ℝ×ℝ`; a hand-rolled `max`-metric contraction is
  also elementary. No ABSENT items for the 1-D plan.

Nothing on the critical path is ABSENT from mathlib v4.31.0. The only NEW content
is **repo-side modelling** (the combined-slope def and its offset→slope sensitivity),
not upstream infrastructure.

---

## 4. Milestone ladder

Ordered; each gives a Lean sketch, scope tag, prerequisites, tractability
(A = one session on current mathlib / B = hard but plausible / C = needs new
infrastructure or open math).

**M1 — abstract two-leg box contraction (the spine).** `[REDUCED]` · prereq: none
· **A**.
```
theorem outerContraction_box
    {Tmin Tmax nemin nemax L1 L2 : ℝ} {legNe legT : ℝ → ℝ}
    (hmapsNe : ∀ T ∈ Icc Tmin Tmax, legNe T ∈ Icc nemin nemax)
    (hmapsT  : ∀ n ∈ Icc nemin nemax, legT n ∈ Icc Tmin Tmax)
    (hL1 : ∀ T T' ∈ Icc Tmin Tmax, |legNe T − legNe T'| ≤ L1*|T−T'|)
    (hL2 : ∀ n n' ∈ Icc nemin nemax, |legT n − legT n'| ≤ L2*|n−n'|)
    (hq : L1*L2 < 1) (hL1nn : 0 ≤ L1) (hL2nn : 0 ≤ L2) :
    -- Φ := legT ∘ legNe maps Tbox→Tbox, contracts by L1*L2,
    -- has a unique fixed point in Tbox, and Φ^[n] T0 → T⋆.
```
Mirror the `sahaIter` block verbatim: `mapsTo`, one-step contraction, geometric
error (induction), `Tendsto` via `tendsto_pow_atTop_nhds_zero_of_lt_one` +
`squeeze_zero`; uniqueness from two fixed points + `hq`. This *is* direction (a)'s
headline stated abstractly. Reusable for M6 and (lifted) for Model C.

**M2 — `n_e`-leg interval invariance.** `[REDUCED]` · prereq: M-none · **A/B**.
```
theorem neLeg_mapsTo … : ∀ T ∈ Icc Tmin Tmax,
    electronDensityFromRatio kB T me h chi gZ EZ gZ1 EZ1 R ∈ Icc nemin nemax
```
`n_e(T)=S(T)/R`; bound `S(T)` on the box using the floor/ceiling lemmas already in
`SahaStability.lean` (`partitionFunction_ge_floor`, `partitionFunction_le_sum`,
`thermalBracket_mono`). Mostly assembling existing box bounds. **A** if `nemin/nemax`
are defined *as* those box bounds; **B** if independent numeric bounds are required.

**M3 — package `n_e`-leg as `LipschitzOnWith`.** `[REDUCED]` · prereq: M2 · **A**.
Restate `electronDensityFromRatio_lipschitz_temp` (`SahaStability.lean:660`) as
`LipschitzOnWith (sahaFactorLipConst…/R₀) (fun T => n_e(T)) (Icc Tmin Tmax)` via
`lipschitzOnWith_iff_restrict` + the `nndist/edist ↔ |·|` bridge on `ℝ`. Gives the
reusable `L₁` for M1/M6.

**M4 — combined Saha–Boltzmann slope + offset sensitivity (crux new content).**
`[REDUCED]` · prereq: none (independent) · **B**.
```
noncomputable def combinedSahaBoltzmannSlope … (ne : ℝ) : ℝ  -- OLS slope over
    -- neutral ordinates ∪ (ion ordinates + offset c(ne)),  c(ne)=…−log ne+…
theorem combinedSlope_offset_lipschitz … :
    |combinedSlope ne1 − combinedSlope ne2|
      ≤ (|mean_ion E − mean_all E|·(n_ion/N)/Var(E)) · |log ne1 − log ne2|
```
Pure OLS `Cov/Var` algebra — squarely in `ErrorBudget.lean`'s idiom
(`olsSlope_stable_*`). The def is new; the lemma is the linear slope-vs-offset
identity. This is where the real work is.

**M5 — `T`-leg Lipschitz (`n_e → T`).** `[REDUCED]` · prereq: M4 · **B**.
Compose three pieces with `LipschitzOnWith.comp` (product constants):
`n_e ↦ log n_e` (const `1/nemin` on `n_e ≥ nemin`) → `combinedSlope` (M4) →
`slope ↦ 1/(k_B·slope)` (const `1/(k_B·slope_min²)` on `slope ≥ slope_min`, the
temp-from-slope Lipschitz already implicit in `temp_rel_error_le`). Yields
`L₂ = (1/nemin)·(offset-const)·(1/(k_B slope_min²))` and invariance `hmapsT`
(direction c side-condition: `slope(neBox) ⊆ [1/(k_B Tmax), 1/(k_B Tmin)]`).

**M6 — HEADLINE: the outer loop contracts.** `[REDUCED]` · prereq: M1,M2,M3,M5 ·
**B**.
Instantiate M1 with `legNe` (M2/M3, `L₁`) and `legT` (M5, `L₂`). Conclusion: if
`L₁·L₂ < 1` — the product of the published sensitivity constants — then the CF-LIBS
outer sweep `Φ` on `[Tmin,Tmax]` has a unique self-consistent `T⋆` and iterates
converge geometrically. The hypothesis `L₁·L₂ < 1` is the runtime-checkable
certificate the solver flag should gate on.

**M7 — (optional) mathlib-`ContractingWith` restatement.** `[REDUCED]` · prereq:
M3,M5 · **B**. Re-derive M6 through `efixedPoint'` for an off-the-shelf uniqueness/
`Tendsto`, trading the hand-rolled induction for `edist` plumbing. Nice-to-have,
not on the critical path.

**M8 — (defer) joint `(T,n_e)` 2-D map / multi-element outer.** `[REDUCED]` ·
prereq: M4,M5 · **C**. Lift to `ℝ²` sup-metric (Model C) and/or couple with
`multiElement_exists_pos_fixedPoint`; also unblocks the still-open multi-element
*iteration* convergence. Needs product-metric contraction and is a genuine step up.

---

## 5. Risks & dead ends

* **Degeneracy trap (highest risk).** If `Φ` is modelled from a single-stage
  two-line temperature (`temperature_from_two_lines`, exact composition
  cancellation), `Φ` is **constant**, `L = 0`, and M6 is *true but vacuous* — a
  "contraction" that says nothing about a real loop. The theorem only has content
  under Model B's combined-slope coupling. Any reviewer will check this first;
  the dossier's headline must be Model B, not Model A.
* **Non-sharp constants ⇒ conservative gate.** `sahaFactorLipConst` is explicitly
  `REDUCED` (box floor/ceiling over-estimates; `SahaStability.lean:534–541`), and
  `sahaFactor` is **not** monotone in `T` (partition ratio can run either way — the
  scope note at `:563`), so only the sign-free Lipschitz constant is available.
  Hence `L₁·L₂ < 1` is a **sufficient**, not necessary, convergence certificate: it
  may fail to certify a loop that actually converges. Honest framing required
  (SUFFICIENT gate), and the constant may need tightening to be useful in practice.
* **Interval invariance can fail.** If `Φ` leaves `[Tmin,Tmax]` (slope drifts out
  of `[1/(k_B Tmax),1/(k_B Tmin)]`), there is no fixed-point claim. `hmaps` is a
  real hypothesis, not a formality (cf. `sahaIter_mapsTo`).
* **M4 is not a one-liner.** The offset→slope sensitivity needs a clean OLS
  `Cov/Var` identity for a *subset* vertical shift. Plausible (ErrorBudget idiom)
  but the algebra (partitioning the sum into neutral/ion subsets, tracking
  `mean_ion − mean_all`) is fiddly; budget a full session.
* **`ContractingWith` edist tax.** The mathlib route (M7) forces `nndist/edist`
  bookkeeping on the `Icc` subtype; the repo already voted against this by
  hand-rolling `sahaIter`. Don't start there — hand-roll M1, add M7 only if the
  off-the-shelf uniqueness pays for the plumbing.
* **Physical Jacobian may exceed 1.** In real LIBS the outer loop is often
  under-relaxed/damped (Cristoforetti & Tognoni 2013 [UNVERIFIED]); the bare
  contraction gate may seldom fire without damping. A damped variant
  `Φ_λ = (1−λ)·id + λ·Φ` (contraction constant `|1−λ| + λ·L`) is a natural
  follow-on and widens the certifiable regime — worth a note, not a blocker.
* **Multi-element outer (Model C / M8)** compounds the still-open multi-element
  `n_e`-iteration convergence; keep it deferred.

---

## 6. Recommendation

**Attack now, starting with M1.** The abstract two-leg box contraction is
tractability **A**, needs zero new physics defs, mirrors the already-proven
`sahaIter` block, and immediately encodes direction (a)'s headline ("product of
published sensitivity constants `< 1` ⇒ the outer loop contracts on the box").
It is the reusable spine that M6 (and, lifted, Model C) plug into.

Sequence: **M1** (spine, A) → **M2/M3** (n_e leg — the Lipschitz constant already
exists, just repackage, A) → **M4/M5** (the crux: combined-slope def + n_e→T
Lipschitz, B) → **M6** (headline, B). Defer **M7** (mathlib `ContractingWith`
restatement) and **M8** (2-D / multi-element, C).

**Single best first milestone: M1** — `outerContraction_box`, scope `[REDUCED]`,
grade **A**.

**Key dependency to flag loudly:** the outer map is non-degenerate *only* through
the combined Saha–Boltzmann slope (Model B), because the single-stage two-line
temperature is composition-independent by `temperature_from_two_lines`. Building
`combinedSahaBoltzmannSlope` and its offset→slope sensitivity (M4) is the one piece
of genuinely new content the whole frontier rests on; without it, M6 is vacuous.
