# Plan — upstreaming the Saha layer to physlib (eventually, not now)

A deliberate plan for contributing cflibs-formal's novel **Saha ionization** physics to
[physlib](https://github.com/leanprover-community/physlib) (formerly PhysLean + Lean-QuantumInfo).
This is a *future* effort with explicit triggers — **do not start now**.

## 1. Decision and rationale

**Keep our discrete, dimensionless, `Finset`/algebraic Boltzmann–Saha core** (Lean v4.31,
mathlib-only). It is the right abstraction for the CF-LIBS *inverse problem*: the soundness /
identifiability / reliability theorems are dimensionally trivial and want plain-ℝ
`field_simp`/`ring`/`log`/`exp`, not measure theory.

physlib is an **upstream target for our forward Saha physics, not a dependency.** Verified state
(2026-06-23, via `gh`):

- physlib is **actively maintained** but on **Lean v4.30.0** (we are v4.31.0) — depending on it
  forces a downgrade of our mathlib.
- Its statistical mechanics is **measure-theoretic and unit-aware**: even
  `CanonicalEnsemble/Finite.lean`'s discrete `Z = ∑ᵢ exp(−βEᵢ)` carries `[MeasurableSpace ι]` and a
  `Temperature` units type — heavier than our needs for the inverse-problem layer.
- It has `StatisticalMechanics` (`CanonicalEnsemble`, `TwoState`, `BoltzmannConstant`),
  `Thermodynamics`, `Units`/`Dimension`, and `translational`/`idealGas` physics — **but no
  ionization equilibrium**: `Saha`, `grandCanonical`, `chemicalPotential`, `ionization` all return
  **0 code hits**.

So the relationship is naturally **inverted**: physlib has Boltzmann / canonical ensemble /
translational partition function but no Saha; our Saha–Boltzmann is a clean *additive* contribution.

## 2. Scope — what to upstream (and what not)

**Primary candidate (one coherent concept = one PR):** the **Saha–Eggert ionization equation**
`n_{z+1}·n_e / n_z = 2·(U_{z+1}/U_z)·(2π m_e k_B T / h²)^{3/2}·exp(−χ / k_B T)`, plus its minimal API:
the `sahaFactor` definition, positivity, the `electronDensityFromRatio` inverse, and
`electronDensity` antitone in the stage ratio. (Our `Saha.lean` — audited *faithful* to Saha–Eggert
against Griem.)

**Secondary candidates (each a separate, later, single-concept PR — general physics, reusable
beyond CF-LIBS):**
- curve-of-growth escape factor `(1−e^−τ)/τ` *derived* from the radiative-transfer slab
  (`SelfAbsorption.slabIntensity_eq_thin_mul_SA`) — general radiative transfer;
- McWhirter LTE criterion `n_e ≥ 1.6e12·√T·ΔE³` (`StarkBroadening.mcWhirterBound`) — plasma physics;
- Stark linear-width electron-density diagnostic (Griem) — plasma diagnostics.

**Stays in cflibs-formal (domain-specific CF-LIBS *algorithm*, not library physics):** the
inverse-problem framework (`Inverse`, `Classic`, `Alt/*`), identifiability
(`Identifiability`, `CompositionIdentifiability`, `SahaInverse` joint inversion), reliability /
error budget (`Robustness`, `CompositionRobustness`, `ErrorBudget`), self-absorption *inverse*,
spatial Abel inversion, the closure / composition-simplex layer, and the oracle.

## 3. Form — fitting physlib's idiom

- **Build on** physlib's `StatisticalMechanics/CanonicalEnsemble` (esp. `Finite.lean`'s discrete
  `Fintype` partition function), `BoltzmannConstant`, `Temperature`, `Units`/`Dimension`, and its
  `translational`/`idealGas` physics for the `(2π m k T / h²)^{3/2}` factor (confirm whether
  `translational` already provides the translational partition function / thermal de-Broglie factor;
  if not, that becomes a small prerequisite sub-contribution). The two-stage neutral/ion system maps
  onto `CanonicalEnsemble/TwoState` or two `Finite` ensembles.
- **The main porting work is units:** restate our *bare-ℝ* `sahaFactor` / `thermalBracket` /
  `electronDensityFromRatio` in physlib's **unit-aware** form (`Temperature`, masses, energies
  carrying `Dimension`). A dimensionless core + unit-aware wrapper, following their conventions.
- **Likely a new file** `Physlib/StatisticalMechanics/Saha/Basic.lean` — a new file is justified
  (Saha is a distinct coherent concept) but confirm placement with maintainers first (§5b).
- **Conventions (AGENTS.md):** `theorem` only for the Saha equation itself (well known in the
  literature); `lemma` for supporting results; docstring every definition; numbered `# A.` / `## A.1.`
  sections; proofs < 50 LOC (split via their extract-by-meaning/structure rules); no trivial rewrites
  of mathlib/physlib; **no `axiom`, no `sorry`** (we are already axiom-clean — a strong fit).

## 4. Governance — physlib's AI policy (this is binding)

physlib **welcomes AI-assisted PRs**, but with hard human-accountability rules (AI-POLICY.md):

- **Brian is the human author and owner.** He must vouch that every definition, theorem statement,
  and proof step means what it claims (a green build only proves what was written, not that it is
  what was meant).
- **Brian verifies the references himself** — that the work exists and the cited statement/pages are
  right (Saha, M. N., *Phil. Mag.* **40** (1920) 472; Eggert, J., *Phys. Z.* **20** (1919) 570;
  Griem, *Principles of Plasma Spectroscopy*). **This must not be delegated to an AI.**
- **All reviewer communication must be by Brian**, not an AI agent. AI-assisted fixes to review
  feedback must be human-verified before re-request.
- AI (me) assists drafting/porting only; disclose per AI-POLICY §1.6.
- Finish checklist: import into `Physlib.lean` (sorted), `lake exe cache get` then `lake build`,
  `lake exe lint_all`, `./scripts/lint-style.sh` (commit first — it reads committed state),
  spell-check words in `scripts/MetaPrograms/spellingWords.txt`. **Single-concept PR**, atomic
  commits, **DCO sign-off**.

## 5. Prerequisites, triggers, and steps

**Triggers (all should hold before starting):**
1. Our Saha module is stable and audited — ✅ done (literature-validity audit: faithful).
2. A **minimal, CF-LIBS-free Saha** is extracted from cflibs-formal (strip inverse/oracle
   scaffolding so the upstream candidate is just the forward physics). *Prep task, doable anytime.*
3. physlib's stat-mech API is stable enough to build on (track `CanonicalEnsemble`/`translational`).
4. Brian has bandwidth for the human-author / voucher / **reviewer-communication** burden.
5. Develop the PR against **physlib's** pinned Lean version (in a physlib checkout) — so physlib's
   version is a blocker for *depending*, not for *upstreaming*.

**Step sequence (when triggered):**
a. Re-scout physlib (current Lean version; whether Saha / translational-PF / grand-canonical were
   added since; the `CanonicalEnsemble.Finite` and `translational` APIs).
b. **Brian opens a physlib issue/discussion** proposing the Saha contribution to get maintainer
   agreement on the abstraction *before* building — state-the-ratio vs derive-from-grand-canonical,
   file placement, units convention. (Avoids a large PR on the wrong abstraction.)
c. Prototype `Saha/Basic.lean` against a physlib checkout — unit-aware, on top of their PF /
   translational / Temperature API.
d. Run physlib's gates (lake build, `lint_all`, `lint-style`, alpha linters if under `PhyslibAlpha`).
e. **Brian opens the PR** (single concept, atomic commits, DCO sign-off) and drives review.
f. *Optional, much later:* once merged and physlib reaches 4.31+, reconsider whether cflibs-formal
   should *depend* on physlib's Saha (letting us delete our forward Saha and keep only the inverse
   layer) — a separate future decision.

## 6. Risks / open questions

- **Abstraction risk:** maintainers may want Saha derived from a grand-canonical ensemble (which
  physlib lacks) rather than stated as the Saha–Eggert ratio — could expand scope into building
  grand-canonical first. Mitigated by the upfront issue (5b).
- **Units overhead:** porting bare-ℝ to `Temperature`/`Dimension` may be fiddly; budget for it.
- **Version churn + review latency** on physlib's side.
- **AI-policy human burden** on Brian — especially the human-only reviewer-communication rule.

## 7. Watch-items

- Track physlib's `lean-toolchain` (v4.30.0 as of 2026-06-23) and any new `StatisticalMechanics`
  ionization / grand-canonical / Saha work — re-scout before acting.
- The minimal-Saha extraction (trigger 2) is the one piece of prep worth doing on our side ahead of
  time; everything else waits for Brian's go-ahead.
