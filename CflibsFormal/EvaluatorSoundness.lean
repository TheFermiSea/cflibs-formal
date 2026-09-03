/-
Copyright (c) 2026 Brian Squires. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Squires
-/
import Mathlib
import CflibsFormal.Certificates
import CflibsFormal.NoiseToComposition

/-!
# CF-LIBS formalization — evaluator soundness (what passing the hard certificate gate buys)

The companion's algorithm-search evaluator (`cflibs/evolution/certificate_gate.py`:
`GateProtocol`, `hard_certificate_gate`) rejects a candidate answer unless a HARD set of runtime
certificates passes on inputs the evaluator re-derives itself (energies / Einstein coefficients
from the atomic DB, SNR from the spectrum, the McWhirter gap from the DB term scheme). This module
answers the one question a verified spec can answer about that gate: **which of its clauses do
formal work, in which theorem, and which do none?** Nothing is reproven — every result is a thin
re-export of `NoiseToComposition.noise_to_composition` or of a `Certificates.lean` soundness
theorem, and the value of the module is the *ledger* below, made precise as Lean predicates.

The shipped HARD set (read from `certificate_gate.py`, `HARD_CERTIFICATES_DEFAULT` + the box and
simplex checks), and where each clause lands here:

| gate clause | Lean predicate | formal consumer in this module |
|---|---|---|
| C1 energy spread | `energySpreadCert ET` | `noise_to_composition` (its `hvarT`) |
| C3 conditioning | `conditioningCert ET` | none — the *same* predicate as C1 |
| C4 slope budget (`ε = 1/min SNR`) | `slopeBudgetCert` | `hardGateBundle_slope_error_le` only |
| C7 McWhirter at reported `(T̂, nₑ)` | `mcWhirterCert C T̂ ΔE nₑ` | `…_thermalizationLimit` only |
| C12 known τ ≥ 0 per SA-corrected line | `∀ k, knownTauCert (τ k)` | none here |
| physical box on the reported `T̂` | `Tmin ≤ T̂ ≤ Tmax` | `noise_to_composition` (`hThat`, …) |
| `nₑ` floor | `neMin ≤ nₑ` | none (a physical floor; no theorem consumes it) |
| protocol constants | `0 < kB`, `0 < Tmin` | `noise_to_composition` |
| atomic-DB positivity | `0 < g`, `0 ≤ E`, `0 < A` | `noise_to_composition` |
| simplex on the composition | — | automatic for the Lean model (`composition_sum_one`) |
| C2 / C9 / C10 / C13 | `conditionalGateClauses` | none — materialized only when reported |

The unconditional clauses form `hardGateBundle`; the sub-conjunction that `noise_to_composition`
actually consumes is `gateCoreForComposition`, and
`hardGateBundle_implies_noise_to_composition_hyps` is the projection between them. The payoff
`hardGateBundle_composition_error_le` is the composed end-to-end bound under the bundle **plus the
hypotheses no runtime gate can supply**:

* **R1 (not certifiable at runtime).** `hδT : ∀ k, |ŷₖ − yₖ| ≤ εₖ` — the per-line ordinate noise
  bound is a distance to the *unknown true* ordinates. The gate can compute `ε = 1/min SNR`, but
  that `|ŷ − y| ≤ ε` is a *noise-model assumption*; it is carried explicitly, never certified.
* **A-priori bracket on the truth** (`aprioriBracket`). The gate boxes the *reported* `T̂`; the
  bound also needs the *true* `T ∈ [Tmin, Tmax]`, `0 < Fcal`, `0 < Nₛ ≤ Nmax` — statements about
  unknown quantities, i.e. modeling assumptions, not runtime checks.
* **Definitional** `hβ`, `hβHat` — the OLS Boltzmann-plot slopes are `1/(kB·T)`, `1/(kB·T̂)`: this
  is what "the temperature" *means* in the spec, not a check.
* **`envelopeCert`** — the worst-case exp-channel smallness and the uniform envelope `Φ` at the
  noise-derived gap `dmax`. Runtime-*evaluable* (arithmetic in `ε`, the DB data and the protocol
  box, exactly as C4 is evaluable in `ε`), but the shipped gate does **not** compute it; it is
  carried explicitly and named so the evaluator can add it as a fifth runtime predicate.

**Negative clarity (C7).** `mcWhirterCert` is *not* a hypothesis of `noise_to_composition`, and
the McWhirter data `(C, ΔE, nₑ)` do not even occur in the signature of `gateCoreForComposition`
or `gateCore_composition_error_le`. C7 certifies LTE admissibility of the emission *model*
(`mcWhirter_certificate_sound`: `ΔE ≤ thermalizationLimit`) — a REDUCED premise under which the
Boltzmann/Saha forward model is meaningful at all. Passing it does not enter the error bound and
must not be reported as tightening it; failing it means the *model* premise is unsupported, which
the bound cannot see. The same holds for C12 (exactness of the self-absorption pre-correction).

## Literature and scope

Scope: **REDUCED**, inherited verbatim from the wrapped theorems — the composed error budget of
Tognoni et al. 2010 (`NoiseToComposition.lean`; worst-case ℓ¹ slope error, `Tmax` over-estimate,
non-sharp temperature-response constants, uniform envelope `Φ`), the rank / budget certificates
(Tognoni 2010, Aguilera & Aragón 2007) and the McWhirter criterion (McWhirter 1965 via
Cristoforetti et al. 2010), all as cited in `Certificates.lean`. This module adds no mathematics.
R1 stated plainly: the per-line noise bound `ε` is a distance to an unknown truth and cannot be
certified at runtime; every result that mentions it carries it as an explicit hypothesis. Float ≠ ℝ
near a threshold (R6) applies to every predicate here exactly as it does in `Certificates.lean`.
The non-vacuity witnesses reuse the `oracle/fixtures.json` certificate-scenario inputs anchored in
`OracleAnchors.lean` (`E = (0,1)`, `ε = 1`, `τ_β = 2`, `C = ΔE = 1`, `nₑ = 2`, `τ = 1`).
-/

namespace CflibsFormal

variable {ι κ ιT : Type*} [Fintype ιT]

/-! ## The shipped HARD set as Lean predicates -/

/-- **The unconditional HARD gate** (`certificate_gate.py`, `HARD_CERTIFICATES_DEFAULT` minus the
`None`-gated C2/C9/C10/C13, plus the physical box and the protocol / atomic-DB positivity the
evaluator re-derives). Inputs: protocol constants `kB, Tmin, Tmax, neMin, tauBeta, C`; the
candidate's reported temperature `That` and electron density `ne`; the SNR-derived `eps`; the
DB resonance gap `dE`; the witness lines' upper-level energies `ET` and per-line optical depths
`tau` (an uncorrected line carries `τ = 0`, which passes C12 trivially — the Python checks
`min τ ≥ 0` over the corrected lines); and the per-species atomic data `g, E, A` at the analysis
line `u`. The box is on the *reported* `That`, exactly as the Python checks it. Every clause is
runtime-checkable arithmetic. -/
def hardGateBundle (kB Tmin Tmax That eps tauBeta C dE ne neMin : ℝ)
    (ET tau : ιT → ℝ) (g E A : κ → ι → ℝ) (u : κ → ι) : Prop :=
  -- C1 energy spread and C3 conditioning (the same predicate, both evaluated by the gate)
  energySpreadCert ET ∧ conditioningCert ET
    -- C4 slope budget with `eps = 1/min SNR` and the protocol `tauBeta`
    ∧ slopeBudgetCert eps tauBeta (∑ k, (ET k - mean ET) ^ 2) (Fintype.card ιT)
    -- C7 McWhirter at the REPORTED temperature and a measured `ne`
    ∧ mcWhirterCert C That dE ne
    -- C12 known optical depth for every SA-corrected line
    ∧ (∀ k, knownTauCert (tau k))
    -- physical box on the REPORTED temperature, and the electron-density floor
    ∧ (Tmin ≤ That ∧ That ≤ Tmax) ∧ neMin ≤ ne
    -- protocol constants
    ∧ (0 < kB ∧ 0 < Tmin)
    -- atomic-DB positivity, re-derived on the evaluator side
    ∧ (∀ s k, 0 < g s k) ∧ (∀ s k, 0 ≤ E s k) ∧ (∀ s, 0 < A s (u s))

/-- **The `None`-gated HARD clauses** — C2 (joint rank, only when ≥ 2 ion stages are used), C9
(Saha iteration, only when `saha_iter` is reported), C10 (damped multi-element iteration, only
when `damped_iter` is reported) and C13 (distinct curve-of-growth widths, only when `cog_widths`
are given). `none` mirrors the Python's "input not materialized ⇒ clause skipped". They are kept
OUT of `hardGateBundle` for two reasons: the gate itself evaluates them only conditionally, and
none of them is a hypothesis of `noise_to_composition` — each certifies a *different* theorem
(joint (T, nₑ) identifiability, closure-iteration convergence, self-absorption identifiability).
Bundling them would misdescribe both the gate and the bound. -/
def conditionalGateClauses {ιD : Type*} (ET : ιT → ℝ) (stage : Option (ιT → ℝ))
    (saha : Option (ℝ × ℝ × ℝ)) (damped : Option ((ιD → ℝ) × (ιD → ℝ)))
    (cog : Option (ℝ × ℝ)) : Prop :=
  stage.elim True (fun s => jointRankCert ET s)
    ∧ saha.elim True (fun p => sahaIterCert p.1 p.2.1 p.2.2)
    ∧ damped.elim True (fun p => dampedIterCert p.1 p.2)
    ∧ cog.elim True (fun w => saDistinctCert w.1 w.2)

/-! ## What `noise_to_composition` consumes, and what no gate can supply -/

/-- **The sub-conjunction of `hardGateBundle` that `noise_to_composition` consumes.** Exactly the
hypotheses `hkB, hTmin, hThat, hTmaxThat, hvarT, hg, hE, hA` of `NoiseToComposition.lean:281`.
Note what is absent: the McWhirter data `(C, dE, ne)`, the slope budget `(eps, tauBeta)`, the
optical depths `tau` and the `ne` floor are not even parameters — C3/C4/C7/C12 and the floor do
no work in the composition bound. -/
def gateCoreForComposition (kB Tmin Tmax That : ℝ) (ET : ιT → ℝ) (g E A : κ → ι → ℝ)
    (u : κ → ι) : Prop :=
  0 < kB ∧ 0 < Tmin ∧ Tmin ≤ That ∧ That ≤ Tmax
    ∧ 0 < ∑ k, (ET k - mean ET) ^ 2
    ∧ (∀ s k, 0 < g s k) ∧ (∀ s k, 0 ≤ E s k) ∧ (∀ s, 0 < A s (u s))

/-- **Envelope certificate** — the `hΦ0`, `hsmallmax`, `henvmax` hypotheses of
`noise_to_composition`, stated at the noise-derived worst-case gap
`dmax = noiseTempGapBound kB Tmax ET epsT`. Runtime-*evaluable*: pure arithmetic in the per-line
budgets `epsT` (the same epistemic input C4 consumes, R1), the DB data `g, E` at `u`/`k0`, the
protocol box and the chosen envelope `Φ`. The shipped gate does **not** compute it; it is carried
explicitly by the payoff theorem so that the evaluator can add it as a fifth runtime predicate. -/
def envelopeCert [Fintype ι] (kB Tmin Tmax Φ : ℝ) (ET epsT : ιT → ℝ) (g E : κ → ι → ℝ)
    (u k0 : κ → ι) : Prop :=
  0 ≤ Φ
    ∧ (∀ s, Real.exp (E s (u s) * noiseTempGapBound kB Tmax ET epsT / (kB * Tmin ^ 2)) - 1 < 1)
    ∧ (∀ s, tempResponseErrorBoundOfGap kB Tmin (noiseTempGapBound kB Tmax ET epsT)
        (g s) (E s) (u s) (k0 s) ≤ Φ)

/-- **A-priori bracket on the unknown truth — NOT runtime-checkable.** The hypotheses `hT, hTmaxT,
hFcal, hN, hNmax` of `noise_to_composition` constrain the *true* temperature `T`, the
experimental factor `Fcal` and the *true* densities `N`: `Tmin ≤ T ≤ Tmax`, `0 < Fcal`,
`0 < Nₛ ≤ Nmax`. The gate boxes the *reported* `T̂` (in `hardGateBundle`), never the truth; these
are modeling assumptions and are carried explicitly, separate from the bundle, so that no reader
mistakes them for gate output. -/
def aprioriBracket (Tmin Tmax T Fcal Nmax : ℝ) (N : κ → ℝ) : Prop :=
  (Tmin ≤ T ∧ T ≤ Tmax) ∧ 0 < Fcal ∧ (∀ s, 0 < N s) ∧ (∀ s, N s ≤ Nmax)

/-- **The hard gate discharges exactly the `gateCoreForComposition` hypotheses** of
`noise_to_composition` — C1 (as `hvarT`), the box on the reported `T̂`, the protocol constants and
the DB positivity. A projection; the clauses C3, C4, C7, C12 and the `nₑ` floor are dropped on
the way, which is the formal content: they do not feed the composition bound. -/
theorem hardGateBundle_implies_noise_to_composition_hyps
    {kB Tmin Tmax That eps tauBeta C dE ne neMin : ℝ} {ET tau : ιT → ℝ}
    {g E A : κ → ι → ℝ} {u : κ → ι}
    (hgate : hardGateBundle kB Tmin Tmax That eps tauBeta C dE ne neMin ET tau g E A u) :
    gateCoreForComposition kB Tmin Tmax That ET g E A u := by
  obtain ⟨h1, -, -, -, -, ⟨hThat, hTmax⟩, -, ⟨hkB, hTmin⟩, hg, hE, hA⟩ := hgate
  exact ⟨hkB, hTmin, hThat, hTmax, h1, hg, hE, hA⟩

/-- **The gate is implied by the individual certificate verdicts** as the companion's
`evaluate_certificates` reports them: the Python `all_passed` on the unconditional HARD subset,
together with the box / floor / positivity checks, *is* `hardGateBundle`. The constructor, named so
the correspondence is a theorem rather than folklore. -/
theorem hardGateBundle_of_certificates_report
    {kB Tmin Tmax That eps tauBeta C dE ne neMin : ℝ} {ET tau : ιT → ℝ}
    {g E A : κ → ι → ℝ} {u : κ → ι}
    (h1 : energySpreadCert ET) (h3 : conditioningCert ET)
    (h4 : slopeBudgetCert eps tauBeta (∑ k, (ET k - mean ET) ^ 2) (Fintype.card ιT))
    (h7 : mcWhirterCert C That dE ne) (h12 : ∀ k, knownTauCert (tau k))
    (hbox : Tmin ≤ That ∧ That ≤ Tmax) (hne : neMin ≤ ne) (hproto : 0 < kB ∧ 0 < Tmin)
    (hg : ∀ s k, 0 < g s k) (hE : ∀ s k, 0 ≤ E s k) (hA : ∀ s, 0 < A s (u s)) :
    hardGateBundle kB Tmin Tmax That eps tauBeta C dE ne neMin ET tau g E A u :=
  ⟨h1, h3, h4, h7, h12, hbox, hne, hproto, hg, hE, hA⟩

/-! ## The payoff: the composed error bound under the gate -/

/-- **Composition error under the core clauses (REDUCED, Tognoni 2010).** `noise_to_composition`
re-exported with its hypotheses regrouped: the gate-supplied `gateCoreForComposition`, the
runtime-evaluable `envelopeCert`, the a-priori `aprioriBracket`, the **R1 noise bound `hδT`
(not certifiable)**, and the definitional slope identifications `hβ`, `hβHat`. The McWhirter data
do not occur in this statement. -/
theorem gateCore_composition_error_le [Fintype ι] [Fintype κ] [Nonempty ι] [Nonempty κ]
    [Nonempty ιT] {kB Tmin Tmax T That Fcal Φ Nmax : ℝ} {ET yT yHatT epsT : ιT → ℝ}
    {N : κ → ℝ} {g E A : κ → ι → ℝ} {u k0 : κ → ι}
    (hcore : gateCoreForComposition kB Tmin Tmax That ET g E A u)
    (henv : envelopeCert kB Tmin Tmax Φ ET epsT g E u k0)
    (hprior : aprioriBracket Tmin Tmax T Fcal Nmax N)
    (hδT : ∀ k, |yHatT k - yT k| ≤ epsT k)
    (hβ : olsSlope ET yT = 1 / (kB * T))
    (hβHat : olsSlope ET yHatT = 1 / (kB * That))
    (s : κ) :
    |composition (recoveredDensityAtT kB T That Fcal g E A u N) s - composition N s|
      ≤ compositionErrorBound N
          (totalDensity (recoveredDensityAtT kB T That Fcal g E A u N)) (Nmax * Φ) s := by
  obtain ⟨hkB, hTmin, hThat, hTmaxThat, hvarT, hg, hE, hA⟩ := hcore
  obtain ⟨hΦ0, hsmallmax, henvmax⟩ := henv
  obtain ⟨⟨hT, hTmaxT⟩, hFcal, hN, hNmax⟩ := hprior
  exact noise_to_composition hkB hTmin hT hThat hTmaxT hTmaxThat hg hE hFcal hA hN hNmax hΦ0
    hvarT hδT hβ hβHat hsmallmax henvmax s

/-- **HEADLINE — what passing the hard gate formally buys (REDUCED, Tognoni 2010).** Under the
shipped unconditional HARD gate `hardGateBundle`, PLUS the hypotheses no gate can supply — the
runtime-evaluable but not-yet-shipped `envelopeCert`, the a-priori `aprioriBracket` on the truth,
the **R1 per-line noise bound `hδT` (a distance to the unknown true ordinates; not certifiable at
runtime)** and the definitional slope identifications — the recovered composition error obeys
exactly the `noise_to_composition` bound
  `|Ĉ_s − C_s| ≤ compositionErrorBound N Ŝ (Nmax·Φ) s`.
Of the gate's clauses only C1, the box on `T̂`, and the positivity data do work here (via
`hardGateBundle_implies_noise_to_composition_hyps`); C3, C4, C7, C12 and the `nₑ` floor are
discharged unused. In particular C7 (`mcWhirterCert`) certifies LTE validity of the *model* — a
separate REDUCED premise — and does not enter, tighten, or condition this bound. -/
theorem hardGateBundle_composition_error_le [Fintype ι] [Fintype κ] [Nonempty ι] [Nonempty κ]
    [Nonempty ιT] {kB Tmin Tmax T That Fcal Φ Nmax eps tauBeta C dE ne neMin : ℝ}
    {ET yT yHatT epsT tau : ιT → ℝ} {N : κ → ℝ} {g E A : κ → ι → ℝ} {u k0 : κ → ι}
    (hgate : hardGateBundle kB Tmin Tmax That eps tauBeta C dE ne neMin ET tau g E A u)
    (henv : envelopeCert kB Tmin Tmax Φ ET epsT g E u k0)
    (hprior : aprioriBracket Tmin Tmax T Fcal Nmax N)
    (hδT : ∀ k, |yHatT k - yT k| ≤ epsT k)
    (hβ : olsSlope ET yT = 1 / (kB * T))
    (hβHat : olsSlope ET yHatT = 1 / (kB * That))
    (s : κ) :
    |composition (recoveredDensityAtT kB T That Fcal g E A u N) s - composition N s|
      ≤ compositionErrorBound N
          (totalDensity (recoveredDensityAtT kB T That Fcal g E A u N)) (Nmax * Φ) s :=
  gateCore_composition_error_le (hardGateBundle_implies_noise_to_composition_hyps hgate) henv
    hprior hδT hβ hβHat s

/-! ## What the remaining clauses buy — elsewhere, not in the composition bound -/

/-- **C4 buys a slope (inverse-temperature) precision certificate, not a composition bound.**
Under the gate and a *uniform* R1 noise bound `|ŷₖ − yₖ| ≤ eps` (the `eps = 1/min SNR` the gate
plugs into C4 — again an assumption about the unknown truth), the OLS slope error is within the
protocol target `tauBeta`. Thin re-export of `slopeBudget_certificate_sound`; uses only C1 and
C4 of the bundle. This is a parallel route to temperature precision — `noise_to_composition`
carries the per-line noise directly and never consumes `tauBeta`. -/
theorem hardGateBundle_slope_error_le [Nonempty ιT]
    {kB Tmin Tmax That eps tauBeta C dE ne neMin : ℝ} {ET yT yHatT tau : ιT → ℝ}
    {g E A : κ → ι → ℝ} {u : κ → ι}
    (hgate : hardGateBundle kB Tmin Tmax That eps tauBeta C dE ne neMin ET tau g E A u)
    (htau : 0 < tauBeta) (hδ : ∀ k, |yHatT k - yT k| ≤ eps) :
    |olsSlope ET yHatT - olsSlope ET yT| ≤ tauBeta := by
  obtain ⟨h1, -, h4, -⟩ := hgate
  exact slopeBudget_certificate_sound htau h1 hδ h4

/-- **C7 buys LTE admissibility of the reported state, not a composition bound.** Under the gate
(C7 at the reported `T̂`, the box giving `0 < T̂`, the floor giving `0 ≤ nₑ`) and the DB / protocol
positivity `0 < C`, `0 ≤ ΔE`, `0 ≤ neMin`, the DB resonance gap is within the thermalization limit
at the reported `(T̂, nₑ)`. Thin re-export of `mcWhirter_certificate_sound`. This is a REDUCED
statement about the *model's* collisional-LTE premise (R3: internal consistency at one diagnostic,
not physical LTE); it is the only formal work C7 does, and it is disjoint from
`hardGateBundle_composition_error_le`. -/
theorem hardGateBundle_thermalizationLimit
    {kB Tmin Tmax That eps tauBeta C dE ne neMin : ℝ} {ET tau : ιT → ℝ}
    {g E A : κ → ι → ℝ} {u : κ → ι}
    (hgate : hardGateBundle kB Tmin Tmax That eps tauBeta C dE ne neMin ET tau g E A u)
    (hC : 0 < C) (hdE : 0 ≤ dE) (hneMin : 0 ≤ neMin) :
    dE ≤ thermalizationLimit C That ne := by
  obtain ⟨-, -, -, h7, -, ⟨hThat, -⟩, hne, ⟨-, hTmin⟩, -⟩ := hgate
  exact mcWhirter_certificate_sound hC (lt_of_lt_of_le hTmin hThat) hdE (hneMin.trans hne) h7

/-! ### Non-vacuity witnesses

**Fixture anchor.** The `oracle/fixtures.json` certificate-scenario inputs anchored in
`OracleAnchors.lean` — C1/C3 `E = (0,1)`, C4 `(ε, τ_β, SS_E, n) = (1, 2, 1/2, 2)`, C7
`(C, T, ΔE, nₑ) = (1, 1, 1, 2)`, C12 `τ = 1` — together with the toy box `[1/2, 2] ∋ T̂ = 1`,
floor `neMin = 1`, `kB = 1`, and one species / one line with `g = A = 1`, `E = 0`, satisfy the
whole unconditional bundle: the Python `all_passed` on the hard subset and the Lean predicate
agree on the fixtures. -/
example : hardGateBundle (ι := Fin 1) (κ := Fin 1) (kB := 1) (Tmin := 1 / 2) (Tmax := 2)
    (That := 1) (eps := 1) (tauBeta := 2) (C := 1) (dE := 1) (ne := 2) (neMin := 1)
    ![0, 1] (fun _ => 1) (fun _ _ => 1) (fun _ _ => 0) (fun _ _ => 1) (fun _ => 0) :=
  hardGateBundle_of_certificates_report
    (by norm_num [energySpreadCert, mean, Fin.sum_univ_two])
    (by norm_num [conditioningCert, mean, Fin.sum_univ_two])
    (by norm_num [slopeBudgetCert, mean, Fin.sum_univ_two])
    (by norm_num [mcWhirterCert, Real.sqrt_one])
    (fun _ => by norm_num [knownTauCert])
    ⟨by norm_num, by norm_num⟩ (by norm_num) ⟨by norm_num, by norm_num⟩
    (fun _ _ => one_pos) (fun _ _ => le_rfl) (fun _ => one_pos)

/-! **Payoff instantiation.** The `NoiseToComposition` witness — Boltzmann plot `ET = (0, 1)`,
`yT = (0, 1)`, `ŷT = (0, 3/2)`, so the slopes fix a genuine `T = 1 ≠ T̂ = 2/3`, with per-line
budgets `ε = (0, 1/2)` — extended to TWO species `N = (1, 3)` (so the composition LHS is a genuine
fraction difference, not the single-species `0`), the fixture certificate inputs, C7 and the box
at the *reported* `T̂ = 2/3`. All hypotheses of `hardGateBundle_composition_error_le` are jointly
satisfiable and the headline inequality is stated concretely. With `E = 0` the temperature
channel is inert (the recovered densities are exact and `Φ = 0`), so the inequality is `0 ≤ 0`
in value — this witness certifies joint satisfiability of every hypothesis, not tightness. -/

private def evET : Fin 2 → ℝ := ![0, 1]
private def evYt : Fin 2 → ℝ := ![0, 1]
private noncomputable def evYhat : Fin 2 → ℝ := ![0, 3 / 2]
private noncomputable def evEps : Fin 2 → ℝ := ![0, 1 / 2]
private def evTau : Fin 2 → ℝ := fun _ => 1
private def evN : Fin 2 → ℝ := ![1, 3]
private def evg : Fin 2 → Fin 1 → ℝ := fun _ _ => 1
private def evE : Fin 2 → Fin 1 → ℝ := fun _ _ => 0
private def evA : Fin 2 → Fin 1 → ℝ := fun _ _ => 1
private def evu : Fin 2 → Fin 1 := fun _ => 0
private def evk0 : Fin 2 → Fin 1 := fun _ => 0

example :
    |composition (recoveredDensityAtT 1 1 (2 / 3) 1 evg evE evA evu evN) 0 - composition evN 0|
      ≤ compositionErrorBound evN
          (totalDensity (recoveredDensityAtT 1 1 (2 / 3) 1 evg evE evA evu evN)) (3 * 0) 0 :=
  hardGateBundle_composition_error_le (kB := 1) (Tmin := 1 / 2) (Tmax := 2) (T := 1)
    (That := 2 / 3) (Fcal := 1) (Φ := 0) (Nmax := 3) (eps := 1) (tauBeta := 2) (C := 1)
    (dE := 1) (ne := 2) (neMin := 1) (ET := evET) (yT := evYt) (yHatT := evYhat)
    (epsT := evEps) (tau := evTau) (N := evN) (g := evg) (E := evE) (A := evA) (u := evu)
    (k0 := evk0)
    (hardGateBundle_of_certificates_report
      (by norm_num [energySpreadCert, evET, mean, Fin.sum_univ_two])
      (by norm_num [conditioningCert, evET, mean, Fin.sum_univ_two])
      (by norm_num [slopeBudgetCert, evET, mean, Fin.sum_univ_two])
      (by
        unfold mcWhirterCert
        have h : Real.sqrt (2 / 3) ≤ 1 := by
          calc Real.sqrt (2 / 3) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt (by norm_num)
            _ = 1 := Real.sqrt_one
        nlinarith [h])
      (fun _ => by norm_num [knownTauCert, evTau])
      ⟨by norm_num, by norm_num⟩ (by norm_num) ⟨by norm_num, by norm_num⟩
      (fun _ _ => by norm_num [evg]) (fun _ _ => by norm_num [evE]) (fun _ => by norm_num [evA]))
    ⟨le_rfl,
     fun _ => by simp [evE, Real.exp_zero],
     fun _ => by simp [tempResponseErrorBoundOfGap, evE, evg, Real.exp_zero]⟩
    ⟨⟨by norm_num, by norm_num⟩, by norm_num,
     fun s => by fin_cases s <;> norm_num [evN],
     fun s => by fin_cases s <;> norm_num [evN]⟩
    (by intro k; fin_cases k <;> norm_num [evYt, evYhat, evEps])
    (by norm_num [olsSlope, evET, evYt, mean, Fin.sum_univ_two])
    (by norm_num [olsSlope, evET, evYhat, mean, Fin.sum_univ_two])
    0

end CflibsFormal
