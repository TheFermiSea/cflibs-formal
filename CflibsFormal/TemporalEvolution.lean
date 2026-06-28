/-
Copyright (c) 2026 Brian Squires. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Squires
-/
import Mathlib
import CflibsFormal.Boltzmann
import CflibsFormal.Closure
import CflibsFormal.ForwardMap
import CflibsFormal.Classic
import CflibsFormal.Saha
import CflibsFormal.StarkBroadening
import CflibsFormal.PartialLTE

/-!
# CF-LIBS formalization — time-resolved (gate-delayed) recovery

Every other CF-LIBS module fixes a *single* plasma state. A real gated LIBS
measurement instead samples the plasma at a sequence of gate delays `t`, and the
state evolves: the temperature `T(t)`, the electron density `n_e(t)`, and the
overall ablation dilution `ρ(t)` (the shared scalar relating the true element
densities `N0` to the sampled densities) all drift between gates. This module
formalizes that the calibration-free recovery is **sound at each individual
gate**, and that the recovered composition therefore tracks the (stoichiometric)
true composition `composition N0` at every gate.

## What is genuinely non-trivial here (honest framing)

The hypothesis `hDilute : nI + nII = ρ(t)·N0` is the **stoichiometric (non-
fractionating) ablation assumption**: it *already forces* the true element
composition to equal `composition N0` at every gate (the dilution `ρ(t)` is a
single scalar shared across elements, so it cancels in the closure ratio). The
cross-gate "invariance" theorems (`temporal_composition_gate_independent`,
`temporal_saha_composition_gate_independent`) are therefore **thin corollaries**
of this assumption, NOT an emergent discovery — they are openly flagged as such.

The substantive content is the **per-gate soundness** of the recovery:

* `gateSahaTotalDensity_eq` — the load-bearing result. Observing one *neutral*
  line and completing to the total element density via the two-stage Saha sum
  `nI·(1 + S/n_e)` returns exactly `ρ(t)·N0` at the gate, with the electron
  density `n_e(t)` **cancelling** through the Saha relation `nII·n_e = nI·S`.
* `temporal_composition_invariant` / `temporal_saha_composition_invariant` — the
  recovered composition equals `composition N0`, with the dilution `ρ(t)`
  cancelling in the closure (`composition_smul_invariant`).
* `temporal_temperature_insitu` — the in-situ Boltzmann-slope temperature at the
  gate state `(T(t), ρ(t)·N0)`; a specialization of `temperature_from_two_lines`
  that licenses feeding the gate temperature `T(t)` to the estimator. It is a
  SEPARATE leg from the composition soundness (same convention as
  `Classic.classic_temperature_correct` vs `Classic.classic_sound`); there is no
  formal in-Lean fusion of the two.

## Relation to the classic calibration-free theorem (no over-claim)

This is a **complementary / orthogonal temporal analogue** of
`Classic.classic_calibration_free`, **neither stronger than nor a generalization
of it**. The two concern different symmetries: `classic_calibration_free` is
invariance under instrumental `Fcal`-rescaling and holds for ALL data with no
positivity; this development concerns invariance under physical-state evolution
`(T(t), n_e(t), ρ(t))` and needs forward-generation + Saha completion +
stoichiometric dilution. Setting `t₁ = t₂` collapses the cross-gate theorems to
`rfl`, not to `Fcal`-invariance. Neither implies the other.

## Modeling boundary (honest scope)

The algebraic cancellations hold everywhere; they are *physically meaningful*
only on the LTE window `lteWindow ΔE T ne`, where the McWhirter criterion (a
**necessary, not sufficient** condition; Cristoforetti 2010) is met — framed
here as an applicability bound (`mem_lteWindow_thermalized`,
`mcwhirter_requirement_antitone`), NOT as where the theorems hold. Reduced
scope: single neutral + first-ion two-stage Saha closure per element (higher
stages out); only `(T(t), n_e(t), ρ(t))` carry time-dependence (self-absorption,
continuum, spatial-profile evolution out); the in-situ soundness of `n_e(t)`
itself is cited from `Saha` / `StarkBroadening`, not re-proven. Under
fractionation `ρ` becomes element-dependent and the true composition genuinely
drifts — the honest validity boundary (Tognoni 2010). A compiling non-vacuity
`example` witnesses that the Saha + dilution hypotheses are jointly satisfiable
with genuinely differing `T` and dilution across two gates, so the implications
are substantive, not vacuous.

## Literature

* A. Ciucci, M. Corsi, V. Palleschi, S. Rastelli, A. Salvetti, E. Tognoni, "New
  procedure for quantitative elemental analysis by laser-induced plasma
  spectroscopy," *Applied Spectroscopy* **53** (1999) 960–964 — the CF-LIBS
  closure / calibration-free composition recovery reused here per gate.
* E. Tognoni, G. Cristoforetti, S. Legnaioli, V. Palleschi, "Calibration-free
  laser-induced breakdown spectroscopy: State of the art," *Spectrochimica Acta
  Part B* **65** (2010) 1–14 — stoichiometric (non-fractionating) ablation and
  the time-resolved / gated measurement context.
* G. Cristoforetti, A. De Giacomo, M. Dell'Aglio, S. Legnaioli, E. Tognoni,
  V. Palleschi, N. Omenetto, "Local Thermodynamic Equilibrium in Laser-Induced
  Breakdown Spectroscopy: Beyond the McWhirter criterion," *Spectrochimica Acta
  Part B* **65** (2010) 86–95 — McWhirter as necessary-not-sufficient; the LTE
  window bounding physical applicability.
* R. W. P. McWhirter, "Spectral Intensities," in R. H. Huddlestone,
  S. L. Leonard (eds.), *Plasma Diagnostic Techniques*, Academic Press (1965),
  ch. 5 — the bound `n_e ≥ 1.6×10¹²·√T·(ΔE)³` used in the applicability window.
-/

namespace CflibsFormal

open Finset Real
open scoped BigOperators

variable {σ : Type*} [Fintype σ]
variable {ι : Type*} [Fintype ι]
variable {κ : Type*} [Fintype κ]

/-- **Gate spectrum.** The optically-thin line intensity observed at gate delay
`t` for element `s` on its chosen upper level `u s`, generated by the forward
model at the gate state `(T t, ρ t · N0 s)`: the temperature is the gate
temperature `T t` and the emitting density is the diluted true density
`ρ t · N0 s` (stoichiometric ablation scales all elements by the shared `ρ t`). -/
noncomputable def gateSpectrum (kB Fcal : ℝ) (T ρ : ℝ → ℝ) (N0 : σ → ℝ)
    (g E A : σ → ι → ℝ) (u : σ → ι) (t : ℝ) (s : σ) : ℝ :=
  lineIntensity kB (T t) (ρ t * N0 s) Fcal (g s) (E s) (A s) (u s)

/-- **Gate composition estimator.** Runs the classic calibration-free composition
estimator `Classic.classicComposition` on the gate-`t` spectra, evaluated at the
gate temperature `T t`. A pure function of the gate data; `T t` is licensed in
situ by `temporal_temperature_insitu`. -/
noncomputable def gateComposition (kB Fcal : ℝ) (T ρ : ℝ → ℝ) (N0 : σ → ℝ)
    (g E A : σ → ι → ℝ) (u : σ → ι) (t : ℝ) (s : σ) : ℝ :=
  Classic.classicComposition kB (T t) Fcal g E A u
    (fun r => gateSpectrum kB Fcal T ρ N0 g E A u t r) s

/-- **Gate Saha factor.** The Saha right-hand side `S(T t)` for element `s` at the
gate state, between its neutral stage (levels `ι`, data `gI s, EI s`) and its
first-ion stage (levels `κ`, data `gII s, EII s`), with ionization energy
`chi s`. Reused verbatim from `Saha.sahaFactor`. -/
noncomputable def gateSahaFactor (kB me h : ℝ) (T : ℝ → ℝ) (chi : σ → ℝ)
    (gI EI : σ → ι → ℝ) (gII EII : σ → κ → ℝ) (t : ℝ) (s : σ) : ℝ :=
  sahaFactor kB (T t) me h (chi s) (gI s) (EI s) (gII s) (EII s)

/-- **Gate neutral spectrum.** The observed *neutral*-stage line intensity at gate
`t` for element `s`, generated by the forward model at `(T t, nI s t)` where
`nI s t` is the gate neutral number density. The single observed line from which
the Saha completion reconstructs the total element density. -/
noncomputable def gateNeutralSpectrum (kB Fcal : ℝ) (T : ℝ → ℝ) (nI : σ → ℝ → ℝ)
    (gI EI AI : σ → ι → ℝ) (uI : σ → ι) (t : ℝ) (s : σ) : ℝ :=
  lineIntensity kB (T t) (nI s t) Fcal (gI s) (EI s) (AI s) (uI s)

/-- **Saha-completed total element density at the gate.** From the *one* observed
neutral line, `Classic.classicDensity` inverts back the neutral density `nI s t`,
then the two-stage Saha sum `nI · (1 + S/n_e)` adds the first-ion population to
give the total element density. This is where the electron density `n_e t`
enters; `gateSahaTotalDensity_eq` shows it cancels via the Saha relation. -/
noncomputable def gateSahaTotalDensity (kB me h Fcal : ℝ) (T ne : ℝ → ℝ)
    (chi : σ → ℝ) (nI : σ → ℝ → ℝ) (gI EI AI : σ → ι → ℝ) (uI : σ → ι)
    (gII EII : σ → κ → ℝ) (t : ℝ) (s : σ) : ℝ :=
  Classic.classicDensity kB (T t) Fcal (gI s) (EI s) (AI s) (uI s)
      (gateNeutralSpectrum kB Fcal T nI gI EI AI uI t s)
    * (1 + gateSahaFactor kB me h T chi gI EI gII EII t s / ne t)

/-- **Gate Saha composition estimator.** Closure (`composition`) applied to the
per-element Saha-completed total densities at gate `t`. The full
neutral-observe + Saha-complete + normalize recovery at one gate. -/
noncomputable def gateSahaComposition (kB me h Fcal : ℝ) (T ne : ℝ → ℝ)
    (chi : σ → ℝ) (nI : σ → ℝ → ℝ) (gI EI AI : σ → ι → ℝ) (uI : σ → ι)
    (gII EII : σ → κ → ℝ) (t : ℝ) (s : σ) : ℝ :=
  composition
    (fun r => gateSahaTotalDensity kB me h Fcal T ne chi nI gI EI AI uI gII EII t r) s

/-- **LTE window.** The set of gate delays `t` at which the gate state
`(T t, n_e t)` satisfies the McWhirter LTE-admissibility bound for energy gap
`ΔE` (`StarkBroadening.lteValid`). The cancellations below hold algebraically for
all `t`; they are *physically meaningful* on this window (McWhirter being
necessary, not sufficient — Cristoforetti 2010). -/
def lteWindow (ΔE : ℝ) (T ne : ℝ → ℝ) : Set ℝ :=
  {t | lteValid (T t) ΔE (ne t)}

omit [Fintype σ] in
/-- **In-situ gate temperature (Boltzmann slope).** The slope of the intensity
Boltzmann plot between two distinct-energy lines `i, j` of element `s`, built from
the gate-`t` spectra at the gate state `(T t, ρ t · N0 s)`, recovers `1/(k_B·T t)`
exactly. A direct specialization of `ForwardMap.temperature_from_two_lines` at the
gate state (density `N := ρ t · N0 s`); this is the SEPARATE temperature leg that
licenses feeding `T t` to the composition estimator, with no formal in-Lean
fusion to the composition soundness below. -/
theorem temporal_temperature_insitu [Nonempty ι] {kB Fcal : ℝ} {T ρ : ℝ → ℝ}
    {N0 : σ → ℝ} {g E A : σ → ι → ℝ}
    (hg : ∀ s k, 0 < g s k) (hN0 : ∀ s, 0 < N0 s) (hFcal : 0 < Fcal)
    (hA : ∀ s k, 0 < A s k) (t : ℝ) (hρ : 0 < ρ t) (s : σ) (i j : ι)
    (hE : E s i ≠ E s j) :
    (Real.log (lineIntensity kB (T t) (ρ t * N0 s) Fcal (g s) (E s) (A s) j
          / (g s j * A s j))
        - Real.log (lineIntensity kB (T t) (ρ t * N0 s) Fcal (g s) (E s) (A s) i
          / (g s i * A s i))) / (E s i - E s j)
      = 1 / (kB * T t) :=
  temperature_from_two_lines (hg s) (mul_pos hρ (hN0 s)) hFcal (hA s) i j hE

/-- **Per-gate composition soundness (dilution cancels).** At any single gate `t`
with positive dilution `ρ t`, the classic gate estimator returns exactly the true
composition `composition N0`. The shared scalar dilution `ρ t` cancels in the
closure (`composition_smul_invariant`), so the recovered composition is the
(stoichiometrically time-invariant) true composition. This is the genuine content;
the cross-gate corollary below is thin. -/
theorem temporal_composition_invariant [Nonempty ι] [Nonempty σ] {kB Fcal : ℝ}
    {T ρ : ℝ → ℝ} {N0 : σ → ℝ} {g E A : σ → ι → ℝ} {u : σ → ι}
    (hg : ∀ s k, 0 < g s k) (hFcal : 0 < Fcal) (hA : ∀ s, 0 < A s (u s))
    (hN0 : ∀ s, 0 < N0 s) (t : ℝ) (hρ : 0 < ρ t) (s : σ) :
    gateComposition kB Fcal T ρ N0 g E A u t s = composition N0 s := by
  have htot : 0 < totalDensity (fun r => ρ t * N0 r) :=
    totalDensity_pos (fun r => mul_pos hρ (hN0 r))
  have h1 : gateComposition kB Fcal T ρ N0 g E A u t s
      = composition (fun r => ρ t * N0 r) s :=
    Classic.classic_sound (N := fun r => ρ t * N0 r) hg hFcal hA htot s
  rw [h1]
  exact composition_smul_invariant hρ.ne' s

/-- **Cross-gate composition invariance (thin corollary).** The classic gate
estimator returns the same composition at any two gates `t₁, t₂` (each with
positive dilution). This is *not* an emergent discovery: it is `rw` of
`temporal_composition_invariant` at each gate, both equalling `composition N0`.
Distinctness `t₁ ≠ t₂` is NOT assumed (the non-vacuity `example` carries the
genuine-difference burden); setting `t₁ = t₂` makes it `rfl`. -/
theorem temporal_composition_gate_independent [Nonempty ι] [Nonempty σ]
    {kB Fcal : ℝ} {T ρ : ℝ → ℝ} {N0 : σ → ℝ} {g E A : σ → ι → ℝ} {u : σ → ι}
    (hg : ∀ s k, 0 < g s k) (hFcal : 0 < Fcal) (hA : ∀ s, 0 < A s (u s))
    (hN0 : ∀ s, 0 < N0 s) (t₁ t₂ : ℝ) (hρ₁ : 0 < ρ t₁) (hρ₂ : 0 < ρ t₂) (s : σ) :
    gateComposition kB Fcal T ρ N0 g E A u t₁ s
      = gateComposition kB Fcal T ρ N0 g E A u t₂ s := by
  rw [temporal_composition_invariant hg hFcal hA hN0 t₁ hρ₁ s,
    temporal_composition_invariant hg hFcal hA hN0 t₂ hρ₂ s]

omit [Fintype σ] in
/-- **The Saha completion is sound at the gate — `n_e` cancels (load-bearing).**
From the single observed neutral line at gate `t`, inverting to `nI s t` and
completing with the two-stage Saha sum `nI·(1 + S/n_e)` returns exactly the
diluted true density `ρ t · N0 s`. The electron density `n_e t` **cancels** via
the gate Saha relation `hSaha : nII·n_e = nI·S` (so `nI·(S/n_e) = nII`); the
dilution then closes through `hDilute`. Both `hSaha` and `hne : n_e t ≠ 0` are
load-bearing (drop either and the cancellation fails). `hDilute` is the
stoichiometric-ablation assumption. -/
theorem gateSahaTotalDensity_eq [Nonempty ι] {kB me h Fcal : ℝ} {T ne ρ : ℝ → ℝ}
    {N0 chi : σ → ℝ} {nI nII : σ → ℝ → ℝ} {gI EI AI : σ → ι → ℝ} {uI : σ → ι}
    {gII EII : σ → κ → ℝ}
    (hgI : ∀ s k, 0 < gI s k) (hFcal : 0 < Fcal) (hAI : ∀ s, 0 < AI s (uI s))
    (t : ℝ) (hne : ne t ≠ 0) (s : σ)
    (hSaha : nII s t * ne t = nI s t * gateSahaFactor kB me h T chi gI EI gII EII t s)
    (hDilute : nI s t + nII s t = ρ t * N0 s) :
    gateSahaTotalDensity kB me h Fcal T ne chi nI gI EI AI uI gII EII t s
      = ρ t * N0 s := by
  unfold gateSahaTotalDensity gateNeutralSpectrum
  rw [Classic.classicDensity_recovers (hgI s) hFcal (uI s) (hAI s)]
  have hmul : nI s t * (gateSahaFactor kB me h T chi gI EI gII EII t s / ne t)
      = nII s t := by
    rw [← mul_div_assoc, ← hSaha, mul_div_assoc, div_self hne, mul_one]
  rw [mul_add, mul_one, hmul, hDilute]

/-- **Per-gate Saha composition soundness (`n_e` and `ρ` both cancel).** The full
neutral-observe + Saha-complete + normalize recovery at gate `t` returns exactly
`composition N0`: each element's Saha-completed density equals `ρ t · N0`
(`gateSahaTotalDensity_eq`, with `n_e t` cancelling), and the shared dilution
`ρ t` then cancels in the closure (`composition_smul_invariant`). This and
`gateSahaTotalDensity_eq` are the substantive results of the module. -/
theorem temporal_saha_composition_invariant [Nonempty ι] [Nonempty σ]
    {kB me h Fcal : ℝ} {T ne ρ : ℝ → ℝ} {N0 chi : σ → ℝ} {nI nII : σ → ℝ → ℝ}
    {gI EI AI : σ → ι → ℝ} {uI : σ → ι} {gII EII : σ → κ → ℝ}
    (hgI : ∀ s k, 0 < gI s k) (hFcal : 0 < Fcal) (hAI : ∀ s, 0 < AI s (uI s))
    (t : ℝ) (hne : ne t ≠ 0) (hρ : ρ t ≠ 0)
    (hSaha : ∀ s, nII s t * ne t
      = nI s t * gateSahaFactor kB me h T chi gI EI gII EII t s)
    (hDilute : ∀ s, nI s t + nII s t = ρ t * N0 s) (s : σ) :
    gateSahaComposition kB me h Fcal T ne chi nI gI EI AI uI gII EII t s
      = composition N0 s := by
  have hrec :
      (fun r => gateSahaTotalDensity kB me h Fcal T ne chi nI gI EI AI uI gII EII t r)
        = (fun r => ρ t * N0 r) :=
    funext (fun r =>
      gateSahaTotalDensity_eq hgI hFcal hAI t hne r (hSaha r) (hDilute r))
  unfold gateSahaComposition
  rw [hrec]
  exact composition_smul_invariant hρ s

/-- **Cross-gate Saha composition invariance (HEADLINE — thin corollary).** The
full Saha recovery returns the same composition at any two gates `t₁, t₂`. This is
the honest thin corollary of `temporal_saha_composition_invariant`: both gates
recover `composition N0` (the true composition is gate-invariant *because*
`hDilute` is stoichiometric, not because the recovery discovers it). The
substantive per-gate soundness — `n_e(t)` cancelling via Saha, `ρ(t)` cancelling
in closure — lives in `gateSahaTotalDensity_eq` and the invariant theorem.
Distinctness `t₁ ≠ t₂` is NOT a hypothesis. -/
theorem temporal_saha_composition_gate_independent [Nonempty ι] [Nonempty σ]
    {kB me h Fcal : ℝ} {T ne ρ : ℝ → ℝ} {N0 chi : σ → ℝ} {nI nII : σ → ℝ → ℝ}
    {gI EI AI : σ → ι → ℝ} {uI : σ → ι} {gII EII : σ → κ → ℝ}
    (hgI : ∀ s k, 0 < gI s k) (hFcal : 0 < Fcal) (hAI : ∀ s, 0 < AI s (uI s))
    (t₁ t₂ : ℝ) (hne₁ : ne t₁ ≠ 0) (hne₂ : ne t₂ ≠ 0) (hρ₁ : ρ t₁ ≠ 0)
    (hρ₂ : ρ t₂ ≠ 0)
    (hSaha₁ : ∀ s, nII s t₁ * ne t₁
      = nI s t₁ * gateSahaFactor kB me h T chi gI EI gII EII t₁ s)
    (hSaha₂ : ∀ s, nII s t₂ * ne t₂
      = nI s t₂ * gateSahaFactor kB me h T chi gI EI gII EII t₂ s)
    (hDilute₁ : ∀ s, nI s t₁ + nII s t₁ = ρ t₁ * N0 s)
    (hDilute₂ : ∀ s, nI s t₂ + nII s t₂ = ρ t₂ * N0 s) (s : σ) :
    gateSahaComposition kB me h Fcal T ne chi nI gI EI AI uI gII EII t₁ s
      = gateSahaComposition kB me h Fcal T ne chi nI gI EI AI uI gII EII t₂ s := by
  rw [temporal_saha_composition_invariant hgI hFcal hAI t₁ hne₁ hρ₁ hSaha₁ hDilute₁ s,
    temporal_saha_composition_invariant hgI hFcal hAI t₂ hne₂ hρ₂ hSaha₂ hDilute₂ s]

/-- **Applicability: gate in the LTE window ⇒ thermalized.** If a gate `t` lies in
`lteWindow ΔE T ne` (the gate state clears the McWhirter bound), the transition of
gap `ΔE` is collisionally thermalized at the McWhirter prefactor `1.6·10¹²`
(`PartialLTE.thermalized`). This bounds where the cancellations are *physically
meaningful* — McWhirter being necessary, not sufficient. -/
theorem mem_lteWindow_thermalized {ΔE : ℝ} {T ne : ℝ → ℝ} {t : ℝ}
    (hT : 0 < T t) (hΔE : 0 ≤ ΔE) (hne : 0 ≤ ne t) (ht : t ∈ lteWindow ΔE T ne) :
    thermalized 1.6e12 (T t) (ne t) ΔE := by
  rw [lteWindow, Set.mem_setOf_eq] at ht
  exact (lteValid_iff_thermalized hT hΔE hne).mp ht

/-- **McWhirter requirement falls as the plasma cools.** Between two gates with
`T t₂ ≤ T t₁` (gate `t₂` cooler), the LTE electron-density floor at the cooler
gate is no larger: `mcWhirterBound (T t₂) ΔE ≤ mcWhirterBound (T t₁) ΔE`. Pure
reuse of `StarkBroadening.mcWhirterBound_mono_T`, documenting that as the gated
plasma cools its LTE demand on `n_e` relaxes. -/
theorem mcwhirter_requirement_antitone {ΔE : ℝ} {T : ℝ → ℝ} {t₁ t₂ : ℝ}
    (hΔE : 0 ≤ ΔE) (hT : T t₂ ≤ T t₁) :
    mcWhirterBound (T t₂) ΔE ≤ mcWhirterBound (T t₁) ΔE :=
  mcWhirterBound_mono_T hΔE hT

/-! ### Non-vacuity witness

Concrete data with `σ = Fin 2` (TWO elements), `ι = Fin 2`, `κ = Fin 1`, scalar
constants `kB = me = h = Fcal = 1`, GENUINELY DIFFERING gate states
`T 0 = 1 ≠ 2 = T 1` and `ρ 0 = 1 ≠ 3 = ρ 1`, DISTINCT initial densities
`N0 = ![1, 3]`, and the neutral/ion split chosen as
`nI = ρ·N0/(1+S)`, `nII = ρ·N0·S/(1+S)` (`S = gateSahaFactor`). The `example`
below discharges the Saha and dilution hypotheses at both gates and evaluates the
recovered composition of element `0` to the genuine non-trivial fraction
`1/(1+3) = 1/4` at each, certifying that the headline theorem's hypotheses are
jointly satisfiable with differing `T` and dilution AND that the
stoichiometric-dilution factor `ρ` cancels in a real composition RATIO across two
elements (gate-independent despite `ρ 0 = 1 ≠ 3 = ρ 1`) — so the implication is
substantive, not vacuous. -/

private noncomputable def tT : ℝ → ℝ := fun t => 1 + t
private noncomputable def tρ : ℝ → ℝ := fun t => 1 + 2 * t
private noncomputable def tne : ℝ → ℝ := fun _ => 1
private noncomputable def tN0 : Fin 2 → ℝ := ![1, 3]
private noncomputable def tchi : Fin 2 → ℝ := fun _ => 1
private noncomputable def tgI : Fin 2 → Fin 2 → ℝ := fun _ _ => 1
private noncomputable def tEI : Fin 2 → Fin 2 → ℝ := fun _ _ => 0
private noncomputable def tAI : Fin 2 → Fin 2 → ℝ := fun _ _ => 1
private noncomputable def tuI : Fin 2 → Fin 2 := fun _ => 0
private noncomputable def tgII : Fin 2 → Fin 1 → ℝ := fun _ _ => 1
private noncomputable def tEII : Fin 2 → Fin 1 → ℝ := fun _ _ => 0

private noncomputable def tnI : Fin 2 → ℝ → ℝ :=
  fun s t => tρ t * tN0 s / (1 + gateSahaFactor 1 1 1 tT tchi tgI tEI tgII tEII t s)

private noncomputable def tnII : Fin 2 → ℝ → ℝ :=
  fun s t => tρ t * tN0 s * gateSahaFactor 1 1 1 tT tchi tgI tEI tgII tEII t s
    / (1 + gateSahaFactor 1 1 1 tT tchi tgI tEI tgII tEII t s)

/-- Non-vacuity / non-tautology witness for the time-resolved Saha recovery: with
TWO elements (`σ = Fin 2`) and DISTINCT initial densities `N0 = ![1, 3]`, the Saha
(`hSaha`) and stoichiometric-dilution (`hDilute`) hypotheses are jointly
satisfiable at two gates with genuinely different temperature (`T 0 ≠ T 1`) and
dilution (`ρ 0 ≠ ρ 1`), and the recovered composition of element `0` is
gate-independent and equals the genuine non-trivial ratio `1/(1+3) = 1/4` at each
gate — non-trivially witnessing that the dilution factor `ρ` cancels in a real
composition ratio across elements. -/
example :
    tT 0 ≠ tT 1
      ∧ tρ 0 ≠ tρ 1
      ∧ (∀ s : Fin 2, tnII s 0 * tne 0
          = tnI s 0 * gateSahaFactor 1 1 1 tT tchi tgI tEI tgII tEII 0 s)
      ∧ (∀ s : Fin 2, tnI s 0 + tnII s 0 = tρ 0 * tN0 s)
      ∧ (∀ s : Fin 2, tnII s 1 * tne 1
          = tnI s 1 * gateSahaFactor 1 1 1 tT tchi tgI tEI tgII tEII 1 s)
      ∧ (∀ s : Fin 2, tnI s 1 + tnII s 1 = tρ 1 * tN0 s)
      ∧ gateSahaComposition 1 1 1 1 tT tne tchi tnI tgI tEI tAI tuI tgII tEII 0 0
          = gateSahaComposition 1 1 1 1 tT tne tchi tnI tgI tEI tAI tuI tgII tEII 1 0
      ∧ gateSahaComposition 1 1 1 1 tT tne tchi tnI tgI tEI tAI tuI tgII tEII 0 0 = 1/4 := by
  have hgI : ∀ (s : Fin 2) (k : Fin 2), 0 < tgI s k := fun s k => by norm_num [tgI]
  have hFcal : (0 : ℝ) < 1 := one_pos
  have hAI : ∀ s : Fin 2, 0 < tAI s (tuI s) := fun s => by norm_num [tAI]
  have hG : ∀ (s : Fin 2) (t : ℝ), 0 < tT t →
      0 < gateSahaFactor 1 1 1 tT tchi tgI tEI tgII tEII t s := by
    intro s t ht
    unfold gateSahaFactor
    exact sahaFactor_pos one_pos ht one_pos one_pos
      (fun k => by norm_num [tgI]) (fun k => by norm_num [tgII])
  have hSaha : ∀ (t : ℝ) (s : Fin 2), tnII s t * tne t
      = tnI s t * gateSahaFactor 1 1 1 tT tchi tgI tEI tgII tEII t s := by
    intro t s
    simp only [tnI, tnII, tne]
    ring
  have hDilute : ∀ (t : ℝ), 0 < tT t → ∀ s : Fin 2,
      tnI s t + tnII s t = tρ t * tN0 s := by
    intro t ht s
    have hden : (1 : ℝ) + gateSahaFactor 1 1 1 tT tchi tgI tEI tgII tEII t s ≠ 0 :=
      ne_of_gt (by have := hG s t ht; linarith)
    simp only [tnI, tnII]
    field_simp
  have hT0 : (0 : ℝ) < tT 0 := by norm_num [tT]
  have hT1 : (0 : ℝ) < tT 1 := by norm_num [tT]
  have hcomp : composition tN0 (0 : Fin 2) = 1/4 := by
    simp only [composition, totalDensity, tN0, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    norm_num
  have key0 : gateSahaComposition 1 1 1 1 tT tne tchi tnI tgI tEI tAI tuI tgII tEII 0 0
      = composition tN0 0 :=
    temporal_saha_composition_invariant hgI hFcal hAI 0 (by norm_num [tne])
      (by norm_num [tρ]) (hSaha 0) (hDilute 0 hT0) 0
  have key1 : gateSahaComposition 1 1 1 1 tT tne tchi tnI tgI tEI tAI tuI tgII tEII 1 0
      = composition tN0 0 :=
    temporal_saha_composition_invariant hgI hFcal hAI 1 (by norm_num [tne])
      (by norm_num [tρ]) (hSaha 1) (hDilute 1 hT1) 0
  refine ⟨by norm_num [tT], by norm_num [tρ], hSaha 0, hDilute 0 hT0, hSaha 1,
    hDilute 1 hT1, ?_, ?_⟩
  · rw [key0, key1]
  · rw [key0]; exact hcomp

end CflibsFormal
