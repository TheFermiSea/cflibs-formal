/-
Copyright (c) 2026 Brian Squires. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Squires
-/
import Mathlib
import CflibsFormal.OLS
import CflibsFormal.ErrorBudget
import CflibsFormal.PartialLTE
import CflibsFormal.SahaEquilibrium
import CflibsFormal.SelfAbsorption
import CflibsFormal.CurveOfGrowth
import CflibsFormal.AtomicDataPerturbation

/-!
# CF-LIBS formalization — runtime certificates (the typed bridge)

This module is the **typed bridge** between the verified spec and a floating-point pipeline.
Each *certificate* is a `def …Cert (… : ℝ) : Prop` whose body is **pure arithmetic** over runtime
inputs (comparisons, `+ − · /`, `max`, `Real.sqrt`): the predicate a float checker can evaluate
once it has those inputs. Some inputs are unknown in the inverse problem (the absolute element
totals `Ntot` of C9/C10) or not formed by the companion pipeline (the opacity coefficients of
C13), and some are assumed rather than measured (C4's `ε`, C5's `B`, C6's `δ`, C14's `δ`).
Paired with each certificate is a **soundness theorem**
`…_certificate_sound : …Cert … → <guarantee>` that is a *thin re-export* of an existing
`CflibsFormal` theorem, named in each docstring by its fully qualified name. When the predicate
holds and the soundness theorem's remaining hypotheses hold, the guarantee holds **for the model
the wrapped theorem is stated over**. Those models carry their own scope; each soundness
theorem's published tag is in `docs/scope-published.tsv`.

Every certificate has a concrete witness that satisfies its predicate. Not every witness exercises
the guarantee at a nonzero error: the C4, C6 and C14 guarantee witnesses sit at zero-error
corners, where the conclusion reads `0 ≤ bound`. They show that the soundness theorem applies,
not that its bound is informative. Witnesses at a nonzero error are future work.

## What each certificate certifies, and what it does not

Every soundness theorem below is a correct re-export. What passing a predicate buys is narrower
than the certificate names suggest (deep audit 2026-09-24, ledger U-04):

* **C1** certifies that the pooled, single-intercept `[1 | E]` normal matrix is nonsingular. It
  passes for any two distinct energies. It says nothing about the accuracy of `T`, nor about a fit
  with one intercept per element, whose rank condition is a positive within-element spread.
* **C2** certifies the same for the pooled `[1 | E | s]` design, with the same two limits.
* **C3** has C1's predicate verbatim, and its conclusion holds for every design with positive
  spread, so it certifies nothing beyond C1.
* **C4** is conditional on a deterministic bound `|ŷₖ − yₖ| ≤ ε` on every line. An `ε` read off
  as `1/SNR` is a one-sigma noise scale, not such a bound.
* **C5** turns an exact identity into a budget; its slope-error bound `B` is assumed.
* **C6** takes one assumed absolute density error `δ` for all species, so its fraction bound is
  loose for minor species.
* **C7** checks the McWhirter condition, which is necessary for LTE but not sufficient. At the
  recovered `(T̂, n̂ₑ)` it checks internal consistency only.
* **C9** and **C10** certify forward Saha closure iterations at fixed `T` and known absolute
  element totals `Ntot`. The inverse problem does not know `Ntot`, and neither certificate says
  anything about the inverse `(T, nₑ)` loop or its damping.
* **C12** is `0 ≤ τ`. Its soundness theorem is the model's left-inverse identity, true for every
  `τ ≥ 0` including a wrong estimate, so C12 certifies nothing about the data (NON-INFORMATIVE).
* **C13** takes per-line opacity coefficients (not widths). Its guarantee holds for the flat
  kernel `1 − e^{−w n}` with a shared source term and a shared lower-level column, and the Prop
  encodes neither sharing condition.
* **C14** is `0 ≤ δ < 1`; all of its content sits in the assumed atomic-data bound (R2).
* **C8** and **C11** have no certificate here.

No conjunction of these certificates gives an informative composition-error bound at realistic
parameters. The one composed chain (`EvaluatorSoundness`, via `noise_to_composition`) gives
composition bounds of 26 to 1.4·10³ at 0.5–5 % noise on the full NIST Fe/Cr/Ni level lists, where
a fraction error is at most 1 (audit finding U-01). On that test's grid (`ε` of 0.5, 1, 2 and 5 %;
boxes [8000, 12000] and [9000, 11000] K) the Fe and Ni bounds are both below 1 only when the level
lists are truncated to `E ≤ 1 eV` and `ε ≤ 2 %`. With a 3 eV truncation only the Ni bound falls
below 1, in three of the eight cells, and the Fe bound never does (`NoiseToComposition`,
*Non-vacuity range*, from a re-run of the U-01 script).

## Honest scope

* A certificate is **SUFFICIENT** for its guarantee, and (except where the wrapped theorem is a
  biconditional, C1/C2/C7) **generally not necessary**. A `False` verdict names which proven
  precondition failed; it does not prove the guarantee false.
* **Only runtime-checkable arithmetic lives in a certificate.** Hypotheses that reference an
  *unknown truth* stay OUT of the `Cert` and remain explicit hypotheses of the soundness theorem
  (the dossier §5 refusals): the per-line error bound `ε` (C4) and per-species density error `δ`
  (C6) are distances to the true intensities/densities (R1); the atomic-data aliasing `δ` (C14) is
  unknowable in principle (R2, the A* mark — see the `-- REFUSAL` note there); the fixed-point
  data `r` (C10), the slope-error bound `B`, and all positivity of *true* quantities are epistemic
  inputs, never part of the checkable predicate. Keeping them out does not make a predicate
  informative: C12's predicate is satisfied by any nonnegative estimate.
* **C10 has no smallness condition, and it certifies a forward closure.** Unlike the scalar Saha
  leg (C9), the damped multi-element iteration converges at rate `1 − lam < 1` with *no*
  smallness/contraction side condition — the certificate is just positivity of the (physically
  always positive) Saha factors and total densities. It certifies the fixed-`T` forward
  charge-neutrality closure at known `Ntot`. It says nothing about the inverse `(T, nₑ)` loop or
  the pipeline's `0.5` damping of that loop.
* **Float ≠ ℝ near a threshold (R6).** All predicates are exact-ℝ; a float checker is IEEE-754, so
  near a boundary (`SS_E ≈ 0`, `δ ≈ 1`) the float verdict may disagree with the proven ℝ verdict.
  The companion checker carries an interval margin.

The reference Python mirror is `docs/integration/cflibs_certificates.py` (one function per
certificate, 1:1 with these defs).

## Literature

The wrapped theorems (and hence these certificates) inherit their physics citations: the
Boltzmann-plot rank / conditioning gates (C1–C3) from Tognoni et al. 2010 and Aguilera & Aragón
2007; the deterministic error budget (C4–C6) from Tognoni et al. 2010; the McWhirter LTE criterion
(C7) from R. W. P. McWhirter (1965) via G. Cristoforetti et al., *Spectrochim. Acta B* **65**
(2010) 86–95; the Saha–Eggert closure iterations (C9, C10) from H. R. Griem, *Principles of Plasma
Spectroscopy* (1997); the self-absorption and curve-of-growth models (C12, C13) from I. B.
Gornushkin et al. 1999 and Cristoforetti & Tognoni 2013; and the atomic-data aliasing floor (C14)
from Tognoni et al. 2010. This module adds **no new mathematics** — it only re-exports.
-/

namespace CflibsFormal

variable {ι : Type*} [Fintype ι]

/-! ## C1 — Energy-spread rank gate (T-identifiability)

Wraps `CflibsFormal.designNormalMatrix_det_ne_zero_iff` (module `OLS`). Predicate: positive
energy spread. Guarantee: the normal matrix of the single-intercept Boltzmann-plot design
`[1 | E]` is nonsingular, so the slope→T fit is well-posed.

Not certified: the accuracy of the fitted slope or of `T`; and the rank of a fit with one
intercept per element (a common-slope fit), whose condition is a positive *within-element*
spread. Lines pooled across elements can pass C1 while that fit is rank-deficient, e.g. two
elements each observed at a single energy (audit findings SPC-01, INV-04). -/

/-- **C1 certificate.** Positive energy spread `SS_E = ∑ₖ (Eₖ − Ē)² > 0` — the runtime rank gate
mirrored by the pipeline's `temperature_identifiable` guard. Any two lines at distinct energies
satisfy it. -/
def energySpreadCert (E : ι → ℝ) : Prop := 0 < ∑ k, (E k - mean E) ^ 2

/-- **C1 soundness: the single-intercept design is nonsingular** (thin re-export of
`CflibsFormal.designNormalMatrix_det_ne_zero_iff`). A positive energy spread certifies that the
single-intercept Boltzmann-plot normal matrix is nonsingular. -/
theorem energySpread_certificate_sound [Nonempty ι] (E : ι → ℝ)
    (hcert : energySpreadCert E) : (designNormalMatrix E).det ≠ 0 :=
  (designNormalMatrix_det_ne_zero_iff E).mpr hcert

-- Non-vacuity: two lines at distinct energies `E = (0, 1)` (`SS_E = 1/2 > 0`) certify a
-- nonsingular design (`det = 1 ≠ 0`).
example : (designNormalMatrix (ι := Fin 2) ![0, 1]).det ≠ 0 :=
  energySpread_certificate_sound ![0, 1]
    (by norm_num [energySpreadCert, mean, Fin.sum_univ_two])

/-! ## C2 — Joint Saha–Boltzmann rank gate

Wraps `CflibsFormal.jointDesign_det_pos_iff` (module `OLS`) via
`CflibsFormal.det_jointDesignNormalMatrix`. Predicate: `SS_E·SS_s − S_Es² > 0`. Guarantee: the
centered energies and ion-stage indicator are not proportional, so the joint (T, nₑ) fit with a
single intercept is identifiable.

Not certified: accuracy; and identifiability of a fit with one intercept per element. One element
seen only in stage I and another seen only in stage II can pass C2 while the per-element design
`[x | element dummies | s]` is rank-deficient (audit finding INV-04). -/

/-- **C2 certificate.** Positive joint Gram determinant per line-count,
`SS_E·SS_s − S_Es² > 0`, with `S_Es = ∑ₖ (Eₖ − Ē)(sₖ − s̄)` — the runtime identifiability gate for
the three-column `[1 | E | s]` design. -/
def jointRankCert (E s : ι → ℝ) : Prop :=
  0 < (∑ k, (E k - mean E) ^ 2) * (∑ k, (s k - mean s) ^ 2)
        - (∑ k, (E k - mean E) * (s k - mean s)) ^ 2

/-- **C2 soundness: the single-intercept joint design is identifiable** (thin re-export of
`CflibsFormal.jointDesign_det_pos_iff`). A positive joint Gram determinant certifies the centered
energies and ion indicator are not collinear, i.e. the single-intercept joint (T, nₑ) fit is
identifiable. -/
theorem jointRank_certificate_sound [Nonempty ι] (E s : ι → ℝ)
    (hcert : jointRankCert E s) : ¬ jointDesignCenteredProportional E s := by
  apply (jointDesign_det_pos_iff E s).mp
  rw [det_jointDesignNormalMatrix]
  exact mul_pos (by exact_mod_cast Fintype.card_pos) hcert

-- Non-vacuity: `E = (0,1,2)`, `s = (0,0,1)` (two neutral, one ionized line) gives
-- `SS_E·SS_s − S_Es² = 2·(2/3) − 1 = 1/3 > 0`, so the joint fit is identifiable.
example : ¬ jointDesignCenteredProportional (ι := Fin 3) ![0, 1, 2] ![0, 0, 1] :=
  jointRank_certificate_sound ![0, 1, 2] ![0, 0, 1]
    (by unfold jointRankCert mean; simp [Fin.sum_univ_three]; norm_num)

/-! ## C3 — Boltzmann-plot conditioning

Wraps `CflibsFormal.boltzmannConditionNumber_ge_one` and
`CflibsFormal.centeredScaledDesign_orthonormal` (module `OLS`). Same predicate as C1. Guarantee:
the raw condition number is `≥ 1`, and the *scaled* design is orthonormal (`κ_scaled = 1`), so the
remaining sensitivity is the slope noise gain `1/SS_E`. That gain carries units (energy⁻²), so it
is not scale-free (see `ConditionNumber`).

Not certified: anything beyond C1. The conclusion holds for every design with positive spread
(`κ ≥ 1` for any such design, and the scaling makes the design orthonormal by construction), so
C3 passes exactly when C1 does and adds no check (audit finding U-07). -/

/-- **C3 certificate: C1's predicate verbatim.** Positive energy spread — identical to
`energySpreadCert`, restated because it gates a distinct guarantee (conditioning rather than
rank). That guarantee holds whenever C1 does, so C3 carries no information beyond C1. -/
def conditioningCert (E : ι → ℝ) : Prop := 0 < ∑ k, (E k - mean E) ^ 2

/-- **C3 soundness: adds nothing to C1** (thin re-export of
`CflibsFormal.boltzmannConditionNumber_ge_one` and
`CflibsFormal.centeredScaledDesign_orthonormal`). Positive spread certifies `κ ≥ 1` and that the
scaled centered design is orthonormal (`κ_scaled = 1`): no matrix-conditioning content remains
beyond the slope gain `1/SS_E`, which carries units of energy⁻². -/
theorem conditioning_certificate_sound [Nonempty ι] (E : ι → ℝ)
    (hcert : conditioningCert E) :
    1 ≤ boltzmannConditionNumber E
      ∧ (∑ k, ((E k - mean E) / Real.sqrt (∑ k, (E k - mean E) ^ 2)) ^ 2 = 1)
      ∧ (∑ _k : ι, (1 / Real.sqrt (Fintype.card ι : ℝ)) ^ 2 = (1 : ℝ))
      ∧ (∑ k, ((E k - mean E) / Real.sqrt (∑ k, (E k - mean E) ^ 2))
            * (1 / Real.sqrt (Fintype.card ι : ℝ)) = 0) :=
  ⟨boltzmannConditionNumber_ge_one E hcert, centeredScaledDesign_orthonormal E hcert⟩

-- Non-vacuity: `E = (0,1)` has `κ = max(1/2, 2)/min(1/2, 2) = 4 ≥ 1` (a genuine `κ > 1`).
example : 1 ≤ boltzmannConditionNumber (ι := Fin 2) ![0, 1] :=
  (conditioning_certificate_sound ![0, 1]
    (by norm_num [conditioningCert, mean, Fin.sum_univ_two])).1

/-! ## C4 — Slope / energy-spread error budget

Wraps `CflibsFormal.maxPerLineError_sufficient` (module `ErrorBudget`). Predicate:
`ε²·card ≤ τ_β²·SS_E`. Guarantee: if every line's ordinate error is at most `ε`, the OLS slope
(inverse-temperature) error is within `τ_β`. `ε` is a distance to the *true* ordinates and stays
out of the certificate (R1).

Conditional on a deterministic error bound. The hypothesis is `|ŷₖ − yₖ| ≤ ε` for **every** line,
and any atomic-data error in the ordinates must be inside `ε` (or handled separately, C14). An
`ε = 1/SNR` is a one-sigma noise scale, not a bound: with independent Gaussian noise of standard
deviation `ε` on every line, all `n` lines fall within `ε` with probability `0.683ⁿ` (about 0.02
at `n = 10`; audit finding U-03). A statistical slope certificate is future work (audit FT-12). -/

/-- **C4 certificate.** The per-line error / energy-spread budget `ε²·n ≤ τ_β²·SS_E` (`n` = line
count). Runtime-checkable given a value for `ε`, the target slope error `τ_β`, and the design
quantities `n`, `SS_E`. The guarantee needs `ε` to bound every line's error, which an SNR
estimate does not (see the section note). -/
def slopeBudgetCert (eps tauBeta SSe : ℝ) (n : ℕ) : Prop :=
  eps ^ 2 * (n : ℝ) ≤ tauBeta ^ 2 * SSe

/-- **C4 soundness, conditional on a deterministic per-line error bound** (thin re-export of
`CflibsFormal.maxPerLineError_sufficient`). If every line's error is bounded by `ε` (an epistemic
input, R1) and the budget certificate holds, the OLS slope error is `≤ τ_β`. -/
theorem slopeBudget_certificate_sound [Nonempty ι] {E y yHat : ι → ℝ} {eps tauBeta : ℝ}
    (htau : 0 < tauBeta) (hvar : 0 < ∑ k, (E k - mean E) ^ 2)
    (hδ : ∀ k, |yHat k - y k| ≤ eps)
    (hcert : slopeBudgetCert eps tauBeta (∑ k, (E k - mean E) ^ 2) (Fintype.card ι)) :
    |olsSlope E yHat - olsSlope E y| ≤ tauBeta :=
  maxPerLineError_sufficient htau hvar hδ hcert

-- Witness: `E = (0,1)` (`SS_E = 1/2`), `ε = 1`, `τ_β = 2`: the budget `1²·2 ≤ 2²·(1/2)` is
-- tight (`2 ≤ 2`). The guarantee is applied at the zero-error corner `ŷ = y`, where the slope
-- error is `0 ≤ 2`: this shows the theorem applies, not that the bound is informative.
example : |olsSlope (ι := Fin 2) ![0, 1] ![0, 0] - olsSlope ![0, 1] ![0, 0]| ≤ 2 :=
  slopeBudget_certificate_sound (eps := 1) (by norm_num)
    (by norm_num [mean, Fin.sum_univ_two]) (fun k => by norm_num)
    (by norm_num [slopeBudgetCert, mean, Fin.sum_univ_two])

/-! ## C5 — Temperature-error budget

Wraps `CflibsFormal.temp_rel_error_le` (module `ErrorBudget`; exact identity
`CflibsFormal.temp_rel_error_eq`). Predicate: `k_B·T̂·B ≤ τ_T`. Guarantee: the relative
temperature error is within `τ_T`. `B` (a slope-error bound) is an epistemic input (R1).

Not certified: `B` itself. No theorem in this module composes C4 with C5, so a C4 pass does not
by itself discharge C5's hypothesis here. -/

/-- **C5 certificate.** The temperature budget `k_B·T̂·B ≤ τ_T`, where `B` bounds the
inverse-temperature (slope) error. Uses the exact identity `|ΔT|/T = k_B·T̂·|Δβ|`. -/
def tempBudgetCert (kB THat B tauT : ℝ) : Prop := kB * THat * B ≤ tauT

/-- **C5 soundness, conditional on an assumed slope-error bound** (thin re-export of
`CflibsFormal.temp_rel_error_le`). Given a slope-error bound `B` (epistemic, R1) and the
temperature budget, the relative temperature error is `≤ τ_T`. -/
theorem tempBudget_certificate_sound {kB T THat B tauT : ℝ}
    (hkB : 0 < kB) (hT : 0 < T) (hTHat : 0 < THat)
    (hB : |1 / (kB * THat) - 1 / (kB * T)| ≤ B)
    (hcert : tempBudgetCert kB THat B tauT) :
    |THat - T| / T ≤ tauT :=
  le_trans (temp_rel_error_le hkB hT hTHat hB) hcert

-- Non-vacuity: `k_B = 1`, `T = 1`, `T̂ = 2`, `B = 1/2`, `τ_T = 1`: the budget `1·2·(1/2) ≤ 1` is
-- tight, certifying the relative error `|2 − 1|/1 = 1 ≤ 1` (a genuine, nonzero, tight bound).
example : |(2 : ℝ) - 1| / 1 ≤ 1 :=
  tempBudget_certificate_sound (kB := 1) (T := 1) (THat := 2) (B := 1 / 2) (tauT := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [tempBudgetCert])

/-! ## C6 — Composition error budget

Wraps `CflibsFormal.composition_target_sufficient` (module `ErrorBudget`). Predicate:
`(card + 1)·δ ≤ τ_C·Ŝ`. Guarantee: each composition fraction is within `τ_C`. `δ` (per-species
density error) is a distance to the truth and stays out of the certificate (R1).

Not certified: `δ` itself; and anything abundance-aware. One absolute `δ` and one absolute `τ_C`
serve every species, so for a minor species the certified bound `τ_C` can exceed the fraction
itself (audit finding LIT-05). A relative-tolerance variant is future work. -/

/-- **C6 certificate.** The composition budget `(m + 1)·δ ≤ τ_C·Ŝ` (`m` = species count,
`Ŝ = ∑ₛ N̂ₛ`), with `δ` the per-species absolute density error. -/
def compBudgetCert (delta tauC Shat : ℝ) (n : ℕ) : Prop :=
  ((n : ℝ) + 1) * delta ≤ tauC * Shat

/-- **C6 soundness, conditional on an assumed absolute density error** (thin re-export of
`CflibsFormal.composition_target_sufficient`). Given a per-species density error bounded by `δ`
(epistemic, R1) and the composition budget, every composition fraction error is `≤ τ_C`. -/
theorem compBudget_certificate_sound {κ : Type*} [Fintype κ] {N Nhat : κ → ℝ} {delta tauC : ℝ}
    (hN : ∀ s, 0 ≤ N s) (hS : 0 < totalDensity N) (hShat : 0 < totalDensity Nhat)
    (hdelta : ∀ s, |Nhat s - N s| ≤ delta)
    (hcert : compBudgetCert delta tauC (totalDensity Nhat) (Fintype.card κ)) (s : κ) :
    |composition Nhat s - composition N s| ≤ tauC :=
  composition_target_sufficient hN hS hShat hdelta hcert s

-- Witness: two species `N = N̂ = (1, 1)` (`Ŝ = 2`), `δ = 1`, `τ_C = 2`: the budget
-- `(2 + 1)·1 ≤ 2·2` holds non-trivially (`3 ≤ 4`), certifying each fraction error `≤ 2`. This is a
-- zero-error corner (`N̂ = N`, left side `0`), and `τ_C = 2` exceeds any fraction error anyway:
-- the witness shows the theorem applies, not that the bound is informative.
example : |composition (κ := Fin 2) ![1, 1] 0 - composition ![1, 1] 0| ≤ 2 :=
  compBudget_certificate_sound (N := ![1, 1]) (Nhat := ![1, 1]) (delta := 1) (tauC := 2)
    (fun s => by fin_cases s <;> norm_num)
    (by simp [totalDensity, Fin.sum_univ_two])
    (by simp [totalDensity, Fin.sum_univ_two])
    (fun s => by fin_cases s <;> norm_num)
    (by simp [compBudgetCert, totalDensity, Fin.sum_univ_two]; norm_num) 0

/-! ## C7 — McWhirter LTE admissibility

Wraps `CflibsFormal.mcwhirter_iff_thermalizationLimit` (module `PartialLTE`), a biconditional.
Predicate: `C·√T·ΔE³ ≤ nₑ`. Guarantee: the transition gap is within the thermalization limit
(collisionally LTE-admissible). See R3: a single diagnostic certifies *internal consistency*, not
physical LTE.

Not certified: LTE. The McWhirter condition is necessary for LTE, not sufficient; transient and
inhomogeneous plasmas need further criteria (see `PartialLTE`). Evaluated at the recovered
`(T̂, n̂ₑ)`, the check is self-referential (R3). Units: the constant `C = 1.6·10¹²` presumes `nₑ`
in cm⁻³, `T` in K and `ΔE` in eV; the same predicate with `T` in eV or `nₑ` in m⁻³ is wrong by
orders of magnitude. -/

/-- **C7 certificate.** The McWhirter density condition `C·√T·ΔE³ ≤ nₑ` (`C = 1.6·10¹²` with
`nₑ` in cm⁻³, `T` in K and `ΔE` in eV, a mixed convention rather than CGS). -/
def mcWhirterCert (C T dE ne : ℝ) : Prop := C * Real.sqrt T * dE ^ 3 ≤ ne

/-- **C7 soundness: McWhirter admissibility, necessary but not sufficient for LTE** (thin
re-export of `CflibsFormal.mcwhirter_iff_thermalizationLimit`). The McWhirter density condition
certifies the transition gap `ΔE` is within the thermalization
limit `E*`. This is a necessary condition for LTE, not a sufficient one. -/
theorem mcWhirter_certificate_sound {C T dE ne : ℝ}
    (hC : 0 < C) (hT : 0 < T) (hdE : 0 ≤ dE) (hne : 0 ≤ ne)
    (hcert : mcWhirterCert C T dE ne) :
    dE ≤ thermalizationLimit C T ne :=
  (mcwhirter_iff_thermalizationLimit hC hT hdE hne).mp hcert

-- Non-vacuity: `C = 1`, `T = 1`, `ΔE = 1`, `nₑ = 2`: `1·√1·1³ = 1 ≤ 2` certifies
-- `ΔE = 1 ≤ E* = 2^(1/3) ≈ 1.26` (a genuine strict admissibility margin).
example : (1 : ℝ) ≤ thermalizationLimit 1 1 2 :=
  mcWhirter_certificate_sound (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [mcWhirterCert, Real.sqrt_one])

/-! ## C9 — Inner Saha-iteration contraction

Wraps `CflibsFormal.sahaIter_tendsto` (module `SahaEquilibrium`, via `sahaIter_contraction` and
`sahaIter_mapsTo`). Predicate: the four interval/contraction clauses. Guarantee: the fixed-point
iteration converges to the closed-form root `sahaEquilibriumNe S Ntot`. The soundness theorem
states the limit only; the per-step contraction factor is proved in `sahaIter_contraction`.

Scope: a forward-solver certificate for one element with two stages, at fixed `T` (so `S` is a
fixed number) and known absolute element total `Ntot`. The inverse problem does not know `Ntot`,
so C9 says nothing about the inverse `(T, nₑ)` loop. -/

/-- **C9 certificate.** The four runtime clauses for the single-element two-stage Saha iteration:
`b < Ntot`, the closed-form root `sahaEquilibriumNe S Ntot ≤ b`, the contraction rate
`√S/(2·√(Ntot − b)) < 1`, and the interval-invariance bound `√(S·Ntot) ≤ b`. -/
def sahaIterCert (S Ntot b : ℝ) : Prop :=
  b < Ntot
    ∧ sahaEquilibriumNe S Ntot ≤ b
    ∧ Real.sqrt S / (2 * Real.sqrt (Ntot - b)) < 1
    ∧ Real.sqrt (S * Ntot) ≤ b

/-- **C9 soundness: forward single-element Saha closure at known `Ntot`** (thin re-export of
`CflibsFormal.sahaIter_tendsto`). The four clauses, with
positivity of `S`, `Ntot` and a start `x₀ ∈ [0, b]`, certify convergence of the iterates to the
closed-form electron density of the single-element forward Saha closure. The conclusion is the
limit only; it states no rate. -/
theorem sahaIter_certificate_sound {S Ntot b x0 : ℝ} (hS : 0 < S) (hN : 0 < Ntot)
    (hx0 : 0 ≤ x0) (hx0b : x0 ≤ b) (hcert : sahaIterCert S Ntot b) :
    Filter.Tendsto (fun n => (sahaIter S Ntot)^[n] x0) Filter.atTop
      (nhds (sahaEquilibriumNe S Ntot)) :=
  sahaIter_tendsto hS hN hcert.1 hcert.2.1 hcert.2.2.2 hcert.2.2.1 hx0 hx0b

-- Non-vacuity: `S = 1`, `Ntot = 3`, `b = 2`, start `x₀ = 0`. All four clauses hold
-- (`2 < 3`; root `(−1+√13)/2 ≈ 1.30 ≤ 2`; rate `√1/(2√1) = 1/2 < 1`; `√3 ≈ 1.73 ≤ 2`), certifying
-- convergence to `sahaEquilibriumNe 1 3`.
example : Filter.Tendsto (fun n => (sahaIter 1 3)^[n] 0) Filter.atTop
    (nhds (sahaEquilibriumNe 1 3)) :=
  sahaIter_certificate_sound (S := 1) (Ntot := 3) (b := 2) (x0 := 0)
    (by norm_num) (by norm_num) le_rfl (by norm_num)
    ⟨by norm_num,
     by have h : Real.sqrt ((1 : ℝ) ^ 2 + 4 * 1 * 3) ≤ 5 := by
          rw [show (5 : ℝ) = Real.sqrt 25 by
            rw [show (25 : ℝ) = 5 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
          exact Real.sqrt_le_sqrt (by norm_num)
        unfold sahaEquilibriumNe
        rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
        linarith,
     by rw [show (3 : ℝ) - 2 = 1 by norm_num]; simp only [Real.sqrt_one]; norm_num,
     by rw [show (2 : ℝ) = Real.sqrt 4 by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
        exact Real.sqrt_le_sqrt (by norm_num)⟩

/-! ## C10 — Damped multi-element closure contraction (forward model, no smallness condition)

Wraps `CflibsFormal.dampedMultiElementIter_tendsto` (module `SahaEquilibrium`). With the
canonical relaxation `lam = 1/(1 + ∑ₛ Ntotₛ/Sₛ)` the averaged iteration contracts at rate
`1 − lam < 1` **with no smallness hypothesis** (`CflibsFormal.dampedMultiElementIter_contraction`)
— the certificate is just positivity. The soundness theorem states the limit only.

Scope: C10 certifies the fixed-`T` forward charge-neutrality closure
`x ↦ ∑ₛ Ntotₛ·Sₛ/(x + Sₛ)` at known absolute element totals `Ntot`. It says nothing about the
inverse `(T, nₑ)` loop, and nothing about the pipeline's `0.5` damping, which acts on that inverse
loop. (An earlier version of this note said C10 replaces that damping; it does not. Audit
findings U-02, INV-05.) A certificate for the loop the pipeline runs is future work (audit RF-17).

The soundness theorem takes the fixed point `r` as a hypothesis. Its existence, its uniqueness
and the geometric rate are proved without that hypothesis in
`CflibsFormal.dampedMultiElementIter_converges_to_equilibrium` (module `SahaContraction`, not
imported here). -/

/-- **C10 certificate: positivity of `S` and of the absolute totals `Ntot`.** Positivity of every
Saha factor `Sₛ` and total density `Ntotₛ` — the only runtime-checkable content the unconditional
convergence needs. There is deliberately **no** contraction-rate clause: the canonical
`lam = 1/(1 + ∑ Ntotₛ/Sₛ)` makes `1 − lam < 1` automatic. `Ntotₛ` are absolute element totals:
known in the forward problem, unknown in the inverse one. -/
def dampedIterCert (S Ntot : ι → ℝ) : Prop := (∀ s, 0 < S s) ∧ (∀ s, 0 < Ntot s)

/-- **C10 soundness: forward charge-neutrality closure at known `Ntot`, not the inverse loop**
(thin re-export of `CflibsFormal.dampedMultiElementIter_tendsto`). Positivity, the canonical
`lam`, and any nonnegative start certify convergence, with no smallness condition, of the
fixed-`T` forward charge-neutrality closure iteration to a given nonnegative coupled fixed point
`r` (a hypothesis here; see the section note). It says nothing about the inverse `(T, nₑ)`
loop. -/
theorem dampedIter_certificate_sound (S Ntot : ι → ℝ) {lam r x0 : ℝ}
    (hcert : dampedIterCert S Ntot)
    (hlamval : lam = 1 / (1 + ∑ s, Ntot s / S s))
    (hr : 0 ≤ r) (hfix : r = multiElementIonized S Ntot r) (hx0 : 0 ≤ x0) :
    Filter.Tendsto (fun n => (dampedMultiElementIter S Ntot lam)^[n] x0) Filter.atTop
      (nhds r) :=
  dampedMultiElementIter_tendsto S Ntot hcert.1 hcert.2 hlamval hr hfix hx0

-- Non-vacuity: two species `S = Ntot = (1, 1)`, canonical `lam = 1/(1 + 2) = 1/3`, fixed point
-- `r = 1` (`G 1 = 2/(1+1) = 1`), start `x₀ = 0`. Certifies convergence of the damped iteration
-- to `1`.
example : Filter.Tendsto
    (fun n => (dampedMultiElementIter (ι := Fin 2) ![1, 1] ![1, 1] (1 / 3))^[n] 0)
    Filter.atTop (nhds 1) :=
  dampedIter_certificate_sound ![1, 1] ![1, 1]
    ⟨fun s => by fin_cases s <;> norm_num, fun s => by fin_cases s <;> norm_num⟩
    (by simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]; norm_num)
    (by norm_num)
    (by simp only [multiElementIonized, Fin.sum_univ_two, Matrix.cons_val_zero,
          Matrix.cons_val_one]; norm_num)
    le_rfl

/-! ## C12 — Self-absorption model left-inverse (`0 ≤ τ`) · NON-INFORMATIVE

Wraps `CflibsFormal.lineIntensity_eq_selfAbsorbedIntensity_div` (module `SelfAbsorption`), which
holds for every `τ ≥ 0`. Predicate: `0 ≤ τ`. Guarantee: dividing the *model* self-absorbed
intensity `selfAbsorbedIntensity … τ` by `SA(τ)` returns the model thin intensity `lineIntensity`.

Not certified: that `τ` is known, or that it is the plasma's optical depth. Because
`selfAbsorbedIntensity` is defined as `lineIntensity · SA(τ)`, the identity is algebra on the
model. It holds for every `τ ≥ 0`, including a wrong estimate `τ̂`, and no measured intensity and
no true optical depth appears in it. Passing C12 therefore certifies nothing about the data
(audit findings LF-11, U-05, SPC-03). The model is itself approximate: `SA` is the flat,
line-centre escape factor, and applied to the frequency-integrated intensity of a peaked profile
it over-corrects (1.4–3.5× for Gaussian and Lorentzian profiles at `τ₀ = 3–10`, audit finding
LF-01). `CflibsFormal.opticalDepth_knownTauCert` discharges only the nonnegativity of the model
optical depth.

The name `knownTauCert` is kept because downstream modules and the oracle reference it. Future
work (audit FT-13): a ½-Lipschitz bound on `log SA` and a `τ`-error propagation lemma, in which
an assumed `|τ̂ − τ| ≤ Δ` bounds the log error of the corrected intensity by `Δ/2` for a known
profile shape. Its content would sit in the assumed `Δ` (a C14-style refusal), not in a
checkable predicate. -/

/-- **C12 certificate: `0 ≤ τ`, nothing more.** Despite the name, it does not check that `τ` is
known or correct; any nonnegative estimate satisfies it (see the section note). -/
def knownTauCert (tau : ℝ) : Prop := 0 ≤ tau

/-- **C12 soundness: a model identity, not a recovery guarantee** (thin re-export of
`CflibsFormal.lineIntensity_eq_selfAbsorbedIntensity_div`). For every `τ ≥ 0`, the model thin
intensity equals the model self-absorbed intensity at that same `τ` divided by `SA(τ)`. This is a
definitional identity of the flat-kernel self-absorption model, not a recovery guarantee for a
measured intensity: the `τ` on both sides is the same number, whatever its relation to the
plasma. -/
theorem knownTau_certificate_sound {kB T N Fcal : ℝ} {g E A : ι → ℝ} (k : ι) {tau : ℝ}
    (hcert : knownTauCert tau) :
    lineIntensity kB T N Fcal g E A k
      = selfAbsorbedIntensity kB T N Fcal g E A k tau / selfAbsorptionFactor tau :=
  lineIntensity_eq_selfAbsorbedIntensity_div k hcert

-- Witness: at `τ = 1` (`SA(1) = 1 − e⁻¹ ≠ 1`) the identity holds. It holds at every other
-- `τ ≥ 0` as well, which is why C12 carries no information about the data.
example {kB T N Fcal : ℝ} {g E A : Fin 1 → ℝ} :
    lineIntensity kB T N Fcal g E A 0
      = selfAbsorbedIntensity kB T N Fcal g E A 0 1 / selfAbsorptionFactor 1 :=
  knownTau_certificate_sound 0 zero_le_one

/-! ## C13 — Two-line curve-of-growth identifiability (flat kernel, unknown scale)

Wraps `CflibsFormal.cogRatio_injOn` (module `CurveOfGrowth`), the recovery direction. Predicate:
two lines with distinct positive opacity coefficients `0 < w₂ < w₁`. Guarantee: the flat-kernel
curve-of-growth ratio `(1 − e^{−w₁ n})/(1 − e^{−w₂ n})` is injective in the column density
`n > 0`, so `n` is determined by the ratio alone. The single-line failure mode is
`CflibsFormal.selfAbsorption_breaks_identifiability`.

Scope (relation REDUCED; published APPROXIMATION via the `cogRatio` model row,
`docs/conventions.md` §8; audit findings U-06, LF-04, LF-08):
* `w₁`, `w₂` are per-line opacity coefficients (`τ = w·n`, proportional to oscillator strength),
  not line widths.
* The ratio model assumes the two lines share one source term and one lower-level column `n`.
  Two distinct transitions have different source terms in general; in the state-bound model
  their ratio is given by `CflibsFormal.lteSourceStrength_ratio_calibration_free` and is not 1
  in general. The Prop encodes neither condition.
* Injectivity is a property of the flat kernel `1 − e^{−w n}`. For a profile-resolved (Voigt)
  curve of growth of Stark-broadened lines the audit's probes (γ/σ = 0.1, 0.3, 0.93; no larger
  γ/σ probed) found the pair ratio non-monotone within line-centre depths `≤ 30`, rising about
  0.4–1.6% past its minimum, so conditioning is the practical issue there.
* `n` is one species' column density, not a relative composition.

The dossier's C13 disjunction also had a `τ`-known branch, C12, which carries no information
(see C12). -/

/-- **C13 certificate: distinct positive opacity coefficients (not widths).** Two lines with
`0 < w₂ < w₁`, where `τ = w·n` — the runtime "≥ 2 distinct opacities" content that breaks the
single-line (N, τ) alias in the flat-kernel model. -/
def saDistinctCert (w₁ w₂ : ℝ) : Prop := 0 < w₂ ∧ w₂ < w₁

/-- **C13 soundness: flat-kernel pair-ratio injectivity** (thin re-export of
`CflibsFormal.cogRatio_injOn`). Distinct positive opacity coefficients certify that the
flat-kernel curve-of-growth ratio is injective on `(0, ∞)`, so the shared column density is
determined by the ratio without knowing the common source scale. Relation REDUCED (one shared
source term and one shared lower-level column); publishes APPROXIMATION because `cogRatio` is the
flat-kernel model (see the section note). -/
theorem saDistinct_certificate_sound {w₁ w₂ : ℝ} (hcert : saDistinctCert w₁ w₂) :
    Set.InjOn (fun n => cogRatio w₁ w₂ n) (Set.Ioi 0) :=
  cogRatio_injOn hcert.2 hcert.1

-- Witness: opacity coefficients `w₁ = 2`, `w₂ = 1` (`0 < 1 < 2`) certify an injective, hence
-- invertible, flat-kernel ratio observable.
example : Set.InjOn (fun n => cogRatio 2 1 n) (Set.Ioi 0) :=
  saDistinct_certificate_sound ⟨by norm_num, by norm_num⟩

/-! ## C14 — Atomic-data aliasing error budget (A* — refusal-flagged)

Wraps `CflibsFormal.classicDensity_aliasing_error` (module `AtomicDataPerturbation`). Predicate:
`0 ≤ δ < 1`. Guarantee: `|N̂ − N| ≤ N·δ/(1 − δ)` for the classic known-`T` density reader.

Not certified: the size of the atomic-data error. Every `δ ∈ [0, 1)` satisfies the predicate; all
of the guarantee's content sits in the assumed bound `hpert` on the response-factor error.

REFUSAL (R2): `δ` is the relative atomic-data error — a distance to an *unknown* truth (you use
tabulated data precisely because truth is unknown). Only a literature-uncertainty `δ` (e.g. a NIST
grade) can be plugged; the bound is exactly as honest as that catalog claim. The predicate is
runtime-*evaluable* but its input is ASSUMED, not MEASURED — report "conditional on the atomic-data
uncertainty," never "proven." -/

/-- **C14 certificate.** The atomic-data aliasing budget `0 ≤ δ < 1`.
    REFUSAL: `δ` is assumed (a catalog uncertainty), not measured — see the section note (R2). -/
def aliasBudgetCert (delta : ℝ) : Prop := 0 ≤ delta ∧ delta < 1

/-- **C14 soundness, conditional on an assumed atomic-data error** (thin re-export of
`CflibsFormal.classicDensity_aliasing_error`). Given an assumed relative atomic-data error bound
`δ` (R2) and `δ < 1`, the recovered density obeys `|N̂ − N| ≤ N·δ/(1 − δ)`. -/
theorem aliasBudget_certificate_sound [Nonempty ι] {kB T N Fcal delta : ℝ}
    {g E A g' E' A' : ι → ℝ} (hg : ∀ k, 0 < g k) (hg' : ∀ k, 0 < g' k) (hFcal : 0 < Fcal) (u : ι)
    (hA : 0 < A u) (hA' : 0 < A' u) (hN : 0 < N)
    (hpert : |responseFactor kB T g' E' A' u - responseFactor kB T g E A u|
              ≤ delta * responseFactor kB T g E A u)
    (hcert : aliasBudgetCert delta) :
    |Classic.classicDensity kB T Fcal g' E' A' u (lineIntensity kB T N Fcal g E A u) - N|
      ≤ N * (delta / (1 - delta)) :=
  classicDensity_aliasing_error hg hg' hFcal u hA hA' hN hcert.1 hcert.2 hpert

-- Non-vacuity (certificate satisfiable at a genuine interior `δ`): `δ = 1/2 ∈ [0, 1)`.
example : aliasBudgetCert (1 / 2) := ⟨by norm_num, by norm_num⟩

-- Guarantee witness at the zero-error corner: with correct atomic data (`g' = g`, `E' = E`,
-- `A' = A`) and `δ = 0`, the aliasing bound is `≤ N·(0/1) = 0` — the exact-recovery corner. It
-- shows the theorem applies, not that the bound is informative at `δ > 0`.
example {kB T N Fcal : ℝ} {g E A : Fin 1 → ℝ}
    (hg : ∀ k, 0 < g k) (hFcal : 0 < Fcal) (hA : 0 < A 0) (hN : 0 < N) :
    |Classic.classicDensity kB T Fcal g E A 0 (lineIntensity kB T N Fcal g E A 0) - N|
      ≤ N * ((0 : ℝ) / (1 - 0)) :=
  aliasBudget_certificate_sound (delta := 0) (g' := g) (E' := E) (A' := A)
    hg hg hFcal 0 hA hA hN (by simp) ⟨le_rfl, by norm_num⟩

end CflibsFormal
