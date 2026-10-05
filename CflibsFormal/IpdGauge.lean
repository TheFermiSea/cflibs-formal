/-
Copyright (c) 2026 Brian Squires. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Squires
-/
import Mathlib
import CflibsFormal.Saha
import CflibsFormal.Closure

/-!
# CF-LIBS formalization — the IPD gauge of the ideal Saha factor (frontier FT-02)

An ionization-potential depression (IPD) lowers the ionization energy `χ` of a plasma atom by
some `d ≥ 0`. In the ideal Saha factor that is a gauge: `S(χ − d) = S(χ)·exp(d/(k_B T))`
(`sahaFactor_ipd_gauge`). This module states what follows when the forward model uses the
lowered energy and the inverse does not, which is how a pipeline ends up when the depression is
switched on in one place only.

## Main results

* `sahaFactor_ipd_gauge`: the gauge identity, for every real `d`.
* `ne_ipd_mismatch`: data generated with `χ − d` and inverted with `χ` give the electron density
  `n_e · exp(−d/(k_B T))`. The reported density is low by exactly the factor the depression
  would have supplied.
* `sahaRatio_ipd_gauge`: on the ratio route the error cancels. If the density estimate `n̂`
  comes from one element's depression-free inverse, then for every species `s`
  `S_s(χ_s)/n̂ = S_s(χ_s − d)/n_e`: the ion-to-neutral ratio the inverse assigns to `s` is the
  true one, provided the same `d` applies to every element.
* `twoStageTotal_ipd_gauge`: so each species' two-stage total `N_I·(1 + S_s/n_e)` is the same
  either way.
* `composition_ipd_gauge`: and with the totals, the composition (`Closure.composition`).

## Honest limitations

* **The depression is an input.** `d` is a given real number. Nothing here says how large it is
  or how it depends on `n_e` and `T`; the fixed-point structure that dependence creates is
  `IpdSahaInverse` (with the coefficient abstract).
* **One ionization edge, one `d`.** The cancellation in `sahaRatio_ipd_gauge` needs the same
  `d` for the reference element and for the species. It is stated for the neutral-to-ion edge.
  A second edge with a different lowering (decision D18 uses `2Δχ` at the next edge) does not
  cancel, and neither does a depression that differs between elements.
* **Partition functions are frozen.** The same level lists and weights appear on both sides. A
  depression also removes high levels from the partition sums; that effect is not modelled.
* **The density must come from the ratio route.** If `n_e` is measured independently (Stark
  width) or imposed, the estimate is no longer `n_e·exp(−d/(k_B T))` and the cancellation is
  lost: the ion fractions are then wrong by the gauge factor.
* **Model.** Everything is stated for the ideal `sahaFactor` (model tag REDUCED), so every
  result here is published REDUCED whatever its own relation tag.

## Literature

The Saha–Eggert equation with a lowered ionization energy: Griem, *Principles of Plasma
Spectroscopy*, Cambridge University Press, 1997. The identities are algebra on the equation's
exponential factor; no source is cited for them, and no lowering model (Debye–Hückel or other)
is asserted.
-/

namespace CflibsFormal

variable {ι : Type*} [Fintype ι]
variable {κ : Type*} [Fintype κ]

/-- **IPD gauge of the Saha factor.** Lowering the ionization energy by `d` multiplies the Saha
factor by `exp(d/(k_B T))`: `S(χ − d) = S(χ)·exp(d/(k_B T))`. An identity of the defined
function, with no hypothesis; it also holds for negative `d` (a raised energy) and in the
totalized cases (`k_B T = 0`).

Scope (two-axis): own relation EXACT; definition used: `sahaFactor` (model tag REDUCED: ideal
Saha, level sums over the supplied lists); published REDUCED. Reading `d` as a physical
depression adds the assumption that the partition functions do not change with it. -/
theorem sahaFactor_ipd_gauge (kB T me h chi d : ℝ) (gZ EZ : ι → ℝ) (gZ1 EZ1 : κ → ℝ) :
    sahaFactor kB T me h (chi - d) gZ EZ gZ1 EZ1
      = sahaFactor kB T me h chi gZ EZ gZ1 EZ1 * Real.exp (d / (kB * T)) := by
  unfold sahaFactor
  rw [show -(chi - d) / (kB * T) = -chi / (kB * T) + d / (kB * T) by ring, Real.exp_add]
  ring

/-- **Depression on in the forward model, off in the inverse.** If the measured stage ratio `R`
satisfies the Saha relation with the lowered energy, `R·n_e = S(χ − d)`, then the density
diagnostic evaluated with the unlowered `χ` returns `n_e·exp(−d/(k_B T))`.

For `d > 0` at positive temperature the estimate is low. As an illustration, a lowering of
`0.063 eV` at `k_B T = 0.948 eV` gives the factor `exp(−0.0665) ≈ 0.936` [derivation,
unchecked here].

Hypothesis `hR : R ≠ 0` is needed: the diagnostic divides by `R`, and with `R = 0` it returns
Lean's `x/0 = 0` whatever `n_e` is. Nothing is assumed about the signs of `T`, `n_e` or `d`.

Scope (two-axis): own relation REDUCED (one ionization edge, a given `d`, partition functions
unchanged by the depression); definitions used: `sahaFactor` (REDUCED) and
`electronDensityFromRatio`; published REDUCED. -/
theorem ne_ipd_mismatch (kB T me h chi d R ne : ℝ) (gZ EZ : ι → ℝ) (gZ1 EZ1 : κ → ℝ)
    (hR : R ≠ 0) (hfwd : R * ne = sahaFactor kB T me h (chi - d) gZ EZ gZ1 EZ1) :
    electronDensityFromRatio kB T me h chi gZ EZ gZ1 EZ1 R
      = ne * Real.exp (-(d / (kB * T))) := by
  unfold electronDensityFromRatio
  rw [sahaFactor_ipd_gauge] at hfwd
  have he : Real.exp (d / (kB * T)) ≠ 0 := Real.exp_ne_zero _
  rw [Real.exp_neg, div_eq_iff hR]
  field_simp
  linarith [hfwd]

/-- **On the ratio route the depression cancels.** Let the density estimate be the
depression-free inverse of a reference element `m`, whose data obey the lowered relation
`R_m·n_e = S_m(χ_m − d)`. Then for any species `s`, with its own levels and ionization energy,
`S_s(χ_s)/n̂ = S_s(χ_s − d)/n_e`.

Reading: `S_s/n_e` is the ion-to-neutral ratio of species `s`. The inverse uses the wrong Saha
factor and the wrong density, and the two errors are the same factor `exp(d/(k_B T))`, so the
ratio it assigns to every species is the true one. This is why switching the depression off in
the inverse leaves the composition unchanged while the reported `n_e` is biased.

Hypothesis `hR : R_m ≠ 0` keeps the density estimate out of Lean's `x/0 = 0` branch; without
it the statement is false (`R_m = 0` with a vanishing reference Saha factor satisfies `hfwd` for
any `n_e`). No `n_e ≠ 0` is assumed: at `n_e = 0` the forward relation forces the reference
Saha factor to `0`, the estimate is `0`, and both sides are `x/0 = 0`, so the identity holds
there without content. The same `d` for `m` and `s` is built into the statement and is the
substantive assumption.

Scope (two-axis): own relation REDUCED (one ionization edge, element-independent `d`, partition
functions unchanged by the depression, `n̂` from the ratio route); published REDUCED. -/
theorem sahaRatio_ipd_gauge {ι' κ' : Type*} [Fintype ι'] [Fintype κ']
    {kB T me h chim chis d Rm ne : ℝ} {gZ EZ : ι → ℝ} {gZ1 EZ1 : κ → ℝ}
    {gS ES : ι' → ℝ} {gS1 ES1 : κ' → ℝ} (hR : Rm ≠ 0)
    (hfwd : Rm * ne = sahaFactor kB T me h (chim - d) gZ EZ gZ1 EZ1) :
    sahaFactor kB T me h chis gS ES gS1 ES1
        / electronDensityFromRatio kB T me h chim gZ EZ gZ1 EZ1 Rm
      = sahaFactor kB T me h (chis - d) gS ES gS1 ES1 / ne := by
  rw [sahaFactor_ipd_gauge] at hfwd ⊢
  unfold electronDensityFromRatio
  have he : Real.exp (d / (kB * T)) ≠ 0 := Real.exp_ne_zero _
  by_cases hne : ne = 0
  · have hS : sahaFactor kB T me h chim gZ EZ gZ1 EZ1 = 0 := by
      rw [hne, mul_zero] at hfwd
      exact (mul_eq_zero.mp hfwd.symm).resolve_right he
    rw [hS, hne, zero_div, div_zero, div_zero]
  · rw [div_div_eq_mul_div, eq_div_iff hne]
    by_cases hS : sahaFactor kB T me h chim gZ EZ gZ1 EZ1 = 0
    · rw [hS, zero_mul] at hfwd
      exact absurd (mul_eq_zero.mp hfwd) (by tauto)
    · field_simp
      linear_combination (sahaFactor kB T me h chis gS ES gS1 ES1) * hfwd

/-- **Two-stage totals are unchanged.** With neutral density `N_I` of species `s`, the total
`N_I·(1 + S_s/n_e)` computed by the depression-free inverse (unlowered `χ_s`, density estimate
from the reference element) equals the total computed with the lowered energy and the true
`n_e`. The statement is for one species; `composition_ipd_gauge` applies it to all species at
once. An immediate consequence of `sahaRatio_ipd_gauge`, with its hypothesis and its scope
(REDUCED; published REDUCED). -/
theorem twoStageTotal_ipd_gauge {ι' κ' : Type*} [Fintype ι'] [Fintype κ']
    {kB T me h chim chis d Rm ne : ℝ} {gZ EZ : ι → ℝ} {gZ1 EZ1 : κ → ℝ}
    {gS ES : ι' → ℝ} {gS1 ES1 : κ' → ℝ} (NI : ℝ) (hR : Rm ≠ 0)
    (hfwd : Rm * ne = sahaFactor kB T me h (chim - d) gZ EZ gZ1 EZ1) :
    NI * (1 + sahaFactor kB T me h chis gS ES gS1 ES1
        / electronDensityFromRatio kB T me h chim gZ EZ gZ1 EZ1 Rm)
      = NI * (1 + sahaFactor kB T me h (chis - d) gS ES gS1 ES1 / ne) := by
  rw [sahaRatio_ipd_gauge hR hfwd]

/-- **The composition is unchanged.** For a family of species `s : σ`, each with its own
neutral density `N_I s`, ionization energy `χ s` and level lists, the composition
(`Closure.composition`, each total divided by the sum of the totals) computed from the
depression-free inverse equals the composition computed with the lowered energies and the true
`n_e`. The two vectors of totals are equal species by species (`twoStageTotal_ipd_gauge`), so
nothing is assumed about their sum; when it vanishes both sides are Lean's `x/0 = 0`.

The species share the index types `ι'`, `κ'` of their level lists, which is no restriction on
finite lists (pad the shorter ones with zero-weight levels). The same `d` for every species and
for the reference element is the substantive assumption, as in `sahaRatio_ipd_gauge`.

Scope (two-axis): own relation REDUCED (two stages per species, one ionization edge,
element-independent `d`, partition functions unchanged by the depression, `n̂` from the ratio
route); published REDUCED. -/
theorem composition_ipd_gauge {σ ι' κ' : Type*} [Fintype σ] [Fintype ι'] [Fintype κ']
    {kB T me h chim d Rm ne : ℝ} {gZ EZ : ι → ℝ} {gZ1 EZ1 : κ → ℝ} (NI chis : σ → ℝ)
    (gS ES : σ → ι' → ℝ) (gS1 ES1 : σ → κ' → ℝ) (hR : Rm ≠ 0)
    (hfwd : Rm * ne = sahaFactor kB T me h (chim - d) gZ EZ gZ1 EZ1) :
    composition (fun s => NI s * (1 + sahaFactor kB T me h (chis s) (gS s) (ES s) (gS1 s) (ES1 s)
        / electronDensityFromRatio kB T me h chim gZ EZ gZ1 EZ1 Rm))
      = composition (fun s => NI s * (1 + sahaFactor kB T me h (chis s - d) (gS s) (ES s)
        (gS1 s) (ES1 s) / ne)) := by
  congr 1
  funext s
  exact twoStageTotal_ipd_gauge (NI s) hR hfwd

/-- Non-vacuity of `ne_ipd_mismatch`: unit constants, ground-state-only level lists, `χ = 1`,
`d = 1/10`, true density `n_e = 1`, and the stage ratio the lowered Saha relation then gives
(`R = S(χ − d)`, nonzero because the Saha factor is positive). -/
example :
    electronDensityFromRatio 1 1 1 1 1 (fun _ : Fin 1 => (1:ℝ)) (fun _ => 0)
        (fun _ : Fin 1 => (1:ℝ)) (fun _ => 0)
        (sahaFactor 1 1 1 1 (1 - 1 / 10) (fun _ : Fin 1 => (1:ℝ)) (fun _ => 0)
          (fun _ : Fin 1 => (1:ℝ)) (fun _ => 0))
      = 1 * Real.exp (-((1 / 10 : ℝ) / (1 * 1))) :=
  ne_ipd_mismatch 1 1 1 1 1 (1 / 10) _ 1 _ _ _ _
    (sahaFactor_pos (ι := Fin 1) (κ := Fin 1) one_pos one_pos one_pos one_pos
      (fun _ => one_pos) (fun _ => one_pos)).ne'
    (mul_one _)

/-- Non-vacuity of `sahaRatio_ipd_gauge` (and so of the two results built on it): a reference
element with `χ = 1` and true density `n_e = 2`, whose stage ratio is the one the lowered
relation gives (`R = S(1 − 1/2)/2`), and a different species with `χ = 3` and two ion levels. -/
example :
    sahaFactor 1 1 1 1 3 (fun _ : Fin 1 => (1:ℝ)) (fun _ => 0) (fun _ : Fin 2 => (3:ℝ)) ![0, 1]
        / electronDensityFromRatio 1 1 1 1 1 (fun _ : Fin 1 => (1:ℝ)) (fun _ => 0)
          (fun _ : Fin 1 => (1:ℝ)) (fun _ => 0)
          (sahaFactor 1 1 1 1 (1 - 1 / 2) (fun _ : Fin 1 => (1:ℝ)) (fun _ => 0)
            (fun _ : Fin 1 => (1:ℝ)) (fun _ => 0) / 2)
      = sahaFactor 1 1 1 1 (3 - 1 / 2) (fun _ : Fin 1 => (1:ℝ)) (fun _ => 0)
          (fun _ : Fin 2 => (3:ℝ)) ![0, 1] / 2 :=
  sahaRatio_ipd_gauge
    (div_ne_zero (sahaFactor_pos (ι := Fin 1) (κ := Fin 1) one_pos one_pos one_pos one_pos
      (fun _ => one_pos) (fun _ => one_pos)).ne' two_ne_zero)
    (by field_simp)

end CflibsFormal
