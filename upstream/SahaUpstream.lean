/-
Copyright (c) 2026 Brian Squires. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Squires
-/
import Mathlib

/-!
# Upstream candidate — Saha ionization equilibrium (seed for a physlib PR)

A **self-contained (mathlib-only), CF-LIBS-free** extract of the forward Saha physics from
`CflibsFormal/Saha.lean`, together with the minimal discrete partition function it needs from
`CflibsFormal/Boltzmann.lean`. This is the prepared seed for an eventual upstream PR to
[physlib](https://github.com/leanprover-community/physlib), which currently has Boltzmann /
canonical-ensemble / translational physics but **no Saha / ionization equilibrium**.

This file is **not part of the verified `CflibsFormal` spec** — it is a separate `lean_lib`
staging artifact (built + axiom-audited independently), kept in lockstep with `Saha.lean`. See
`docs/upstream-physlib-plan.md` for scope, governance (physlib's AI policy — the human author
certifies every line, verifies references, and conducts all reviewer communication), triggers,
and the step sequence.

## Porting notes (do NOT port verbatim — adapt to physlib's idiom)

* Replace `partitionFunction` below with physlib's discrete
  `StatisticalMechanics/CanonicalEnsemble/Finite` partition function `Z = ∑ exp(−βEᵢ)`
  (degeneracy-weighted) — do not re-introduce our own.
* Restate **unit-aware**: `kB` → physlib `BoltzmannConstant`, `T` → `Temperature`, and the masses
  / energies carry `Units`/`Dimension`. The `(2π·m_e·k_B·T / h²)^{3/2}` factor should reuse
  physlib's `translational` / ideal-gas physics if it already provides the translational partition
  function / thermal de-Broglie wavelength (else contribute that as a prerequisite).
* physlib `AGENTS.md` conventions: `theorem` only for the Saha equation itself (well known in the
  literature), `lemma` for the rest; numbered `# A.` / `## A.1.` sections; a docstring on every
  definition; proofs < 50 LOC; no trivial rewrites of mathlib/physlib; no `axiom`, no `sorry`;
  atomic commits with DCO sign-off; the human author verifies the references below personally.

## Literature

Saha, M. N. "Ionization in the solar chromosphere." *Phil. Mag.* **40** (1920) 472–488.
Eggert, J. "Über den Dissoziationszustand der Fixsterngase." *Phys. Z.* **20** (1919) 570.
Griem, H. R. *Principles of Plasma Spectroscopy* (Cambridge, 1997) — Saha–Eggert equation.
-/

namespace SahaUpstream

open Finset Real
open scoped BigOperators

variable {ι : Type*} [Fintype ι]
variable {κ : Type*} [Fintype κ]

/-- Minimal discrete (degeneracy-weighted) partition function `U(T) = ∑ₖ gₖ·exp(−Eₖ/(k_B T))`.
Inlined here so the seed is mathlib-only; in physlib this is replaced by
`StatisticalMechanics/CanonicalEnsemble/Finite`'s `Z = ∑ exp(−βEᵢ)`. -/
noncomputable def partitionFunction {α : Type*} [Fintype α] (kB T : ℝ) (g E : α → ℝ) : ℝ :=
  ∑ k, g k * Real.exp (-E k / (kB * T))

/-- The partition function is strictly positive when the statistical weights are positive and
there is at least one level. -/
lemma partitionFunction_pos {α : Type*} [Fintype α] [Nonempty α] {kB T : ℝ} {g E : α → ℝ}
    (hg : ∀ k, 0 < g k) : 0 < partitionFunction kB T g E :=
  Finset.sum_pos (fun k _ => mul_pos (hg k) (Real.exp_pos _)) Finset.univ_nonempty

/-- The de-Broglie bracket `2π·m_e·k_B·T / h²` appearing (to the `3/2` power) in the Saha factor.
Factored out so positivity and the log identity reuse it. -/
noncomputable def thermalBracket (kB T me h : ℝ) : ℝ :=
  (2 * Real.pi * me * kB * T) / h ^ 2

/-- The thermal-de-Broglie bracket is strictly positive when the physical constants and
temperature are positive. -/
lemma thermalBracket_pos {kB T me h : ℝ}
    (hkB : 0 < kB) (hT : 0 < T) (hme : 0 < me) (hh : 0 < h) :
    0 < thermalBracket kB T me h := by
  unfold thermalBracket
  have hnum : 0 < 2 * Real.pi * me * kB * T :=
    mul_pos (mul_pos (mul_pos (mul_pos (by norm_num) Real.pi_pos) hme) hkB) hT
  exact div_pos hnum (pow_pos hh 2)

/-- **Saha factor** `S(T)`: the full right-hand side of the Saha equation *excluding* the electron
density `n_e` and the stage population ratio. With `U_z = partitionFunction kB T gZ EZ`,
`U_{z+1} = partitionFunction kB T gZ1 EZ1`:
`S(T) = 2 · (U_{z+1}/U_z) · (2π·m_e·k_B·T / h²)^(3/2) · exp(−χ/(k_B T))`.
The full Saha law reads `(n_{z+1} · n_e)/n_z = S(T)`. The leading `2` is the free-electron spin
weight `2·g_e` (`g_e = 1`); the exponent `−χ/(k_B T)` reflects that ionization costs energy
`χ > 0`; the `(3/2)` power (via `Real.rpow`) is the thermal-de-Broglie volume scaling. -/
noncomputable def sahaFactor (kB T me h chi : ℝ) (gZ EZ : ι → ℝ) (gZ1 EZ1 : κ → ℝ) : ℝ :=
  2 * (partitionFunction kB T gZ1 EZ1 / partitionFunction kB T gZ EZ)
    * (thermalBracket kB T me h) ^ (3 / 2 : ℝ)
    * Real.exp (-chi / (kB * T))

/-- **Saha density diagnostic.** Given a measured stage population ratio `R = n_{z+1}/n_z`, the
electron density implied by the Saha equation is `n_e = S(T) / R`. -/
noncomputable def electronDensityFromRatio (kB T me h chi : ℝ) (gZ EZ : ι → ℝ)
    (gZ1 EZ1 : κ → ℝ) (R : ℝ) : ℝ :=
  sahaFactor kB T me h chi gZ EZ gZ1 EZ1 / R

/-- **Positivity of the Saha factor.** Given positive physical constants and temperature, and
positive statistical weights for both stages, `S(T) > 0`. The ionization energy `χ` is
unconstrained: `exp(−χ/(k_B T))` is positive for any sign of `χ`. -/
theorem sahaFactor_pos [Nonempty ι] [Nonempty κ] {kB T me h chi : ℝ}
    {gZ EZ : ι → ℝ} {gZ1 EZ1 : κ → ℝ}
    (hkB : 0 < kB) (hT : 0 < T) (hme : 0 < me) (hh : 0 < h)
    (hgZ : ∀ k, 0 < gZ k) (hgZ1 : ∀ k, 0 < gZ1 k) :
    0 < sahaFactor kB T me h chi gZ EZ gZ1 EZ1 := by
  unfold sahaFactor
  have hbr : 0 < thermalBracket kB T me h := thermalBracket_pos hkB hT hme hh
  have hrpow : 0 < (thermalBracket kB T me h) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hbr _
  have hUratio : 0 < partitionFunction kB T gZ1 EZ1 / partitionFunction kB T gZ EZ :=
    div_pos (partitionFunction_pos hgZ1) (partitionFunction_pos hgZ)
  have hexp : 0 < Real.exp (-chi / (kB * T)) := Real.exp_pos _
  exact mul_pos (mul_pos (mul_pos (by norm_num) hUratio) hrpow) hexp

/-- **Saha law ⇔ density inversion.** For a nonzero stage ratio `R`, the diagnostic form
`n_e = S/R` is equivalent to the structural Saha law `R · n_e = S`. -/
theorem saha_relation {kB T me h chi : ℝ} {gZ EZ : ι → ℝ} {gZ1 EZ1 : κ → ℝ}
    {R ne : ℝ} (hR : R ≠ 0) :
    ne = electronDensityFromRatio kB T me h chi gZ EZ gZ1 EZ1 R
      ↔ R * ne = sahaFactor kB T me h chi gZ EZ gZ1 EZ1 := by
  unfold electronDensityFromRatio
  rw [eq_div_iff hR]
  constructor <;> intro h <;> linarith

/-- **Density diagnostic is injective.** The map `R ↦ n_e = S(T)/R` is strictly antitone on the
positive reals: a larger measured stage ratio yields a strictly smaller inferred electron density,
so a measured ratio determines `n_e` uniquely. Relies on `S(T) > 0`. -/
theorem electronDensity_antitone [Nonempty ι] [Nonempty κ] {kB T me h chi : ℝ}
    {gZ EZ : ι → ℝ} {gZ1 EZ1 : κ → ℝ}
    (hkB : 0 < kB) (hT : 0 < T) (hme : 0 < me) (hh : 0 < h)
    (hgZ : ∀ k, 0 < gZ k) (hgZ1 : ∀ k, 0 < gZ1 k) :
    StrictAntiOn (electronDensityFromRatio kB T me h chi gZ EZ gZ1 EZ1) (Set.Ioi 0) := by
  intro a ha b hb hab
  have hS : 0 < sahaFactor kB T me h chi gZ EZ gZ1 EZ1 :=
    sahaFactor_pos hkB hT hme hh hgZ hgZ1
  unfold electronDensityFromRatio
  exact (div_lt_div_iff_of_pos_left hS (Set.mem_Ioi.mp hb) (Set.mem_Ioi.mp ha)).mpr hab

/-- **Saha-plot log identity.** `log S(T)` is affine in `1/(k_B T)` with slope `−χ`, plus a
`(3/2)·log(bracket)` term, plus `log 2` and the partition-function difference — the ionization
analogue of the Boltzmann plot, underlying linearized Saha-plot fitting. -/
theorem log_sahaFactor [Nonempty ι] [Nonempty κ] {kB T me h chi : ℝ}
    {gZ EZ : ι → ℝ} {gZ1 EZ1 : κ → ℝ}
    (hkB : 0 < kB) (hT : 0 < T) (hme : 0 < me) (hh : 0 < h)
    (hgZ : ∀ k, 0 < gZ k) (hgZ1 : ∀ k, 0 < gZ1 k) :
    Real.log (sahaFactor kB T me h chi gZ EZ gZ1 EZ1)
      = Real.log 2
        + (Real.log (partitionFunction kB T gZ1 EZ1)
            - Real.log (partitionFunction kB T gZ EZ))
        + (3 / 2 : ℝ) * Real.log (thermalBracket kB T me h)
        - chi / (kB * T) := by
  have hbr : 0 < thermalBracket kB T me h := thermalBracket_pos hkB hT hme hh
  have hUz1 : 0 < partitionFunction kB T gZ1 EZ1 := partitionFunction_pos hgZ1
  have hUz : 0 < partitionFunction kB T gZ EZ := partitionFunction_pos hgZ
  have hUratio : 0 < partitionFunction kB T gZ1 EZ1 / partitionFunction kB T gZ EZ :=
    div_pos hUz1 hUz
  have hrpow : 0 < (thermalBracket kB T me h) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hbr _
  unfold sahaFactor
  rw [Real.log_mul (mul_pos (mul_pos (by norm_num) hUratio) hrpow).ne' (Real.exp_ne_zero _),
      Real.log_mul (mul_pos (by norm_num) hUratio).ne' hrpow.ne',
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hUratio.ne',
      Real.log_div hUz1.ne' hUz.ne', Real.log_rpow hbr, Real.log_exp]
  ring

end SahaUpstream
