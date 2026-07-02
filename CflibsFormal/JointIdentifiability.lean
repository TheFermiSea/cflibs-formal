/-
Copyright (c) 2026 Brian Squires. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Squires
-/
import Mathlib
import CflibsFormal.Inverse

/-!
# CF-LIBS formalization — Part 7: joint (temperature, composition) identifiability

This module closes the *honest caveat* of `Inverse.general_identifiability`. There the
temperature equality `T₁ = T₂` was **not** extracted from the observations `hObs`; it was
delivered by a separately *assumed* two-line Boltzmann-ratio hypothesis `hTratio` on a
distinct-energy pair. Physically the CF-LIBS solver never assumes that ratio — it *measures*
at least two lines per species and fits `(T, composition)` simultaneously. This module models
exactly that: a **two-line** observation map, from which the temperature is now *derived*.

* `observe₂` — the two-line observation map: for species `s` it reports the ordered pair of
  integrated intensities of two emitting lines `emitA s`, `emitB s`, reusing `Inverse.observe`
  (hence `ForwardMap.lineIntensity`) verbatim on each component.
* `joint_identifiability` — **the main theorem.** For admissible `p₁, p₂` sharing calibration
  and atomic data, if their two-line observations are *equal* and *some* species `s₀` carries a
  distinct-energy line pair (`p₁.E (emitA s₀) ≠ p₁.E (emitB s₀)`), then `T₁ = T₂` **and** the
  compositions agree — with **no** assumed ratio hypothesis. The temperature is now extracted
  from the two-line observations at `s₀` (the two matched line intensities furnish the ratio
  equality that `temperature_identifiability` consumes), discharging the `hTratio` caveat of
  `general_identifiability`. Composition then follows per species from `density_identifiability`
  exactly as in `general_identifiability`.

Both `temperature_identifiability` and `density_identifiability` are reused verbatim (neither is
reproven). *Honest scope:* two lines per species is the **minimal** multi-line case; the full
`n`-line ordinary-least-squares slope fit and its own identifiability live in the
`Alt`/`LeastSquares` layer and are not addressed here.
-/

namespace CflibsFormal

open Finset Real
open scoped BigOperators

variable {species levelIndex : Type*}

/-- **Two-line observation / forward map.** For species `s` the observable is the ordered pair
of integrated intensities of its two emitting lines, whose upper levels are `emitA s` and
`emitB s`:
`observe₂ kB Fcal emitA emitB p s = (observe kB Fcal emitA p s, observe kB Fcal emitB p s)`.

Each component reuses `Inverse.observe` (hence `ForwardMap.lineIntensity`) verbatim; `kB` is
Boltzmann's constant and `Fcal` the shared instrument/geometry calibration constant. This is the
minimal multi-line data the CF-LIBS solver fits `(T, composition)` on: two distinct-energy lines
on a single species already pin the temperature through the two-line Boltzmann ratio, which the
single-line `observe` cannot do. -/
noncomputable def observe₂ [Fintype levelIndex] (kB Fcal : ℝ)
    (emitA emitB : species → levelIndex) (p : PlasmaParams species levelIndex)
    (s : species) : ℝ × ℝ :=
  (observe kB Fcal emitA p s, observe kB Fcal emitB p s)

variable [Fintype species]

/-- **Joint (temperature, composition) identifiability — discharging the `hTratio` caveat.**

Under explicit nondegeneracy (positive `T`, `N`, `g`, `A` via `Admissible`; two emitting lines
per species via `emitA`, `emitB`), if two admissible parameter sets produce **equal two-line
observations** `hObs`, share calibration (`hFeq`) and atomic data (`hgeq`, `hEeq`, `hAeq`), and
**some** species `s₀` carries a distinct-energy line pair (`hEdist`), then they have **equal
temperature** and **equal composition** — with **no assumed ratio hypothesis**.

This is the honest advance over `general_identifiability`: there `T₁ = T₂` rested on an
*assumed* two-line Boltzmann ratio `hTratio` that `observe` (one line per species) could not
supply. Here the two-line map `observe₂` *delivers* that ratio from the data: at `s₀` the
paired observation forces both line intensities to match individually, so their ratio matches
too (equal numerators over equal denominators), and `temperature_identifiability` extracts
`T₁ = T₂` from that ratio alone. Composition then follows exactly as in `general_identifiability`:
once temperatures are matched, `density_identifiability` forces equal `N s` for every species
(hence equal closure composition). So `(T, composition)` is jointly identifiable from the
observations alone, given ≥ 2 distinct-energy lines on at least one species.

Assembled strictly from the already-proven `temperature_identifiability` and
`density_identifiability` (neither reproven). *Honest scope:* two lines per species is the
minimal multi-line case; the full `n`-line ordinary-least-squares slope fit is the
`Alt`/`LeastSquares` layer's concern.

Non-vacuous: `species = Fin 1`, `levelIndex = Fin 2`, `kB = Fcal₁ = Fcal₂ = 1`,
`emitA = fun _ => 0`, `emitB = fun _ => 1`, `p₁ = p₂` with `T = N = g = A = 1`, `E = ![0,1]`;
then `E (emitA 0) ≠ E (emitB 0)` (`0 ≠ 1`), `Admissible` holds, and the observation equality is
reflexive (see the witness below). The content for differing parameter sets is that `hObs` at
`s₀` forces `T₁ = T₂` via `Real.exp` injectivity and equal composition via positive-constant
cancellation — neither is `rfl`. -/
theorem joint_identifiability
    [Fintype levelIndex] [Nonempty levelIndex]
    {kB Fcal₁ Fcal₂ : ℝ} {emitA emitB : species → levelIndex}
    {p₁ p₂ : PlasmaParams species levelIndex}
    (s₀ : species)
    (hkB : 0 < kB) (hFcal₁ : 0 < Fcal₁) (hFcal₂ : 0 < Fcal₂)
    (ha₁ : p₁.Admissible) (ha₂ : p₂.Admissible)
    (hEdist : p₁.E (emitA s₀) ≠ p₁.E (emitB s₀))
    (hEeq : p₁.E = p₂.E) (hgeq : p₁.g = p₂.g) (hAeq : p₁.A = p₂.A)
    (hFeq : Fcal₁ = Fcal₂)
    (hObs : observe₂ kB Fcal₁ emitA emitB p₁ = observe₂ kB Fcal₂ emitA emitB p₂) :
    p₁.T = p₂.T ∧ (∀ s, trueComposition p₁ s = trueComposition p₂ s) := by
  obtain ⟨hT₁, hN₁, hg₁, hA₁⟩ := ha₁
  obtain ⟨hT₂, hN₂, _, _⟩ := ha₂
  -- (1) Temperature: read off both line intensities at the distinct-energy species `s₀`.
  have h₀ := congrFun hObs s₀
  simp only [observe₂, observe, Prod.mk.injEq] at h₀
  obtain ⟨hA0, hB0⟩ := h₀
  -- The two matched intensities give an intensity *ratio* equality — no assumed hypothesis.
  have hratio :
      lineIntensity kB p₁.T (p₁.N s₀) Fcal₁ p₁.g p₁.E p₁.A (emitB s₀)
          / lineIntensity kB p₁.T (p₁.N s₀) Fcal₁ p₁.g p₁.E p₁.A (emitA s₀)
        = lineIntensity kB p₂.T (p₂.N s₀) Fcal₂ p₂.g p₂.E p₂.A (emitB s₀)
          / lineIntensity kB p₂.T (p₂.N s₀) Fcal₂ p₂.g p₂.E p₂.A (emitA s₀) := by
    rw [hA0, hB0]
  -- Bring the right-hand ratio to share `p₁`'s atomic data, then apply temperature
  -- identifiability to the distinct-energy pair `(emitA s₀, emitB s₀)`.
  rw [← hgeq, ← hEeq, ← hAeq] at hratio
  have hT : p₁.T = p₂.T :=
    temperature_identifiability hkB hT₁ hT₂ hg₁ (hN₁ s₀) (hN₂ s₀)
      hFcal₁ hFcal₂ hA₁ (emitA s₀) (emitB s₀) hEdist hratio
  refine ⟨hT, ?_⟩
  -- (2) Composition: per species, the first line intensity matches; bring both sides to
  -- share `p₁`'s temperature, calibration and atomic data, then `density_identifiability`.
  have hNeq : ∀ s, p₁.N s = p₂.N s := by
    intro s
    have hs := congrFun hObs s
    simp only [observe₂, observe, Prod.mk.injEq] at hs
    obtain ⟨hAs, _⟩ := hs
    rw [← hT, ← hFeq, ← hgeq, ← hEeq, ← hAeq] at hAs
    exact density_identifiability hg₁ hFcal₁ (emitA s) (hA₁ (emitA s)) hAs
  -- (3) Equal densities ⇒ equal closure composition.
  have hNfun : p₁.N = p₂.N := funext hNeq
  intro s
  simp only [trueComposition, hNfun]

/-! ### Non-vacuity witness for `joint_identifiability`

A concrete `species = Fin 1`, `levelIndex = Fin 2` instance with two distinct-energy emitting
lines (`emitA = fun _ => 0`, `emitB = fun _ => 1`, energies `E = ![0,1]`, so
`E (emitA 0) ≠ E (emitB 0)`) shows the full hypothesis bundle of `joint_identifiability` is
jointly satisfiable: taking `p₁ = p₂` makes the shared-data and observation equalities reflexive
while `Admissible` and the distinct-energy pair genuinely hold, and the theorem then delivers its
conclusion. -/

private def nvJidEmitA : Fin 1 → Fin 2 := fun _ => 0
private def nvJidEmitB : Fin 1 → Fin 2 := fun _ => 1
private def nvJidE : Fin 2 → ℝ := ![0, 1]

private def nvJidParams : PlasmaParams (Fin 1) (Fin 2) where
  T := 1
  N := fun _ => 1
  g := fun _ => 1
  E := nvJidE
  A := fun _ => 1

/-- **Non-vacuity for `joint_identifiability`.** The hypothesis bundle is jointly satisfiable:
the `Fin 1` / `Fin 2` instance above is `Admissible`, carries a genuine distinct-energy line
pair (`E (emitA 0) = 0 ≠ 1 = E (emitB 0)`), and (with `p₁ = p₂`) satisfies the shared-data and
observation equalities reflexively — so `joint_identifiability` applies and yields its
conclusion. -/
example :
    nvJidParams.T = nvJidParams.T ∧
      (∀ s, trueComposition nvJidParams s = trueComposition nvJidParams s) := by
  have hadm : nvJidParams.Admissible :=
    ⟨by norm_num [nvJidParams], fun _ => by norm_num [nvJidParams],
      fun _ => by norm_num [nvJidParams], fun _ => by norm_num [nvJidParams]⟩
  have hE : nvJidParams.E (nvJidEmitA (0 : Fin 1)) ≠ nvJidParams.E (nvJidEmitB 0) := by
    norm_num [nvJidParams, nvJidE, nvJidEmitA, nvJidEmitB]
  exact joint_identifiability (0 : Fin 1) one_pos one_pos one_pos hadm hadm hE
    rfl rfl rfl rfl rfl

end CflibsFormal
