/-
Copyright (c) 2026 Brian Squires. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Squires
-/
import Mathlib
import CflibsFormal.Inverse
import CflibsFormal.Identifiability
import CflibsFormal.ForwardMap
import CflibsFormal.Closure

/-!
# CF-LIBS formalization — multi-line / many-element composition identifiability

This module **strengthens** `Inverse.general_identifiability` by *removing its `hTratio`
caveat*. There, the observation map `observe` exposed only **one** line per species, so
the temperature was pinned by a *separately supplied* two-line Boltzmann ratio
hypothesis `hTratio` rather than being extracted from the observations themselves.
Its other two caveats remain here: the statement is over the shared-catalog
`PlasmaParams` (one level table and one partition function for every species, a modeling
reduction; published scope REDUCED), and it assumes a known, equal calibration `hFeq`.

Here we define a richer observation map `observeMulti` that additionally exposes, for a
designated **anchor species** `s₀`, **two** lines on a distinct-energy level pair
`(i, j)`. The temperature is then recovered **from the observations**: the ratio of the
two anchor observables (both components of the single observation vector) supplies the
input to the already-proven `temperature_identifiability` — no extra `hTratio` is needed.

* `MultiObsIndex species := species ⊕ Bool` — the index type of the richer observation
  vector: `Sum.inl s` is species `s`'s single emitting line (exactly `observe`),
  `Sum.inr false` / `Sum.inr true` are the two anchor lines of `s₀` on levels `i` / `j`.
* `observeMulti` — the richer forward map, reusing `ForwardMap.lineIntensity` verbatim.
* `observeMulti_inl` — the bridge lemma (`rfl`) identifying the non-anchor component with
  `Inverse.observe`.
* `compositionIdentifiable` — the strengthened uniqueness theorem: equal `observeMulti`
  observations (with matched calibration/atomic data) force **equal temperature** (now
  extracted from the anchor pair inside the observations) **and equal full composition**.
* `compositionIdentifiable_T` — the value-level corollary delivering `p₁.T = p₂.T` from
  *any* valid anchor; this is the reusable, content-bearing anchor-independence
  statement (the temperature is recovered from any distinct-energy anchor pair).

Nothing forward or any identifiability *core* is reproven: the temperature step routes
through `temperature_identifiability` (Real.exp injectivity) and the per-species density
step through `density_identifiability`, exactly as in `general_identifiability`, but with
the temperature ratio now sourced from the observation vector `hObs`.
-/

namespace CflibsFormal

open Finset Real
open scoped BigOperators

variable {species levelIndex : Type*}

/-- A two-valued tag selecting one of the **two anchor lines** of the designated anchor
species `s₀`. `false ↦ lower-tagged line i`, `true ↦ upper-tagged line j`. Using `Bool`
(two elements, `DecidableEq`) keeps the anchor-pair observation index concrete and the
case analysis trivial. -/
abbrev AnchorLine : Type := Bool

/-- Index type of the **richer observation vector**: a tagged sum of
* `Sum.inl s` — the single emitting line of species `s` (the one-line-per-species data,
  exactly as in `Inverse.observe`), and
* `Sum.inr b` — one of the two anchor lines (`b : AnchorLine`) of the designated anchor
  species `s₀` on a distinct-energy level pair `(i, j)`.

As a single function type `MultiObsIndex species → ℝ`, equality of two observation
vectors is just `congrFun`, with no `Prod`/`Sum` decomposition lemmas needed. Kept as an
`abbrev` (reducible) so `congrFun` typechecks pointwise without an index `Fintype`. -/
abbrev MultiObsIndex (species : Type*) : Type _ := species ⊕ AnchorLine

/-- **Richer observation / forward map.** Extends `Inverse.observe` so the temperature is
recovered *from the observations themselves*. The observable at:
* `Sum.inl s` is the integrated intensity of species `s`'s single emitting line `emit s`
  — identical to `observe kB Fcal emit p s`;
* `Sum.inr false` is the anchor species `s₀`'s line on level `i`;
* `Sum.inr true`  is the anchor species `s₀`'s line on level `j`.

The two anchor observables expose a same-species, distinct-energy line pair `(i, j)` for
`s₀`, so their *ratio* fixes `T` via `temperature_identifiability` — no separately
supplied `hTratio` is needed. Reuses `ForwardMap.lineIntensity` verbatim everywhere. -/
noncomputable def observeMulti [Fintype levelIndex]
    (kB Fcal : ℝ) (emit : species → levelIndex) (s₀ : species) (i j : levelIndex)
    (p : PlasmaParams species levelIndex) : MultiObsIndex species → ℝ
  | Sum.inl s => lineIntensity kB p.T (p.N s) Fcal p.g p.E p.A (emit s)
  | Sum.inr false => lineIntensity kB p.T (p.N s₀) Fcal p.g p.E p.A i
  | Sum.inr true  => lineIntensity kB p.T (p.N s₀) Fcal p.g p.E p.A j

/-- The non-anchor component of `observeMulti` is exactly the one-line `observe`
observable, so all reasoning about per-species densities reduces to the existing
`Inverse.observe` / `density_identifiability` machinery. Proof: `rfl` (both unfold to the
same `lineIntensity` application). -/
lemma observeMulti_inl [Fintype levelIndex]
    (kB Fcal : ℝ) (emit : species → levelIndex) (s₀ : species) (i j : levelIndex)
    (p : PlasmaParams species levelIndex) (s : species) :
    observeMulti kB Fcal emit s₀ i j p (Sum.inl s) = observe kB Fcal emit p s := rfl

variable [Fintype species]

/-- **Multi-line / many-element composition identifiability — strengthening of
`general_identifiability`.**

If two admissible `PlasmaParams` produce **equal `observeMulti` observations** (matched
calibration `hFeq` and atomic data `hEeq`, `hgeq`, `hAeq`), with the anchor pair `(i, j)`
of the anchor species `s₀` having distinct energies (`hE₁`), then they have **equal
temperature** and **equal full composition** `∀ s, trueComposition p₁ s = trueComposition
p₂ s`.

*The `hTratio` caveat of `general_identifiability` is removed.* The temperature equality is now
extracted **from `hObs`**: the two anchor observables `observeMulti … (Sum.inr false)` and
`(Sum.inr true)` are exactly `p`'s `lineIntensity` on levels `i` and `j` of the same
anchor species `s₀`, so projecting `hObs` at those indices and taking the ratio supplies
the hypothesis of the proven `temperature_identifiability` — no separately supplied
`hTratio`. The composition equality is extracted per-species from the `Sum.inl`
components (`observeMulti_inl` + `density_identifiability`), exactly as in
`general_identifiability`.

Non-vacuous: `species = Fin 1`, `levelIndex = Fin 2`, `kB = Fcal₁ = Fcal₂ = 1`,
`emit = fun _ => 0`, `s₀ = 0`, `i = 0`, `j = 1`, `p₁ = p₂` with `T = 1`,
`N = g = A = fun _ => 1`, `E = ![0,1]`. Then `E i = 0 ≠ 1 = E j`, `Admissible` holds, the
data/calibration equalities are `rfl`, and `hObs` is `rfl`. The content (for differing
parameter sets) is genuine: the anchor-ratio equality forces `T₁ = T₂` only via
`Real.exp` injectivity, and the per-species equality forces equal `N s` via positive
constant cancellation — neither is `rfl`. This is an injectivity statement about the
forward map; `trueComposition` is the estimator-independent target, never defined to
equal a hypothesis.

*Model and calibration.* The statement is over `PlasmaParams`: one level catalog, hence one
partition function `U(T)`, serves every species. That is a modeling reduction (real elements
have their own `U_s(T)`), so the published scope is REDUCED. `hFeq` assumes both parameter
sets carry the same known calibration, which is not the calibration-free setting; it is
stronger than the conclusion needs, since `Fcal` cancels in the anchor ratio and a calibration
mismatch only rescales every `N s` by `Fcal₂/Fcal₁`, which closure removes. That `hFeq`-free
version is not formalized in this repository. -/
theorem compositionIdentifiable
    [Fintype levelIndex] [Nonempty levelIndex]
    {kB Fcal₁ Fcal₂ : ℝ} {emit : species → levelIndex}
    {p₁ p₂ : PlasmaParams species levelIndex}
    (s₀ : species) (i j : levelIndex)
    (hkB : 0 < kB) (hFcal₁ : 0 < Fcal₁) (hFcal₂ : 0 < Fcal₂)
    (ha₁ : p₁.Admissible) (ha₂ : p₂.Admissible)
    (hE₁ : p₁.E i ≠ p₁.E j)
    (hEeq : p₁.E = p₂.E) (hgeq : p₁.g = p₂.g) (hAeq : p₁.A = p₂.A)
    (hFeq : Fcal₁ = Fcal₂)
    (hObs : observeMulti kB Fcal₁ emit s₀ i j p₁
          = observeMulti kB Fcal₂ emit s₀ i j p₂) :
    p₁.T = p₂.T ∧ (∀ s, trueComposition p₁ s = trueComposition p₂ s) := by
  obtain ⟨hT₁, hN₁, hg₁, hA₁⟩ := ha₁
  obtain ⟨hT₂, hN₂, hg₂, hA₂⟩ := ha₂
  -- (1) Temperature: the two anchor observables come straight from `hObs`.
  have hI_i :
      lineIntensity kB p₁.T (p₁.N s₀) Fcal₁ p₁.g p₁.E p₁.A i
        = lineIntensity kB p₂.T (p₂.N s₀) Fcal₂ p₂.g p₂.E p₂.A i :=
    congrFun hObs (Sum.inr false)
  have hI_j :
      lineIntensity kB p₁.T (p₁.N s₀) Fcal₁ p₁.g p₁.E p₁.A j
        = lineIntensity kB p₂.T (p₂.N s₀) Fcal₂ p₂.g p₂.E p₂.A j :=
    congrFun hObs (Sum.inr true)
  -- Build the anchor ratio `I_j / I_i = I_j' / I_i'` from the two anchor equalities.
  have hTratio :
      lineIntensity kB p₁.T (p₁.N s₀) Fcal₁ p₁.g p₁.E p₁.A j
          / lineIntensity kB p₁.T (p₁.N s₀) Fcal₁ p₁.g p₁.E p₁.A i
        = lineIntensity kB p₂.T (p₂.N s₀) Fcal₂ p₂.g p₂.E p₂.A j
          / lineIntensity kB p₂.T (p₂.N s₀) Fcal₂ p₂.g p₂.E p₂.A i :=
    congrArg₂ (· / ·) hI_j hI_i
  -- Bring the right side to share p₁'s atomic data, leaving T and N to differ.
  rw [← hgeq, ← hEeq, ← hAeq] at hTratio
  have hT : p₁.T = p₂.T :=
    temperature_identifiability hkB hT₁ hT₂ hg₁ (hN₁ s₀) (hN₂ s₀)
      hFcal₁ hFcal₂ hA₁ i j hE₁ hTratio
  refine ⟨hT, ?_⟩
  -- (2) Composition: each species' emitting-line intensity matches (via `Sum.inl`).
  have hNeq : ∀ s, p₁.N s = p₂.N s := by
    intro s
    have hObs_s :
        lineIntensity kB p₁.T (p₁.N s) Fcal₁ p₁.g p₁.E p₁.A (emit s)
          = lineIntensity kB p₂.T (p₂.N s) Fcal₂ p₂.g p₂.E p₂.A (emit s) := by
      have := congrFun hObs (Sum.inl s)
      simpa only [observeMulti] using this
    rw [← hT, ← hFeq, ← hgeq, ← hEeq, ← hAeq] at hObs_s
    exact density_identifiability hg₁ hFcal₁ (emit s) (hA₁ (emit s)) hObs_s
  have hNfun : p₁.N = p₂.N := funext hNeq
  intro s
  simp only [trueComposition, hNfun]

set_option linter.unusedFintypeInType false in
/-- **Anchor-independence of the recovered temperature (value level).**

The temperature is recovered as `p₁.T = p₂.T` from *any* valid anchor `(s₀, i, j)` whose
energies are distinct (`hE₁`). This is the reusable, content-bearing form of
anchor-independence: a different valid anchor species / line pair discharges *the same*
physical conclusion `p₁.T = p₂.T`. The non-triviality is genuine — it routes through
`temperature_identifiability` (Real.exp injectivity), not `rfl`. (We deliberately do
*not* ship a proof-term equality between two `.1` projections: that would be closable by
`Prop` proof-irrelevance and carry no physics content.)

(`[Fintype species]` is retained because it is required by `compositionIdentifiable`,
whose first projection this corollary returns.)

Scope: it inherits `compositionIdentifiable`'s hypotheses, including the shared-catalog
`PlasmaParams` (published REDUCED) and `hFeq`. `hFeq` is not needed for the temperature
alone, since `Fcal` cancels in the anchor ratio, but it is part of this statement. -/
theorem compositionIdentifiable_T
    [Fintype levelIndex] [Nonempty levelIndex]
    {kB Fcal₁ Fcal₂ : ℝ} {emit : species → levelIndex}
    {p₁ p₂ : PlasmaParams species levelIndex}
    (s₀ : species) (i j : levelIndex)
    (hkB : 0 < kB) (hFcal₁ : 0 < Fcal₁) (hFcal₂ : 0 < Fcal₂)
    (ha₁ : p₁.Admissible) (ha₂ : p₂.Admissible)
    (hE₁ : p₁.E i ≠ p₁.E j)
    (hEeq : p₁.E = p₂.E) (hgeq : p₁.g = p₂.g) (hAeq : p₁.A = p₂.A)
    (hFeq : Fcal₁ = Fcal₂)
    (hObs : observeMulti kB Fcal₁ emit s₀ i j p₁
          = observeMulti kB Fcal₂ emit s₀ i j p₂) :
    p₁.T = p₂.T :=
  (compositionIdentifiable s₀ i j hkB hFcal₁ hFcal₂ ha₁ ha₂ hE₁ hEeq hgeq hAeq hFeq hObs).1

end CflibsFormal
