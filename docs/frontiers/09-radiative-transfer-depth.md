# Frontier 09 — Radiative transfer beyond the uniform slab

*Planning dossier. No Lean edited; every current-state claim anchored to a real
declaration, every mathlib claim grepped against `.lake/packages/mathlib` (v4.31.0).*

---

## 1. The formal obstacle

The repo has exactly **two** radiative-transfer (RT) kernels, and both are hard-coded
special cases of the depth-integrated formal solution:

- **One uniform zone** — `slabIntensity S tau = S * (1 - Real.exp (-tau))`
  (`SelfAbsorption.lean:184`), with `slabIntensity_le_thin` and
  `slabIntensity_eq_thin_mul_SA` deriving the escape factor `SA(τ)` from it. This is the
  emergent intensity of a *single* homogeneous LTE layer.
- **Two zones (core + shell)** — `emergentIntensity Score Sshell τc τs
  = Score·(1 − e^{−τc})·e^{−τs} + Sshell·(1 − e^{−τs})` (`SelfReversal.lean:59`), the
  Cowan–Dieke two-layer model, with the dip criterion
  `emergentIntensity_strictAnti_shell` (`SelfReversal.lean`).

The curve-of-growth layer (`CurveOfGrowth.lean`, `EquivalentWidth.lean`) and the
spatially-resolved layer (`SpatialForward.lean`, discrete Abel / onion-peeling) all inherit
these two kernels or work in a different (chord-geometry) variable. `SpatialForward` even
frames the single zone as the `N = 1` case of an `N`-shell system — but that generalization
is about *chord geometry* (`Matrix.mulVec` invertibility), **not** about the depth-stacked
RT source integral.

What the repo **cannot state today** is the general **depth-structured formal solution**

```
I(τ) = ∫₀^τ S(t) · exp(−(τ − t)) dt          (source S varying along optical depth t)
```

nor its two most useful discretizations/evaluations:

> There is no `rtEmergent`/`rtFormal` definition folding an *arbitrary* stack of `N`
> homogeneous zones (the two-zone `emergentIntensity` is the `N = 2` base case, hand-written
> and not recursive); there is no theorem that a **non-uniform** source is sandwiched
> `S_min·(1−e^{−τ}) ≤ I ≤ S_max·(1−e^{−τ})` (the "uniform slab is the extremal case"
> statement); and there is no exact evaluation of the **linear-in-τ (Eddington–Barbier)**
> source, `∫₀^τ (S₀+S₁t)e^{−(τ−t)}dt`.

The physical consequence the repo therefore cannot express: **depth structure — the hot
core / cool periphery temperature gradient that is the dominant LIBS reality (Gornushkin
2010; Zhang 2022 [PROPOSED ADDITION — needs vetting]) — is currently invisible to the forward
model beyond the single hand-coded shell.** The target objects we cannot yet write:

```
def rtEmergent : List (ℝ × ℝ) → ℝ                         -- N-zone stacked emission
theorem rtEmergent_sandwich … : Smin*(1 - exp(-T)) ≤ rtEmergent zs ∧ rtEmergent zs ≤ Smax*(1 - exp(-T))
theorem rtFormalLinear … : (∫ t in 0..τ, (S₀+S₁*t)*Real.exp (-(τ-t))) = S₀*(1-exp(-τ)) + S₁*(τ-1+exp(-τ))
```

matching the repo idioms (`slabIntensity`/`emergentIntensity` for the kernels; the
`intervalIntegral` + `integral_mono` machinery already exercised in `EquivalentWidth.lean`).

---

## 2. Mathematical landscape

### 2.1 The `N`-zone piecewise-constant recursion — CONFIRMED, and it subsumes both existing kernels

Discretize the formal solution into `N` homogeneous zones ordered **deepest-first** (zone
`0` farthest from the observer, zone `N−1` at the surface), each carrying a source `Sₖ` and
an optical depth `τₖ ≥ 0`. Photons from the accumulated intensity `I` entering zone `k` are
attenuated by `e^{−τₖ}` and the zone adds its own emission `Sₖ(1−e^{−τₖ})`:

```
rtStep I (S, τ) := I · e^{−τ} + S · (1 − e^{−τ})          -- one homogeneous zone
rtEmergent zs   := zs.foldl rtStep 0                       -- fold over the ordered stack
```

This is the standard operator-splitting/short-characteristics discretization of
`I(τ)=∫₀^τ S(t)e^{−(τ−t)}dt` with piecewise-constant `S`. **Two base-case identities close
by definitional unfolding**, proving the fold is a *strict generalization*:

- **`rtEmergent [(S,τ)] = slabIntensity S τ`.** `foldl rtStep 0 [(S,τ)] = rtStep 0 (S,τ)
  = 0·e^{−τ} + S(1−e^{−τ}) = S(1−e^{−τ})`. One `simp [rtEmergent, rtStep, slabIntensity]`.
- **`rtEmergent [(Score,τc),(Sshell,τs)] = emergentIntensity Score Sshell τc τs`.**
  `foldl rtStep 0 [c,s] = rtStep (rtStep 0 c) s = rtStep (Score(1−e^{−τc})) s
  = Score(1−e^{−τc})e^{−τs} + Sshell(1−e^{−τs})`, which is `emergentIntensity`
  verbatim (`SelfReversal.lean:59`). One `simp` + `ring`.

So the two hand-coded kernels become the `N=1` and `N=2` instances of one recursive object —
exactly the `singleZone_identifiable`-from-`chord_profile_identifiable` framing already
established in `SpatialForward.lean:178`. [Corpus grounding: multi-layer / two-layer
core-corona stratification is the standard LIBS non-uniformity treatment — Cowan–Dieke 1948
(vetted). Zhang 2022 (core-corona self-reversal) and Bultel 2019 (two-uniform-layer shock
model) both surfaced from the CF-LIBS corpus but are **PROPOSED ADDITIONS — need vetting**
before use; see §6. They are supporting context only and are not milestone citations.]

### 2.2 The monotone sandwich `S_min(1−e^{−T}) ≤ I ≤ S_max(1−e^{−T})` — CONFIRMED, telescoping induction, no calculus

This is the headline and it is **derivative-free**. Let `T = Σₖ τₖ` be the total optical
depth. Claim: if every zone source lies in `[S_min, S_max]` and every `τₖ ≥ 0`, then
`S_min(1−e^{−T}) ≤ rtEmergent zs ≤ S_max(1−e^{−T})`.

**Upper bound, by list induction with a generalized accumulator.** Prove the invariant

```
∀ zs I₀ T₀,  I₀ ≤ S_max·(1 − e^{−T₀})  →  (∀ z ∈ zs, z.1 ≤ S_max ∧ 0 ≤ z.2)
           →  zs.foldl rtStep I₀ ≤ S_max·(1 − e^{−(T₀ + sumDepth zs)})
```

- **Base** `zs = []`: `foldl = I₀ ≤ S_max(1−e^{−T₀}) = S_max(1−e^{−(T₀+0)})`. ✓
- **Step** `zs = (S,τ)::rest`: `foldl rtStep I₀ ((S,τ)::rest) = foldl rtStep (rtStep I₀ (S,τ)) rest`.
  The single zone satisfies

  ```
  rtStep I₀ (S,τ) = I₀·e^{−τ} + S(1−e^{−τ})
                 ≤ S_max(1−e^{−T₀})·e^{−τ} + S_max(1−e^{−τ})     [I₀ ≤ S_max(1−e^{−T₀}), e^{−τ}≥0; S≤S_max, 1−e^{−τ}≥0]
                 = S_max·[e^{−τ} − e^{−(T₀+τ)} + 1 − e^{−τ}]
                 = S_max·(1 − e^{−(T₀+τ)}),
  ```

  the exact hypothesis needed to apply the IH with `T₀' = T₀+τ`; then `sumDepth((S,τ)::rest)
  = τ + sumDepth rest` closes it. The single-zone step is the **telescoping identity**
  `(1−e^{−T₀})e^{−τ} + (1−e^{−τ}) = 1 − e^{−(T₀+τ)}` — pure `Real.exp_add`/`ring`.

- **Instantiate** `I₀ = 0`, `T₀ = 0`: `0 ≤ S_max(1−e^0)=0` ✓, giving
  `rtEmergent zs ≤ S_max(1−e^{−T})`.

**Lower bound** is the mirror image with `S_min` (multiply through by `e^{−τ}≥0` and
`1−e^{−τ}≥0`, both direction-preserving) — **and it needs no sign hypothesis on `S_min`**
(works for any real `S_min ≤ Sₖ`), because the only nonnegativity used is of the *weights*
`e^{−τ}` and `1−e^{−τ}`, never of the sources. The two exp facts —
`Real.exp_pos` and `1 − e^{−τ} ≥ 0` (from `Real.exp_le_one_iff`) — are already used verbatim
in `emergentIntensity_nonneg` (`SelfReversal.lean`) and `selfAbsorptionFactor_le_one`.

**Physical reading (the whole point):** the emergent intensity of *any* depth-structured LTE
column is bracketed by the uniform slabs at its coldest and hottest source values, sharing the
same total-depth escape factor `(1−e^{−T})`. Depth structure can only move `I` *within* that
band — it cannot brighten past `S_max(1−e^{−T})` nor darken below `S_min(1−e^{−T})`. This is
the rigorous bound behind "spatial non-uniformity biases the extracted temperature"
(Gornushkin 2010): the bias is confined, and its size is `(S_max−S_min)(1−e^{−T})`.

### 2.3 "Uniform slab is the extremal case" — CONFIRMED, squeeze corollary

Instantiate §2.2 with `S_min = S_max = S` (all zones share one source): the two bounds
collapse and `rtEmergent zs = S(1−e^{−T}) = slabIntensity S T`. So the uniform slab is
*exactly* the degenerate (zero-width band) case of the sandwich — the extremal/boundary
configuration, and the only one where depth structure carries no information. Provable
either as a squeeze from §2.2 (`le_antisymm`) or by a direct one-line induction reusing the
telescoping identity. Matches `selfReversal_uniformSource` (`SelfReversal.lean`), the `S_shell
= S_core` collapse, and generalizes it to `N` zones.

### 2.4 The formal integral solution and the linear (Eddington–Barbier) source — CONFIRMED as an `intervalIntegral` evaluation

Define the continuous formal solution as an interval integral (the depth `t` runs `0..τ`):

```
rtFormal S τ := ∫ t in (0:ℝ)..τ, S t * Real.exp (−(τ − t))
```

- **Constant source recovers the slab.** For `S t = S₀`:
  `rtFormal (fun _ => S₀) τ = S₀·∫₀^τ e^{−(τ−t)}dt = S₀·e^{−τ}·∫₀^τ e^{t}dt
  = S₀·e^{−τ}·(e^τ − 1) = S₀(1 − e^{−τ}) = slabIntensity S₀ τ`. Uses
  `integral_const_mul` + `integral_exp` (`∫ₐᵇ eˣ = eᵇ−eᵃ`) after pulling out `e^{−τ}`
  via `integral_comp_sub_left`/`ring`. This ties the *continuous* solution back to the
  audited kernel, exactly as `slabIntensity_eq_thin_mul_SA` ties the kernel to `SA`.

- **Linear-in-τ source — the exact Eddington–Barbier evaluation.** For `S t = S₀ + S₁·t`,

  ```
  ∫₀^τ (S₀ + S₁ t) e^{−(τ−t)} dt = S₀(1 − e^{−τ}) + S₁(τ − 1 + e^{−τ}).
  ```

  **Proof by FTC-2** (`intervalIntegral.integral_eq_sub_of_hasDerivAt`): the antiderivative is
  `G(t) = (S₀ − S₁ + S₁ t)·e^{t−τ}`, and
  `G'(t) = S₁·e^{t−τ} + (S₀−S₁+S₁t)·e^{t−τ} = (S₀+S₁t)·e^{t−τ} = (S₀+S₁t)e^{−(τ−t)}`
  (a `HasDerivAt.mul` of the linear factor with `HasDerivAt.exp` of `t−τ`). Then
  `G(τ)−G(0) = (S₀−S₁+S₁τ)·e^0 − (S₀−S₁)·e^{−τ} = S₀(1−e^{−τ}) + S₁(τ−1+e^{−τ})` by `ring`.
  The `τ→∞` reading `I → S₀ + S₁(τ−1) = S(τ−1)` is the Eddington–Barbier law "emergent
  intensity ≈ source at optical depth 1 below the surface" — but see the **scope caveat in
  §5**: this is the *stellar-atmosphere* idealization (linear `S(τ)`), **not** a faithful LIBS
  profile, so the theorem must be tagged PURE-MATH / APPROXIMATION, never EXACT-for-LIBS.

### 2.5 Integral sandwich (continuous form) — CONFIRMED, `integral_mono`

The §2.2 bracket holds pointwise-under-the-integral too: for continuous `S` with
`S_min ≤ S t ≤ S_max` on `ℝ` (global bound; `integral_mono` compares the integrands as
functions on all of `ℝ`) and `τ ≥ 0`,
`S_min(1−e^{−τ}) ≤ rtFormal S τ ≤ S_max(1−e^{−τ})`. Because `e^{−(τ−t)} ≥ 0`, the integrand is
monotone in `S t`; `intervalIntegral.integral_mono` (needs `0 ≤ τ` + interval-integrability of
both sides, supplied by `Continuous.intervalIntegrable`) against the constant-source integrals
of §2.4 gives both sides. This is the continuous companion of the discrete sandwich and closes
the loop between `rtFormal` and `rtEmergent`.

### 2.6 Frequency-angle-coupled RT with depth-dependent `τ(λ)` — REFUTED (out of scope)

The genuinely-hard object — `I(λ) = ∫ S(t) e^{−(τ_λ(surface)−τ_λ(t))} dτ_λ` with
`τ_λ` a **Voigt/Stark line profile** integrated over depth — needs the Faddeeva/Voigt special
function (ABSENT from mathlib; it is the subject of Frontier 07's Ladenburg–Reiche deferral)
*coupled* with a depth integral. The corpus confirms this is where even production solvers
(OPSIAL, Hermann) abandon analytics and go line-by-line numerical. **Refuse** (see §5).

### 2.7 Non-LTE source coupling `S = (1−ε)J + εB` — REFUTED

If the source function is coupled to the mean intensity `J` (scattering), the formal solution
becomes an integro-differential Λ-operator fixed point — no closed form, no elementary
sandwich. Every result above assumes `S(t)` is a *given* function of depth (LTE, `S=B_λ(T(t))`
in physics, abstract `S` here). **Refuse** the coupled problem; keep `S` an input.

---

## 3. mathlib inventory

Everything the fold layer (§2.1–2.3) needs is elementary and already used in-repo; the
integral layer (§2.4–2.5) needs the `intervalIntegral` FTC/monotonicity toolkit, all present
and already exercised in `EquivalentWidth.lean`. **No new mathlib infrastructure.**

| Needed lemma | Status (grep-verified) |
|---|---|
| `∫ₐᵇ eˣ = eᵇ − eᵃ` | `integral_exp` (root namespace — NOT `Real.integral_exp`) — `Analysis/SpecialFunctions/Integrals/Basic.lean:235` |
| FTC-2 `∫ f' = F b − F a` | `intervalIntegral.integral_eq_sub_of_hasDerivAt` — `MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean:1150` |
| interval `integral_mono` | `intervalIntegral.integral_mono` — `MeasureTheory/Integral/IntervalIntegral/Basic.lean:1442` |
| pull constant out | `intervalIntegral.integral_const_mul` — `…/IntervalIntegral/Basic.lean:817` |
| `∫ c = (b−a)•c` | `intervalIntegral.integral_const` — `…/IntervalIntegral/Basic.lean:836` |
| shift variable `∫ f(d−x)` | `intervalIntegral.integral_comp_sub_left` — `…/IntervalIntegral/Basic.lean:1054` |
| continuity ⇒ integrable | `Continuous.intervalIntegrable` — `…/IntervalIntegral/Basic.lean:513` (ContinuousOn variant at :503) |
| product rule | `HasDerivAt.mul` — `Analysis/Calculus/Deriv/Mul.lean:268` |
| exp chain rule | `HasDerivAt.exp` — `Analysis/SpecialFunctions/ExpDeriv.lean:304` |
| `e^{a+b}=e^a e^b` | `Real.exp_add` — used throughout repo (`SelfReversal.lean:selfReversal_uniformSource`) |
| `0 < eˣ` / `1−e^{−τ}≥0` | `Real.exp_pos`, `Real.exp_le_one_iff` — used in `emergentIntensity_nonneg` |
| `1 − e^{−τ} ≤ τ` | `Real.one_sub_le_exp_neg` — used in `slabIntensity_le_thin` |
| `e^{−τ}` antitone | `Real.exp_le_exp` / `Real.exp_lt_exp` — used in `emergentIntensity_strictAnti_shell` |
| list fold unfold | `List.foldl_cons`, `List.foldl_nil` — core/`Data/List/Basic.lean` (simp) |
| list sum unfold | `List.sum_cons`, `List.sum_nil` — `Data/List` (for `sumDepth = (zs.map Prod.snd).sum`) |

Reusable **in-repo** anchors (all build-verified):

- `slabIntensity` (`SelfAbsorption.lean:184`) — `N=1` base case; `rtEmergent [(S,τ)]` must
  equal it. `slabIntensity_le_thin`, `slabIntensity_eq_thin_mul_SA` inherited.
- `emergentIntensity` (`SelfReversal.lean:59`) + `emergentIntensity_nonneg`, `_strictAnti_shell`,
  `selfReversal_noShell`, `selfReversal_uniformSource` (`SelfReversal.lean`) — `N=2` base case
  and the exp-algebra template the induction step copies.
- `lineIntensity` / `lineIntensity_pos` (`ForwardMap.lean:68,74`) — the physical `Sₖ` in a
  fuller pipeline is a zone's Boltzmann line emission; kept abstract here (as in `SpatialForward`).
- `chordIntensity` (`SpatialForward.lean:111`) / `singleZone_identifiable`
  (`SpatialForward.lean:178`) — the "`N=1` is the special case of the general `N`" documentation
  pattern to mirror in docstrings.
- `equivWidth` (`EquivalentWidth.lean:75`) and its `integral_mono`/`ContinuousOn.intervalIntegrable`
  proofs (`EquivalentWidth.lean:110–118`) — the exact `intervalIntegral` idiom §2.4–2.5 reuse.
  (`Mihalas, Stellar Atmospheres` is already cited in-repo at `EquivalentWidth.lean:57` as
  standard-RT background — legitimate prose anchor, but NOT a scope-tags citation.)

---

## 4. Milestone ladder

Ordered; the **fold layer M1–M4 is grade A** (elementary exp algebra already in-repo + list
induction), the **integral layer M5–M7 is grade B** (present but delicate `intervalIntegral`
machinery). Proposed new module `CflibsFormal/RadiativeTransferDepth.lean` (imports
`SelfAbsorption`, `SelfReversal`), or fold M1–M4 directly into `SelfReversal.lean`.

### M1 — `rtStep` / `rtEmergent` defs + single-zone base case · tractability **A**
```
def rtStep (I : ℝ) (z : ℝ × ℝ) : ℝ := I * Real.exp (-z.2) + z.1 * (1 - Real.exp (-z.2))
def rtEmergent (zs : List (ℝ × ℝ)) : ℝ := zs.foldl rtStep 0
theorem rtEmergent_single (S τ : ℝ) : rtEmergent [(S, τ)] = slabIntensity S τ
```
Scope: PURE-MATH (kernel definition) / EXACT (base-case identity to `slabIntensity`).
Citation: Gornushkin 1999 (slab kernel) / `—`. Proof: `simp [rtEmergent, rtStep,
slabIntensity]` — `0*e^{−τ} + S(1−e^{−τ}) = S(1−e^{−τ})`.

### M2 — `rtEmergent_two = emergentIntensity` (ties to Cowan–Dieke) · **A**
```
theorem rtEmergent_two (Score Sshell τc τs : ℝ) :
    rtEmergent [(Score, τc), (Sshell, τs)] = emergentIntensity Score Sshell τc τs
```
Scope: EXACT. Citation: Cowan–Dieke 1948. Proof: `simp [rtEmergent, rtStep]` then `ring`
(unfold two `foldl_cons`; the RHS is `emergentIntensity` verbatim). Establishes the fold as
the strict generalization of *both* existing kernels — the headline structural payoff.

### M3 — `rtEmergent_sandwich` (the monotone bound) · **A**
```
theorem rtEmergent_sandwich {zs : List (ℝ × ℝ)} {Smin Smax : ℝ}
    (hS : ∀ z ∈ zs, Smin ≤ z.1 ∧ z.1 ≤ Smax) (hτ : ∀ z ∈ zs, 0 ≤ z.2) :
    Smin * (1 - Real.exp (-(zs.map Prod.snd).sum)) ≤ rtEmergent zs
    ∧ rtEmergent zs ≤ Smax * (1 - Real.exp (-(zs.map Prod.snd).sum))
```
Scope: EXACT (the bound is exact for the piecewise-constant model). Citation: Gornushkin 2010
(spatial-nonuniformity bias — the bound *confines* it). Prereq: none. Proof: the generalized-
accumulator invariant of §2.2 by `List.rec`/`induction zs`, telescoping
`(1−e^{−T₀})e^{−τ}+(1−e^{−τ}) = 1−e^{−(T₀+τ)}` via `Real.exp_add`+`ring`, then `nlinarith`/
`linarith` on the two direction-preserving weight facts (`Real.exp_pos`, `1−e^{−τ}≥0`).
Add a non-vacuity witness (2 zones, `Smin<Smax`, `τ={1,1}`) in the `SelfReversal`/`SpatialForward`
`example` style, checking strict interiority `Smin(1−e^{−2}) < rtEmergent < Smax(1−e^{−2})`.

### M4 — `rtEmergent_uniform` (uniform slab is extremal) · **A**
```
theorem rtEmergent_uniform (S : ℝ) {zs : List (ℝ × ℝ)} (hS : ∀ z ∈ zs, z.1 = S)
    (hτ : ∀ z ∈ zs, 0 ≤ z.2) :
    rtEmergent zs = slabIntensity S (zs.map Prod.snd).sum
```
Scope: EXACT. Citation: Gornushkin 1999. Prereq: M3 (squeeze with `Smin=Smax=S`,
`le_antisymm`) or a direct induction. Generalizes `selfReversal_uniformSource` to `N` zones;
the "depth structure carries no information iff isothermal" statement.

### M5 — `rtFormal` def + constant-source recovers slab · **B**
```
noncomputable def rtFormal (S : ℝ → ℝ) (τ : ℝ) : ℝ := ∫ t in (0:ℝ)..τ, S t * Real.exp (-(τ - t))
theorem rtFormal_const (S₀ τ : ℝ) : rtFormal (fun _ => S₀) τ = slabIntensity S₀ τ
```
Scope: EXACT (formal solution ↔ slab kernel). Scope-tags citation: **Gornushkin 1999** (kernel).
Prose background (not a scope-tags citation): the formal-solution form is standard RT — Mihalas,
*Stellar Atmospheres* (already cited at `EquivalentWidth.lean:57`). Proof: `integral_const_mul`,
pull `e^{−τ}` out (`integral_comp_sub_left` or a `ring_nf` on `e^{−(τ−t)}=e^{−τ}e^{t}`),
`integral_exp`, `ring`.

### M6 — `rtFormal_sandwich` (continuous bound) · **B**
```
theorem rtFormal_sandwich {S : ℝ → ℝ} {Smin Smax τ : ℝ} (hτ : 0 ≤ τ) (hcont : Continuous S)
    (hlo : ∀ t, Smin ≤ S t) (hhi : ∀ t, S t ≤ Smax) :
    Smin * (1 - Real.exp (-τ)) ≤ rtFormal S τ ∧ rtFormal S τ ≤ Smax * (1 - Real.exp (-τ))
```
Scope: EXACT. Citation: Gornushkin 2010. Prereq: M5. Proof: `intervalIntegral.integral_mono`
(with `Continuous.intervalIntegrable`, `0≤τ`) against the two constant-source integrals of M5;
integrand monotone in `S t` because `e^{−(τ−t)}≥0` (`Real.exp_pos`) and the `hlo`/`hhi` bounds
are global (`integral_mono` compares integrands on all of `ℝ`). The continuous companion of M3.

### M7 — `rtFormalLinear` (exact Eddington–Barbier evaluation) · **B**
```
theorem rtFormalLinear (S₀ S₁ τ : ℝ) :
    (∫ t in (0:ℝ)..τ, (S₀ + S₁ * t) * Real.exp (-(τ - t)))
      = S₀ * (1 - Real.exp (-τ)) + S₁ * (τ - 1 + Real.exp (-τ))
```
Scope: **PURE-MATH** (real-analysis integral evaluation) — **NOT** EXACT-for-LIBS; the
linear-in-τ source is a stellar-atmosphere idealization, not a LIBS profile (see §5, and the
corpus note that Eddington–Barbier "is rarely used in LIBS"). Scope-tags citation: `—`
(evaluation); Mihalas as prose background only, not as a LIBS law. Prereq: none. Proof: FTC-2
(`integral_eq_sub_of_hasDerivAt`) with antiderivative `G(t)=(S₀−S₁+S₁t)·e^{t−τ}`, whose
`HasDerivAt … ((S₀+S₁t)·e^{−(τ−t)})` is `HasDerivAt.mul` + `HasDerivAt.exp`; then `ring`.
Non-vacuity: instantiate `S₁=0` recovers M5's slab; `S₀=0,S₁=1,τ=1` gives `∫ = e^{−1}` checkable.

---

## 5. Refusals / traps

- **Do NOT attempt frequency-angle-coupled RT with depth-dependent `τ(λ)`.** The emergent
  *profile* `I(λ)` over a Voigt/Stark `τ_λ(t)` integrated across depth needs the Faddeeva/Voigt
  special function — ABSENT from mathlib and the explicit deferral of Frontier 07
  (`docs/frontiers/07-ladenburg-reiche.md`). Coupling it with a depth integral compounds two
  hard problems. This is also the recorded "spectral κ stacks" refusal territory — keep `τ` a
  scalar per zone, never a stacked frequency-resolved opacity. This is where production solvers
  go numerical (OPSIAL/Hermann, per corpus). The source `S` stays a scalar per zone or a
  scalar-valued `S(t)`.
- **Do NOT re-tag M7 (linear source) as EXACT/faithful-LIBS.** The Eddington–Barbier linear-in-τ
  source is a *stellar-atmosphere* model; LIBS temperature profiles are step-like/transient and
  the relation "is rarely used in LIBS" (corpus, synthesizing Gornushkin/Zhang). Tag M7
  **PURE-MATH**; cite Mihalas as background, not as a LIBS law. Over-claiming here is exactly the
  `StarkShift.lean` "state the conditional, don't over-claim" lesson.
- **Do NOT wire in the Planck source function `B_λ(T)`.** In LTE the physical source is
  `S = B_λ(T(t))`, but the repo has no Planck def and is dimensionless `ℝ` (non-negotiable #3).
  Keep `S` an abstract input (as `SpatialForward` keeps emissivity `ε` abstract). Formalizing
  `B_λ` is a separate frontier and must not be smuggled in here.
- **Do NOT re-attempt the continuous Abel inversion.** `SpatialForward.lean:64-73` already
  scopes it OUT (improper singular integral). The depth stack here is orthogonal (line-of-sight
  optical depth, not lateral chord geometry); do not conflate `rtEmergent`'s depth index with
  `chordIntensity`'s shell index.
- **Do NOT attempt non-LTE / scattering source coupling** `S=(1−ε)J+εB` (§2.7): integro-
  differential Λ-operator fixed point, no closed form, no elementary sandwich. Every M1–M7
  result assumes `S` is a *given* function of depth.
- **Do NOT attempt inversion of `(T,n_e)` from a measured self-reversed profile.** Already OUT
  of scope in `SelfReversal.lean` ("## Honest scope"); the forward sandwich M3/M6 is the honest
  deliverable, not a reversed-profile inverse.
- **Sign/order trap.** The fold is **deepest-first** (`foldl` from `0`); zone `0` is farthest
  from the observer, the last list element is at the surface. The two-zone check M2 pins the
  convention (`[core, shell]` = core then shell). Getting the order backwards silently breaks
  the `emergentIntensity` match — M2 is the guard.
- **Scope-tag / docs trap.** Each of M1–M7 needs a `docs/scope-tags.tsv` row or the docs-sync CI
  fails (memory discipline). The scope-tags citation column must be one of the curated/vetted
  strings (Gornushkin 1999, Cowan–Dieke 1948, `—`, …) — Mihalas/Zhang/Bultel are NOT in that
  set, so use them only as prose background, never in the citation column. The one judgement to
  get right is M7 = PURE-MATH (not EXACT).

---

## 6. Recommendation

**Attack the fold layer M1–M4 now.** It is unusually favourable: the mathematics is settled
(a derivative-free telescoping induction that reuses the repo's exact exp-algebra house style),
needs **zero new mathlib**, and delivers a genuine structural unification — the two hand-coded
kernels `slabIntensity` (`N=1`) and `emergentIntensity` (`N=2`) become base cases of one
recursive `rtEmergent`, mirroring `SpatialForward`'s `singleZone`-from-`N`-shell framing. **Best
first milestone: M3 (`rtEmergent_sandwich`)** — the one real idea (each zone is a convex
combination `I·e^{−τ} + S(1−e^{−τ})`, so the telescoping bound is invariant) is Tier-A and
self-contained; once it lands, M4 is a squeeze and M1/M2 are `simp`. The integral layer M5–M7 is
a clean grade-B follow-up reusing the `EquivalentWidth.lean` `intervalIntegral` idiom, with M7
(linear source) valuable as the *honest* PURE-MATH Eddington–Barbier evaluation — a mathematical
result explicitly **not** over-claimed as a LIBS law.

**PROPOSED ADDITIONS — need vetting (do NOT cite as established or in scope-tags until vetted):**
- *Zhang, Y., et al.*, review of self-absorption/self-reversal mechanisms in LIBS (core-corona
  two-layer, *Frontiers in Physics*, 2022) — grounds the hot-core/cool-periphery gradient.
- *Bultel, A., et al.* (2019) — two-uniform-layer shock-model stratification. Used as supporting
  context in §2.1; **not yet in the verified citation set** — full bibliographic data and source
  verification required before any use.
- *Völker, T. & Gornushkin, I. B.* (2023) — the homogeneous isothermal collapse
  `I = B_λ(1−e^{−κl})`.

All three surfaced from the CF-LIBS corpus (NotebookLM, 75-source notebook) but none is in the
current verified citation set; **verify full bibliographic data before use.** Gornushkin 2010
(spatial non-uniformity → temperature bias) and Cowan–Dieke 1948 are already vetted and suffice
for M1–M6.