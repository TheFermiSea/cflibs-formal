# 03 — Module specifications

Each section follows the frontier-dossier discipline: obstacle → statement → predicted scope tag →
literature (whitelist only) → mathlib prerequisites (with hit counts from the pinned checkout on
2026-09-20) → milestones with tractability grade → acceptance criteria → pre-registration draft.
Lean snippets are **statement sketches**, not code to paste; the pre-registration fixes the exact form
before any proof is attempted. Any mathlib name marked "grep at implementation" was not confirmed.

---

## 1. `SahaCascade.lean` — Z-stage ionization cascade with unique charge-neutral n_e (P0)

### 1.1 Obstacle
`SahaEquilibrium.lean` handles one ionization step per element (`Ntot·S/(x+S)`). Any plasma whose
spectrum shows II/III lines populates several stages, and the pipeline already carries multi-stage
partition data. No declaration states the multi-stage neutrality balance or that
it has a unique positive solution.

### 1.2 Definitions (all new; nothing here redefines a core concept)

```
/-- Π_{j<z} S j : neutral→stage-z Saha product (dimensionless in the ℝ core). -/
noncomputable def sahaStageProduct (S : ℕ → ℝ) : ℕ → ℝ
  | 0     => 1
  | z + 1 => sahaStageProduct S z * S z

/-- Fraction of a species in stage z at electron density ne (0 < ne). -/
noncomputable def stageFraction (Z : ℕ) (S : ℕ → ℝ) (ne : ℝ) (z : ℕ) : ℝ :=
  (sahaStageProduct S z / ne ^ z) / ∑ k ∈ Finset.range (Z + 1), sahaStageProduct S k / ne ^ k

/-- Free electrons liberated by one species. -/
noncomputable def speciesCharge (Z : ℕ) (S : ℕ → ℝ) (Ntot ne : ℝ) : ℝ :=
  Ntot * ∑ z ∈ Finset.range (Z + 1), (z : ℝ) * stageFraction Z S ne z

/-- Total liberated charge, all species. -/
noncomputable def totalIonizedCharge {κ} [Fintype κ] (Z : κ → ℕ) (S : κ → ℕ → ℝ)
    (Ntot : κ → ℝ) (ne : ℝ) : ℝ := ∑ s, speciesCharge (Z s) (S s) (Ntot s) ne
```

Convention lock (add a new §8 "Saha stage index" to `docs/conventions.md`, which today has §1–§7): `S z` is the Saha factor from stage `z` to
`z+1`, `n_{z+1} n_e / n_z = S z`, the same object as `Saha.sahaFactor` with that stage's `(χ_z, U_z, U_{z+1})`.

### 1.3 Statements (predicted)

| # | Statement | Tag | Grade |
|---|---|---|---|
| S1 | `stageFraction_sum_one : 0 < ne → (∀ z < Z, 0 < S z) → ∑ z ∈ range (Z+1), stageFraction Z S ne z = 1` | PURE-MATH | A |
| S2 | `stageFraction_pos` under the same hypotheses | PURE-MATH | A |
| S3 | `speciesCharge_strictAntiOn : 1 ≤ Z → 0 < Ntot → (∀ z < Z, 0 < S z) → StrictAntiOn (speciesCharge Z S Ntot) (Set.Ioi 0)` | PURE-MATH | B |
| S4 | `speciesCharge_lt_Z_mul_Ntot` and `speciesCharge_pos`: under `0 < ne`, `1 ≤ Z`, `0 < Ntot`, `∀ z < Z, 0 < S z`: `0 < speciesCharge Z S Ntot ne < Z * Ntot` (strict on both sides because `p₀ > 0` and `p_Z < 1`) | PURE-MATH | A |
| S5 | `cascade_exists_pos_fixedPoint [Nonempty κ] (hZ : ∀ s, 1 ≤ Z s) (hN : ∀ s, 0 < Ntot s) (hS : ∀ s, ∀ z < Z s, 0 < S s z) : ∃ ne, 0 < ne ∧ ne = totalIonizedCharge Z S Ntot ne` — `[Nonempty κ]` is load-bearing (for empty `κ` the map is `0` and the statement is false); binder list mirrors `multiElement_exists_pos_fixedPoint` (`SahaEquilibrium.lean:314`) | PURE-MATH | B |
| S6 | `cascade_pos_fixedPoint_unique`, same binders as S5 | PURE-MATH | A given S3 |
| S7 | `totalIonizedCharge_Z_one (hne : ne ≠ 0) (hZ : ∀ s, Z s = 1) : totalIonizedCharge Z S Ntot ne = multiElementIonized (fun s => S s 0) Ntot ne` — `ne ≠ 0` is load-bearing (at `ne = 0` Lean's totalized division makes the LHS `0` while the RHS is `∑ Ntot`); **no positivity of `S` is needed**: when `ne + S = 0` both sides are `0` under totalized division, otherwise they agree (checked with `lake env lean` on the single-species identity, 2026-09-20). Do not add `0 < S s 0`: a hypothesis the proof never uses is a docstring over-claim | EXACT (reduction) | A |
| S8 | `cascade_residual_enclosure`, S5's binders plus `0 < x`: `\|x − ne*\| ≤ \|x − totalIonizedCharge Z S Ntot x\|` where `ne*` is the S5/S6 fixed point | PURE-MATH | B |
| S9 | Physics binding: with `S s z := sahaFactor kB T me h (χ s z) (g s z) (E s z) (g s (z+1)) (E s (z+1))`, S5/S6 give the unique LTE charge-neutral `n_e` at fixed `T`. **Design point:** `sahaFactor` takes two level-index types (`ι` for stage `z`, `κ` for stage `z+1`; see `SahaRangeEnclosure.sahaFactor_mem_Icc {ι κ}`), so a cascade over `ℕ` stages needs a dependent family `ι : ℕ → Type` with `[∀ z, Fintype (ι z)] [∀ z, Nonempty (ι z)]`; a uniform padded type with `g = 0` on padding would break `partitionFunction_pos`. The pre-registration must fix this choice | EXACT (Saha–Eggert) | B |

S8 is the certificate payload: `F x := x − Q(x)` is strictly increasing with `F' ≥ 1` (Q antitone),
so a posteriori `|x − x*| ≤ |F x|`. Prove derivative-free: for `x < x*`, `F x ≤ F x* − (x* − x)`.

### 1.4 Proof routes
- **S3 (crux).** Write `speciesCharge = Ntot · E_p[z]` with `p_z ∝ Π_{j<z} S_j · ne^{−z}`. For
  `0 < a < b`, `p_z(b)/p_z(a) ∝ (a/b)^z` is strictly decreasing in `z`, so `E_{p(b)}[z] < E_{p(a)}[z]`
  by the Chebyshev sum inequality (monotone likelihood ratio). mathlib (verified 2026-09-20):
  `MonovaryOn.sum_mul_sum_le_card_mul_sum` (`Algebra/Order/Chebyshev.lean:105`) and
  `AntivaryOn.card_mul_sum_le_sum_mul_sum` (`:113`) are **non-strict only**; no strict Chebyshev exists
  in the pinned checkout, so the strict two-point inequality must be proved directly (the single-stage
  `multiElementIonized_strictAntiOn` at `SahaEquilibrium.lean:295` is the termwise-then-sum template:
  each species' charge strictly decreasing, summed over a nonempty type).
  Avoid the derivative/variance route: `Finset.sum_mul_sq_le_sq_mul_sq` has no strict-equality case in
  mathlib (ROADMAP §3), and `HasDerivAt` through a `Finset.sum` of `ne ^ z` powers is heavier than the
  pairwise argument.
- **S5.** `intermediate_value_Icc` (4 hits) on `F x = x − Q x` over `[ε, M]` with
  `M := ∑ Z s · Ntot s`. `F M > 0` by S4 (`Q M < M`). `F ε < 0` needs `Q ε > ε`, which S4's
  positivity alone does not give: use S3 (antitone) to get `Q ε ≥ Q 1 > 0` for `ε ≤ 1` and take
  `ε := min 1 (Q 1 / 2)`. Continuity from `ContinuousOn` of rational functions with `ne ^ z ≠ 0` on
  `Ioi 0`.
- **S7.** `Finset.sum_range_succ` (64 hits) twice; `field_simp`.

### 1.5 Literature
Griem 1997 (*Principles of Plasma Spectroscopy*, Saha–Eggert per stage) — whitelisted. Cremers &
Radziemski 2013 for the multi-stage LIBS context — whitelisted. No new citation needed. Do not cite
any "Saha cascade" paper from memory; if one is wanted, route through `citation-integrity`.

### 1.6 Acceptance
Green; `#print axioms` clean; `mutate-check.sh` kills: `<` → `≤` in S3, drop `0 < ne`, drop
`1 ≤ Z`, `x − Q x` → `Q x − x` in S8, drop `ne ≠ 0` in S7 (must fail: the totalized `ne = 0` case
breaks the identity), drop `[Nonempty κ]` in S5 (must fail); positive control: adding `∀ s, 0 < S s 0`
to S7 must leave it provable, which is why it is not stated; S7 closes by unfolding plus the §1.4 route (`Finset.sum_range_succ`, `field_simp`)
with no hypotheses beyond those in the frozen statement, so the reduction is a computation, not a
re-proof of `SahaEquilibrium`; scope-tag rows; `C15` and Scenario 7 (below).

### 1.7 Pre-registration draft (freeze before Lean)
```
Intended module: CflibsFormal/SahaCascade.lean (does not exist)
Predicted: S1,S2,S4,S6,S7 PURE-MATH/EXACT grade A; S3,S5,S8 PURE-MATH grade B; S9 EXACT grade B
(dependent level-index family; see the S9 design point).
Not predicted (exploratory if it appears): any convergence theorem for a cascade iteration; any
statement about T-dependence of ne*.
Disclosure of prior state: SahaEquilibrium.lean already proves the Z=1 theory listed in 01 §1.3;
nothing below may be a corollary of those declarations except S7, which is the reduction.
```

---

## 2. `ContinuousProfile.lean` — Lorentzian, Gaussian, Voigt as functions on ℝ (P1)

### 2.1 Obstacle
The repo has an unshifted unit-width `lorentzian` with `lorentzian_integral = 1`
(`EquivalentWidth.lean:337–355`) and a scaled `lorentzianG γ` (`LadenburgReiche.lean:84`), but no
shifted profile, no Gaussian profile, and no Voigt *profile* (only the O–L FWHM formula). `equivWidth`
and the self-absorption layer therefore cannot be instantiated on a real line shape.

### 2.2 Design decision: define by equality to mathlib densities
mathlib (pinned) has `ProbabilityTheory.cauchyPDFReal x₀ γ` (`Probability/Distributions/Cauchy.lean:42`)
with `lintegral_cauchyPDF_eq_one` (`:155`) and `ProbabilityTheory.gaussianPDFReal μ v`
(`Gaussian/Real.lean:49`) with `integral_gaussianPDFReal_eq_one` (`:130`). Define our profiles in the
repo's own parameters (center `lam₀`, HWHM `γ`, Gaussian `σ`) and prove **equality to the mathlib PDF**;
normalization is then inherited. This satisfies "define once" (the PDFs are mathlib's) while keeping the
spectroscopic parameterization the pipeline uses.

```
-- `λ` is Lean's lambda token and cannot be an identifier; the repo's name for wavelength is `lam`.
noncomputable def lorentzianProfile (γ lam₀ x : ℝ) : ℝ := lorentzianG γ (x - lam₀)
noncomputable def gaussianProfile  (σ lam₀ x : ℝ) : ℝ :=
  (1 / (σ * Real.sqrt (2 * Real.pi))) * Real.exp (-(x - lam₀) ^ 2 / (2 * σ ^ 2))
noncomputable def voigtProfile (γ σ lam₀ : ℝ) : ℝ → ℝ :=
  MeasureTheory.convolution (lorentzianProfile γ 0) (gaussianProfile σ lam₀) (ContinuousLinearMap.lsmul ℝ ℝ) volume
```

### 2.3 Statements (predicted)

| # | Statement | Tag | Grade |
|---|---|---|---|
| L1 | `lorentzianProfile_eq_cauchyPDFReal (hγ : 0 ≤ γ) : lorentzianProfile γ lam₀ = cauchyPDFReal lam₀ ⟨γ, hγ⟩` — non-strict suffices (both sides are `0` at `γ = 0`: `cauchyPDFReal_scale_zero`, `Cauchy.lean:48`) | PURE-MATH | A |
| L2 | `lorentzianProfile_integral (hγ : 0 < γ) : ∫ x, lorentzianProfile γ lam₀ x = 1` — direct from L1 and `integral_cauchyPDFReal_eq_one (hγ : γ ≠ 0)` (`Cauchy.lean:131`; integrability `integrable_cauchyPDFReal` `:142`). Alternative route: `lorentzian_integral` + `integral_comp_mul_left` + the whole-line shift lemma `MeasureTheory.integral_sub_right_eq_self` (the `to_additive` twin of `integral_div_right_eq_self`, `Group/Integral.lean:109`). Strict `0 < γ` is load-bearing here (at `γ = 0` the integral is `0`) | PURE-MATH | A |
| L3 | `lorentzianProfile_integrable`, positivity, symmetry `lorentzianProfile γ lam₀ (lam₀+u) = lorentzianProfile γ lam₀ (lam₀−u)` | PURE-MATH | A |
| G1 | `gaussianProfile_eq_gaussianPDFReal (hσ : 0 < σ) : gaussianProfile σ lam₀ = gaussianPDFReal lam₀ ⟨σ^2, _⟩` | PURE-MATH | A–B (unfold mathlib's def; `Real.sqrt (2π σ²)` vs `σ √(2π)` bookkeeping) |
| G2 | `gaussianProfile_integral (hσ) : ∫ = 1` | PURE-MATH | A given G1 |
| G3 | Half-maximum: `gaussianProfile σ lam₀ (lam₀ ± σ √(2 ln 2)) = ½ · gaussianProfile σ lam₀ lam₀`, i.e. FWHM `= 2√(2 ln 2) σ` | PURE-MATH | A |
| G4 | Doppler binding: `dopplerFWHM lam kB T m c = 2 √(2 ln 2) · (lam · √(kB T / (m c²)))` — `LineBroadening.lean:52` defines `dopplerFWHM lam kB T m c = lam · √(8 ln 2 · kB T/(m c²))` and has no `σ`; this lemma is what ties G3's `σ` to the width the repo already uses | EXACT | A |
| V1 | `voigtProfile_integral (hγ hσ) : ∫ x, voigtProfile γ σ lam₀ x = 1` via `MeasureTheory.integral_convolution` (`Analysis/Convolution.lean:845`, 1 hit) with L3/G integrability | PURE-MATH | B |
| V2 | `voigtProfile_nonneg`, `voigtProfile_integrable` | PURE-MATH | B |
| V3 | Honest non-theorem, recorded as a docstring caveat and a `nonvacuity_*`-style witness: the FWHM of `voigtProfile` is **not** `voigtFWHM` of `VoigtWidth.lean` (O–L is an APPROXIMATION); no equality is claimed | — | — |
| E1 | `equivWidth_lorentzianProfile_eq (hγ) : equivWidth (lorentzianProfile γ lam₀) τ = equivWidth (lorentzianG γ) τ` (shift invariance of `equivWidth` via `integral_sub_right_eq_self`) — connects the sharp L–R constant to a centered real line | EXACT | A |

### 2.4 Literature
Griem 1974 (*Spectral Line Broadening by Plasmas*: Lorentzian Stark, Gaussian Doppler, Voigt
convolution) — whitelisted. Olivero–Longbothum 1977 for V3's caveat — whitelisted. No new citation.

### 2.5 Acceptance
Green, axiom-clean; mutants killed: replace `γ` by `γ²` in L1, drop `0 < γ` in L2 (must fail), `2 σ²` → `σ²` in G1, `ln 2` → `ln 4` in G4;
scope-tag rows; docstring for V3 states the non-claim in words.

### 2.6 Pre-registration draft
```
Intended module: CflibsFormal/ContinuousProfile.lean (does not exist)
Predicted: L1–L3, G1–G4, E1 grade A (PURE-MATH/EXACT); V1–V2 grade B (PURE-MATH).
Not predicted: any FWHM theorem about the Voigt convolution; any Faddeeva/complex-error-function
representation (out of scope, mathlib lacks it).
Disclosure: EquivalentWidth.lorentzian_integral and LadenburgReiche.lorentzianG exist; L2 must not be
a restatement of lorentzian_integral — it must carry the shift and the scale.
```

---

## 3. `SpectrometerForward.lean` — instrument kernel and line-intensity identifiability (P2)

### 3.1 Obstacle
The forward map produces per-line intensities `I : ι → ℝ`; the instrument produces per-pixel sums. No
declaration connects them, so "the line intensity the Boltzmann plot consumes" has no formal
provenance from a spectrum. The companion's `InstrumentModel` (Gaussian response, `sigma_at_wavelength`,
`apply_response`) is the object to align with.

### 3.2 Decision: abstract kernel first, Gaussian IRF as the first instance
The module is stated for an arbitrary pixel response family `R : Pixels → ℝ → ℝ` and profile family
`φ : Lines → ℝ → ℝ`; the companion's Gaussian IRF with top-hat pixels is instantiated as a corollary.
This keeps the REDUCED tag honest (the physics reduction is "linear, optically thin, additive lines,
known profiles") and avoids baking one instrument into the theorem.

```
noncomputable def pixelKernel (R φ : ℝ → ℝ) : ℝ := ∫ x, φ x * R x   -- `x` is wavelength; `λ` is not a legal identifier
noncomputable def kernelMatrix {P L} [Fintype P] [Fintype L] (R : P → ℝ → ℝ) (φ : L → ℝ → ℝ) :
    Matrix P L ℝ := fun p l => pixelKernel (R p) (φ l)
noncomputable def pixelSignal … (I : L → ℝ) : P → ℝ := (kernelMatrix R φ).mulVec I
```

### 3.3 Statements (predicted)

| # | Statement | Tag | Grade |
|---|---|---|---|
| K1 | Linearity: `(∀ l, Integrable (fun x => φ l x * R p x)) → ∫ x, (∑ l, I l * φ l x) * R p x = pixelSignal R φ I p` (`MeasureTheory.integral_finsetSum` — note `integral_finset_sum` is deprecated since 2026-04-08 — plus `integral_const_mul`, `Bochner/Basic.lean:288`) | EXACT (definitional) | A |
| K2 | `pixelSignal_injective_iff : Function.Injective (pixelSignal R φ) ↔ LinearMap.ker (kernelMatrix R φ).mulVecLin = ⊥` via `Matrix.mulVecLin` (abbrev, `LinearAlgebra/Matrix/ToLin.lean:286`), `Matrix.coe_mulVecLin` (`:288`) and `LinearMap.ker_eq_bot : ker f = ⊥ ↔ Injective f` (`Algebra/Module/Submodule/Ker.lean:199`); in-repo pattern `OLSIdentifiability.boltzmannDesign_mulVec_injective_iff` | PURE-MATH | A |
| K3 | Private-pixel sufficient condition: if there is a function `π : L → P` with `K (π l) l ≠ 0` and `K (π l) l' = 0` for `l' ≠ l`, then `ker = ⊥` (injectivity of `π` is implied by the two conditions, so it is not a hypothesis) | PURE-MATH | B |
| K4 | Strict-diagonal-dominance (crosstalk bound) on `Kᵀ * K` ⇒ `det (Kᵀ * K) ≠ 0`, directly from `Matrix.det_ne_zero_of_sum_row_lt_diag` (`LinearAlgebra/Matrix/Gershgorin.lean:63`; column form `:73`); the work is bounding the off-diagonal entries `∑_p (∫ φ_l R_p)(∫ φ_l' R_p)` | PURE-MATH | B |
| K5 | Least-squares recovery: `det (Kᵀ * K) ≠ 0 → ((Kᵀ * K)⁻¹ * Kᵀ).mulVec (K.mulVec I) = I` (exact-fit), and the normal-equations minimizer for noisy `y` | PURE-MATH | B |
| K6 | Gaussian-IRF instance: `R p := indicator of pixel bin ⋆ gaussianProfile σ_inst` and `φ l := voigtProfile …` are integrable, so K1–K2 apply | REDUCED | B |
| K7 | Bridge: `Function.Injective pixelSignal → ` the `ForwardMap` identifiability theorems apply to `I` recovered from `y` (compose with `Identifiability.temperature_identifiability`) | REDUCED | A given K2 |

Scope caveat to state in the docstring: self-absorption makes the emission non-additive in `I`; K1–K7
hold for the optically-thin forward model only. Saturation is handled upstream (`SelfAbsorption`).

### 3.4 Literature
Cremers & Radziemski 2013 (instrument function, resolution) — whitelisted. For Gaussian instrument
response as convolution, Griem 1974 — whitelisted. Anything more specific (e.g. a spectrometer
line-spread-function paper) must go through `citation-integrity` first.

### 3.5 Acceptance
Mutants: K2 with `≠ ⊥` (must fail), K3 with `K (π l) l ≠ 0` dropped (must fail), K5 with
`Kᵀ` dropped (must fail). A `nonvacuity_*` witness: two lines, three pixels, explicit `K` with `det (KᵀK) = 1` by
`norm_num`. Oracle: Scenario 7 pixel-integrated block.

### 3.6 Pre-registration draft
```
Intended module: CflibsFormal/SpectrometerForward.lean (does not exist)
Predicted: K1,K2,K7 grade A; K3,K4,K5,K6 grade B.
Not predicted: any condition-number bound for K (deferred to a later frontier);
any self-absorbed pixel model.
Disclosure: OLSIdentifiability and SpatialForward (chord matrix, Matrix.mulVec) exist; K2 must not be a
renaming of boltzmannDesign_mulVec_injective_iff.
```

---

## 4. Stoichiometry corollaries (P3) — append to `MatrixEffects.lean`

```
def preservesStoichiometry {κ} (C N : κ → ℝ) : Prop :=
  ∀ s₁ s₂, C s₂ ≠ 0 → N s₁ / N s₂ = C s₁ / C s₂

theorem preservesStoichiometry_iff_smul (hC : ∃ s, C s ≠ 0) :
    preservesStoichiometry C N ↔ ∃ c ≠ 0, N = fun s => c * C s                    -- PURE-MATH, A
theorem composition_of_preservesStoichiometry (hsum : ∑ s, C s = 1) (h : preservesStoichiometry C N) :
    composition N = C                                                              -- EXACT, A
```
No positivity hypothesis on `C` and no `[Nonempty κ]`: `∑ C = 1` supplies a coordinate `s₀` with
`C s₀ ≠ 0`; the predicate at `s₂ = s₀` forces `N s₀ ≠ 0` (else every `C s₁` would be `0`) and
`N = (N s₀ / C s₀) • C`, so `composition_smul_invariant` closes it. An earlier draft carried
`∀ s, 0 < C s`; it was decorative (the red-team pre-check of 2026-09-20 caught it), and a hypothesis
the proof never uses is a docstring over-claim.
A third theorem tying the cascade's per-species totals to this predicate was considered and dropped:
`Ntot s` is an *input* of `SahaCascade`, so "`Σ_z N_{s,z} = Ntot s`" is S1 restated, and stating it in
`MatrixEffects.lean` would pull `SahaCascade` into that module's import cone for no content.
Second theorem is `composition_smul_invariant` (`Closure.lean:93`) plus `composition_sum_one`.
Literature: Tognoni 2010 (stoichiometric ablation) — whitelisted (already cited in `TemporalEvolution`).
Cross-reference `TemporalEvolution.hDilute` in the docstring; do not introduce a second dilution notion.

---

## 5. `Dimensions.lean` additions (with the blueprint's errors corrected)

All in `CflibsFormal.Dimension`, ⟨L, M, T, Θ⟩ exponents:

| Quantity | Vector | Lean |
|---|---|---|
| line emission coefficient `A · E_photon · n` | ⟨−1, 1, −3, 0⟩ | `mul (mul einsteinA energy) numberDensity` |
| slab-integrated emergent intensity `ε · ℓ` | ⟨0, 1, −3, 0⟩ | `mul lengthDim (mul (mul einsteinA energy) numberDensity)` |
| spectral radiance per unit wavelength | ⟨−1, 1, −3, 0⟩ | `div (div energy timeDim) (qpow lengthDim 3)` |
| profile `φ(λ)` | ⟨−1, 0, 0, 0⟩ | `inv lengthDim` (so `∫ φ dλ` is dimensionless) |
| pixel kernel `∫ φ R dλ` with dimensionless `R` | ⟨0, 0, 0, 0⟩ | `one` |

Theorems: `emissionCoefficient_dim`, `slabIntensity_dim`, `profile_integral_dimensionless`,
`pixelKernel_dimensionless` — each closes by `unfold …; ext <;> norm_num` (the pattern of
`sahaLaw_homogeneous`). The blueprint's `spectralRadiance` and `forward_intensity_radiance_homogeneous`
must **not** be transcribed (01 §1.2).

---

## 6. Certificates C15, C16 (`Certificates.lean`) and oracle Scenario 7

| # | Certificate | Inputs | Predicate (exact-ℝ `Prop`; mirrored in float by `check_fixtures.py` and the companion, with the interval margin the `Certificates.lean` header calls R6) | Guarantee theorem | Grade |
|---|---|---|---|---|---|
| C15 | Cascade residual enclosure | `Z`, `S s z`, `Ntot s`, candidate `x`, tolerance `tol` | a non-empty species list (`[Nonempty κ]`) ∧ `0 < x ∧ (∀ s z<Z s, 0 < S s z) ∧ (∀ s, 0 < Ntot s) ∧ (∀ s, 1 ≤ Z s) ∧ \|x − totalIonizedCharge Z S Ntot x\| ≤ tol` | S8: `\|x − ne*\| ≤ tol` with `ne*` the unique positive fixed point (S5/S6) | B |
| C16 | Kernel rank gate | `K` (P×L floats) | `det (Kᵀ * K) ≠ 0` (or the K3 private-pixel witness, cheaper to evaluate) | K2/K5: line intensities identifiable and recoverable from pixel sums | B |

Scenario 7 (`oracle/Generate.lean`): (a) a two-species, `Z = (2, 1)` cascade at one `T`; emit `S`,
`Ntot`, the bisection solution `x`, its residual, and the C15 verdict; (b) two Gaussian lines on
three top-hat pixels; emit `K`, `det (KᵀK)`, and the C16 verdict; (c) a rejection case for each (a
zero `Ntot`; two lines in one pixel). `check_fixtures.py` mirrors the predicates; the companion vendors
the scenario as it does the certificates scenario.

Note on numbering: C8 and C11 are unused in `Certificates.lean`; keep C15/C16 as the blueprint proposed
and do not back-fill.

## 7. `Alt/NeutralityScale.lean` — the calibration factor from charge neutrality (C3, owner-directed 2026-09-21)

**Origin.** Candidate C3 of `docs/research/first-principles-alternatives.md`: classic CF-LIBS removes the
unknown instrument factor `Fcal` by closure (`∑ C = 1`); charge neutrality is a second absolute
equation whose left side a Stark width measures independently of `Fcal`. Prior art: Abbass, Ahmed,
Ahmed & Baig, Plasma Chem. Plasma Process. 36 (2016) 1287 ("electron density conservation" CF-LIBS,
Pb–Sn, Saha-derived `n_e`); Tognoni et al. 2010 on closure failing when elements are missing. What is
new here is the exact statement of what neutrality buys with a *measured* `n_e` and what an undetected
species does to each normalization. Chosen by the owner as the first *real* target for the local
Worker (decision D12) rather than the SahaCascade module of §1.

### 7.1 Model and definitions (reuse only)

Single shared `T`, one neutral line per species `s : κ`, singly ionized stages; `N s` neutral density,
`R s` the Saha stage ratio `n_ion/N` (positive, supplied), `ne` the measured electron density.
`I s := lineIntensity kB T (N s) Fcal g E A (emit s)` (ForwardMap, verbatim); `unitI s :=
lineIntensity kB T 1 1 g E A (emit s)`, the per-unit line factor; linearity `I s = Fcal · N s · unitI s`
follows from `population kB T N g E k = N * g k * boltzmannFactor kB T (E k) / partitionFunction kB T g E`.
Neutrality is the existing `chargeNeutrality (fun _ => 1) (fun s => N s * R s) ne` (Saha.lean).

```
noncomputable def neutralityScale (I unitI R : κ → ℝ) (ne : ℝ) : ℝ := (∑ s, I s * R s / unitI s) / ne
noncomputable def closureEstimate (I unitI : κ → ℝ) (s : κ) : ℝ := (I s / unitI s) / ∑ t, I t / unitI t
```

### 7.2 Statements (three files, one `sorry` each; typecheck against the built `.lake` 2026-09-21)

```
theorem neutralityScale_eq_Fcal (hne : 0 < ne) (hunit : ∀ s, 0 < unitI s)
    (hneut : chargeNeutrality (fun _ : κ => (1:ℝ)) (fun s => N s * R s) ne) :
    neutralityScale I unitI R ne = Fcal                                   -- EXACT, grade A
theorem neutralityScale_undetected (hne : 0 < ne) (hunit : ∀ s, 0 < unitI s)
    (hneut : ne = (∑ s, N s * R s) + Nu * Ru) :
    neutralityScale I unitI R ne = Fcal * (1 - Nu * Ru / ne)               -- EXACT, grade A
theorem closureEstimate_bias (hFcal : 0 < Fcal) (hNu : 0 ≤ Nu) (hsum : 0 < ∑ t, N t)
    (hunit : ∀ s, 0 < unitI s) (s : κ) :
    closureEstimate I unitI s = (N s / (∑ t, N t + Nu)) / (1 - Nu / (∑ t, N t + Nu))  -- EXACT, grade A
```
(`I`, `unitI` written out as the `lineIntensity` expressions in the files; see
`tools/openprover/dryrun/C3_*.lean` once landed.)

**Physics content, stated honestly.** Neutrality counts *charge*: the second theorem says the
estimator is off by the undetected species' charge fraction `Nu·Ru/ne`, not its mass fraction, so it
is nearly blind to the high-ionization-energy elements CF-LIBS typically misses (H, O, N, C are mostly
neutral at LIBS temperatures) — the good news is that the scale is then nearly unbiased; the
limitation is that neutrality alone cannot report those elements' mass fraction as a deficit, which
needs an independent total-density scale (out of scope here). The third theorem makes "closure fails
when elements are missing" exact: the bias factor is `1/(1 − Cu)`. The memo's earlier phrase "closure
residual = C_missing" was an overstatement and is corrected by these statements.

### 7.3 Acceptance and gates

Statement audit (Mode B, three independent reviewers, 2026-09-21): **all three `passed`, `drift_class:
none`**, with docstring-level findings applied to the files (identities are sign-free; guards are used
only as `≠ 0`; shared-partition-function scope; unused imports removed; the closure-bias right-hand side
is `Nu`-invariant, so its content is `closureEstimate = N s / ∑ N` and the inflation dressing already
exists as `MatrixEffects.recoveredComposition_eq_inflation` — noted as a follow-up architectural
reuse, not a landing blocker). Each reviewer also produced an axiom-clean proof as a probe, so the
three statements are known provable before the Worker sees them; those probe proofs stay outside
the Worker's world (`/tmp/aud-*`, not indexed by `lean_search`). Files:
`tools/openprover/dryrun/C3_*.lean` with dossiers `C3_*.md`. Scope tags EXACT with citations
Abbass 2016 / Tognoni 2010 / Ciucci 1999; non-vacuity witnesses `κ = Fin 2`, `Fcal ≠ 1`,
`Nu·Ru ≠ 0`; acceptance mutants recorded in the audit transcripts: drop `hne` (division by zero
makes the estimator `0`), replace `N s * R s` by `N s` in neutrality (statement false), drop the
`Nu·Ru` term (reduces to theorem 1), `Nu = −∑ N` (breaks the closure-bias identity).

### 7.4 Worker result (2026-09-21–22, decision D12) — **PR #6, `feat/neutrality-scale`, open (CI green), not merged**

Both local models ran all three audited statements, same harness, 60-minute caps each, after the
two harness fixes from the Frontier 02/07 dry run (§10.4: server-side `--reasoning-budget 8192`,
`--answer-reserve 16384`; OpenProver search-loop breaker + 12-turn cap).

| statement | Qwen3.8-27B (infer-01) | Leanstral 1.5 Q6_K (infer-03) |
|---|---|---|
| `neutralityScale_eq_Fcal` | **proved**, 23 min, 18 planner calls | not proved, 7 failed `lean_verify` |
| `neutralityScale_undetected` | **proved**, 42 min, 40 planner calls | not proved, running to cap |
| `closureEstimate_bias` | **proved**, 50 min (after two silent SIGKILLs of the Qwen service, unrelated to the proof — see below) | not proved, running to cap |

**3/3 for Qwen, 0/3 for Leanstral** — the opposite of the owner's stated expectation going in.
Every Qwen proof was independently re-verified by the lead before landing: `lake env lean`,
`#print axioms` (the standard three), and a full statement/definition diff against the audited
files (identical). Qwen's route in each case matched the reviewers' own probe proofs: a
`lineIntensity_linear`/`_ratio` helper by `unfold; ring`, then `Finset.mul_sum` + `field_simp`.
Leanstral's failures on this target are consistent with its performance on the algebraic smoke
tests (2/5, both one-liners) and the Frontier 02 dry run (proved three helper lemmas by
decomposition, lost the assembly to harness limits): it can decompose and prove short lemmas but
has not closed a multi-step `field_simp`/`Finset` assembly in this campaign.

**Caveat (2026-09-22, owner question "is it the right model?"): the Leanstral 0/3 is not a
model-quality verdict.** The weights are correct: `GZGavinZhao/Leanstral-1.5-119B-A6B-GGUF`
Q6_K, byte size identical to the Hub file, sha256 checked at download; Leanstral 1.5 is Mistral's
update *of* `Leanstral-2603` (the Hub's `base_model` tag), so 1.5 is the newer of the two. But the
A/B was not symmetric, and every asymmetry favored Qwen:

| setting | Qwen3.8-27B | Leanstral 1.5 | Mistral's card |
|---|---|---|---|
| server `--reasoning-budget` | 16384 | 8192 | `max_tokens` 32000 in its example |
| server context | 131072 | 65536 | ≤ 200k |
| decode throughput under the same 60-min wall-clock cap | ~41 tok/s (dense, fully on GPU) | ~10–14 tok/s (MoE, experts on CPU) | — |
| temperature | 0.6 (OpenProver `HFClient` hard-codes it) | 0.6 (same) | **1.0** |
| chat template | model's own | the GGUF's embedded **2603** template (5.7 kB), not 1.5's current 12.8 kB one | 1.5's `chat_template.jinja` |
| agent harness | OpenProver (drops prior-turn reasoning) | same | Mistral Vibe (`LEAN.md` system prompt); 1.5's template re-injects prior reasoning |

What the logs support, and what they do not:

- **Throughput mattered on the first statement only.** Summed over every Worker and verifier call,
  Leanstral generated 12k / 33k / 42k output tokens on the three statements; Qwen used 38k / 25k /
  86k to prove them. On `neutralityScale_undetected` Leanstral had *more* tokens than Qwen needed
  and still failed, so speed alone does not explain the result. Leanstral decoded at 8–12 tok/s
  (falling as context grew) and reached only 3–4 planner steps per hour; its three
  `lean_verify — ok` results were definition probes, not the target.
- **Four Worker calls failed outright on a template defect.** The GGUF's embedded 2603 template
  `raise_exception()`s when a user message follows a tool result ("roles must alternate"), which is
  exactly what the OpenProver search-loop breaker sends. The infer-03 server log records four
  HTTP 500s: two in the second run, two in the third. Qwen's template accepts that sequence.
- **Per-turn thinking cap half of Qwen's, temperature not the card's.** As in the table above.
- **The infer-03 crash was at shutdown.** The segfault in `libggml-cpu` (`2026-09-22T03:19:38Z`,
  `status=11/SEGV`) follows "Received second interrupt, terminating immediately" in the server log:
  an external interrupt during the last minutes of the third run, most likely from the lead's own
  Q4 benchmark job. It is a teardown crash, not an inference crash; recorded, not chased further.

Until a matched rerun, what the table shows is "Qwen closes these under OpenProver at Qwen's
settings", not "Qwen is the better Worker". The D7 Mistral Vibe arm (the harness Leanstral was
trained for) has still not been run.

Incident: the Qwen `systemd` service was killed twice with no error logged and no OOM record
between the second and third runs; root cause was `systemctl set-property` for CPU pinning not
persisting across a service restart, silently returning the instance to all 36 threads (not itself
fatal) — the actual SIGKILL sender was not identified. Fix applied: re-pin after every restart;
open follow-up to make the pin a persistent drop-in instead of a transient `set-property`.

Written as `CflibsFormal/Alt/NeutralityScale.lean`, gates green (`lake build`, `axiom-audit`,
`runLinter`, `stats.sh`, oracle regression, `check-citations.sh`/`check-scope-consistency.sh`
advisory clean), `docs/scope-tags.tsv` +5 EXACT rows, auto docs regenerated — on a fresh branch off
`main` (`docs/formalization-spec` carries no Lean, per its own contract), PR #6 — open, CI green,
awaiting the owner's merge (earlier drafts of this section and the v0.4.2 change log said "landed on
`main`"; it has not been merged).

### 7.5 Leanstral matched rerun (2026-09-22–23) — **3/3 proved**

Same three audited statements, same OpenProver harness and Claude `sonnet` planner, after the
serving corrections of 04 §10.4 (Mistral's 1.5 chat template, card sampling, reasoning budget
equal to Qwen's, Worker usage summed over all turns) and with an equal-*token* budget
(`--max-tokens 150000`; Qwen's largest full-count total was ~125k) instead of a wall-clock cap.
Every proof re-verified by the lead: `lake env lean`, `#print axioms` (the standard three), no
`sorry`/`admit`/`native_decide`, imports and local definitions and the theorem statement identical
to the audited file after whitespace normalisation.

| statement | Qwen3.8-27B (§7.4) | Leanstral 1.5, first run (§7.4) | Leanstral 1.5, matched rerun |
|---|---|---|---|
| `neutralityScale_eq_Fcal` | proved, 20 min | not proved | **proved**: Lean proof verified at step 4, 42.5k tokens, 4 h 34 min (infer-03, pinned and balanced) |
| `neutralityScale_undetected` | proved, 40 min, ~99k tokens | not proved | **proved**: verified at step 4, ≤ 96k tokens, 4 h 54 min (infer-03, vCPUs unpinned for most of the run) |
| `closureEstimate_bias` | proved, 47 min, ~125k tokens | not proved | **Lean proof complete and verified** at step 9, 72k tokens, ~8 h 30 min (infer-02, model split 10/21/31/31 GB across NUMA nodes); the harness run was then killed by the lead's 9 h wall-clock guard while writing the informal proof, so OpenProver recorded `not_proved` |

Reading. (1) The first run's 0/3 was the serving setup, not the model: under matched settings
Leanstral closes all three, at a token cost equal to or below Qwen's. (2) Wall-clock is the real
gap: 4.5–8.5 h against 20–47 min. Leanstral's routed experts run on CPU (decode 8–15 tok/s, prefill
60–140 tok/s against Qwen's fully GPU-resident ~41 tok/s), and every agent turn re-prefills a long
prompt. Two fleet faults found during this rerun inflated the times further (04 §10.4, "Fleet
fixes"): infer-03 decoded at ~5 tok/s until its vCPUs were pinned, infer-02 at 4–6 tok/s until the
model was reloaded evenly across NUMA nodes (15–16 tok/s after, short context). (3) Behaviour:
Leanstral explores before it attempts — long `lean_search` runs under OpenProver, and under Mistral
Vibe (below) long `find`/`read_file` runs with no compile. The search-loop breaker matters more for
it than for Qwen. (4) Scope of the evidence: three algebraic statements from one family, with a
Claude planner doing much of the decomposition in both arms. It shows both Workers close this
class; it does not rank them on harder targets.

Mistral Vibe arm (D7; in progress). `vibe -p --agent lean-local` (Vibe 2.25.7, the model card's
local-server configuration, `system_prompt_id = "lean"`) in a `bwrap` sandbox holding the Lean
project's build (minus every `NeutralityScale` artifact) and, from the second attempt on, the
repository's sources as of this branch (which has no `NeutralityScale.lean`). First attempt, no
sources: 2 h 11 min of `find`/`read_file` (96 and 30 calls), no compile, no edit — stopped as a
sandbox artifact. Second attempt on `neutralityScale_eq_Fcal`: ended after 2 h 51 min when Vibe's
own HTTP client timed out (1800 s) on an auto-compaction request, with the working file's
conclusion line deleted (the edit would have failed the statement check); API timeout raised to
7200 s for later runs.
