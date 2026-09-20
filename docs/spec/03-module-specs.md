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

theorem preservesStoichiometry_iff_smul [Nonempty κ] (hC : ∀ s, 0 < C s) :
    preservesStoichiometry C N ↔ ∃ c ≠ 0, N = fun s => c * C s                    -- PURE-MATH, A
theorem composition_of_preservesStoichiometry (hC) (hsum : ∑ s, C s = 1) (h : preservesStoichiometry C N) :
    composition N = C                                                              -- EXACT, A
```
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
