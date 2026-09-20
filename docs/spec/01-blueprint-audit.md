# 01 — Audit of the "Revised Architectural Blueprint" (Google Doc, 2026-09-20)

Every claim in the blueprint was checked against the repo working tree at commit `5daee7c` (main) and
the pinned mathlib checkout (Lean `v4.33.1`). Verdicts use the vocabulary in `README.md`.

## 0. Provenance caveat

The blueprint's Executive Summary critiques a "preliminary architecture blueprint" (dependent unit
subtypes, `sorry`-backed existence statements, monolithic `EnergyLevel` / `AtomicTransition` records).
That preliminary document is not in the repo or in Drive. The three anti-patterns it lists are
**accepted as stated, not verified**. They are consistent with this repo's design decisions
(`CONTEXT.md` #1, #4, the abstract-index-type convention), so nothing in this spec depends on them.

## 1. Section-by-section verdicts

### 1.1 Architectural philosophy (§1)

| Claim | Verdict | Evidence |
|---|---|---|
| Axiom purity, `axiom-audit` CI | VERIFIED | `.github/workflows/lean_action_ci.yml:28`; `tools/` |
| Dimensionless core + additive `Dimensions` over "rational exponent vectors over an abelian group" | VERIFIED, one correction | `Dimensions.lean:41` — `Dimension` has **four** components ⟨L, M, T, Θ⟩ over `ℚ`, not the six SI base dimensions the blueprint's §2.2 assumes |
| Four scope tags with the stated meanings | VERIFIED | `docs/scope-tags.tsv`: 158 EXACT, 221 REDUCED, 14 APPROXIMATION, 358 PURE-MATH as of 2026-09-20 |
| "Inverse-first principle" | VERIFIED as repo doctrine | `CONTEXT.md` "rigor, not accuracy"; `AGENTS.md` |

### 1.2 Foundational abstractions (§2)

| Claim | Verdict | Evidence / correction |
|---|---|---|
| Re-declares `partitionFunction (kB T) (g E : ι → ℝ)` and `partitionFunction_pos` | CORRECTED — **must not be redefined** | Both exist in `Boltzmann.lean:42` and downstream; AGENTS.md "define each concept once". The blueprint's signature happens to match, which makes silent duplication more likely, not less |
| `[Nonempty ι]` on levels | VERIFIED as convention, with a caveat | PR #4 (2026-09-02) removed 26 unused `[Nonempty _]` binders; add it only where a proof uses it |
| `spectralRadiance := div (div energy timeDim) (mul (qpow lengthDim 3) timeDim)` | CORRECTED — dimensionally wrong | In ⟨L,M,T,Θ⟩ this evaluates to ⟨−1, 1, −4, 0⟩. Spectral radiance per unit wavelength (W m⁻² sr⁻¹ m⁻¹) is ⟨−1, 1, −3, 0⟩. The extra `timeDim` factor is the error |
| `forward_intensity_radiance_homogeneous : div (mul (mul einsteinA energy) numberDensity) lengthDim = spectralRadiance` by `ext <;> norm_num` | CORRECTED — false, would not compile | LHS = ⟨−1,1,−3,0⟩ − ⟨1,0,0,0⟩ = ⟨−2, 1, −3, 0⟩. The volume emission coefficient `A·(hν)·n` is ⟨−1,1,−3,0⟩ (W m⁻³ sr⁻¹); the slab-integrated quantity is `mul lengthDim (…)` = ⟨0,1,−3,0⟩ (W m⁻² sr⁻¹). Dividing by length is the wrong direction. Correct statements are given in `03-module-specs.md` §5 |

### 1.3 Module 1 — Z-stage Saha cascade (§3.1)

| Claim | Verdict | Evidence / correction |
|---|---|---|
| "Existing formalization (SahaEquilibrium.lean) models a two-stage equilibrium" | VERIFIED (per element: neutral + first ion), **but the blueprint under-reports what exists** | `SahaEquilibrium.lean`: `multiElementIonized` (:286), `multiElementIonized_strictAntiOn` (:295), `multiElement_exists_pos_fixedPoint` (:314), `multiElement_pos_fixedPoint_unique` (:363), damped iteration `dampedMultiElementIter_{contraction,tendsto}` (:778, :869), direct iteration `multiElementIonized_iter_tendsto` (:946), `SahaContraction.lean`, `MatrixIonizationCoupling.lean` — the whole multi-element charge-neutrality theory at Z = 1 is DONE |
| Milestone 1 bullets "Prove Q_s(n_e) strictly antitone", "prove uniqueness via IVT + StrictAntiOn" | DONE at Z = 1; NEW only for Z ≥ 2 | The genuine content is the cascade. Its `sahaStageProduct` / `stageFraction` / `speciesCharge` design is sound (see 03 §1) |
| "Verify reduction to `sahaEquilibriumNe` when Z_s = 1" | CORRECTED (wrong target) | At Z ≡ 1, `speciesCharge Z S Ntot ne = Ntot·S₀/(ne + S₀)` is the summand of `multiElementIonized`; the reduction target is `multiElementIonized`, and only then `multiElement_single_eq_sahaEquilibriumNe` (:387) for one species |
| Variance identity via `Finset.sum_mul_sq_le_sq_mul_sq` | VERIFIED lemma exists (4 mathlib hits; already used in `ErrorBudget.lean:115`) | Strict positivity needs the strict-inequality case, which mathlib lacks (ROADMAP §3); a derivative-free monotone-likelihood-ratio route via the Chebyshev sum inequality avoids it (03 §1) |
| `intermediate_value_Icc` | VERIFIED | `Topology/Order/IntermediateValue.lean:559` |
| `hS : ∀ s z, 0 < S s z` over all `z : ℕ` | Acceptable but over-strong | Only stages `z < Z s` are used; state it as `∀ z < Z s` to keep hypotheses minimal (statement-retreat discipline cuts both ways) |

### 1.4 Module 2 — continuous profiles (§3.2)

| Claim | Verdict | Evidence / correction |
|---|---|---|
| "LineBroadening.lean and VoigtWidth.lean treat broadening exclusively at the level of scalar FWHM values" | CORRECTED — **false for the repo as a whole** | `EquivalentWidth.lean:337` `lorentzian`, `:346` `lorentzian_integrable`, `:355` `lorentzian_integral : ∫ x, lorentzian x = 1`; `LadenburgReiche.lean:84` `lorentzianG γ` with positivity and `lorentzianG_one`; `equivWidth φ τ := ∫ (1 − exp(−τ φ))` is already a continuous-profile functional |
| `lorentzian_profile_integral_eq_one` (shifted, scaled) is a new theorem | Partly DONE | Unshifted unit-width: DONE. Scaled: `lorentzianG` DONE (normalization not yet stated). Shift: new, one lemma. **mathlib already has** `ProbabilityTheory.cauchyPDFReal x₀ γ` with `lintegral_cauchyPDF_eq_one` (`Probability/Distributions/Cauchy.lean:42, :155`) |
| `gaussian_profile_integral_eq_one` via `integral_gaussian` | VERIFIED route, but reuse is better | `integral_gaussian (b) : ∫ exp(−b x²) = √(π/b)` exists (`GaussianIntegral.lean:211`). **mathlib also has** `ProbabilityTheory.gaussianPDFReal μ v` with `integral_gaussianPDFReal_eq_one` (`Gaussian/Real.lean:49, :130`). Define the profile as equal to the mathlib PDF and inherit normalization |
| Voigt normalization "by Fubini (`MeasureTheory.Integrable.prod_symm`)" | CORRECTED — lemma name does not exist (0 hits) | Use `MeasureTheory.convolution` and `integral_convolution` (`Analysis/Convolution.lean:845`): ∫ (f ⋆ g) = (∫ f)(∫ g) for integrable f, g |
| `integral_comp_mul_left`, `integral_comp_add_right` | VERIFIED names, mixed scope | `integral_comp_mul_left` exists for the whole-line Bochner integral (`Measure/Haar/NormedSpace.lean:152`); the `integral_comp_add_right` hit is the **interval**-integral version (`IntervalIntegral/Basic.lean:954`). The whole-line shift lemma is `MeasureTheory.integral_sub_right_eq_self` / `integral_add_right_eq_self`, generated by `to_additive` from `integral_div_right_eq_self` / `integral_mul_right_eq_self` (`MeasureTheory/Group/Integral.lean:102–109`); a plain `rg "theorem integral_sub_right_eq_self"` misses it, which is why an earlier draft called it unverified |
| The Lorentzian defined as `(γ/π)/((λ−λ₀)² + γ²)` | VERIFIED correct normalization | Matches `lorentzianG` up to the shift |

### 1.5 Module 3 — spectrometer operator (§3.3)

| Claim | Verdict | Evidence / correction |
|---|---|---|
| `Matrix.toLin'_injective_iff.mpr hK` | CORRECTED — no such lemma | The single `toLin'_injective` hit is in `LinearAlgebra/Matrix/SpecialLinearGroup.lean:216` (a different statement). In-repo pattern: `OLSIdentifiability.boltzmannDesign_mulVec_injective` (:119) and `_iff` (:179); mathlib route `LinearMap.ker_eq_bot` on `Matrix.mulVecLin` |
| "Connect K to `LeastSquaresFit.lean` projection inverse" | CORRECTED (scope) | `LeastSquaresFit` is the **two-parameter Boltzmann-plane** OLS (`ols_minimizes_rss` over `(m, b)`). Recovering a line-intensity vector from pixel sums needs a general full-column-rank least squares result, which does not exist in the repo (new PURE-MATH, 03 §3) |
| Pixel kernel `∫ φ R` | VERIFIED as the right object; needs integrability hypotheses | The companion's `cflibs/instrument/model.py` `InstrumentModel` applies a Gaussian response with `sigma_at_wavelength` and `apply_response`; that is the first concrete instance the module must reduce to |
| "Full column rank if lines fall in distinct bins with minimal crosstalk" | Plausible, new | Sufficient condition via strict diagonal dominance of `Kᵀ K` or a private-pixel argument (03 §3 M3) |

### 1.6 Module 4 — stoichiometry (§3.4)

| Claim | Verdict | Evidence / correction |
|---|---|---|
| `stoichiometry_closure_recovers` needs a new module | CORRECTED — it is a corollary | `preservesStoichiometry C N` forces `N = c · C` for `c = N s₀ / C s₀`; `Closure.composition_smul_invariant (hc : c ≠ 0)` (`Closure.lean:93`) finishes it. Belongs in `MatrixEffects.lean` (which already has `recoveredComposition_ratio_matrix_invariant`) or beside `TemporalEvolution`'s `hDilute` (`:29`), which is the same stoichiometric-ablation hypothesis |
| Aitchison isometry reference | VERIFIED module exists | `AitchisonIsometry.lean`, `Aitchison.lean` |
| Multi-stage sum `N_s = Σ_z N_{s,z}` feeding closure | Correct and the real link to Module 1 | `totalDensity` sums species; the cascade supplies per-species totals |

### 1.7 Roadmap and edits table (§4–5)

| Claim | Verdict |
|---|---|
| "Register new certificates C15, C16" | VERIFIED numbering is free. Existing: C1–C7, C9, C10, C12–C14 (12 predicates; C8 and C11 are unused numbers) — `Certificates.lean` |
| "Add Scenario 7" to the oracle | VERIFIED: `oracle/fixtures.json` has 6 scenarios today |
| Milestone 4 "unified `libs_inversion_well_posed` theorem" with constant `C` composed of condition numbers | Over-ambitious as stated; the composed chain exists piecewise (`NoiseToComposition.lean`, `ConditionNumber.lean`, `ErrorBudget.lean`). Treat as an integration target after Modules 1–3 land, and pre-register its statement before attempting it |
| ASCII architecture diagram placing `StoichiometryClosure` downstream of `SpectrometerForward` | Wrong direction: closure consumes recovered densities, which come from the Boltzmann/Saha inverse, not from the instrument operator. See `02-architecture.md` |

## 2. What the blueprint gets right and this spec keeps

- The cascade is the right next physics target and the variance/likelihood-ratio route is correct.
- Abstract index types over `Fintype` and no unit-carrying subtypes.
- Certificate + oracle + scope-tag as the definition of "done" for every new theorem.
- Priority order P0 cascade → P1 profiles → P2 instrument → P3 stoichiometry is kept, with P3 shrunk
  to two corollaries and P2 re-scoped.

## 3. What the blueprint is missing entirely

- Any statement-faithfulness discipline (pre-registration, adversarial review, mutation kill). The
  blueprint ships `sorry` skeletons with docstrings written as if proven, which is exactly the pattern
  `scripts/prereg.sh` exists to prevent.
- Literature anchoring. No citations; `docs/citation-whitelist.tsv` governs which may be used.
- The oracle bridge details (`OracleAnchors.lean`, `check_fixtures.py`, companion vendoring).
- The frontier dossiers (`docs/frontiers/*`), which already cover radiative transfer depth (09),
  spatial Abel (10), non-LTE (08), and runtime certificates (12); the new modules must be placed
  relative to them (02 §4).
