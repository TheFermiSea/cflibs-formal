# Theorem catalog

> **AUTO-GENERATED** by `scripts/gen-docs.sh`. Every named result and definition, grouped
> by module, with a one-line summary lifted from its docstring. Scope tags
> (EXACT / REDUCED / APPROXIMATION / PURE-MATH) and per-result citations are being layered
> in on top of this index — see `reviews/literature-validity-audit.md` for the current
> faithful/reduced/idealized/pure-math classification of the established corpus.

## `Alt/CSigma.lean`  (CflibsFormal.Alt)
*the C-sigma (Cσ) single-line method (alternative estimator)*

**Definitions**
- `csigmaOffset` — Per-species C-sigma offset `q_s = log (Fcal · N_s / U_s(T))`, the composition-bearing intercept of the species-`s` intensity Boltzmann plot (`boltzmann_plot_…
- `csigmaOrdinate` — C-sigma master-line ordinate of line `k` (upper level `k`) of a species with data `(N, g, E, A)`: `Y_{s,k} = log (I_{s,k} / (g_k A_k)) − q_s`, where `I_{s,k}…
- `csigmaDensity` — Recover the species number density from its C-sigma offset: `N_s = exp(q_s) · U_s(T) / Fcal`.
- `csigmaOffsetOfIntensity` — C-sigma offset read off a measured line.
- `csigmaComposition` — C-sigma composition estimator.
- `sahaBracketLog` — Log of the Saha bracket `2·(2π m_e k_B T / h²)^{3/2} / n_e`.
- `csigmaSahaOrdinate` — Saha-corrected ionic-stage ordinate.
- `csigmaConcentrationLog` — The concentration/partition normalization `ln(N_s/U_s(T))` — subtracted from a Boltzmann ordinate to remove a species' concentration-and-partition dependence…
- `csigmaUniversalOrdinate` — Universal Cσ ordinate (neutral stage).
- `csigmaSahaUniversalOrdinate` — Universal Cσ ordinate (ionic stage).

**Results**
- `csigma_master_line` — C-sigma master line.
- `csigma_master_line_indep_species` — Species independence, made explicit.
- `csigma_density_offset` — Inverse identity.
- `csigmaOffset_of_lineIntensity` — The measurement step recovers the true offset.
- `csigma_sound` — Soundness of the C-sigma estimator.
- `sound_agree` — Abstract agreement bridge.
- `csigma_agrees_of_sound` — Agreement via shared soundness (abstract classic estimator).
- `csigmaDensity_offset_eq_classicDensity` — The C-sigma and classic density inverses are the SAME function (pointwise).
- `csigmaComposition_eq_classicComposition` — The two estimators are the SAME function of the observations.
- `csigma_agrees_classic` — Cross-method agreement on a measured spectrum (forward-data instance).
- `csigma_saha_master_line` — Cσ cross-stage master line (the Saha-coupled collapse).
- `csigma_cross_stage_collapse` — Neutral and ionic lines share one line.
- `csigma_master_olsSlope` — Multi-line temperature from the Cσ master line.
- `csigma_temperature_cross_stage` — Cross-stage two-line temperature (the Saha–Boltzmann diagnostic).
- `csigma_universal_line` — The Cσ universal line.
- `csigma_universal_indep_species` — Universal-line element independence.
- `csigma_saha_universal_line` — The universal line spans both stages.

## `Alt/CSigmaCurveOfGrowth.lean`  (CflibsFormal.Alt)
*The Cσ curve of growth — self-absorption droop below the universal line*

**Definitions**
- `csigmaOpticalDepth` — Cσ optical depth `τ = σ_ℓ · ℓ · C`: the line cross-section `σ_ℓ`, the absorption path length `ℓ`, and the absorber column scale `C` (the species number densi…
- `csigmaSelfAbsorbedUniversalOrdinate` — Self-absorbed Cσ universal ordinate.

**Results**
- `csigma_curve_of_growth_droop` — The Cσ curve-of-growth droop identity (the BRIDGE).
- `csigma_curve_of_growth_thin` — Optically-thin limit (`τ = 0`).
- `csigma_curve_of_growth_le` — The droop is downward (non-strict).
- `csigma_curve_of_growth_lt` — The droop is strict for an actually thick line (`τ > 0`).
- `csigma_curve_of_growth_tendsto_universal` — The droop vanishes continuously as `τ → 0⁺`.
- `csigma_curve_of_growth_strictAntiOn` — The Cσ curve of growth is strictly antitone in optical depth.
- `csigma_curve_of_growth_density_droop` — The density droop (the σ cross-section weighting, `N`-coupled).

## `Alt/GaussMarkov.lean`  (CflibsFormal.Alt)
*Gauss–Markov optimality (BLUE) for the OLS Boltzmann-plot slope*

**Definitions**
- `linEstimator` — A general linear estimator of the ordinates.

**Results**
- `linEstimator_eq` — Estimator = deterministic part + weighted noise (pure pointwise algebra, no probability).
- `linEstimator_eq_unbiased` — Under the unbiasedness constraints the deterministic part collapses to `β`.
- `linEstimator_expectation` — Expectation of a general linear estimator `𝔼[Tₐ] = α·(∑ₖaₖ) + β·(∑ₖaₖEₖ)`.
- `linEstimator_unbiased_iff` — Unbiasedness characterization (an `iff`).
- `linEstimator_variance` — Variance of a general linear estimator `Var(Tₐ) = σ²·∑ₖaₖ²`.
- `weight_sq_ge_noiseGain` — The deterministic algebraic core of Gauss–Markov optimality `∑ₖwₖ² ≤ ∑ₖaₖ²`, with `wₖ = olsWeight E k`, for ANY unbiased weights (`∑ₖaₖ = 0`, `∑ₖaₖEₖ = 1`).
- `ols_is_blue` — THE headline — OLS is the Best Linear Unbiased Estimator (BLUE) of the slope.

## `Alt/LeastSquares.lean`  (CflibsFormal.Alt)
*the multi-line ordinary-least-squares Boltzmann-plot estimator*

**Definitions**
- `olsBoltzmannOrdinate` — The Boltzmann-plot ordinate `y_k = log (I_k / (g_k A_k))` built from a (measured / forward-model) line intensity.
- `olsDensity` — Per-species density read off the OLS intercept: `N_s = exp(b_s) · U_s(T) / Fcal`, where `b_s = olsIntercept` of the observed ordinates `y_k = log (I_k / (g_k…
- `leastSquaresComposition` — Full OLS CF-LIBS composition estimator.

**Results**
- `olsIntercept_of_forward` — Links OLS recovery to the physics.
- `olsDensity_recovers` — Per-species soundness core.
- `leastSquares_sound` — MAIN soundness.
- `leastSquares_agrees_classic` — Same-spectrum agreement on the noise-free forward fixpoint.

## `Alt/OLSVariance.lean`  (CflibsFormal.Alt)
*the Gauss–Markov variance law for the OLS Boltzmann-plot slope*

**Definitions**
- `betaHat` — The OLS-slope estimator as a random variable.

**Results**
- `olsSlope_estimator_eq` — Estimator = truth + weighted noise (pure pointwise algebra, no probability).
- `expectation_const_add_weightedNoise` — Expectation of a constant plus independent weighted noise `𝔼[c + ∑ₖ wₖ·εₖ] = c`, for zero-mean L² noise.
- `variance_const_add_weightedNoise` — Variance of a constant plus independent weighted noise `Var(c + ∑ₖ wₖ·εₖ) = σ²·∑ₖ wₖ²`, for independent, homoscedastic L² noise.
- `olsSlope_unbiased` — Unbiasedness `𝔼[β̂] = β`.
- `olsSlope_variance_noiseGain` — Slope variance as the noise gain `Var(β̂) = σ²·∑ₖ wₖ²`.
- `olsSlope_variance_eq` — THE headline — the Gauss–Markov slope-variance law `Var(β̂) = σ²/SS_E`.
- `olsSlope_variance_antitone` — Monotonicity — more energy spread ⇒ less slope variance.

## `Alt/SelfAbsorbed.lean`  (CflibsFormal.Alt)
*the self-absorption-corrected composition estimator (alternative)*

**Definitions**
- `selfAbsorbedComposition` — Self-absorption-corrected (curve-of-growth) composition estimator.

**Results**
- `classicDensity_smul_intensity` — Linearity of the algebraic inverse in the intensity.
- `selfAbsorbed_sound` — Soundness even when lines are optically thick.
- `selfAbsorbed_corrects_bias` — Bias-direction value theorem for the NAIVE classic estimator.
- `selfAbsorbed_eq_classic_corrected` — Relationship to classic — structural identity.
- `selfAbsorbed_eq_classic_thin` — Reduction to classic in the optically-thin limit.

## `Boltzmann.lean`  (CflibsFormal)
*Part 1: the Boltzmann distribution*

**Definitions**
- `boltzmannFactor` — Boltzmann factor `exp(-E / (k_B T))` for a level of energy `E`.
- `partitionFunction` — Partition function `U(T) = ∑ₖ gₖ · exp(-Eₖ / (k_B T))`.
- `population` — LTE level population `nₖ = N · gₖ · exp(-Eₖ / (k_B T)) / U(T)`.

**Results**
- `boltzmannFactor_pos` — —
- `partitionFunction_pos` — —
- `population_sum` — Normalization.
- `boltzmann_plot` — Boltzmann-plot identity.
- `temperature_from_two_levels` — Temperature from two levels.

## `Classic.lean`  (CflibsFormal.Classic)
*the classic calibration-free algorithm, assembled and sound*

**Definitions**
- `classicDensity` — Step (1)–(2) packaged as a function of the data.
- `classicComposition` — Step (3): the full classic CF-LIBS composition estimator.

**Results**
- `classicDensity_recovers` — Per-species soundness core.
- `classic_sound` — Composition soundness of the classic algorithm (given the temperature).
- `classic_sound_sum_one` — Normalization corollary.
- `classic_temperature_correct` — Temperature-correctness leg of soundness.
- `classic_calibration_free` — Calibration-free property.

## `Closure.lean`  (CflibsFormal)
*Closure of species composition*

**Definitions**
- `totalDensity` — Total number density `N_tot = ∑ₛ n s` summed over all species/stages `s`.
- `composition` — Number fraction (composition) of species `s`: `C s = n s / N_tot`, the CF-LIBS closure variable with constraint `∑ₛ C s = 1`.

**Results**
- `totalDensity_pos` — The total density is positive when at least one species exists and every species has strictly positive density.
- `composition_sum_one` — Normalization identity.
- `composition_nonneg` — Each number fraction is nonnegative (left end of the unit interval).
- `composition_le_one` — Each number fraction is at most one (right end of the unit interval).
- `composition_mem_stdSimplex` — Closure as simplex membership.
- `composition_smul_invariant` — Scale invariance.

## `CompositionIdentifiability.lean`  (CflibsFormal)
*multi-line / many-element composition identifiability*

**Definitions**
- `observeMulti` — Richer observation / forward map.

**Results**
- `observeMulti_inl` — The non-anchor component of `observeMulti` is exactly the one-line `observe` observable, so all reasoning about per-species densities reduces to the existing…
- `compositionIdentifiable` — Multi-line / many-element composition identifiability — strengthening of `general_identifiability`.
- `compositionIdentifiable_T` — Anchor-independence of the recovered temperature (value level).

## `CompositionRobustness.lean`  (CflibsFormal)
*Whole-composition-vector error propagation*

**Definitions**
- `compositionErrorBound` — Explicit a-priori bound on the per-species composition error `|composition Nhat s - composition N s|` in terms of the per-species absolute density error `del…

**Results**
- `totalDensity_abs_sub_le` — Total-density stability (shared CORE).
- `composition_sub_eq` — Exact composition-error decomposition.
- `composition_abs_sub_le` — HEADLINE per-fraction stability bound.
- `composition_abs_sub_le_bound` — The headline bound restated in terms of the named `compositionErrorBound`, giving downstream callers a single clean symbol for the per-element error budget.
- `composition_dist_vector_le` — WHOLE-VECTOR error bound.

## `Continuum.lean`  (CflibsFormal)
*the continuum background*

**Definitions**
- `contEmissivity` — Continuum emissivity (Kramers/Biberman, dimensionless reduced form).
- `contEmissivitySingly` — Continuum emissivity in a singly-ionized plasma (`n_ion ≈ n_e`), so `ε ∝ n_e²·exp(-u)/√T`.
- `totalIntensity` — Additive measured intensity at a line pixel: `I_meas = I_line + ε_cont`.
- `subtractBaseline` — Baseline (continuum) subtraction: remove a fitted continuum level `eCont` from the measured intensity.
- `lineToContRatio` — Line-to-continuum intensity ratio, reduced form `R_LC(T) = B·√T·exp(-a/T)`.

**Results**
- `contEmissivity_pos` — The continuum emissivity is strictly positive for positive constant, densities, and temperature (the `exp` factor is positive for any reduced photon energy `…
- `contEmissivitySingly_eq` — The singly-ionized continuum emissivity is the `n_ion := n_e` case of `contEmissivity`.
- `contEmissivity_strictMono_ne` — The continuum brightens with electron density.
- `lineToContRatio_pos` — The line-to-continuum ratio is strictly positive for positive `B` and temperature.
- `baseline_subtraction_exact` — Baseline subtraction is exact.
- `lineToContRatio_strictMono_T` — The line-to-continuum ratio is a thermometer — in the regime `E_k ≥ hc/λ`.

## `CurveOfGrowth.lean`  (CflibsFormal)
*the curve of growth and multi-line self-absorption*

**Definitions**
- `cogIntensity` — Curve-of-growth (self-absorbed) line intensity.
- `cogRatio` — Source-free curve-of-growth ratio.

**Results**
- `cogIntensity_slab_eq` — The curve-of-growth intensity is the radiative-transfer slab kernel.
- `cogIntensity_strictMono` — Single-line monotonicity in column density.
- `cogIntensity_injective` — Single-line injectivity (column-density recovery).
- `cogRatio_eq_intensity_ratio` — The common source scale cancels in the ratio.
- `cog_denom_pos` — Positivity of the curve-of-growth denominator on `(0, ∞)`: for `w > 0`, `n > 0` we have `0 < 1 - exp(-(w·n))` (since `w·n > 0` makes `exp(-(w·n)) < 1`).
- `exp_mul_one_sub_lt_one` — Key transcendental inequality: `exp x · (1 - x) < 1` for `x > 0`.
- `cogSlope_strictAntiOn` — The per-line *slope function* `φ(x) = x / (exp x - 1)` is strictly antitone on `(0, ∞)`.
- `cogRatio_deriv_num_neg` — The curve-of-growth ratio derivative numerator is negative on `(0, ∞)` for `w₁ > w₂ > 0`: `w₁ · exp(-(w₁·n)) · (1 - exp(-(w₂·n))) < (1 - exp(-(w₁·n))) · w₂ ·…
- `cogRatio_strictAntiOn` — Multi-line, unknown-scale identifiability (monotonicity).
- `cogRatio_injOn` — Multi-line, unknown-scale identifiability (injectivity).

## `Dimensions.lean`  (CflibsFormal)
*a dimensional-analysis layer*

**Definitions**
- `one` — The dimensionless dimension (all exponents zero) — the multiplicative identity.
- `mul` — Product of dimensions: exponents add.
- `inv` — Inverse dimension: exponents negate.
- `div` — Quotient of dimensions: `a / b = a · b⁻¹`.
- `qpow` — Rational power of a dimension: exponents scale by `q`.
- `lengthDim` — Length `L`.
- `massDim` — Mass `M`.
- `timeDim` — Time.
- `tempDim` — Temperature `Θ`.
- `energy` — Energy `M L² time⁻²`.
- `numberDensity` — Number density `L⁻³`.
- `boltzmannConstant` — Boltzmann constant `k_B` = energy / temperature.
- `planckConstant` — Planck constant `h` (action) = energy · time = `M L² time⁻¹`.
- `einsteinA` — Einstein spontaneous-emission coefficient `A_ki` (a transition rate) = `time⁻¹`.
- `siToCgs` — SI→CGS numeric-value conversion factor for a quantity of dimension `d`: `100^(d.length) · 1000^(d.mass)`.

**Results**
- `energy_eq` — Energy is `M·L²·time⁻²`.
- `boltzmannConstant_eq` — The Boltzmann constant is energy per temperature.
- `planckConstant_eq` — The Planck constant has the dimension of action, energy·time.
- `boltzmann_arg_dimensionless` — The Boltzmann-factor argument is dimensionless.
- `thermalBracket_dim` — The thermal-de-Broglie bracket has dimension `L⁻²`.
- `sahaFactor_dim` — The Saha factor has dimension of number density.
- `sahaLaw_homogeneous` — The Saha law is dimensionally homogeneous.
- `einsteinA_photonEnergy_dim` — Line-emission power is dimensionally consistent.
- `starkShift_homogeneous` — The Stark-shift law is dimensionally homogeneous.
- `shiftWidthRatio_dimensionless` — The shift-to-width ratio is dimensionless.
- `rootSumSquare_length_dim` — A squared length, square-rooted, is a length (`√(length²) = length`).
- `hydrogenStark_homogeneous` — The hydrogen-line Stark width law is dimensionally homogeneous.
- `siToCgs_one` — A dimensionless quantity has conversion factor `1`.
- `siToCgs_mul` — The conversion factor is multiplicative: `siToCgs (a·b) = siToCgs a · siToCgs b` (it is a group homomorphism `Dimension → ℝˣ`).
- `siToCgs_energy` — Energy converts J → erg by `10⁷`.
- `siToCgs_numberDensity` — Number density converts m⁻³ → cm⁻³ by `10⁻⁶`.

## `ErrorBudget.lean`  (CflibsFormal)
*the error-propagation chain and DERIVED reliability thresholds*

**Results**
- `olsSlope_stable_l1` — N-line slope sensitivity (ℓ¹ worst-case bound).
- `olsSlope_stable_l2_sq` — N-line slope sensitivity (ℓ², squared form).
- `olsSlope_stable_l2` — N-line slope sensitivity (ℓ², root form).
- `olsSlope_l1_const_two` — N = 2 reduces to the classic two-line constant.
- `olsSlope_stable_two` — N = 2 bound matches `twoLineBeta_stable`.
- `temp_rel_error_eq` — Exact temperature relative error.
- `temp_rel_error_le` — Temperature stability from a slope-error bound.
- `requiredEnergySpread_sufficient` — Minimum energy spread is SUFFICIENT for a target slope accuracy.
- `maxPerLineError_sufficient` — Maximum per-line error (minimum SNR) is SUFFICIENT for a target slope accuracy.
- `abs_exp_sub_one_le` — A clean exponential perturbation bound: `|exp x − 1| ≤ exp η − 1` whenever `|x| ≤ η`.
- `relDensity_le` — Relative density error from an intercept (log-concentration) error.
- `olsIntercept_stable_centered` — Intercept (concentration) sensitivity, centered convention.
- `composition_abs_sub_le_uniform` — Uniform composition error bound.
- `composition_target_sufficient` — Composition accuracy ⇒ per-species density-error budget (the closure-leg inverse).

## `ForwardMap.lean`  (CflibsFormal)
*Part 4: the optically-thin forward map*

**Definitions**
- `lineIntensity` — Integrated intensity of the optically-thin emission line for the bound-bound transition with upper level `k`: `I_{ki} = Fcal · A_k · n_k`, where `n_k = popul…

**Results**
- `lineIntensity_pos` — Positivity of the observable.
- `boltzmann_plot_intensity` — Intensity Boltzmann-plot identity.
- `temperature_from_two_lines` — Temperature from two lines.

## `ForwardMapEnergy.lean`  (CflibsFormal)
*the energy-intensity forward map and convention equivalence*

**Definitions**
- `lineIntensityEnergy` — Energy-intensity forward map.

**Results**
- `lineIntensityEnergy_pos` — Positivity of the energy observable.
- `lineIntensityEnergy_eq_lineIntensity` — Reduction to the canonical map.
- `lineIntensityEnergy_mul_lam` — The wavelength factor cancels the photon-energy factor.
- `boltzmann_plot_intensity_wavelength` — Wavelength-form Boltzmann plot.
- `temperature_from_two_lines_wavelength` — Temperature from two lines, wavelength form.

## `HydrogenStark.lean`  (CflibsFormal)
*the hydrogen-line (Balmer) Stark electron-density diagnostic*

**Definitions**
- `hydrogenStarkFWHM` — Hydrogen Balmer-line Stark FWHM (forward map).
- `densityFromHydrogenStark` — Hydrogen-line electron-density diagnostic (inverse map).

**Results**
- `hydrogenStarkFWHM_pos` — The hydrogen-line Stark width is strictly positive for positive width parameter, reference density, and electron density.
- `densityFromHydrogenStark_recovers` — Soundness of the hydrogen-line diagnostic.
- `hydrogenStarkFWHM_strictMonoOn` — Strict monotonicity of the Balmer width in `n_e`.
- `hydrogenStarkFWHM_injOn` — Identifiability of `n_e` from the Balmer width.

## `Identifiability.lean`  (CflibsFormal)
*Part 5: identifiability of the inverse problem*

**Results**
- `temperature_identifiability` — Target 1 — temperature identifiability.
- `density_identifiability` — Target 2 — relative-density / composition identifiability.
- `electron_density_identifiability` — Target 3 — electron-density / stage-ratio identifiability via Saha.

## `Inverse.lean`  (CflibsFormal)
*Part 6: the algorithm-agnostic inverse-problem framework*

**Definitions**
- `PlasmaParams.Admissible` — Nondegeneracy / admissibility predicate bundling the positivity hypotheses the identifiability theorems require: positive temperature, strictly positive dens…
- `observe` — Observation / forward map.
- `CompositionEstimator` — A composition estimator: a map from an observation vector `(species → ℝ)` (the measured line intensities, one per species) to a composition vector `(species…
- `trueComposition` — The true composition of a parameter set: the closure number fractions `C s = N s / ∑ₜ N t` of the per-species densities, reusing `Closure.composition`.
- `Sound` — Soundness of an estimator: on any observation vector that genuinely arises from the forward model applied to an *admissible* parameter set `p`, the estimator…
- `rawCompositionEstimator` — A concrete composition estimator: normalize the raw observation vector by its own total, `est obs = composition obs`.

**Results**
- `general_identifiability` — General identifiability — the central theorem.
- `sound_estimators_agree` — Cross-method agreement bridge.
- `rawCompositionEstimator_sound` — Soundness of the raw estimator (constant-`emit` case).

## `LineBroadening.lean`  (CflibsFormal)
*line broadening (Doppler width + the Voigt Gaussian budget)*

**Definitions**
- `dopplerFWHM` — Thermal Doppler FWHM.
- `temperatureFromDoppler` — Recovered temperature from a Doppler width (the inverse of `dopplerFWHM`): `T = (Δλ_D / λ₀)² · m·c² / (8·ln2·k_B)`.
- `gaussQuadrature` — Gaussian widths add in quadrature.
- `deconvolveGaussian` — Gaussian deconvolution.

**Results**
- `dopplerFWHM_pos` — The Doppler width is strictly positive for positive wavelength, constants, and temperature.
- `dopplerFWHM_strictMono_T` — Doppler width is a thermometer (monotone).
- `doppler_recovers` — Doppler thermometry is exact.
- `gaussQuadrature_comm` — Gaussian quadrature is symmetric in its two contributions.
- `deconvolveGaussian_quadrature` — Deconvolution exactly inverts quadrature.

## `MatrixEffects.lean`  (CflibsFormal)
*matrix effects (completeness, ablation, ionization suppression)*

**Definitions**
- `detectedDensity` — Detected density `∑_{t∈D} n_t`: the total number density summed over only the DETECTED species `D` (the matrix-completeness parameter).
- `recoveredComposition` — Recovered composition under incomplete detection `Ĉ_D s = n_s / (∑_{t∈D} n_t)`: closure applied over only the detected species `D`.
- `missingFraction` — Missing (undetected) mass fraction `m = 1 − (∑_{t∈D} n_t)/(∑_t n_t)`: the share of the true number density that falls below the detection limit.
- `inflationFactor` — Inflation factor `T / (∑_{t∈D} n_t)`: the multiplicative bias of every detected element's recovered fraction caused by closing over an incomplete species set.
- `recoveredDensityOfSpectrum` — The per-species density recovered from each species' representative forward line, via `MultiSpecies.deNormalizedDensity` (a function of the FULL measured int…
- `sahaIonDensity` — Saha ion density at electron density `n_e`: `n_ion = N_tot·S/(S+n_e)` (the unique solution of `n_ion·n_e/n_neutral = S` with `n_ion + n_neutral = N_tot`).
- `sahaNeutralDensity` — Saha neutral density at electron density `n_e`: `n_neutral = N_tot·n_e/(S+n_e)`.

**Results**
- `recoveredComposition_sum_one` — The recovered fractions still close to one over the detected set: `∑_{s∈D} Ĉ_D s = 1`.
- `recoveredComposition_ratio` — Subcompositional invariance (the genuinely matrix-independent quantity).
- `recoveredComposition_ratio_matrix_invariant` — THE headline — matrix-independence of the recovered subcomposition.
- `recoveredComposition_absolute_matrix_dependent` — The absolute fractions ARE matrix-dependent.
- `detectedDensity_univ` — Detecting ALL species recovers the ordinary `totalDensity`.
- `recoveredComposition_univ` — Complete detection recovers ordinary closure.
- `detectedDensity_le_totalDensity` — The detected density never exceeds the total (omitting nonnegative terms can only shrink it).
- `inflationFactor_eq` — The inflation factor is exactly `1/(1−m)` with `m` the missing fraction.
- `one_le_inflationFactor` — Incomplete detection over-estimates: the inflation factor is `≥ 1`.
- `recoveredComposition_eq_inflation` — Recovered = true × inflation: `Ĉ_D s = C_s · (T/∑_{t∈D} n_t)`.
- `composition_le_recoveredComposition` — Over-estimation of every detected element: `C_s ≤ Ĉ_D s`.
- `missingFraction_nonneg` — The missing fraction is nonnegative.
- `recoveredDensityOfSpectrum_eq` — The recovered-density vector of a forward spectrum equals the true densities `N` pointwise.
- `recovered_ratio_from_intensities` — The recovered subcomposition from REAL forward intensities is the true ratio `N_s/N_t`, independent of the detected set `D`.
- `sahaSplit_sum` — The two stages partition the element's total density: `n_neutral + n_ion = N_tot` (exact at any `n_e`).
- `sahaSplit_saha` — The split is genuinely the Saha split: `n_ion·n_e/n_neutral = S`.
- `sahaIonDensity_antitone` — Ionization suppression.

## `MultiSpecies.lean`  (CflibsFormal)
*Multi-species / multi-stage composition glue*

**Definitions**
- `speciesComposition` — Elemental/species composition vector: the number fraction of species `s`, `C s = N s / (∑_t N t)`.
- `deNormalizedDensity` — Number density of species `s` recovered from its measured designated-line intensity `I` by dividing out the calibration `Fcal`, Einstein coefficient `A s`, d…

**Results**
- `speciesComposition_sum_one` — Multi-species closure.
- `speciesComposition_mem_stdSimplex` — Multi-species closure as simplex membership.
- `deNormalized_lineIntensity` — Inversion identity.
- `density_ratio_from_intensities` — Density-from-intensity bridge.

## `OLS.lean`  (CflibsFormal)
*the ordinary-least-squares algebraic foundation*

**Definitions**
- `mean` — Arithmetic mean of `f` over the `Fintype` of lines: `(∑ k, f k) / card ι`.
- `olsSlope` — Ordinary-least-squares slope of the Boltzmann-plot points `(E k, y k)`: covariance over variance, `(∑_k (E k − mean E)(y k − mean y)) / (∑_k (E k − mean E)²)`.
- `olsIntercept` — Ordinary-least-squares intercept `b = ybar − m·Ebar`.
- `olsWeight` — Gauss–Markov weight `wₖ = (Eₖ − Ē)/SS_E` with `SS_E = ∑ⱼ (Eⱼ − Ē)²`.

**Results**
- `centered_sum_zero` — The centered energies sum to zero: `∑ₖ (Eₖ − Ē) = 0`.
- `mean_affine` — Mean of an affine transform.
- `olsSlope_eq_centered` — OLS slope is centered-linear in the ordinates.
- `olsSlope_sub_eq` — Slope perturbation is linear in the ordinate perturbation.
- `centered_mul_self` — Centered–energy identity `∑ₖ (Eₖ − Ē)·Eₖ = ∑ₖ (Eₖ − Ē)² = SS_E`.
- `olsSlope_noise_gain` — OLS slope noise gain.
- `ols_recovers_line` — THE CRUX.

## `PartialLTE.lean`  (CflibsFormal)
*the partial-LTE thermalization limit*

**Definitions**
- `thermalizationLimit` — Partial-LTE thermalization (collision) limit energy `E* = (n_e/(C·√T))^(1/3)`: the McWhirter criterion inverted for the largest energy gap a plasma of electr…
- `thermalized` — Partial-LTE membership.

**Results**
- `thermalizationLimit_pos` — The thermalization limit is strictly positive for positive prefactor, temperature, and density.
- `mcwhirter_iff_thermalizationLimit` — The McWhirter bound and the thermalization limit are the same criterion, two ways.
- `lteValid_iff_thermalized` — The same criterion in the project's own vocabulary.
- `thermalizationLimit_mono_ne` — A denser plasma thermalizes more levels.
- `thermalizationLimit_antitone_T` — A hotter plasma thermalizes fewer levels.
- `thermalized_recovers_gap` — Round-trip: the thermalization limit saturates the McWhirter bound.

## `Robustness.lean`  (CflibsFormal)
*Robustness / error-propagation bounds*

**Definitions**
- `twoLineBeta` — Two-line inverse-temperature (slope) estimate from measured Boltzmann-plot ordinates `yi = log(I_i/(g_i A_i))`, `yj = log(I_j/(g_j A_j))` at upper-level ener…
- `logRatioIntercept` — Recovered log number-density ratio of two species `s`, `t` from their measured Boltzmann-plot *intercepts* `bs = log(Fcal · N_s / U_s)`, `bt = log(Fcal · N_t…

**Results**
- `twoLineBeta_stable` — Temperature stability.
- `logRatioIntercept_stable` — Composition/ratio stability.
- `twoLineBeta_continuous` — Continuous dependence.
- `twoLineBeta_stable_sharp` — Sharpness of the temperature bound.
- `logRatioIntercept_stable_sharp` — Sharpness of the composition/ratio bound.

## `Saha.lean`  (CflibsFormal)
*Part 2: the Saha ionization equilibrium*

**Definitions**
- `thermalBracket` — The de-Broglie bracket `2π·m_e·k_B·T / h²` appearing (to the `3/2` power) in the Saha factor.
- `sahaFactor` — Saha factor `S(T)`: the full right-hand side of the Saha equation *excluding* the electron density `n_e` and the stage population ratio.
- `electronDensityFromRatio` — Saha density diagnostic.
- `chargeNeutrality` — Charge neutrality for a multi-stage plasma: the electron density equals the sum over ionization stages `s` of `z s · n_s` (charge-weighted ion densities).

**Results**
- `thermalBracket_pos` — The thermal-de-Broglie bracket is strictly positive when the physical constants and temperature are positive (`h ≠ 0` suffices, here via `h > 0`).
- `sahaFactor_pos` — Positivity of the Saha factor.
- `saha_relation` — Saha law ⇔ density inversion.
- `electronDensity_antitone` — Density diagnostic is injective.
- `log_sahaFactor` — Saha-plot log identity.
- `chargeNeutrality_two_stage` — Charge neutrality, two-stage form.

## `SahaInverse.lean`  (CflibsFormal)
*Part 6: coupling Saha into the inverse problem*

**Definitions**
- `sahaBoltzmannOrdinate` — Saha–Boltzmann plot ordinate (single stage / single line).
- `stageIntercept` — Stage intercept of the Saha–Boltzmann plot.

**Results**
- `sahaBoltzmann_plot` — Saha–Boltzmann plot.
- `sahaBoltzmann_shift_eq_log_saha` — Saha–Boltzmann shift equals the log Saha factor.
- `saha_joint_identifiability` — Joint identifiability of `(T, n_e)` from the Saha–Boltzmann plot.

## `SelfAbsorption.lean`  (CflibsFormal)
*self-absorption / optical-thickness-aware forward map*

**Definitions**
- `selfAbsorptionFactor` — Curve-of-growth self-absorption factor `SA(τ)`.
- `selfAbsorbedIntensity` — Optically-thick (self-absorbed) line intensity.
- `slabIntensity` — Radiative-transfer slab intensity.

**Results**
- `selfAbsorptionFactor_pos` — Positivity of the self-absorption factor.
- `selfAbsorptionFactor_le_one` — Self-absorption only dims.
- `selfAbsorptionFactor_strictAntiOn` — Strict monotonicity of the escape factor.
- `selfAbsorptionFactor_tendsto_one` — Thin limit.
- `selfAbsorbedIntensity_le_lineIntensity` — Bias-direction theorem (non-strict).
- `selfAbsorbedIntensity_lt_lineIntensity` — Bias-direction theorem (strict).
- `slabIntensity_le_thin` — Radiative-transfer dimming, derived.
- `slabIntensity_eq_thin_mul_SA` — Curve-of-growth identity (DERIVED, not definitional).
- `selfAbsorbedIntensity_eq_slab` — The model intensity IS a radiative-transfer slab intensity.
- `lineIntensity_eq_selfAbsorbedIntensity_div` — Exact curve-of-growth correction (model left-inverse).

## `SelfAbsorptionInverse.lean`  (CflibsFormal)
*Self-absorption coupled into the inverse problem — identifiability preserved vs. lost*

**Definitions**
- `thickObserve` — Optically-thick observation map.

**Results**
- `lineIntensity_smul_left` — `N`-linearity of the optically-thin forward map.
- `thick_density_identifiability` — PRESERVED (known, matched `τ`) — per-species density identifiability.
- `thick_composition_identifiability` — PRESERVED (known, matched `τ`) — multi-species composition identifiability.
- `selfAbsorption_breaks_identifiability` — LOST (unknown `τ`) — self-absorption breaks identifiability.

## `SelfReversal.lean`  (CflibsFormal)
*self-reversal (the two-zone line dip)*

**Definitions**
- `emergentIntensity` — Two-zone emergent intensity.

**Results**
- `emergentIntensity_nonneg` — The two-zone emergent intensity is nonnegative for nonnegative source functions and optical depths.
- `selfReversal_noShell` — No-shell limit (exact).
- `selfReversal_uniformSource` — Uniform-source limit (exact).
- `emergentIntensity_strictAnti_shell` — The self-reversal dip mechanism.

## `SpatialForward.lean`  (CflibsFormal)
*spatially-resolved (discrete Abel / onion-peeling) forward model*

**Definitions**
- `chordIntensity` — The line-of-sight forward map for the onion-peeling discretization of the Abel transform: the lateral chord-intensity vector `I = L · ε`, where `ε : Fin N →…

**Results**
- `chordGeometry_det_ne_zero` — The path-length matrix of a physical onion-peeling geometry is nonsingular: its determinant is the product of the (positive) self-path-lengths, hence nonzero.
- `chordGeometry_isUnit` — The path-length matrix is invertible.
- `chord_profile_identifiable` — Spatial identifiability — relaxing single-zone homogeneity.
- `singleZone_identifiable` — The single-zone homogeneous model (`N = 1`) obtained by instantiating the general spatial identifiability at `N = 1`.

## `StarkBroadening.lean`  (CflibsFormal)
*Stark broadening + the McWhirter LTE criterion*

**Definitions**
- `starkFWHM` — Electron-impact (Stark) full width at half maximum.
- `starkDensity` — Stark electron-density diagnostic (inverse map).
- `mcWhirterBound` — McWhirter lower bound on electron density for LTE.
- `lteValid` — LTE-validity predicate.

**Results**
- `starkDensity_recovers` — Soundness of the Stark diagnostic.
- `starkFWHM_strictMono` — Strict monotonicity of the Stark width in `n_e`.
- `starkFWHM_injective` — Identifiability of `n_e` from the Stark width.
- `starkFWHM_isLinear` — Griem linearity, bundled (`IsLinearMap`).
- `mcWhirterBound_mono_T` — McWhirter bound increases with temperature.
- `mcWhirterBound_mono_dE` — McWhirter bound increases with the energy gap.
- `stark_saha_lte_consistent` — Stark–Saha LTE cross-check (conditional bundling).

## `StarkShift.lean`  (CflibsFormal)
*the Stark line-shift electron-density diagnostic*

**Definitions**
- `starkShift` — Stark line-shift forward map (Griem linear).
- `starkDensityFromShift` — Stark-shift electron-density diagnostic (inverse map).
- `shiftWidthRatio` — The tabulated, `n_e`-independent shift-to-width ratio `d_ref/w_ref`.

**Results**
- `starkShift_pos_of_dRef_pos` — Sign-aware positivity (red shift).
- `starkDensityFromShift_recovers` — Soundness of the Stark-shift diagnostic.
- `starkShift_isLinear` — Griem linearity, bundled (`IsLinearMap`).
- `starkShift_strictMono_of_pos` — Conditional monotonicity — red shift.
- `starkShift_strictAnti_of_neg` — Conditional anti-monotonicity — blue shift.
- `starkShift_injective` — Identifiability of `n_e` from the shift.
- `starkShift_abs_strictMono` — Sign-robust magnitude monotonicity.
- `shiftWidthRatio_indep_ne` — The shift-to-width ratio is `n_e`-independent — and that is exactly why it is *not* a density diagnostic.
- `shift_width_density_agree` — Shift- and width-route densities coincide — conditioned on the line-ID check.

## `TemporalEvolution.lean`  (CflibsFormal)
*time-resolved (gate-delayed) recovery*

**Definitions**
- `gateSpectrum` — Gate spectrum.
- `gateComposition` — Gate composition estimator.
- `gateSahaFactor` — Gate Saha factor.
- `gateNeutralSpectrum` — Gate neutral spectrum.
- `gateSahaTotalDensity` — Saha-completed total element density at the gate.
- `gateSahaComposition` — Gate Saha composition estimator.
- `lteWindow` — LTE window.

**Results**
- `temporal_temperature_insitu` — In-situ gate temperature (Boltzmann slope).
- `temporal_composition_invariant` — Per-gate composition soundness (dilution cancels).
- `temporal_composition_gate_independent` — Cross-gate composition invariance (thin corollary).
- `gateSahaTotalDensity_eq` — The Saha completion is sound at the gate — `n_e` cancels (load-bearing).
- `temporal_saha_composition_invariant` — Per-gate Saha composition soundness (`n_e` and `ρ` both cancel).
- `temporal_saha_composition_gate_independent` — Cross-gate Saha composition invariance (HEADLINE — thin corollary).
- `mem_lteWindow_thermalized` — Applicability: gate in the LTE window ⇒ thermalized.
- `mcwhirter_requirement_antitone` — McWhirter requirement falls as the plasma cools.

## `VoigtWidth.lean`  (CflibsFormal)
*the Voigt FWHM combination (Olivero–Longbothum)*

**Definitions**
- `voigtFWHM` — Voigt FWHM (Olivero–Longbothum 1977).

**Results**
- `voigtFWHM_pos` — The Voigt FWHM is strictly positive when there is a nonzero Gaussian width (always true in practice — thermal Doppler — for `wL ≥ 0`).
- `voigtFWHM_ge_gauss` — A Voigt profile is at least as wide as its Gaussian part: `w_G ≤ w_V`.
- `voigtFWHM_ge_lorentz` — A Voigt profile is at least as wide as its Lorentzian part: `w_L ≤ w_V`.
- `voigtFWHM_mono_wL` — The Voigt FWHM is increasing in the Lorentzian width `wL`.
- `voigtFWHM_mono_wG` — The Voigt FWHM is increasing in the Gaussian width `wG`.
- `voigt_gaussian_limit` — Pure-Gaussian limit (exact).
- `voigt_lorentzian_limit` — Pure-Lorentzian limit (honest restatement).

