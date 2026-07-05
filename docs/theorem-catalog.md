# Theorem catalog

> **AUTO-GENERATED** by `scripts/gen-docs.sh`. Every named result and definition, grouped by
> module, with a one-line docstring summary. Each **result** carries a curated **scope tag**
> (the integrity spine) + citation from `docs/scope-tags.tsv`; the docs-sync CI gate fails if
> any result is untagged, so a new theorem cannot land without declaring its epistemic status.

**Scope-tag mix** (354 results): **EXACT** 119 · **REDUCED** 77 · **APPROXIMATION** 9 · **PURE-MATH** 149

`EXACT` = exact identity faithfully encoding the cited physics · `REDUCED` = valid dimensionless/lumped-factor form · `APPROXIMATION` = documented idealization / limiting case · `PURE-MATH` = infrastructure lemma, no physical claim. Classification cross-checked against `reviews/literature-validity-audit.md`.

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
- `EXACT` · `csigma_master_line` — C-sigma master line.  _[Aguilera & Aragón 2007]_
- `EXACT` · `csigma_master_line_indep_species` — Species independence, made explicit.  _[Aguilera & Aragón 2007]_
- `REDUCED` · `csigma_density_offset` — Inverse identity.  _[Aguilera & Aragón 2007]_
- `EXACT` · `csigmaOffset_of_lineIntensity` — The measurement step recovers the true offset.  _[Aguilera & Aragón 2007]_
- `EXACT` · `csigma_sound` — Soundness of the C-sigma estimator.  _[Aguilera & Aragón 2007]_
- `PURE-MATH` · `sound_agree` — Abstract agreement bridge.
- `PURE-MATH` · `csigma_agrees_of_sound` — Agreement via shared soundness (abstract classic estimator).
- `PURE-MATH` · `csigmaDensity_offset_eq_classicDensity` — The C-sigma and classic density inverses are the SAME function (pointwise).
- `PURE-MATH` · `csigmaComposition_eq_classicComposition` — The two estimators are the SAME function of the observations.
- `PURE-MATH` · `csigma_agrees_classic` — Cross-method agreement on a measured spectrum (forward-data instance).
- `EXACT` · `csigma_saha_master_line` — Cσ cross-stage master line (the Saha-coupled collapse).  _[Aragón & Aguilera 2014]_
- `EXACT` · `csigma_cross_stage_collapse` — Neutral and ionic lines share one line.  _[Aragón & Aguilera 2014]_
- `EXACT` · `csigma_master_olsSlope` — Multi-line temperature from the Cσ master line.  _[Aguilera & Aragón 2007]_
- `EXACT` · `csigma_temperature_cross_stage` — Cross-stage two-line temperature (the Saha–Boltzmann diagnostic).  _[Aragón & Aguilera 2014]_
- `EXACT` · `csigma_universal_line` — The Cσ universal line.  _[Aragón & Aguilera 2014]_
- `EXACT` · `csigma_universal_indep_species` — Universal-line element independence.  _[Aragón & Aguilera 2014]_
- `EXACT` · `csigma_saha_universal_line` — The universal line spans both stages.  _[Aragón & Aguilera 2014]_

## `Alt/CSigmaCurveOfGrowth.lean`  (CflibsFormal.Alt)
*The Cσ curve of growth — self-absorption droop below the universal line*

**Definitions**
- `csigmaOpticalDepth` — Cσ optical depth `τ = σ_ℓ · ℓ · C`: the line cross-section `σ_ℓ`, the absorption path length `ℓ`, and the absorber column scale `C` (the species number densi…
- `csigmaSelfAbsorbedUniversalOrdinate` — Self-absorbed Cσ universal ordinate.

**Results**
- `APPROXIMATION` · `csigma_curve_of_growth_droop` — The Cσ curve-of-growth droop identity (the BRIDGE).  _[Aragón & Aguilera 2014]_
- `APPROXIMATION` · `csigma_curve_of_growth_thin` — Optically-thin limit (`τ = 0`).  _[Aragón & Aguilera 2014]_
- `APPROXIMATION` · `csigma_curve_of_growth_le` — The droop is downward (non-strict).  _[Aragón & Aguilera 2014]_
- `APPROXIMATION` · `csigma_curve_of_growth_lt` — The droop is strict for an actually thick line (`τ > 0`).  _[Aragón & Aguilera 2014]_
- `PURE-MATH` · `csigma_curve_of_growth_tendsto_universal` — The droop vanishes continuously as `τ → 0⁺`.
- `PURE-MATH` · `csigma_curve_of_growth_strictAntiOn` — The Cσ curve of growth is strictly antitone in optical depth.
- `APPROXIMATION` · `csigma_curve_of_growth_density_droop` — The density droop (the σ cross-section weighting, `N`-coupled).  _[Aragón & Aguilera 2014]_

## `Alt/GaussMarkov.lean`  (CflibsFormal.Alt)
*Gauss–Markov optimality (BLUE) for the OLS Boltzmann-plot slope*

**Definitions**
- `linEstimator` — A general linear estimator of the ordinates.

**Results**
- `PURE-MATH` · `linEstimator_eq` — Estimator = deterministic part + weighted noise (pure pointwise algebra, no probability).
- `PURE-MATH` · `linEstimator_eq_unbiased` — Under the unbiasedness constraints the deterministic part collapses to `β`.
- `PURE-MATH` · `linEstimator_expectation` — Expectation of a general linear estimator `𝔼[Tₐ] = α·(∑ₖaₖ) + β·(∑ₖaₖEₖ)`.
- `PURE-MATH` · `linEstimator_unbiased_iff` — Unbiasedness characterization (an `iff`).
- `EXACT` · `linEstimator_variance` — Variance of a general linear estimator `Var(Tₐ) = σ²·∑ₖaₖ²`.  _[Aitken 1935]_
- `PURE-MATH` · `weight_sq_ge_noiseGain` — The deterministic algebraic core of Gauss–Markov optimality `∑ₖwₖ² ≤ ∑ₖaₖ²`, with `wₖ = olsWeight E k`, for ANY unbiased weights (`∑ₖaₖ = 0`, `∑ₖaₖEₖ = 1`).
- `EXACT` · `ols_is_blue` — THE headline — OLS is the Best Linear Unbiased Estimator (BLUE) of the slope.  _[Aitken 1935]_

## `Alt/LeastSquares.lean`  (CflibsFormal.Alt)
*the multi-line ordinary-least-squares Boltzmann-plot estimator*

**Definitions**
- `olsBoltzmannOrdinate` — The Boltzmann-plot ordinate `y_k = log (I_k / (g_k A_k))` built from a (measured / forward-model) line intensity.
- `olsDensity` — Per-species density read off the OLS intercept: `N_s = exp(b_s) · U_s(T) / Fcal`, where `b_s = olsIntercept` of the observed ordinates `y_k = log (I_k / (g_k…
- `leastSquaresComposition` — Full OLS CF-LIBS composition estimator.

**Results**
- `REDUCED` · `olsIntercept_of_forward` — Links OLS recovery to the physics.  _[Ciucci 1999]_
- `REDUCED` · `olsDensity_recovers` — Per-species soundness core.  _[Ciucci 1999]_
- `REDUCED` · `leastSquares_sound` — MAIN soundness.  _[Tognoni 2010]_
- `REDUCED` · `leastSquares_agrees_classic` — Same-spectrum agreement on the noise-free forward fixpoint.  _[Tognoni 2010]_
- `REDUCED` · `olsBoltzmann_forward_feasible` — The noise-free forward spectrum is exactly least-squares-feasible.  _[Tognoni 2010]_
- `REDUCED` · `olsBoltzmann_forward_feasible_at` — Feasibility form.  _[Tognoni 2010]_

## `Alt/OLSVariance.lean`  (CflibsFormal.Alt)
*the Gauss–Markov variance law for the OLS Boltzmann-plot slope*

**Definitions**
- `betaHat` — The OLS-slope estimator as a random variable.

**Results**
- `PURE-MATH` · `olsSlope_estimator_eq` — Estimator = truth + weighted noise (pure pointwise algebra, no probability).
- `PURE-MATH` · `expectation_const_add_weightedNoise` — Expectation of a constant plus independent weighted noise `𝔼[c + ∑ₖ wₖ·εₖ] = c`, for zero-mean L² noise.
- `PURE-MATH` · `variance_const_add_weightedNoise` — Variance of a constant plus UNCORRELATED weighted noise `Var(c + ∑ₖ wₖ·εₖ) = σ²·∑ₖ wₖ²`, for pairwise-uncorrelated, homoscedastic L² noise.
- `REDUCED` · `olsSlope_unbiased` — Unbiasedness `𝔼[β̂] = β`.  _[Aitken 1935]_
- `EXACT` · `olsSlope_variance_noiseGain` — Slope variance as the noise gain `Var(β̂) = σ²·∑ₖ wₖ²`.  _[Aitken 1935]_
- `EXACT` · `olsSlope_variance_eq` — THE headline — the Gauss–Markov slope-variance law `Var(β̂) = σ²/SS_E`.  _[Aitken 1935]_
- `EXACT` · `olsSlope_variance_antitone` — Monotonicity — more energy spread ⇒ less slope variance.  _[Aitken 1935]_

## `Alt/SelfAbsorbed.lean`  (CflibsFormal.Alt)
*the self-absorption-corrected composition estimator (alternative)*

**Definitions**
- `selfAbsorbedComposition` — Self-absorption-corrected (curve-of-growth) composition estimator.

**Results**
- `PURE-MATH` · `classicDensity_smul_intensity` — Linearity of the algebraic inverse in the intensity.
- `EXACT` · `selfAbsorbed_sound` — Soundness even when lines are optically thick.  _[Bulajic 2002]_
- `EXACT` · `selfAbsorbed_corrects_bias` — Bias-direction value theorem for the NAIVE classic estimator.  _[Bulajic 2002]_
- `REDUCED` · `selfAbsorbed_eq_classic_corrected` — Relationship to classic — structural identity.  _[Bulajic 2002]_
- `REDUCED` · `selfAbsorbed_eq_classic_thin` — Reduction to classic in the optically-thin limit.  _[Bulajic 2002]_

## `Analysis.lean`  (CflibsFormal)
*Shared analysis scaffolding*

**Results**
- `PURE-MATH` · `strictAntiOn_div_of_deriv_num_neg` — Quotient strictly antitone from a negative derivative numerator.

## `AtomicDataPerturbation.lean`  (CflibsFormal)
*the atomic-data perturbation channel*

**Definitions**
- `responseFactor` — Per-line response factor `ρ = g_u · A_u · exp(−E_u/(k_B T)) / U(T)`.
- `recoveredDensity` — Recovered per-species density under wrong atomic data.
- `tempResponseErrorBound` — Named temperature-response error bound.
- `recoveredDensityAtT` — Recovered per-species density at a wrong temperature.

**Results**
- `EXACT` · `classicDensity_aliasing` — EXACT aliasing identity.  _[Tognoni 2010]_
- `REDUCED` · `classicDensity_aliasing_error` — REDUCED lumped relative-error bound.  _[Tognoni 2010]_
- `REDUCED` · `classicDensity_aliasing_error_channels` — REDUCED two-channel relative-error bound (`E' = E`).  _[Tognoni 2010]_
- `REDUCED` · `classicComposition_atomicData_error` — REDUCED composition corollary.  _[Tognoni 2010]_
- `EXACT` · `classicDensity_temperature_aliasing` — EXACT temperature-aliasing identity.  _[Tognoni 2010]_
- `REDUCED` · `classicDensity_aliasing_error_energy` — REDUCED energy-channel isolation (gap #2 residual).  _[Tognoni 2010]_
- `REDUCED` · `classicDensity_temperature_aliasing_error` — REDUCED temperature-error bound.  _[Tognoni 2010]_
- `REDUCED` · `classicComposition_temperature_error` — REDUCED composition corollary (temperature channel).  _[Tognoni 2010]_

## `Boltzmann.lean`  (CflibsFormal)
*Part 1: the Boltzmann distribution*

**Definitions**
- `boltzmannFactor` — Boltzmann factor `exp(-E / (k_B T))` for a level of energy `E`.
- `partitionFunction` — Partition function `U(T) = ∑ₖ gₖ · exp(-Eₖ / (k_B T))`.
- `population` — LTE level population `nₖ = N · gₖ · exp(-Eₖ / (k_B T)) / U(T)`.

**Results**
- `PURE-MATH` · `boltzmannFactor_pos` — —
- `PURE-MATH` · `partitionFunction_pos` — —
- `EXACT` · `population_sum` — Normalization.  _[Boltzmann]_
- `EXACT` · `boltzmann_plot` — Boltzmann-plot identity.  _[Boltzmann]_
- `EXACT` · `temperature_from_two_levels` — Temperature from two levels.  _[Boltzmann]_

## `Classic.lean`  (CflibsFormal.Classic)
*the classic calibration-free algorithm, assembled and sound*

**Definitions**
- `classicDensity` — Step (1)–(2) packaged as a function of the data.
- `classicComposition` — Step (3): the full classic CF-LIBS composition estimator.

**Results**
- `EXACT` · `classicDensity_recovers` — Per-species soundness core.  _[Ciucci 1999]_
- `EXACT` · `classic_sound` — Composition soundness of the classic algorithm (given the temperature).  _[Ciucci 1999]_
- `PURE-MATH` · `classic_sound_sum_one` — Normalization corollary.
- `REDUCED` · `classic_temperature_correct` — Temperature-correctness leg of soundness.  _[Ciucci 1999]_
- `EXACT` · `classic_calibration_free` — Calibration-free property.  _[Ciucci 1999]_

## `Closure.lean`  (CflibsFormal)
*Closure of species composition*

**Definitions**
- `totalDensity` — Total number density `N_tot = ∑ₛ n s` summed over all species/stages `s`.
- `composition` — Number fraction (composition) of species `s`: `C s = n s / N_tot`, the CF-LIBS closure variable with constraint `∑ₛ C s = 1`.

**Results**
- `PURE-MATH` · `totalDensity_pos` — The total density is positive when at least one species exists and every species has strictly positive density.
- `EXACT` · `composition_sum_one` — Normalization identity.  _[Ciucci 1999]_
- `PURE-MATH` · `composition_nonneg` — Each number fraction is nonnegative (left end of the unit interval).
- `PURE-MATH` · `composition_le_one` — Each number fraction is at most one (right end of the unit interval).
- `EXACT` · `composition_mem_stdSimplex` — Closure as simplex membership.  _[Ciucci 1999]_
- `EXACT` · `composition_smul_invariant` — Scale invariance.  _[Ciucci 1999]_

## `CompositionIdentifiability.lean`  (CflibsFormal)
*multi-line / many-element composition identifiability*

**Definitions**
- `observeMulti` — Richer observation / forward map.

**Results**
- `PURE-MATH` · `observeMulti_inl` — The non-anchor component of `observeMulti` is exactly the one-line `observe` observable, so all reasoning about per-species densities reduces to the existing…
- `EXACT` · `compositionIdentifiable` — Multi-line / many-element composition identifiability — strengthening of `general_identifiability`.  _[Ciucci 1999]_
- `EXACT` · `compositionIdentifiable_T` — Anchor-independence of the recovered temperature (value level).  _[Ciucci 1999]_

## `CompositionRobustness.lean`  (CflibsFormal)
*Whole-composition-vector error propagation*

**Definitions**
- `compositionErrorBound` — Explicit a-priori bound on the per-species composition error `|composition Nhat s - composition N s|` in terms of the per-species absolute density error `del…

**Results**
- `PURE-MATH` · `totalDensity_abs_sub_le` — Total-density stability (shared CORE).
- `PURE-MATH` · `composition_sub_eq` — Exact composition-error decomposition.
- `PURE-MATH` · `composition_abs_sub_le` — HEADLINE per-fraction stability bound.
- `PURE-MATH` · `composition_abs_sub_le_bound` — The headline bound restated in terms of the named `compositionErrorBound`, giving downstream callers a single clean symbol for the per-element error budget.
- `PURE-MATH` · `composition_dist_vector_le` — WHOLE-VECTOR error bound.

## `Continuum.lean`  (CflibsFormal)
*the continuum background*

**Definitions**
- `contEmissivity` — Continuum emissivity (Kramers/Biberman, dimensionless reduced form).
- `contEmissivitySingly` — Continuum emissivity in a singly-ionized plasma (`n_ion ≈ n_e`), so `ε ∝ n_e²·exp(-u)/√T`.
- `totalIntensity` — Additive measured intensity at a line pixel: `I_meas = I_line + ε_cont`.
- `subtractBaseline` — Baseline (continuum) subtraction: remove a fitted continuum level `eCont` from the measured intensity.
- `lineToContRatio` — Line-to-continuum intensity ratio, reduced form `R_LC(T) = B·√T·exp(-a/T)`.

**Results**
- `PURE-MATH` · `contEmissivity_pos` — The continuum emissivity is strictly positive for positive constant, densities, and temperature (the `exp` factor is positive for any reduced photon energy `…
- `PURE-MATH` · `contEmissivitySingly_eq` — The singly-ionized continuum emissivity is the `n_ion := n_e` case of `contEmissivity`.
- `PURE-MATH` · `contEmissivity_strictMono_ne` — The continuum brightens with electron density.
- `PURE-MATH` · `lineToContRatio_pos` — The line-to-continuum ratio is strictly positive for positive `B` and temperature.
- `EXACT` · `baseline_subtraction_exact` — Baseline subtraction is exact.  _[Cremers & Radziemski 2013]_
- `REDUCED` · `lineToContRatio_strictMono_T` — The line-to-continuum ratio is a thermometer — in the regime `E_k ≥ hc/λ`.  _[Aragón & Aguilera 2008]_

## `CurveOfGrowth.lean`  (CflibsFormal)
*the curve of growth and multi-line self-absorption*

**Definitions**
- `cogIntensity` — Curve-of-growth (self-absorbed) line intensity.
- `cogRatio` — Source-free curve-of-growth ratio.

**Results**
- `EXACT` · `cogIntensity_slab_eq` — The curve-of-growth intensity is the radiative-transfer slab kernel.  _[Gornushkin 1999]_
- `EXACT` · `cogIntensity_strictMono` — Single-line monotonicity in column density.  _[Cristoforetti–Tognoni 2013]_
- `EXACT` · `cogIntensity_injective` — Single-line injectivity (column-density recovery).  _[Cristoforetti–Tognoni 2013]_
- `PURE-MATH` · `cogRatio_eq_intensity_ratio` — The common source scale cancels in the ratio.
- `PURE-MATH` · `cog_denom_pos` — Positivity of the curve-of-growth denominator on `(0, ∞)`: for `w > 0`, `n > 0` we have `0 < 1 - exp(-(w·n))` (since `w·n > 0` makes `exp(-(w·n)) < 1`).
- `PURE-MATH` · `exp_mul_one_sub_lt_one` — Key transcendental inequality: `exp x · (1 - x) < 1` for `x > 0`.
- `PURE-MATH` · `cogSlope_strictAntiOn` — The per-line *slope function* `φ(x) = x / (exp x - 1)` is strictly antitone on `(0, ∞)`.
- `PURE-MATH` · `cogRatio_deriv_num_neg` — The curve-of-growth ratio derivative numerator is negative on `(0, ∞)` for `w₁ > w₂ > 0`: `w₁ · exp(-(w₁·n)) · (1 - exp(-(w₂·n))) < (1 - exp(-(w₁·n))) · w₂ ·…
- `PURE-MATH` · `cogRatio_strictAntiOn` — Multi-line, unknown-scale identifiability (monotonicity).
- `EXACT` · `cogRatio_injOn` — Multi-line, unknown-scale identifiability (injectivity).  _[Cristoforetti–Tognoni 2013]_

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
- `PURE-MATH` · `energy_eq` — Energy is `M·L²·time⁻²`.
- `PURE-MATH` · `boltzmannConstant_eq` — The Boltzmann constant is energy per temperature.
- `PURE-MATH` · `planckConstant_eq` — The Planck constant has the dimension of action, energy·time.
- `PURE-MATH` · `boltzmann_arg_dimensionless` — The Boltzmann-factor argument is dimensionless.
- `PURE-MATH` · `thermalBracket_dim` — The thermal-de-Broglie bracket has dimension `L⁻²`.
- `PURE-MATH` · `sahaFactor_dim` — The Saha factor has dimension of number density.
- `PURE-MATH` · `sahaLaw_homogeneous` — The Saha law is dimensionally homogeneous.
- `PURE-MATH` · `einsteinA_photonEnergy_dim` — Line-emission power is dimensionally consistent.
- `PURE-MATH` · `starkShift_homogeneous` — The Stark-shift law is dimensionally homogeneous.
- `PURE-MATH` · `shiftWidthRatio_dimensionless` — The shift-to-width ratio is dimensionless.
- `PURE-MATH` · `rootSumSquare_length_dim` — A squared length, square-rooted, is a length (`√(length²) = length`).
- `PURE-MATH` · `hydrogenStark_homogeneous` — The hydrogen-line Stark width law is dimensionally homogeneous.
- `PURE-MATH` · `siToCgs_one` — A dimensionless quantity has conversion factor `1`.
- `PURE-MATH` · `siToCgs_mul` — The conversion factor is multiplicative: `siToCgs (a·b) = siToCgs a · siToCgs b` (it is a group homomorphism `Dimension → ℝˣ`).
- `PURE-MATH` · `siToCgs_energy` — Energy converts J → erg by `10⁷`.
- `PURE-MATH` · `siToCgs_numberDensity` — Number density converts m⁻³ → cm⁻³ by `10⁻⁶`.

## `EquivalentWidth.lean`  (CflibsFormal)
*the equivalent-width curve of growth*

**Definitions**
- `equivWidth` — Equivalent width (curve of growth).
- `lorentzian` — The (normalized) Lorentzian profile `L(x) = (1/π)·1/(1+x²)` — the natural / pressure- broadening line shape, a unit-area probability density (`∫L = 1`, `lore…

**Results**
- `PURE-MATH` · `equivWidth_integrand_integrable` — The equivalent-width integrand `1 - exp(-(τφ))` is integrable: it is sandwiched `0 ≤ 1 - exp(-(τφ)) ≤ τφ` (from `1 - exp(-y) ≤ y`) by the integrable dominati…
- `PURE-MATH` · `equivWidth_nonneg` — A line only removes flux: the equivalent width is nonnegative for `τ ≥ 0`, `φ ≥ 0`.
- `EXACT` · `equivWidth_le_thin` — The linear-regime upper bound (saturation).  _[Gornushkin 1999]_
- `EXACT` · `equivWidth_mono` — The curve of growth is increasing.  _[Gornushkin 1999]_
- `EXACT` · `equivWidth_rectangular` — The flat-profile curve of growth recovers the slab deficit.  _[Gornushkin 1999]_
- `EXACT` · `equivWidth_weakLine` — The weak-line (linear) limit of the curve of growth.  _[Gornushkin 1999]_
- `EXACT` · `slabCurve_forward_lipschitz` — Saturation kills forward sensitivity (EXACT).  _[Gornushkin 1999]_
- `EXACT` · `slabCurve_inverse_lipschitz` — Inverse ill-conditioning — the condition number of the equivalent-width inversion (EXACT).  _[Gornushkin 1999]_
- `EXACT` · `slabCurve_roundTrip_lipschitz` — Round-trip inverse-Lipschitz bound in τ (EXACT).  _[Gornushkin 1999]_
- `PURE-MATH` · `lorentzian_pos` — The Lorentzian profile is strictly positive.
- `PURE-MATH` · `lorentzian_integrable` — The Lorentzian profile is integrable: `(1 + x²)⁻¹` is (`integrable_inv_one_add_sq`) and `L` is a constant multiple of it.
- `PURE-MATH` · `lorentzian_integral` — The Lorentzian is a unit-area profile: `∫ L = 1` (since `∫ (1 + x²)⁻¹ = π`).
- `EXACT` · `equivWidth_lorentzian_sqrt_lower` — The √τ damping-wing lower bound (EXACT, within the model).  _[Gornushkin 1999]_
- `EXACT` · `nvLz_sqrt_lower_at_threshold` — Non-vacuity: the √τ lower bound fires at the threshold `τ = 8π` (hypothesis `8π ≤ 8π`), so the constant `c = (1 - e⁻¹)/(2√(2π))` gives a genuine lower bound…  _[Gornushkin 1999]_
- `EXACT` · `equivWidth_lorentzian_sqrt_upper` — The √τ damping-wing UPPER bound (EXACT, within the model).  _[Gornushkin 1999]_
- `EXACT` · `equivWidth_lorentzian_sqrt_two_sided` — The √τ damping-wing REGIME, pinned up to constants (EXACT, within the model).  _[Gornushkin 1999]_

## `ErrorBudget.lean`  (CflibsFormal)
*the error-propagation chain and DERIVED reliability thresholds*

**Results**
- `REDUCED` · `olsSlope_stable_l1` — N-line slope sensitivity (ℓ¹ worst-case bound).  _[Tognoni 2010]_
- `REDUCED` · `olsSlope_stable_l2_sq` — N-line slope sensitivity (ℓ², squared form).  _[Tognoni 2010]_
- `REDUCED` · `olsSlope_stable_l2` — N-line slope sensitivity (ℓ², root form).  _[Tognoni 2010]_
- `PURE-MATH` · `olsSlope_l1_const_two` — N = 2 reduces to the classic two-line constant.
- `REDUCED` · `olsSlope_stable_two` — N = 2 bound matches `twoLineBeta_stable`.  _[Tognoni 2010]_
- `EXACT` · `temp_rel_error_eq` — Exact temperature relative error.  _[Tognoni 2010]_
- `REDUCED` · `temp_rel_error_le` — Temperature stability from a slope-error bound.  _[Tognoni 2010]_
- `REDUCED` · `requiredEnergySpread_sufficient` — Minimum energy spread is SUFFICIENT for a target slope accuracy.  _[Tognoni 2010]_
- `REDUCED` · `maxPerLineError_sufficient` — Maximum per-line error (minimum SNR) is SUFFICIENT for a target slope accuracy.  _[Tognoni 2010]_
- `PURE-MATH` · `abs_exp_sub_one_le` — A clean exponential perturbation bound: `|exp x − 1| ≤ exp η − 1` whenever `|x| ≤ η`.
- `EXACT` · `relDensity_le` — Relative density error from an intercept (log-concentration) error.  _[Tognoni 2010]_
- `REDUCED` · `olsIntercept_stable_centered` — Intercept (concentration) sensitivity, centered convention.  _[Tognoni 2010]_
- `PURE-MATH` · `composition_abs_sub_le_uniform` — Uniform composition error bound.
- `REDUCED` · `composition_target_sufficient` — Composition accuracy ⇒ per-species density-error budget (the closure-leg inverse).  _[Tognoni 2010]_
- `REDUCED` · `olsSlope_stable_hetero` — N-line slope sensitivity, HETEROSCEDASTIC (per-line ℓ¹ bound).  _[Tognoni 2010]_
- `REDUCED` · `olsSlope_stable_l1_of_hetero` — The heteroscedastic bound strictly generalizes `olsSlope_stable_l1`.  _[Tognoni 2010]_
- `REDUCED` · `temp_rel_error_hetero` — Composed heteroscedastic noise ⇒ relative temperature error (gap #5, temperature leg).  _[Tognoni 2010]_

## `ForwardMap.lean`  (CflibsFormal)
*Part 4: the optically-thin forward map*

**Definitions**
- `lineIntensity` — Integrated intensity of the optically-thin emission line for the bound-bound transition with upper level `k`: `I_{ki} = Fcal · A_k · n_k`, where `n_k = popul…

**Results**
- `PURE-MATH` · `lineIntensity_pos` — Positivity of the observable.
- `REDUCED` · `boltzmann_plot_intensity` — Intensity Boltzmann-plot identity.  _[Ciucci 1999]_
- `REDUCED` · `temperature_from_two_lines` — Temperature from two lines.  _[Ciucci 1999]_

## `ForwardMapEnergy.lean`  (CflibsFormal)
*the energy-intensity forward map and convention equivalence*

**Definitions**
- `lineIntensityEnergy` — Energy-intensity forward map.

**Results**
- `PURE-MATH` · `lineIntensityEnergy_pos` — Positivity of the energy observable.
- `REDUCED` · `lineIntensityEnergy_eq_lineIntensity` — Reduction to the canonical map.  _[Ciucci 1999]_
- `REDUCED` · `lineIntensityEnergy_mul_lam` — The wavelength factor cancels the photon-energy factor.  _[Ciucci 1999]_
- `EXACT` · `boltzmann_plot_intensity_wavelength` — Wavelength-form Boltzmann plot.  _[Aragón & Aguilera 2008]_
- `EXACT` · `temperature_from_two_lines_wavelength` — Temperature from two lines, wavelength form.  _[Aragón & Aguilera 2008]_

## `HydrogenStark.lean`  (CflibsFormal)
*the hydrogen-line (Balmer) Stark electron-density diagnostic*

**Definitions**
- `hydrogenStarkFWHM` — Hydrogen Balmer-line Stark FWHM (forward map).
- `densityFromHydrogenStark` — Hydrogen-line electron-density diagnostic (inverse map).

**Results**
- `PURE-MATH` · `hydrogenStarkFWHM_pos` — The hydrogen-line Stark width is strictly positive for positive width parameter, reference density, and electron density.
- `REDUCED` · `densityFromHydrogenStark_recovers` — Soundness of the hydrogen-line diagnostic.  _[Gigosos 2003]_
- `PURE-MATH` · `hydrogenStarkFWHM_strictMonoOn` — Strict monotonicity of the Balmer width in `n_e`.
- `PURE-MATH` · `hydrogenStarkFWHM_injOn` — Identifiability of `n_e` from the Balmer width.

## `Identifiability.lean`  (CflibsFormal)
*Part 5: identifiability of the inverse problem*

**Results**
- `EXACT` · `lineIntensity_ratio_closed_form` — Two-line intensity-ratio closed form.  _[Ciucci 1999]_
- `EXACT` · `temperature_identifiability` — Target 1 — temperature identifiability.  _[Ciucci 1999]_
- `EXACT` · `temperature_degeneracy` — Degeneracy converse — equal energies make the ratio `T`-independent.  _[Ciucci 1999]_
- `EXACT` · `temperature_not_identifiable_of_degenerate` — Degenerate pair ⇒ temperature NOT identifiable.  _[Ciucci 1999]_
- `EXACT` · `density_identifiability` — Target 2 — relative-density / composition identifiability.  _[Ciucci 1999]_
- `EXACT` · `electron_density_identifiability` — Target 3 — electron-density / stage-ratio identifiability via Saha.  _[Saha–Eggert (Griem)]_
- `EXACT` · `temperature_ratio_near_degenerate` — Quantitative near-degeneracy — linear-in-`ΔE` temperature-conditioning bound.  _[Ciucci 1999]_

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
- `EXACT` · `general_identifiability` — General identifiability — the central theorem.  _[Ciucci 1999]_
- `PURE-MATH` · `sound_estimators_agree` — Cross-method agreement bridge.
- `APPROXIMATION` · `rawCompositionEstimator_sound` — Soundness of the raw estimator (constant-`emit` case).  _[Ciucci 1999]_

## `JointIdentifiability.lean`  (CflibsFormal)
*Part 7: joint (temperature, composition) identifiability*

**Definitions**
- `observe` — Two-line observation / forward map.

**Results**
- `EXACT` · `joint_identifiability` — Joint (temperature, composition) identifiability — discharging the `hTratio` caveat.  _[Ciucci 1999]_

## `LeastSquaresFit.lean`  (CflibsFormal)
*the ordinary-least-squares projection / feasibility inverse*

**Definitions**
- `rss` — Residual sum of squares of the affine fit `k ↦ m·Eₖ + b` to the ordinates `y`: `rss E y m b = ∑ₖ (m·Eₖ + b − yₖ)²`.
- `leastSquaresResidual` — Minimal (least-squares) residual of the data `(E, y)`: the residual sum of squares at the OLS estimates, `rss E y (olsSlope E y) (olsIntercept E y)`.
- `LeastSquaresFeasible` — Least-squares feasibility at tolerance `ε`: the minimal residual is within `ε`, `leastSquaresResidual E y ≤ ε`.

**Results**
- `PURE-MATH` · `residual_sum_zero` — Normal equation (constant regressor).
- `PURE-MATH` · `residual_centered_dot_zero` — Normal equation (centered energy regressor).
- `PURE-MATH` · `residual_dot_energy_zero` — Normal equation (raw energy regressor).
- `PURE-MATH` · `rss_decomposition` — Projection / Pythagorean identity.
- `PURE-MATH` · `ols_minimizes_rss` — THE CRUX — OLS is the least-squares minimizer.
- `PURE-MATH` · `leastSquaresResidual_nonneg` — The minimal residual is nonnegative (a sum of squares).
- `PURE-MATH` · `leastSquaresFeasible_iff_exists` — Feasibility is minimality.
- `PURE-MATH` · `leastSquaresResidual_eq_zero_iff` — On-manifold characterization.
- `PURE-MATH` · `ols_minimizer_eq_inverse` — Bridge — the least-squares minimizer equals the identifiable inverse on-manifold.

## `LineBroadening.lean`  (CflibsFormal)
*line broadening (Doppler width + the Voigt Gaussian budget)*

**Definitions**
- `dopplerFWHM` — Thermal Doppler FWHM.
- `temperatureFromDoppler` — Recovered temperature from a Doppler width (the inverse of `dopplerFWHM`): `T = (Δλ_D / λ₀)² · m·c² / (8·ln2·k_B)`.
- `gaussQuadrature` — Gaussian widths add in quadrature.
- `deconvolveGaussian` — Gaussian deconvolution.

**Results**
- `PURE-MATH` · `dopplerFWHM_pos` — The Doppler width is strictly positive for positive wavelength, constants, and temperature.
- `PURE-MATH` · `dopplerFWHM_strictMono_T` — Doppler width is a thermometer (monotone).
- `EXACT` · `doppler_recovers` — Doppler thermometry is exact.  _[Griem 1997]_
- `PURE-MATH` · `gaussQuadrature_comm` — Gaussian quadrature is symmetric in its two contributions.
- `EXACT` · `deconvolveGaussian_quadrature` — Deconvolution exactly inverts quadrature.  _[Aragón & Aguilera 2008]_

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
- `PURE-MATH` · `recoveredComposition_sum_one` — The recovered fractions still close to one over the detected set: `∑_{s∈D} Ĉ_D s = 1`.
- `EXACT` · `recoveredComposition_ratio` — Subcompositional invariance (the genuinely matrix-independent quantity).  _[Aitchison 1986]_
- `EXACT` · `recoveredComposition_ratio_matrix_invariant` — THE headline — matrix-independence of the recovered subcomposition.  _[Aitchison 1986]_
- `EXACT` · `recoveredComposition_absolute_matrix_dependent` — The absolute fractions ARE matrix-dependent.  _[Tognoni 2010]_
- `PURE-MATH` · `detectedDensity_univ` — Detecting ALL species recovers the ordinary `totalDensity`.
- `PURE-MATH` · `recoveredComposition_univ` — Complete detection recovers ordinary closure.
- `PURE-MATH` · `detectedDensity_le_totalDensity` — The detected density never exceeds the total (omitting nonnegative terms can only shrink it).
- `EXACT` · `inflationFactor_eq` — The inflation factor is exactly `1/(1−m)` with `m` the missing fraction.  _[Tognoni 2010]_
- `EXACT` · `one_le_inflationFactor` — Incomplete detection over-estimates: the inflation factor is `≥ 1`.  _[Tognoni 2010]_
- `EXACT` · `recoveredComposition_eq_inflation` — Recovered = true × inflation: `Ĉ_D s = C_s · (T/∑_{t∈D} n_t)`.  _[Tognoni 2010]_
- `EXACT` · `composition_le_recoveredComposition` — Over-estimation of every detected element: `C_s ≤ Ĉ_D s`.  _[Tognoni 2010]_
- `PURE-MATH` · `missingFraction_nonneg` — The missing fraction is nonnegative.
- `EXACT` · `recoveredDensityOfSpectrum_eq` — The recovered-density vector of a forward spectrum equals the true densities `N` pointwise.  _[Ciucci 1999]_
- `EXACT` · `recovered_ratio_from_intensities` — The recovered subcomposition from REAL forward intensities is the true ratio `N_s/N_t`, independent of the detected set `D`.  _[Aitchison 1986]_
- `PURE-MATH` · `sahaSplit_sum` — The two stages partition the element's total density: `n_neutral + n_ion = N_tot` (exact at any `n_e`).
- `REDUCED` · `sahaSplit_saha` — The split is genuinely the Saha split: `n_ion·n_e/n_neutral = S`.  _[Aguilera & Aragón 2007]_
- `REDUCED` · `sahaIonDensity_antitone` — Ionization suppression.  _[Aguilera & Aragón 2007]_
- `EXACT` · `homologousPair_ratio_closed_form` — Cross-species two-line ratio — closed form (shared partition function).  _[Ciucci 1999]_
- `EXACT` · `homologousPair_ratio_temperature_invariant` — THE per-shot-`T` deliverable — homologous-pair exact temperature invariance.  _[Ciucci 1999]_
- `EXACT` · `nonHomologousPair_ratio_temperature_dependent` — Contrast — invariance is a property OF the energy matching.  _[Ciucci 1999]_
- `EXACT` · `homologousPair_ratio_perU_closed_form` — Per-species-`U` two-line ratio — closed form with the `U`-residual explicit.  _[Ciucci 1999]_
- `REDUCED` · `homologousPair_ratio_perU_temperature_invariant` — Per-species-`U` homologous-pair temperature invariance (REDUCED).  _[Ciucci 1999]_

## `MultiSpecies.lean`  (CflibsFormal)
*Multi-species / multi-stage composition glue*

**Definitions**
- `speciesComposition` — Elemental/species composition vector: the number fraction of species `s`, `C s = N s / (∑_t N t)`.
- `deNormalizedDensity` — Number density of species `s` recovered from its measured designated-line intensity `I` by dividing out the calibration `Fcal`, Einstein coefficient `A s`, d…
- `deNormalizedDensityPerU` — Per-species de-normalized density reader.
- `lineIntensityPerU` — Per-species forward line-emission model.

**Results**
- `EXACT` · `speciesComposition_sum_one` — Multi-species closure.  _[Ciucci 1999]_
- `EXACT` · `speciesComposition_mem_stdSimplex` — Multi-species closure as simplex membership.  _[Ciucci 1999]_
- `EXACT` · `deNormalized_lineIntensity` — Inversion identity.  _[Ciucci 1999]_
- `EXACT` · `density_ratio_from_intensities` — Density-from-intensity bridge.  _[Ciucci 1999]_
- `PURE-MATH` · `deNormalizedDensity_eq_deNormalizedDensityPerU` — Shared-`U` reader is the per-`U` reader at `Us = partitionFunction kB T g E`.
- `PURE-MATH` · `lineIntensity_eq_lineIntensityPerU` — Shared-`U` forward map is the per-`U` forward map at `Us = partitionFunction kB T g E`.
- `EXACT` · `deNormalized_lineIntensity_perU` — Per-species inversion identity.  _[Ciucci 1999]_
- `EXACT` · `deNormalized_lineIntensity_ofPerU` — Shared-`U` inversion identity as a special case of the per-`U` one.  _[Ciucci 1999]_
- `EXACT` · `density_ratio_from_intensities_perU` — Per-species density-from-intensity bridge.  _[Ciucci 1999]_
- `EXACT` · `density_ratio_from_intensities_ofPerU` — Shared-`U` ratio theorem as a special case of the per-`U` one.  _[Ciucci 1999]_
- `PURE-MATH` · `speciesComposition_ratio` — Composition ratio equals density ratio.
- `EXACT` · `speciesComposition_ratio_from_intensities_perU` — Relative composition from intensities (per-species `U`).  _[Ciucci 1999]_

## `NoiseToComposition.lean`  (CflibsFormal)
*the end-to-end noise → composition chain (gap #5, the composed bound)*

**Definitions**
- `noiseTempGapBound` — Noise-derived temperature-gap bound.
- `tempResponseErrorBoundOfGap` — Gap-form temperature-response error bound.

**Results**
- `PURE-MATH` · `tempResponseErrorBound_eq_ofGap` — The named temperature-response bound is the gap-form bound at the actual gap.
- `PURE-MATH` · `tempResponseErrorBoundOfGap_mono` — Temperature-response error bound is monotone in the gap (PURE-MATH).
- `REDUCED` · `noise_to_temperatureGap` — Noise ⇒ temperature gap (REDUCED, Tognoni 2010).  _[Tognoni 2010]_
- `REDUCED` · `noise_to_density` — Noise ⇒ per-species recovered-density error (REDUCED, Tognoni 2010).  _[Tognoni 2010]_
- `REDUCED` · `noise_to_composition` — HEADLINE — noise ⇒ recovered-composition error (REDUCED, Tognoni 2010).  _[Tognoni 2010]_

## `NonlinearLeastSquares.lean`  (CflibsFormal)
*the nonlinear joint `(T, N)` least-squares inverse (existence leg)*

**Definitions**
- `nlObjective` — Nonlinear least-squares objective for the joint `(T, N)` fit: `nlObjective kB Fcal g E A obs (T, N) = ∑ₖ (I_k(T,N) − obs_k)²`, where `I_k(T,N) = lineIntensit…
- `profiledDensity` — Profiled density (variable-projection closed form).

**Results**
- `PURE-MATH` · `nlObjective_continuousOn` — Continuity on the physical box.
- `REDUCED` · `nlObjective_exists_min` — Existence of the joint minimizer (headline).  _[Tognoni 2010]_
- `EXACT` · `nlObjective_onManifold_min` — On-manifold anchor.  _[Tognoni 2010]_
- `EXACT` · `lineIntensity_linear_in_N` — Linearity of the forward map in the density `N` (EXACT).  _[Ciucci 1999]_
- `PURE-MATH` · `nlObjective_Nsection_decomposition` — `N`-section decomposition (PURE-MATH).
- `PURE-MATH` · `profiledDensity_denom_pos` — Nondegeneracy of the profiled least squares.
- `REDUCED` · `profiledDensity_isMinOn_Nsection` — `N`-section global minimality (headline, REDUCED).  _[Tognoni 2010]_
- `REDUCED` · `nlObjective_Nsection_lt_of_ne` — Strict excess off the profiled density (uniqueness core, REDUCED).  _[Tognoni 2010]_
- `REDUCED` · `Nsection_minimizer_unique` — Uniqueness of the `N`-section minimizer (headline, REDUCED).  _[Tognoni 2010]_
- `PURE-MATH` · `nlObjective_eq_sq_sum` — The joint objective at any `(T, N)`, rewritten through linearity in `N`: `nlObjective … (T, N) = ∑ₖ (N·c_k(T) − obs_k)²`, `c_k(T) = lineIntensity kB T 1 Fcal…
- `PURE-MATH` · `nlObjective_eq_zero_iff` — Exact-fit characterization of a zero residual.
- `PURE-MATH` · `profiledDensity_onManifold` — Profiled density recovers the true density on-manifold.
- `PURE-MATH` · `profiledResidual_two_closed_form` — Two-line profiled-residual closed form (PURE-MATH).
- `EXACT` · `profiledT_onManifold_unique` — On-manifold `T`-uniqueness for `m` lines (EXACT, Ciucci 1999).  _[Ciucci 1999]_
- `EXACT` · `profiledT_two_onManifold_unique` — Two-line on-manifold `T`-uniqueness (EXACT, Ciucci 1999).  _[Ciucci 1999]_
- `EXACT` · `joint_onManifold_unique` — Joint `(T, N)` on-manifold uniqueness (EXACT, Ciucci 1999).  _[Ciucci 1999]_
- `EXACT` · `profiledT_offManifold_unique` — OFF-manifold `T`-uniqueness for `m` lines (EXACT, Ciucci 1999).  _[Ciucci 1999]_
- `EXACT` · `profiledT_two_offManifold_unique` — Two-line OFF-manifold `T`-uniqueness (EXACT, Ciucci 1999).  _[Ciucci 1999]_
- `REDUCED` · `profiledResidual_stability_in_obs` — Near-manifold stability of the profiled residual in the observation (REDUCED, Tognoni 2010).  _[Tognoni 2010]_
- `REDUCED` · `profiledResidual_nearManifold_bound` — Near-manifold residual bound at the true temperature (REDUCED, Tognoni 2010).  _[Tognoni 2010]_
- `PURE-MATH` · `profiledResidual_of_orthogonal` — Profiled residual at an orthogonal observation (PURE-MATH).
- `EXACT` · `profiledResidual_not_injective_m3` — Off-manifold `T`-non-uniqueness for `m = 3` (EXACT, HONEST NEGATIVE result).  _[Ciucci 1999]_

## `OLS.lean`  (CflibsFormal)
*the ordinary-least-squares algebraic foundation*

**Definitions**
- `mean` — Arithmetic mean of `f` over the `Fintype` of lines: `(∑ k, f k) / card ι`.
- `olsSlope` — Ordinary-least-squares slope of the Boltzmann-plot points `(E k, y k)`: covariance over variance, `(∑_k (E k − mean E)(y k − mean y)) / (∑_k (E k − mean E)²)`.
- `olsIntercept` — Ordinary-least-squares intercept `b = ybar − m·Ebar`.
- `olsWeight` — Gauss–Markov weight `wₖ = (Eₖ − Ē)/SS_E` with `SS_E = ∑ⱼ (Eⱼ − Ē)²`.
- `designNormalMatrix` — Design-matrix normal matrix of the Boltzmann-plot fit.

**Results**
- `PURE-MATH` · `centered_sum_zero` — The centered energies sum to zero: `∑ₖ (Eₖ − Ē) = 0`.
- `PURE-MATH` · `mean_affine` — Mean of an affine transform.
- `PURE-MATH` · `olsSlope_eq_centered` — OLS slope is centered-linear in the ordinates.
- `PURE-MATH` · `olsSlope_sub_eq` — Slope perturbation is linear in the ordinate perturbation.
- `PURE-MATH` · `centered_mul_self` — Centered–energy identity `∑ₖ (Eₖ − Ē)·Eₖ = ∑ₖ (Eₖ − Ē)² = SS_E`.
- `PURE-MATH` · `olsSlope_noise_gain` — OLS slope noise gain.
- `PURE-MATH` · `ols_recovers_line` — THE CRUX.
- `PURE-MATH` · `det_designNormalMatrix` — THE determinant identity (Lagrange / variance identity).
- `REDUCED` · `designNormalMatrix_det_ne_zero_iff` — Nonsingularity ⇔ positive energy spread (the runtime rank gate).  _[Tognoni 2010]_

## `PartialLTE.lean`  (CflibsFormal)
*the partial-LTE thermalization limit*

**Definitions**
- `thermalizationLimit` — Partial-LTE thermalization (collision) limit energy `E* = (n_e/(C·√T))^(1/3)`: the McWhirter criterion inverted for the largest energy gap a plasma of electr…
- `thermalized` — Partial-LTE membership.

**Results**
- `PURE-MATH` · `thermalizationLimit_pos` — The thermalization limit is strictly positive for positive prefactor, temperature, and density.
- `REDUCED` · `mcwhirter_iff_thermalizationLimit` — The McWhirter bound and the thermalization limit are the same criterion, two ways.  _[Cristoforetti 2010]_
- `REDUCED` · `lteValid_iff_thermalized` — The same criterion in the project's own vocabulary.  _[McWhirter 1965]_
- `PURE-MATH` · `thermalizationLimit_mono_ne` — A denser plasma thermalizes more levels.
- `PURE-MATH` · `thermalizationLimit_antitone_T` — A hotter plasma thermalizes fewer levels.
- `REDUCED` · `thermalized_recovers_gap` — Round-trip: the thermalization limit saturates the McWhirter bound.  _[McWhirter 1965]_

## `PartitionLipschitz.lean`  (CflibsFormal)
*the `U_s(T)` partition-function Lipschitz leg (gap #5)*

**Results**
- `REDUCED` · `partitionFunction_two_point_bound` — Two-point partition-function bound — the `U_s(T)` sensitivity leg (`REDUCED`, Tognoni 2010).  _[Tognoni 2010]_
- `REDUCED` · `partitionFunction_lipschitz_temp` — Lipschitz-in-`T` partition-function bound (`REDUCED`, Tognoni 2010).  _[Tognoni 2010]_
- `REDUCED` · `partitionFunction_relative_error_temp` — Relative partition-function error from a temperature error (`REDUCED`, Tognoni 2010).  _[Tognoni 2010]_

## `Robustness.lean`  (CflibsFormal)
*Robustness / error-propagation bounds*

**Definitions**
- `twoLineBeta` — Two-line inverse-temperature (slope) estimate from measured Boltzmann-plot ordinates `yi = log(I_i/(g_i A_i))`, `yj = log(I_j/(g_j A_j))` at upper-level ener…
- `logRatioIntercept` — Recovered log number-density ratio of two species `s`, `t` from their measured Boltzmann-plot *intercepts* `bs = log(Fcal · N_s / U_s)`, `bt = log(Fcal · N_t…

**Results**
- `PURE-MATH` · `twoLineBeta_stable` — Temperature stability.
- `PURE-MATH` · `logRatioIntercept_stable` — Composition/ratio stability.
- `PURE-MATH` · `twoLineBeta_continuous` — Continuous dependence.
- `PURE-MATH` · `twoLineBeta_stable_sharp` — Sharpness of the temperature bound.
- `PURE-MATH` · `logRatioIntercept_stable_sharp` — Sharpness of the composition/ratio bound.

## `Saha.lean`  (CflibsFormal)
*Part 2: the Saha ionization equilibrium*

**Definitions**
- `thermalBracket` — The de-Broglie bracket `2π·m_e·k_B·T / h²` appearing (to the `3/2` power) in the Saha factor.
- `sahaFactor` — Saha factor `S(T)`: the full right-hand side of the Saha equation *excluding* the electron density `n_e` and the stage population ratio.
- `electronDensityFromRatio` — Saha density diagnostic.
- `chargeNeutrality` — Charge neutrality for a multi-stage plasma: the electron density equals the sum over ionization stages `s` of `z s · n_s` (charge-weighted ion densities).

**Results**
- `PURE-MATH` · `thermalBracket_pos` — The thermal-de-Broglie bracket is strictly positive when the physical constants and temperature are positive (`h ≠ 0` suffices, here via `h > 0`).
- `PURE-MATH` · `sahaFactor_pos` — Positivity of the Saha factor.
- `EXACT` · `saha_relation` — Saha law ⇔ density inversion.  _[Saha–Eggert (Griem)]_
- `PURE-MATH` · `electronDensity_antitone` — Density diagnostic is injective.
- `EXACT` · `log_sahaFactor` — Saha-plot log identity.  _[Saha–Eggert (Griem)]_
- `PURE-MATH` · `chargeNeutrality_two_stage` — Charge neutrality, two-stage form.

## `SahaEquilibrium.lean`  (CflibsFormal)
*Coupled Saha–closure–charge self-consistency (reduced core)*

**Definitions**
- `sahaEquilibriumNe` — Self-consistent electron density of the reduced single-element, two-stage, fixed-`T` Saha core: the unique positive root of `n_e² = S · (Ntot − n_e)`,  `n_e…
- `multiElementIonized` — Multi-element ionized-density closure map `G`.
- `sahaIter` — Scalar fixed-point iteration map of the reduced Saha self-consistency equation `n_e² = S · (Ntot − n_e)`.

**Results**
- `PURE-MATH` · `sahaEquilibriumNe_pos` — Positivity of the self-consistent density.
- `REDUCED` · `sahaEquilibriumNe_selfConsistent` — Self-consistency (fixed-point) equation.  _[Saha–Eggert (Griem)]_
- `PURE-MATH` · `sahaEquilibriumNe_lt_totalDensity` — The equilibrium density is below the total density.
- `PURE-MATH` · `selfConsistent_unique` — Uniqueness of the positive root.
- `REDUCED` · `sahaEquilibrium_selfConsistent` — Existence of the self-consistent state.  _[Saha–Eggert (Griem)]_
- `REDUCED` · `selfConsistentState_unique` — Uniqueness of the self-consistent state.  _[Saha–Eggert (Griem)]_
- `REDUCED` · `sahaEquilibrium_unique_state` — Unique existence of the coupled self-consistent state.  _[Saha–Eggert (Griem)]_
- `REDUCED` · `sahaEquilibriumNe_strictMono_S` — Monotonicity in the Saha factor.  _[Saha–Eggert (Griem)]_
- `PURE-MATH` · `multiElementIonized_strictAntiOn` — The ionized-density map is strictly antitone in the electron density on `x ≥ 0`.
- `REDUCED` · `multiElement_exists_pos_fixedPoint` — Existence of the coupled electron density.  _[Saha–Eggert (Griem)]_
- `REDUCED` · `multiElement_pos_fixedPoint_unique` — Uniqueness of the coupled electron density.  _[Saha–Eggert (Griem)]_
- `REDUCED` · `multiElement_single_eq_sahaEquilibriumNe` — Single-species consistency.  _[Saha–Eggert (Griem)]_
- `EXACT` · `sahaIter_fixedPoint` — `sahaEquilibriumNe` is a fixed point of `sahaIter` (`EXACT`; Saha–Eggert, Griem).  _[Saha–Eggert (Griem)]_
- `REDUCED` · `sahaIter_contraction` — One-step geometric contraction toward the fixed point (`REDUCED`; Saha–Eggert, Griem).  _[Saha–Eggert (Griem)]_
- `REDUCED` · `sahaIter_mapsTo` — Interval invariance of the iteration (`REDUCED`; Saha–Eggert, Griem).  _[Saha–Eggert (Griem)]_
- `REDUCED` · `sahaIter_geometric_error` — Geometric error decay of the iterates (`REDUCED`; Saha–Eggert, Griem).  _[Saha–Eggert (Griem)]_
- `REDUCED` · `sahaIter_tendsto` — Geometric convergence of the iteration (`REDUCED`; Saha–Eggert, Griem).  _[Saha–Eggert (Griem)]_

## `SahaInverse.lean`  (CflibsFormal)
*Part 6: coupling Saha into the inverse problem*

**Definitions**
- `sahaBoltzmannOrdinate` — Saha–Boltzmann plot ordinate (single stage / single line).
- `stageIntercept` — Stage intercept of the Saha–Boltzmann plot.

**Results**
- `REDUCED` · `sahaBoltzmann_plot` — Saha–Boltzmann plot.  _[Yalcin 1999]_
- `EXACT` · `sahaBoltzmann_shift_eq_log_saha` — Saha–Boltzmann shift equals the log Saha factor.  _[Yalcin 1999]_
- `EXACT` · `saha_joint_identifiability` — Joint identifiability of `(T, n_e)` from the Saha–Boltzmann plot.  _[Yalcin 1999]_

## `SahaStability.lean`  (CflibsFormal)
*Part 2b: stability of the `n_e` diagnostic*

**Definitions**
- `sahaFactorLipConst` — Explicit `T`-Lipschitz constant for `sahaFactor` on a box `[Tmin, Tmax]` (`REDUCED`, Saha–Eggert (Griem)).

**Results**
- `PURE-MATH` · `saha_ratio_cancel` — Ratio-cancellation core (PURE-MATH).
- `EXACT` · `electronDensity_relativeError` — EXACT relative-error transfer for `n_e`.  _[Saha–Eggert (Griem)]_
- `PURE-MATH` · `saha_inv_lipschitz` — Lipschitz core (PURE-MATH).
- `EXACT` · `electronDensity_lipschitz` — EXACT sensitivity bound for the `n_e` diagnostic.  _[Saha–Eggert (Griem)]_
- `REDUCED` · `sahaFactor_lipschitz_temp` — Saha-factor `T`-Lipschitz (two-sided sensitivity) bound (`REDUCED`, Saha–Eggert (Griem)).  _[Saha–Eggert (Griem)]_
- `REDUCED` · `electronDensityFromRatio_lipschitz_temp` — Electron-density `T`-sensitivity bound (`REDUCED`, Saha–Eggert (Griem)).  _[Saha–Eggert (Griem)]_

## `SelfAbsorption.lean`  (CflibsFormal)
*self-absorption / optical-thickness-aware forward map*

**Definitions**
- `selfAbsorptionFactor` — Curve-of-growth self-absorption factor `SA(τ)`.
- `selfAbsorbedIntensity` — Optically-thick (self-absorbed) line intensity.
- `slabIntensity` — Radiative-transfer slab intensity.

**Results**
- `PURE-MATH` · `selfAbsorptionFactor_pos` — Positivity of the self-absorption factor.
- `PURE-MATH` · `selfAbsorptionFactor_le_one` — Self-absorption only dims.
- `PURE-MATH` · `selfAbsorptionFactor_strictAntiOn` — Strict monotonicity of the escape factor.
- `PURE-MATH` · `selfAbsorptionFactor_tendsto_one` — Thin limit.
- `APPROXIMATION` · `selfAbsorbedIntensity_le_lineIntensity` — Bias-direction theorem (non-strict).  _[Gornushkin 1999]_
- `APPROXIMATION` · `selfAbsorbedIntensity_lt_lineIntensity` — Bias-direction theorem (strict).  _[Gornushkin 1999]_
- `EXACT` · `slabIntensity_le_thin` — Radiative-transfer dimming, derived.  _[Gornushkin 1999]_
- `EXACT` · `slabIntensity_eq_thin_mul_SA` — Curve-of-growth identity (DERIVED, not definitional).  _[Gornushkin 1999]_
- `EXACT` · `selfAbsorbedIntensity_eq_slab` — The model intensity IS a radiative-transfer slab intensity.  _[Gornushkin 1999]_
- `EXACT` · `lineIntensity_eq_selfAbsorbedIntensity_div` — Exact curve-of-growth correction (model left-inverse).  _[Gornushkin 1999]_

## `SelfAbsorptionInverse.lean`  (CflibsFormal)
*Self-absorption coupled into the inverse problem — identifiability preserved vs. lost*

**Definitions**
- `thickObserve` — Optically-thick observation map.

**Results**
- `PURE-MATH` · `lineIntensity_smul_left` — `N`-linearity of the optically-thin forward map.
- `EXACT` · `thick_density_identifiability` — PRESERVED (known, matched `τ`) — per-species density identifiability.  _[Bulajic 2002]_
- `EXACT` · `thick_composition_identifiability` — PRESERVED (known, matched `τ`) — multi-species composition identifiability.  _[Bulajic 2002]_
- `EXACT` · `selfAbsorption_breaks_identifiability` — LOST (unknown `τ`) — self-absorption breaks identifiability.  _[Bulajic 2002]_
- `EXACT` · `selfAbsorption_breaks_composition_identifiability` — LOST at the COMPOSITION level (unknown per-species `τ`) — self-absorption breaks closure identifiability.  _[Bulajic 2002]_

## `SelfReversal.lean`  (CflibsFormal)
*self-reversal (the two-zone line dip)*

**Definitions**
- `emergentIntensity` — Two-zone emergent intensity.

**Results**
- `PURE-MATH` · `emergentIntensity_nonneg` — The two-zone emergent intensity is nonnegative for nonnegative source functions and optical depths.
- `EXACT` · `selfReversal_noShell` — No-shell limit (exact).  _[Cowan–Dieke 1948]_
- `EXACT` · `selfReversal_uniformSource` — Uniform-source limit (exact).  _[Cowan–Dieke 1948]_
- `EXACT` · `emergentIntensity_strictAnti_shell` — The self-reversal dip mechanism.  _[Cowan–Dieke 1948]_

## `SpatialForward.lean`  (CflibsFormal)
*spatially-resolved (discrete Abel / onion-peeling) forward model*

**Definitions**
- `chordIntensity` — The line-of-sight forward map for the onion-peeling discretization of the Abel transform: the lateral chord-intensity vector `I = L · ε`, where `ε : Fin N →…

**Results**
- `PURE-MATH` · `chordGeometry_det_ne_zero` — The path-length matrix of a physical onion-peeling geometry is nonsingular: its determinant is the product of the (positive) self-path-lengths, hence nonzero.
- `PURE-MATH` · `chordGeometry_isUnit` — The path-length matrix is invertible.
- `EXACT` · `chord_profile_identifiable` — Spatial identifiability — relaxing single-zone homogeneity.  _[Parigger 2016]_
- `EXACT` · `singleZone_identifiable` — The single-zone homogeneous model (`N = 1`) obtained by instantiating the general spatial identifiability at `N = 1`.  _[Parigger 2016]_

## `StarkBroadening.lean`  (CflibsFormal)
*Stark broadening + the McWhirter LTE criterion*

**Definitions**
- `starkFWHM` — Electron-impact (Stark) full width at half maximum.
- `starkDensity` — Stark electron-density diagnostic (inverse map).
- `mcWhirterBound` — McWhirter lower bound on electron density for LTE.
- `lteValid` — LTE-validity predicate.

**Results**
- `REDUCED` · `starkDensity_recovers` — Soundness of the Stark diagnostic.  _[Griem 1974]_
- `PURE-MATH` · `starkFWHM_strictMono` — Strict monotonicity of the Stark width in `n_e`.
- `PURE-MATH` · `starkFWHM_injective` — Identifiability of `n_e` from the Stark width.
- `PURE-MATH` · `starkFWHM_isLinear` — Griem linearity, bundled (`IsLinearMap`).
- `PURE-MATH` · `mcWhirterBound_mono_T` — McWhirter bound increases with temperature.
- `PURE-MATH` · `mcWhirterBound_mono_dE` — McWhirter bound increases with the energy gap.
- `EXACT` · `stark_saha_lte_consistent` — Stark–Saha LTE cross-check (conditional bundling).  _[Cristoforetti 2010]_

## `StarkShift.lean`  (CflibsFormal)
*the Stark line-shift electron-density diagnostic*

**Definitions**
- `starkShift` — Stark line-shift forward map (Griem linear).
- `starkDensityFromShift` — Stark-shift electron-density diagnostic (inverse map).
- `shiftWidthRatio` — The tabulated, `n_e`-independent shift-to-width ratio `d_ref/w_ref`.

**Results**
- `PURE-MATH` · `starkShift_pos_of_dRef_pos` — Sign-aware positivity (red shift).
- `REDUCED` · `starkDensityFromShift_recovers` — Soundness of the Stark-shift diagnostic.  _[Griem 1974]_
- `PURE-MATH` · `starkShift_isLinear` — Griem linearity, bundled (`IsLinearMap`).
- `PURE-MATH` · `starkShift_strictMono_of_pos` — Conditional monotonicity — red shift.
- `PURE-MATH` · `starkShift_strictAnti_of_neg` — Conditional anti-monotonicity — blue shift.
- `PURE-MATH` · `starkShift_injective` — Identifiability of `n_e` from the shift.
- `PURE-MATH` · `starkShift_abs_strictMono` — Sign-robust magnitude monotonicity.
- `REDUCED` · `shiftWidthRatio_indep_ne` — The shift-to-width ratio is `n_e`-independent — and that is exactly why it is *not* a density diagnostic.  _[Griem 1974]_
- `REDUCED` · `shift_width_density_agree` — Shift- and width-route densities coincide — conditioned on the line-ID check.  _[Griem 1974]_

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
- `REDUCED` · `temporal_temperature_insitu` — In-situ gate temperature (Boltzmann slope).  _[Tognoni 2010]_
- `EXACT` · `temporal_composition_invariant` — Per-gate composition soundness (dilution cancels).  _[Ciucci 1999]_
- `REDUCED` · `temporal_composition_gate_independent` — Cross-gate composition invariance (thin corollary).  _[Tognoni 2010]_
- `EXACT` · `gateSahaTotalDensity_eq` — The Saha completion is sound at the gate — `n_e` cancels (load-bearing).  _[Tognoni 2010]_
- `EXACT` · `temporal_saha_composition_invariant` — Per-gate Saha composition soundness (`n_e` and `ρ` both cancel).  _[Ciucci 1999]_
- `REDUCED` · `temporal_saha_composition_gate_independent` — Cross-gate Saha composition invariance (HEADLINE — thin corollary).  _[Tognoni 2010]_
- `REDUCED` · `mem_lteWindow_thermalized` — Applicability: gate in the LTE window ⇒ thermalized.  _[Cristoforetti 2010]_
- `PURE-MATH` · `mcwhirter_requirement_antitone` — McWhirter requirement falls as the plasma cools.

## `VoigtWidth.lean`  (CflibsFormal)
*the Voigt FWHM combination (Olivero–Longbothum)*

**Definitions**
- `voigtFWHM` — Voigt FWHM (Olivero–Longbothum 1977).

**Results**
- `PURE-MATH` · `voigtFWHM_pos` — The Voigt FWHM is strictly positive when there is a nonzero Gaussian width (always true in practice — thermal Doppler — for `wL ≥ 0`).
- `EXACT` · `voigtFWHM_ge_gauss` — A Voigt profile is at least as wide as its Gaussian part: `w_G ≤ w_V`.  _[Olivero–Longbothum 1977]_
- `EXACT` · `voigtFWHM_ge_lorentz` — A Voigt profile is at least as wide as its Lorentzian part: `w_L ≤ w_V`.  _[Olivero–Longbothum 1977]_
- `PURE-MATH` · `voigtFWHM_mono_wL` — The Voigt FWHM is increasing in the Lorentzian width `wL`.
- `PURE-MATH` · `voigtFWHM_mono_wG` — The Voigt FWHM is increasing in the Gaussian width `wG`.
- `EXACT` · `voigt_gaussian_limit` — Pure-Gaussian limit (exact).  _[Olivero–Longbothum 1977]_
- `APPROXIMATION` · `voigt_lorentzian_limit` — Pure-Lorentzian limit (honest restatement).  _[Olivero–Longbothum 1977]_

