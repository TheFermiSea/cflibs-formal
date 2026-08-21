# LIBS convention lock

**Single owner: this file.** Every convention below is fixed *here*; module docstrings may restate
a choice but must not contradict it. Changing a convention means editing this file **first**, then
the affected Lean sources, then `docs/scope-tags.tsv` if a scope tag moves. A silent per-module
deviation is a defect, not a local decision.

Why a lock: none of these hazards produces an error. Each one produces a finite, plausible,
wrong number. The verified core is deliberately dimensionless bare `ℝ` (CONTEXT.md design decision
#1), so Lean will not catch a unit or convention mismatch — only this document and
`Dimensions.lean` will. See `CONTEXT.md § Metrology & traceability` for the measurand and
traceability framing.

Every claim below was read off the Lean sources cited, not inferred.

---

## 1. Logarithm base on the Boltzmann plane — **natural log, always**

**Choice.** Every ordinate, intercept and slope in this repo is `Real.log`, i.e. `ln`. `log₁₀`
appears nowhere in `CflibsFormal/` (verified by grep: zero hits for `log10`/`logb`), and the
numerical oracle mirrors it — `oracle/Generate.lean` builds its ordinates with `Float.log`, also
natural.

**Fixed by.** `Boltzmann.boltzmann_plot` (`log(n_k/g_k) = log(N/U) − E_k/(k_BT)`),
`ForwardMap.boltzmann_plot_intensity`, `ForwardMapEnergy.boltzmann_plot_intensity_wavelength`,
`Saha.log_sahaFactor`. The whole `OLS`/`ErrorBudget`/`LeastSquaresFit` chain consumes those
ordinates, so `olsSlope` is a *natural-log* slope by construction.

**Failure mode if mixed.** The Boltzmann slope is `β = −1/(k_BT)`. A `log₁₀` ordinate has slope
`β/ln 10`; reading it as natural gives `T̂ = ln 10 · T ≈ 2.303·T`. A genuine 10 000 K plasma is
reported as 23 026 K, with no residual, no warning, and a perfectly straight plot.

The intercept is worse, and this is the part that survives closure. `Classic.classicDensity`
exponentiates the intercept `a = ln(Fcal·N_s/U_s)`. A `log₁₀` intercept read as natural gives
`a′ = a/ln 10`, hence `N̂_s = N_s·(Fcal·N_s/U_s)^(1/ln10 − 1)` — a **power-law distortion with
exponent ≈ −0.566**, not a common factor. Because `N_s` and `U_s` differ between species, the
distortion differs between species, so it does **not** cancel in the closure ratio: unlike a
mis-scaled `Fcal` (`Classic.classic_calibration_free`), a log-base error corrupts composition
itself. **Rule: any ordinate handed to `olsSlope` must already be `ln`-based; convert an external
`log₁₀` plot by `β_ln = ln 10 · β_log10` at the ingestion boundary, never inside the fit.**

---

## 2. Partition function normalization — **`U(T) = ∑_k g_k exp(−E_k/(k_BT))`, energies from each stage's own ground level**

**Choice.** `Boltzmann.partitionFunction kB T g E = ∑ k, g k * boltzmannFactor kB T (E k)`. Nothing
is factored out: no `g_0` prefactor, no `U(T) → g_0` low-`T` normalization, no `exp(+E_0/k_BT)`
ground-state shift. Level energies `E` are taken as measured **from that species-stage's own ground
level** (`E_0 = 0`), and the ionization energy `χ` in `Saha.sahaFactor` from stage-`z` ground to
stage-`z+1` ground.

**Fixed by.** `Boltzmann.partitionFunction`, `Boltzmann.population` (`N·g_k·bf/U`),
`Saha.sahaFactor` (which carries the ratio `U_{z+1}/U_z` alongside `exp(−χ/k_BT)`).

**What is safe.** A *uniform* shift of all `E` within one species cancels: it multiplies the
numerator of `population` and `U` by the same `exp(−ΔE/k_BT)`. So single-species intensities and
Boltzmann slopes are shift-invariant — this is why `boltzmann_plot` needs no ground-state
hypothesis.

**Failure mode if mixed.** The cancellation is *per stage*. `sahaFactor` contains `U_{z+1}/U_z`, and
shifting only the ion stage's energies rescales that ratio with nothing to cancel it. Taking NIST
"level energy" values for an ion relative to the *neutral* ground state (i.e. with `χ` already
included, `E′_k = E_k + χ`) multiplies **every** term of `U_{z+1}` by `exp(−χ/k_BT)` — a
*suppression* of ~2000× at `χ ≈ 7.6 eV`, `k_BT ≈ 1 eV`. That deflates `sahaFactor`'s
`U_{z+1}/U_z`, and hence the inferred `n_e = S/R` (`Saha.electronDensityFromRatio`), by three
orders of magnitude — while `χ` is *also* still being subtracted in the exponent, so the error is
applied twice.

**Known idealization, stated not hidden.** In `ForwardMap.lineIntensity` the partition function is
summed over the *same* finite index `ι` that indexes the fitted lines. The spec therefore identifies
"level set" with "line set" (one line per level). Physically `U(T)` must be summed over the species'
full level list, or taken from a tabulated `U_s(T)`, independently of which lines were fitted.
Truncating `ι` to the handful of fitted lines under-estimates `U` and hence under-estimates `N̂`.
It cancels in closure only if every species' `U` is under-estimated by the *same factor* — which
requires matched level structures, not merely the same number of dropped levels, and is
essentially never true.

---

## 3. Degeneracy `g_k` — **upper-level statistical weight, `g_k = 2J_k+1`, never folded into `A`**

**Choice.** `g : ι → ℝ` is the statistical weight of the **upper** level of the transition. It is
constrained only by `0 < g k` — the spec never assumes integrality, so `2J+1` is a modelling
convention, not a theorem. `g` appears in exactly two roles and both are the upper level's: inside
`U(T)` as the level weight, and in the ordinate denominator `g_k·A_k`.

**Fixed by.** `Boltzmann.partitionFunction`, `ForwardMap.boltzmann_plot_intensity`
(`log(I/(g_k·A_k))`), `ForwardMapEnergy.boltzmann_plot_intensity_wavelength` (`log(I·λ_k/(g_k·A_k))`).

**Failure mode if mixed.** Two traps, both silent. (a) Using the *lower* level's weight. (b) Feeding
a tabulated `g_k A_ki` product into the `A` slot while also dividing by `g_k` — NIST publishes both
`A_ki` and `g_k A_ki`, so this double-counts `g`. Either way the ordinate acquires a per-line
additive offset `δ_k = ln g_k`. This is exactly the structure `NonLTEKinetics.nonlte_ordinate_shift`
formalizes (a per-line multiplicative error `b_k` is an additive shift `ln b_k`), so the damage is
bounded by `ErrorBudget.olsSlope_stable_l1` — and that bound makes the point: the offset only
averages out if it is uncorrelated with `E_k`, which for degeneracies rising with level energy it is
not. It tilts the slope, biasing `T`.

---

## 4. Line strength — **Einstein `A_ki` (s⁻¹), not oscillator strength `f`**

**Choice.** The forward map takes the Einstein coefficient for spontaneous emission, per line,
`A : ι → ℝ`, with `0 < A k`. Oscillator strength `f` is **not formalized anywhere** in
`CflibsFormal/` — it appears only in prose in `CurveOfGrowth` and `EquivalentWidth` (where the
optical depth `τ` is said to lump it) and in `Alt/CSigmaCurveOfGrowth`, where the *cross-section*
`σ_ℓ` enters through `csigmaOpticalDepth sigmaL ell C = σ_ℓ·ℓ·C`. There is no `f`-to-`A` conversion
in this repo, proven or otherwise.

**Fixed by.** `ForwardMap.lineIntensity` (`I = Fcal·A_k·n_k`), `Dimensions.einsteinA = ⟨0,0,−1,0⟩`
(a rate, `time⁻¹`), `Dimensions.einsteinA_photonEnergy_dim`.

**Failure mode if mixed.** `f_ik` is dimensionless and of order `10⁻²–1`; `A_ki` is `10⁶–10⁹ s⁻¹`.
Substituting one for the other biases `N̂` by that ratio *exactly*, via
`AtomicDataPerturbation.classicDensity_aliasing` (`N̂ = N·ρ_true/ρ_wrong`). Worse, the correct
relation `A_ki = (2πe²/ε₀m_ec)·(g_i/g_k)·f_ik/λ²` is per-line and `λ`-dependent, so the bias is not
a common factor: it does not cancel in closure and it tilts the Boltzmann slope. Note also the
`g_i/g_k` in that relation — importing `gf` values re-opens hazard #3. **Rule: convert `f` (or
`gf`) to `A_ki` outside this spec, at the atomic-data ingestion boundary, and record the conversion
in the provenance.**

---

## 5. Composition — **number (atomic/mole) fraction, not mass fraction**

**Choice.** `Closure.composition n s = n s / totalDensity n` where `n : κ → ℝ` is a **number
density**. Every composition result in the repo is therefore about *atomic* fractions: simplex
membership, closure, calibration-freedom, matrix-effect inflation, all of them.

**Fixed by.** `Closure.composition`, `Closure.totalDensity`, `Closure.composition_sum_one`,
`Closure.composition_mem_stdSimplex`, `Classic.classic_sound` (`… = composition N s`).
`oracle/Generate.lean` states the fixture contract as "recovered == true mole fractions".

**Failure mode if mixed.** Converting to weight percent needs atomic masses, `w_s = C_s M_s / ∑_t C_t
M_t`; **atomic masses do not exist in this repo**. CF-LIBS literature and the companion numerical
pipeline usually report wt%. Comparing a Lean-verified `C_s` against a wt% number is a
tens-of-percent disagreement for any multi-element sample with unequal masses (Fe/Al: `M` ratio
2.07), and it will look like a physics bug rather than a units bug.

**Known docstring defect (theorem is correct, noun is wrong).**
`MatrixEffects.missingFraction` is titled "**Missing (undetected) mass fraction**" but is defined as
`1 − detectedDensity n D / totalDensity n` — a *number*-density share, as its own following sentence
correctly says. The same wording appears twice in `MatrixEffects.lean` (module docstring and
definition docstring) and is carried into `docs/theorem-catalog.md`, where the single generated line
reads "mass fraction … the share of the true **number** density". `CONTEXT.md` is clean. The
definition and every theorem about it (`missingFraction_nonneg`, `inflationFactor_eq`,
`one_le_inflationFactor`) are right; only the noun is wrong. **Fix the docstring, not the
definition.**

---

## 6. Units — **the core fixes none; two consistency rules are load-bearing**

**Choice.** The inverse-problem core is deliberately dimensionless bare `ℝ`, so *no* unit system is
fixed and Lean will not catch a mismatch. Two rules are what actually bind:

1. **`E`, `χ` and `k_B·T` must share one energy unit**, because they only ever appear as
   `E/(k_BT)` and `χ/(k_BT)`. Machine-checked as `Dimensions.boltzmann_arg_dimensionless`. Within
   `Boltzmann` alone, eV-based energies with `k_B = 8.617333262×10⁻⁵ eV/K` are perfectly safe.
2. **`Saha.sahaFactor` takes a single `kB` and uses it in *both* the thermal bracket
   `thermalBracket kB T me h = 2π·m_e·k_B·T/h²` and the exponent `exp(−χ/(k_BT))`.** The bracket is
   `L⁻²` (`Dimensions.thermalBracket_dim`) and its `3/2` power is the number density
   (`Dimensions.sahaFactor_dim`), so `k_B`, `m_e` and `h` must be in **one coherent system**, and
   `χ` in that system's energy unit. You cannot pass `χ` in eV and `h` in J·s. This is the single
   place where an eV/CGS hybrid silently breaks.

**Recommended default.** The CF-LIBS literature this repo cites is CGS-flavoured — the McWhirter
criterion constant `1.6×10¹²` and the Stark tables anchored at `n_ref ≈ 10¹⁶ cm⁻³`
(`StarkShift`) — so keep densities in **cm⁻³**, and convert only at an SI boundary. The conversions
are machine-checked: `Dimensions.siToCgs_numberDensity : siToCgs numberDensity = 1e-6` (m⁻³ → cm⁻³),
`Dimensions.siToCgs_energy : siToCgs energy = 1e7` (J → erg), with multiplicativity
`Dimensions.siToCgs_mul`. Caveat carried by `siToCgs`'s own docstring: it drops time and temperature
exponents (second and kelvin coincide) and would need revisiting for electromagnetic units.

**Failure mode if mixed.** An SI thermal bracket (m⁻³) compared against a McWhirter LTE threshold
quoted in cm⁻³ is off by `10⁶`. The LTE gate then passes or fails by six orders of magnitude,
silently, because the dimensionless core has nothing to object to.

---

## 7. Boltzmann-plot ordinate — **both conventions exist; the wavelength form is the faithful one**

**Choice.** The repo carries *two* forward maps, and this is deliberate, not duplication:

| | `ForwardMap` (canonical) | `ForwardMapEnergy` (sibling) |
| --- | --- | --- |
| model | `I = Fcal·A_k·n_k` | `I = (hc/(4π·λ_k))·A_k·n_k·Fgeo` |
| calibration | **scalar** `Fcal`, absorbing `hc/4π` *and* `λ` | `Fgeo`, λ-free; `λ : ι → ℝ` explicit per line |
| ordinate | `ln(I/(g_k·A_k))` | `ln(I·λ_k/(g_k·A_k))` |
| quantity | photon rate | energy / radiance |
| source | Ciucci 1999; Tognoni 2010 | Aragón & Aguilera 2008; Thouin 2023 |

Both are proven to give the **same slope** `−1/(k_BT)`
(`boltzmann_plot_intensity` vs `boltzmann_plot_intensity_wavelength`;
`temperature_from_two_lines` vs `temperature_from_two_lines_wavelength`), and the reduction is
explicit: `lineIntensityEnergy_eq_lineIntensity` (energy map = canonical map with a **per-line**
`Fcal = hc·Fgeo/(4π·λ_k)`) and `lineIntensityEnergy_mul_lam` (`I·λ_k` = canonical map with the
**λ-free** `Fcal = hc·Fgeo/4π`). The intercepts differ by `Fcal ↔ hc·Fgeo/4π`, which is
species-independent and therefore cancels in closure by
`Closure.composition_smul_invariant` / `Classic.classic_calibration_free`.

**Which one is authoritative.** `docs/scope-tags.tsv` already encodes the judgement and it should be
read as the lock: `boltzmann_plot_intensity_wavelength` and `temperature_from_two_lines_wavelength`
are tagged **EXACT**; `boltzmann_plot_intensity` and `temperature_from_two_lines` are tagged
**REDUCED**. The reduction is precisely the assumption that `λ` is line-independent over the fitted
set, or that the detector genuinely counts photons. **A radiometrically calibrated spectrometer
measures energy, so use the `λ`-carrying ordinate.**

**Failure mode if mixed.** Applying `ln(I/(g_kA_k))` to energy-calibrated intensities omits a
per-line term `ln λ_k`. Over a 200–800 nm fitted line set that term spans `ln 4 ≈ 1.39` — comparable
to the ordinate range itself — and it is *anti-correlated* with `E_k` (higher upper levels tend to
shorter wavelengths), so it does not average away. It is an ordinate shift correlated with the
abscissa: the worst case for `ErrorBudget.olsSlope_stable_l1`, which is sharp exactly when the
errors align in sign with `E_k − Ē`. The slope tilts and `T` is biased with a straight-looking plot.

---

## What this file does **not** lock

Honest scope. Not covered here, because the repo does not fix them: wavelength in air vs vacuum;
instrumental-broadening deconvolution reference width (`LineBroadening` takes the Gaussian
quadrature budget as given); the sign convention of a Stark *shift* (`StarkShift` is explicitly
sign-conditional); the definition of the detection limit that populates the detected set `D` in
`MatrixEffects`; and the gate-delay/gate-width bookkeeping that `TemporalEvolution` abstracts into
`ρ(t)`. Each of those is a real silent-mismatch hazard with no current owner.
