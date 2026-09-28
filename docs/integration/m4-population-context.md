# Population-layer theorems for a single `PopulationContext` (CF-LIBS-improved M4)

**Re-issued 2026-09-24 (v2)**, after the cflibs-formal deep audit (finding RF-10) showed that v1 of
this document, adopted by the overhaul as M4 acceptance criteria (amendment A11), was wrong in five
places. What changed is listed at the end ("Changes from v1"). v1 was generated on 2026-09-24 from
`main` at `fb1681d`; v2 uses the same signatures (printed by Lean, not paraphrased) with the tiers,
conditions and fixture checks corrected. Full signatures: [`population-layer-signatures.md`](population-layer-signatures.md).

## When a theorem applies to the pipeline verbatim

The context must compute **the same functions** as the spec:

| spec definition (`CflibsFormal`) | formula | what the context must match |
|---|---|---|
| `boltzmannFactor kB T E` | `exp(-E / (kB·T))` | same sign and units of `E/(kB·T)` |
| `partitionFunction kB T g E` | `∑ₖ gₖ · boltzmannFactor kB T Eₖ` over a **finite, non-empty** level list | a literal level sum over the **same** list the context uses everywhere (see condition 2). A clamped, tabulated or polynomial (Irwin-type) `U(T)` is a different object: no `partitionFunction` theorem transfers to it, and the monotonicity, Lipschitz and growth rows can fail outright for a fit or clamp |
| `population kB T N g E k` | `N · gₖ · boltzmannFactor / U(T)` | the same level list in numerator and `U` |
| `thermalBracket kB T me h` | `2π·me·kB·T / h²` | consistent units for `me`, `kB`, `T`, `h` |
| `sahaFactor kB T me h χ gZ EZ gZ1 EZ1` | `2 · (U_{Z+1}/U_Z) · thermalBracket^(3/2) · exp(-χ/(kB·T))` | `U`s from the same context; `g_e = 2` explicit |
| `electronDensityFromRatio … R` | `sahaFactor / R` | the same `(χ_eff, level list)` pair as the forward model |
| `lineIntensity kB T N Fcal g E A k` | `Fcal · Aₖ · population` (photon-rate convention, Ciucci 1999) | energy-flux form is `ForwardMapEnergy.lineIntensityEnergy`, proven to reduce |

Four conditions:

1. **Level list at or below the ionization energy used.** Several rows (`sahaFactor_strictMonoOn_temp`,
   `electronDensityFromRatio_strictMonoOn_temp`, `partitionFunction_upper_growth`) carry the
   hypothesis `hEχ : ∀ k, E k ≤ χ`. That holds only after the level list is **truncated at or below
   the χ used in the exponent**. It is not a property of real atoms as tabulated: 202 of 324 species
   in `libs_production.db` list levels above their ionization potential (Ca I: 342 of 798 levels,
   up to 34.66 eV against an IP of 6.113 eV). The context must truncate, and state where.
2. **One `(χ_eff, level list)` pair per stage, identical in forward and inverse.** Every Saha result is
   stated for one ionization energy and one level list. With ionization-potential depression,
   `χ_eff = χ − Δχ(n_e, T)` depends on the `n_e` being solved for and moves the level cutoff. Hence:
   - `saha_relation` (the round trip) holds at the pair; an inverse that uses a different `χ` than
     the forward is off by exactly `exp(Δχ/(kB·T))` in `n_e` (the overhaul's 0.936× is this factor).
   - Every row that varies `T` or `n_e` (monotonicity grids, Lipschitz and two-point bounds,
     enclosures, and the runtime certificates C9/C10) applies **only with `Δχ` frozen and the level
     list fixed** across the grid. A sharp, `n_e`-dependent cutoff makes `U` discontinuous in `n_e`
     (Ca I: 178 levels cross the cutoff between 10¹⁶ and 10¹⁸ cm⁻³), and no Lipschitz or contraction
     statement survives a jump. IPD itself is not modelled in the spec yet (audit RF-19, FT-02).
3. **Units.** The population-layer identities hold in any consistent unit system, so a fixture must
   evaluate both sides in one system (SI with `kB` in J/K, or eV with `kB = 8.617e-5`; never energies
   in cm⁻¹ with `kB` in eV/K). **Exception:** anything built on `mcWhirterBound` (its `1.6·10¹²`
   carries units: `n_e` in cm⁻³, `T` in K, `ΔE` in eV), namely `lteValid`, `stark_saha_lte_consistent`,
   `TemporalEvolution.lteWindow` and certificates C7/C8. None of those is an acceptance row here.
4. **Hypotheses are real.** Positivity of `kB`, `T`, `me`, `h`, statistical weights and densities is
   required where listed. A context that admits `T ≤ 0` or `g = 0` is outside every theorem.

## Tier 1: invariants of the context itself (M4 acceptance, 37 rows)

Each row can be checked numerically against the new context at fixture points inside its
hypotheses. The fixture-check column says along which variable (a monotonicity row in `R` is not a
`T`-grid check). The Lipschitz-type rows are true but their constants are far from tight (for
`sahaFactor_lipschitz_temp`, 10⁶–10⁸× on production atomic data): they pass easily and are not
usable as runtime error bounds (audit RF-11, RF-18; tight versions are frontier FT-15). The per-U
rows are the ones to use when the context supplies each species’ own `U`: instantiate
`Us := partitionFunction kB T g E` with the context’s literal sum.

| Lean name | module | scope | hypotheses | conclusion | fixture check |
|---|---|---|---|---|---|
| `boltzmannFactor_pos` | Boltzmann | PURE-MATH | — | `0 < CflibsFormal.boltzmannFactor kB T E` | inequality at sample points |
| `partitionFunction_pos` | Boltzmann | PURE-MATH | [Nonempty ι]; hg : ∀ (k : ι), 0 < g k | `0 < CflibsFormal.partitionFunction kB T g E` | inequality at sample points |
| `population_sum` | Boltzmann | EXACT | [Nonempty ι]; hg : ∀ (k : ι), 0 < g k | `∑ k, CflibsFormal.population kB T N g E k = N` | identity, |lhs − rhs| ≤ tol |
| `boltzmann_plot` | Boltzmann | EXACT | [Nonempty ι]; hg : ∀ (k : ι), 0 < g k; hN : 0 < N | `Real.log (CflibsFormal.population kB T N g E k / g k) =   Real.log (N / CflibsFormal.partitionFunction kB T g E) - E k / (kB * T)` | identity |
| `temperature_from_two_levels` | Boltzmann | EXACT | [Nonempty ι]; hg : ∀ (k : ι), 0 < g k; hN : 0 < N; hE : E i ≠ E j | `(Real.log (CflibsFormal.population kB T N g E j / g j) - Real.log (CflibsFormal.population kB T N g E i / g i)) /     (E i - E j) =   1 / (kB * T)` | identity |
| `thermalBracket_pos` | Saha | PURE-MATH | hkB : 0 < kB; hT : 0 < T; hme : 0 < me; hh : 0 < h | `0 < CflibsFormal.thermalBracket kB T me h` | inequality |
| `thermalBracket_strictMono` | SahaStability | PURE-MATH | hkB : 0 < kB; hme : 0 < me; hh : 0 < h; hab : Ta < Tb | `CflibsFormal.thermalBracket kB Ta me h < CflibsFormal.thermalBracket kB Tb me h` | monotonicity in T |
| `sahaFactor_pos` | Saha | PURE-MATH | [Nonempty ι]; [Nonempty κ]; hkB : 0 < kB; hT : 0 < T; hme : 0 < me; hh : 0 < h; hgZ : ∀ (k : ι), 0 < gZ k; hgZ1 : ∀ (k : κ), 0 < gZ1 k | `0 < CflibsFormal.sahaFactor kB T me h chi gZ EZ gZ1 EZ1` | inequality |
| `log_sahaFactor` | Saha | EXACT | [Nonempty ι]; [Nonempty κ]; hkB : 0 < kB; hT : 0 < T; hme : 0 < me; hh : 0 < h; hgZ : ∀ (k : ι), 0 < gZ k; hgZ1 : ∀ (k : κ), 0 < gZ1 k | `Real.log (CflibsFormal.sahaFactor kB T me h chi gZ EZ gZ1 EZ1) =   Real.log 2 +         (Real.log (CflibsFormal.partitionFunction kB T gZ1 EZ1) -           Real.log (CflibsFormal.partitionFunction kB T gZ EZ)) +       3 / 2 * Real.log (CflibsFormal.thermalBracket kB T me h) -     chi / (kB * T)` | identity |
| `saha_relation` | Saha | EXACT | hR : R ≠ 0 | `ne = CflibsFormal.electronDensityFromRatio kB T me h chi gZ EZ gZ1 EZ1 R ↔   R * ne = CflibsFormal.sahaFactor kB T me h chi gZ EZ gZ1 EZ1` | round trip at one (χ_eff, level list) pair |
| `electronDensity_antitone` | Saha | PURE-MATH | [Nonempty ι]; [Nonempty κ]; hkB : 0 < kB; hT : 0 < T; hme : 0 < me; hh : 0 < h; hgZ : ∀ (k : ι), 0 < gZ k; hgZ1 : ∀ (k : κ), 0 < gZ1 k | `StrictAntiOn (CflibsFormal.electronDensityFromRatio kB T me h chi gZ EZ gZ1 EZ1) (Set.Ioi 0)` | monotonicity in R (the stage ratio), at fixed T |
| `sahaFactor_strictMonoOn_temp` | SahaStability | EXACT | [Nonempty ι]; [Nonempty κ]; hkB : 0 < kB; hme : 0 < me; hh : 0 < h; _hchi : 0 ≤ chi; hgZ : ∀ (k : ι), 0 < gZ k; _hEZ : ∀ (k : ι), 0 ≤ EZ k; hgZ1 : ∀ (k : κ), 0 < gZ1 k; hEZ1 : ∀ (k : κ), 0 ≤ EZ1 k; hEχ : ∀ (k : ι), EZ k ≤ chi | `StrictMonoOn (fun T => CflibsFormal.sahaFactor kB T me h chi gZ EZ gZ1 EZ1) (Set.Ioi 0)` | monotonicity in T; Δχ and level list frozen across the grid; level list must sit at or below χ_eff (hEχ) |
| `electronDensityFromRatio_strictMonoOn_temp` | SahaStability | EXACT | [Nonempty ι]; [Nonempty κ]; hkB : 0 < kB; hme : 0 < me; hh : 0 < h; hchi : 0 ≤ chi; hgZ : ∀ (k : ι), 0 < gZ k; hEZ : ∀ (k : ι), 0 ≤ EZ k; hgZ1 : ∀ (k : κ), 0 < gZ1 k; hEZ1 : ∀ (k : κ), 0 ≤ EZ1 k; hEχ : ∀ (k : ι), EZ k ≤ chi; hR : 0 < R | `StrictMonoOn (fun T => CflibsFormal.electronDensityFromRatio kB T me h chi gZ EZ gZ1 EZ1 R) (Set.Ioi 0)` | monotonicity in T; Δχ and level list frozen across the grid; hEχ |
| `partitionFunction_mono_temp` | SahaStability | PURE-MATH | hkB : 0 < kB; hT1 : 0 < T1; hT12 : T1 ≤ T2; hg : ∀ (k : ι), 0 < g k; hE : ∀ (k : ι), 0 ≤ E k | `CflibsFormal.partitionFunction kB T1 g E ≤ CflibsFormal.partitionFunction kB T2 g E` | monotonicity in T; Δχ and level list frozen across the grid |
| `partitionFunction_upper_growth` | SahaStability | PURE-MATH | hkB : 0 < kB; hT1 : 0 < T1; hT12 : T1 ≤ T2; hg : ∀ (k : ι), 0 < g k; hEχ : ∀ (k : ι), E k ≤ chi | `CflibsFormal.partitionFunction kB T2 g E ≤   Real.exp (chi * (1 / (kB * T1) - 1 / (kB * T2))) * CflibsFormal.partitionFunction kB T1 g E` | inequality at T pairs; Δχ and level list frozen across the grid; hEχ |
| `partitionFunction_lipschitz_temp` | PartitionLipschitz | REDUCED | hkB : 0 < kB; hTmin : 0 < Tmin; hT1 : Tmin ≤ T1; hT2 : Tmin ≤ T2; hg : ∀ (k : ι), 0 < g k; hE : ∀ (k : ι), 0 ≤ E k | `\|CflibsFormal.partitionFunction kB T1 g E - CflibsFormal.partitionFunction kB T2 g E\| ≤   (∑ k, g k * E k) / (kB * Tmin ^ 2) * \|T1 - T2\|` | inequality at T pairs; Δχ and level list frozen across the grid; constant is loose (passes easily, not a runtime bound) |
| `partitionFunction_two_point_bound` | PartitionLipschitz | REDUCED | hkB : 0 < kB; hT1 : 0 < T1; hT2 : 0 < T2; hg : ∀ (k : ι), 0 < g k; hE : ∀ (k : ι), 0 ≤ E k | `\|CflibsFormal.partitionFunction kB T1 g E - CflibsFormal.partitionFunction kB T2 g E\| ≤   (∑ k, g k * E k) * \|1 / (kB * T1) - 1 / (kB * T2)\|` | inequality at T pairs; Δχ and level list frozen across the grid; loose constant |
| `partitionFunction_relative_error_temp` | PartitionLipschitz | REDUCED | [Nonempty ι]; hkB : 0 < kB; hTmin : 0 < Tmin; hT1 : Tmin ≤ T1; hT2 : Tmin ≤ T2; hg : ∀ (k : ι), 0 < g k; hE : ∀ (k : ι), 0 ≤ E k | `\|CflibsFormal.partitionFunction kB T1 g E - CflibsFormal.partitionFunction kB T2 g E\| /     CflibsFormal.partitionFunction kB T2 g E ≤   (∑ k, g k * E k) / (kB * Tmin ^ 2) * \|T1 - T2\| / CflibsFormal.partitionFunction kB T2 g E` | inequality at T pairs; Δχ and level list frozen across the grid; loose constant |
| `sahaFactor_lipschitz_temp` | SahaStability | REDUCED | [Nonempty ι]; [Nonempty κ]; hkB : 0 < kB; hme : 0 < me; hh : 0 < h; hchi : 0 ≤ chi; hTmin : 0 < Tmin; hT1 : Tmin ≤ T1; hT2 : Tmin ≤ T2; hT1M : T1 ≤ Tmax; hT2M : T2 ≤ Tmax; hgZ : ∀ (k : ι), 0 < gZ k; hEZ : ∀ (k : ι), 0 ≤ EZ k; hgZ1 : ∀ (k : κ), 0 < gZ1 k; hEZ1 : ∀ (k : κ), 0 ≤ EZ1 k | `\|CflibsFormal.sahaFactor kB T1 me h chi gZ EZ gZ1 EZ1 - CflibsFormal.sahaFactor kB T2 me h chi gZ EZ gZ1 EZ1\| ≤   CflibsFormal.sahaFactorLipConst kB Tmin Tmax me h chi gZ EZ gZ1 EZ1 * \|T1 - T2\|` | inequality at T pairs; Δχ and level list frozen across the grid; constant 10⁶–10⁸× loose on production data |
| `electronDensityFromRatio_lipschitz_temp` | SahaStability | REDUCED | [Nonempty ι]; [Nonempty κ]; hkB : 0 < kB; hme : 0 < me; hh : 0 < h; hchi : 0 ≤ chi; hTmin : 0 < Tmin; hT1 : Tmin ≤ T1; hT2 : Tmin ≤ T2; hT1M : T1 ≤ Tmax; hT2M : T2 ≤ Tmax; hgZ : ∀ (k : ι), 0 < gZ k; hEZ : ∀ (k : ι), 0 ≤ EZ k; hgZ1 : ∀ (k : κ), 0 < gZ1 k; hEZ1 : ∀ (k : κ), 0 ≤ EZ1 k; hR0 : 0 < R0; hR : R0 ≤ R | `\|CflibsFormal.electronDensityFromRatio kB T1 me h chi gZ EZ gZ1 EZ1 R -       CflibsFormal.electronDensityFromRatio kB T2 me h chi gZ EZ gZ1 EZ1 R\| ≤   CflibsFormal.sahaFactorLipConst kB Tmin Tmax me h chi gZ EZ gZ1 EZ1 / R0 * \|T1 - T2\|` | inequality at T pairs; Δχ and level list frozen across the grid; loose constant |
| `electronDensity_lipschitz` | SahaStability | EXACT | [Nonempty ι]; [Nonempty κ]; hkB : 0 < kB; hT : 0 < T; hme : 0 < me; hh : 0 < h; hgZ : ∀ (k : ι), 0 < gZ k; hgZ1 : ∀ (k : κ), 0 < gZ1 k; hR₀ : 0 < R₀; hR₁ : R₀ ≤ R₁; hR₂ : R₀ ≤ R₂ | `\|CflibsFormal.electronDensityFromRatio kB T me h chi gZ EZ gZ1 EZ1 R₁ -       CflibsFormal.electronDensityFromRatio kB T me h chi gZ EZ gZ1 EZ1 R₂\| ≤   CflibsFormal.sahaFactor kB T me h chi gZ EZ gZ1 EZ1 / R₀ ^ 2 * \|R₁ - R₂\|` | inequality at R pairs, fixed T |
| `electronDensity_relativeError` | SahaStability | EXACT | [Nonempty ι]; [Nonempty κ]; hkB : 0 < kB; hT : 0 < T; hme : 0 < me; hh : 0 < h; hgZ : ∀ (k : ι), 0 < gZ k; hgZ1 : ∀ (k : κ), 0 < gZ1 k; hR₁ : 0 < R₁; hR₂ : 0 < R₂ | `CflibsFormal.electronDensityFromRatio kB T me h chi gZ EZ gZ1 EZ1 R₁ /     CflibsFormal.electronDensityFromRatio kB T me h chi gZ EZ gZ1 EZ1 R₂ =   R₂ / R₁` | identity/inequality at R pairs, fixed T |
| `sahaFactor_mem_Icc` | SahaRangeEnclosure | EXACT | [Nonempty ι]; [Nonempty κ]; hkB : 0 < kB; hme : 0 < me; hh : 0 < h; hchi : 0 ≤ chi; hgZ : ∀ (k : ι), 0 < gZ k; hEZ : ∀ (k : ι), 0 ≤ EZ k; hgZ1 : ∀ (k : κ), 0 < gZ1 k; hEZ1 : ∀ (k : κ), 0 ≤ EZ1 k; hEχ : ∀ (k : ι), EZ k ≤ chi; hTmin : 0 < Tmin; hT : T ∈ Set.Icc Tmin Tmax | `CflibsFormal.sahaFactor kB T me h chi gZ EZ gZ1 EZ1 ∈   Set.Icc (CflibsFormal.sahaFactor kB Tmin me h chi gZ EZ gZ1 EZ1)     (CflibsFormal.sahaFactor kB Tmax me h chi gZ EZ gZ1 EZ1)` | enclosure on a T box; Δχ and level list frozen across the grid |
| `electronDensityFromRatio_mem_Icc` | SahaRangeEnclosure | EXACT | [Nonempty ι]; [Nonempty κ]; hkB : 0 < kB; hme : 0 < me; hh : 0 < h; hchi : 0 ≤ chi; hgZ : ∀ (k : ι), 0 < gZ k; hEZ : ∀ (k : ι), 0 ≤ EZ k; hgZ1 : ∀ (k : κ), 0 < gZ1 k; hEZ1 : ∀ (k : κ), 0 ≤ EZ1 k; hEχ : ∀ (k : ι), EZ k ≤ chi; hTmin : 0 < Tmin; hR : 0 < R; hT : T ∈ Set.Icc Tmin Tmax | `CflibsFormal.electronDensityFromRatio kB T me h chi gZ EZ gZ1 EZ1 R ∈   Set.Icc (CflibsFormal.electronDensityFromRatio kB Tmin me h chi gZ EZ gZ1 EZ1 R)     (CflibsFormal.electronDensityFromRatio kB Tmax me h chi gZ EZ gZ1 EZ1 R)` | enclosure on a T box; Δχ and level list frozen across the grid |
| `lineIntensity_pos` | ForwardMap | PURE-MATH | [Nonempty ι]; hg : ∀ (k : ι), 0 < g k; hN : 0 < N; hFcal : 0 < Fcal; hA : ∀ (k : ι), 0 < A k | `0 < CflibsFormal.lineIntensity kB T N Fcal g E A k` | inequality |
| `boltzmann_plot_intensity` | ForwardMap | REDUCED | [Nonempty ι]; hg : ∀ (k : ι), 0 < g k; hN : 0 < N; hFcal : 0 < Fcal; hA : ∀ (k : ι), 0 < A k | `Real.log (CflibsFormal.lineIntensity kB T N Fcal g E A k / (g k * A k)) =   Real.log (Fcal * N / CflibsFormal.partitionFunction kB T g E) - E k / (kB * T)` | identity |
| `temperature_from_two_lines` | ForwardMap | REDUCED | [Nonempty ι]; hg : ∀ (k : ι), 0 < g k; hN : 0 < N; hFcal : 0 < Fcal; hA : ∀ (k : ι), 0 < A k; hE : E i ≠ E j | `(Real.log (CflibsFormal.lineIntensity kB T N Fcal g E A j / (g j * A j)) -       Real.log (CflibsFormal.lineIntensity kB T N Fcal g E A i / (g i * A i))) /     (E i - E j) =   1 / (kB * T)` | identity |
| `lineIntensityEnergy_eq_lineIntensity` | ForwardMapEnergy | REDUCED | — | `CflibsFormal.lineIntensityEnergy hc fourPi kB T N Fgeo g E A lam k =   CflibsFormal.lineIntensity kB T N (hc * Fgeo / (fourPi * lam k)) g E A k` | identity (energy-flux form reduces to photon-rate form) |
| `lineIntensityEnergy_mul_lam` | ForwardMapEnergy | REDUCED | hlam : lam k ≠ 0 | `CflibsFormal.lineIntensityEnergy hc fourPi kB T N Fgeo g E A lam k * lam k =   CflibsFormal.lineIntensity kB T N (hc * Fgeo / fourPi) g E A k` | identity |
| `boltzmann_plot_intensity_wavelength` | ForwardMapEnergy | EXACT | [Nonempty ι]; hg : ∀ (k : ι), 0 < g k; hN : 0 < N; hhc : 0 < hc; hfp : 0 < fourPi; hFgeo : 0 < Fgeo; hA : ∀ (k : ι), 0 < A k; hlam : ∀ (k : ι), 0 < lam k | `Real.log (CflibsFormal.lineIntensityEnergy hc fourPi kB T N Fgeo g E A lam k * lam k / (g k * A k)) =   Real.log (hc * Fgeo * N / (fourPi * CflibsFormal.partitionFunction kB T g E)) - E k / (kB * T)` | identity |
| `deNormalized_lineIntensity` | MultiSpecies | EXACT | [Nonempty ι]; hg : ∀ (k : ι), 0 < g k; hN : 0 < N; hFcal : 0 < Fcal; hA : ∀ (k : ι), 0 < A k | `CflibsFormal.deNormalizedDensity kB T Fcal g E A s (CflibsFormal.lineIntensity kB T N Fcal g E A s) = N` | round trip: forward one species, de-normalize |
| `deNormalized_lineIntensity_perU` | MultiSpecies | EXACT | hg : ∀ (k : ι), 0 < g k; hFcal : 0 < Fcal; hA : ∀ (k : ι), 0 < A k; hUs : 0 < Us | `CflibsFormal.deNormalizedDensityPerU kB T Fcal Us g E A s (CflibsFormal.lineIntensityPerU kB T N Fcal Us g E A s) = N` | round trip with U supplied per species (instantiate Us := the context’s literal sum) |
| `density_ratio_from_intensities` | MultiSpecies | EXACT | [Nonempty ι]; hg : ∀ (k : ι), 0 < g k; hNs : 0 < Ns; hNt : 0 < Nt; hFcal : 0 < Fcal; hA : ∀ (k : ι), 0 < A k | `CflibsFormal.deNormalizedDensity kB T Fcal g E A s (CflibsFormal.lineIntensity kB T Ns Fcal g E A s) /     CflibsFormal.deNormalizedDensity kB T Fcal g E A t (CflibsFormal.lineIntensity kB T Nt Fcal g E A t) =   Ns / Nt` | identity |
| `density_ratio_from_intensities_perU` | MultiSpecies | EXACT | hg : ∀ (k : ι), 0 < g k; hFcal : 0 < Fcal; hA : ∀ (k : ι), 0 < A k; hUs : 0 < Us; hUt : 0 < Ut | `CflibsFormal.deNormalizedDensityPerU kB T Fcal Us g E A s (CflibsFormal.lineIntensityPerU kB T Ns Fcal Us g E A s) /     CflibsFormal.deNormalizedDensityPerU kB T Fcal Ut g E A t (CflibsFormal.lineIntensityPerU kB T Nt Fcal Ut g E A t) =   Ns / Nt` | identity, per-species U |
| `speciesComposition_ratio_from_intensities_perU` | MultiSpecies | EXACT | hg : ∀ (k : ι), 0 < g k; hFcal : 0 < Fcal; hA : ∀ (k : ι), 0 < A k; hUs : 0 < Us; hUt : 0 < Ut; hD : CflibsFormal.totalDensity N ≠ 0 | `CflibsFormal.deNormalizedDensityPerU kB T Fcal Us g E A s (CflibsFormal.lineIntensityPerU kB T (N s) Fcal Us g E A s) /     CflibsFormal.deNormalizedDensityPerU kB T Fcal Ut g E A t       (CflibsFormal.lineIntensityPerU kB T (N t) Fcal Ut g E A t) =   CflibsFormal.speciesComposition N s / CflibsFormal.speciesComposition N t` | identity, per-species U |
| `sahaBoltzmann_plot` | SahaInverse | REDUCED | [Nonempty ι]; [Nonempty κ]; hgZ : ∀ (k : ι), 0 < gZ k; hgZ1 : ∀ (k : κ), 0 < gZ1 k; hNz : 0 < Nz; hNz1 : 0 < Nz1; hFcal : 0 < Fcal; hAZ : ∀ (k : ι), 0 < AZ k; hAZ1 : ∀ (k : κ), 0 < AZ1 k | `CflibsFormal.sahaBoltzmannOrdinate kB T Nz Fcal gZ EZ AZ kz =     CflibsFormal.stageIntercept kB T Nz Fcal gZ EZ - EZ kz / (kB * T) ∧   CflibsFormal.sahaBoltzmannOrdinate kB T Nz1 Fcal gZ1 EZ1 AZ1 kz1 =       CflibsFormal.stageIntercept kB T Nz1 Fcal gZ1 EZ1 - EZ1 kz1 / (kB * T) ∧     CflibsFormal.stageIntercept kB T Nz1 Fcal gZ1 EZ1 - CflibsFormal.stageIntercept kB T Nz Fcal gZ EZ =       Real.log (Nz1 / Nz) +         (Real.log (CflibsFormal.partitionFunction kB T gZ EZ) - Real.log (CflibsFormal.partitionFunction kB T gZ1 EZ1))` | identity (Saha–Boltzmann ordinate) |
| `sahaBoltzmann_shift_eq_log_saha` | SahaInverse | EXACT | [Nonempty ι]; [Nonempty κ]; hkB : 0 < kB; hT : 0 < T; hme : 0 < me; hh : 0 < h; hgZ : ∀ (k : ι), 0 < gZ k; hgZ1 : ∀ (k : κ), 0 < gZ1 k; hNz : 0 < Nz; hNz1 : 0 < Nz1; hFcal : 0 < Fcal; hne : 0 < ne; hsaha : Nz1 * ne / Nz = CflibsFormal.sahaFactor kB T me h chi gZ EZ gZ1 EZ1 | `CflibsFormal.stageIntercept kB T Nz1 Fcal gZ1 EZ1 - CflibsFormal.stageIntercept kB T Nz Fcal gZ EZ =   Real.log (CflibsFormal.sahaFactor kB T me h chi gZ EZ gZ1 EZ1) - Real.log ne +     (Real.log (CflibsFormal.partitionFunction kB T gZ EZ) - Real.log (CflibsFormal.partitionFunction kB T gZ1 EZ1))` | identity; the one Lean result the default solver cites (iterative.py) |

Duplicates dropped from v1 (identical conclusions, re-derived from the per-U form):
`deNormalized_lineIntensity_ofPerU` (= `deNormalized_lineIntensity`),
`density_ratio_from_intensities_ofPerU` (= `density_ratio_from_intensities`). Definitional bridges
kept out of the fixture list: `lineIntensity_eq_lineIntensityPerU`,
`deNormalizedDensity_eq_deNormalizedDensityPerU`.

## Tier 2: estimator and identifiability results that consume the context (M6 material)

Uniqueness statements are not sample-checkable identities; check them by forwarding two
parameter sets and confirming the observables differ.

| Lean name | module | scope | hypotheses | conclusion | fixture check |
|---|---|---|---|---|---|
| `saha_joint_identifiability` | SahaInverse | EXACT | [Nonempty ι]; [Nonempty κ]; hkB : 0 < kB; _hme : 0 < me; _hh : 0 < h; hT₁ : 0 < T₁; hT₂ : 0 < T₂; hgZ : ∀ (k : ι), 0 < gZ k; hgZ1 : ∀ (k : κ), 0 < gZ1 k; hAZ : ∀ (k : ι), 0 < AZ k; hAZ1 : ∀ (k : κ), 0 < AZ1 k; hNz₁ : 0 < Nz₁; hNz₂ : 0 < Nz₂; hNz1₁ : 0 < Nz1₁; _hNz1₂ : 0 < Nz1₂; hFcal : 0 < Fcal; _hne₁ : 0 < ne₁; _hne₂ : 0 < ne₂; hE : EZ i ≠ EZ j; hslope : CflibsFormal.lineIntensity kB T₁ Nz₁ Fcal gZ EZ AZ j / CflibsFormal.lineIntensity kB T₁ Nz₁ Fcal gZ EZ AZ i =   CflibsFormal.lineIntensity kB T₂ Nz₂ Fcal gZ EZ AZ j / CflibsFormal.lineIntensity kB T₂ Nz₂ Fcal gZ EZ AZ i; hNeutObs : CflibsFormal.lineIntensity kB T₁ Nz₁ Fcal gZ EZ AZ uz = CflibsFormal.lineIntensity kB T₂ Nz₂ Fcal gZ EZ AZ uz; hIonObs : CflibsFormal.lineIntensity kB T₁ Nz1₁ Fcal gZ1 EZ1 AZ1 uz1 = CflibsFormal.lineIntensity kB T₂ Nz1₂ Fcal gZ1 EZ1 AZ1 uz1; hsaha₁ : Nz1₁ * ne₁ / Nz₁ = CflibsFormal.sahaFactor kB T₁ me h chi gZ EZ gZ1 EZ1; hsaha₂ : Nz1₂ * ne₂ / Nz₂ = CflibsFormal.sahaFactor kB T₂ me h chi gZ EZ gZ1 EZ1 | `T₁ = T₂ ∧ ne₁ = ne₂` | uniqueness: forward two parameter sets and check they differ in the observable; not sample-checkable as an identity |

By module, the remaining results about estimators built on top of the population layer. They
apply to a pipeline estimator only when it implements the same formula on the context:

- **NonlinearLeastSquares** (24): `Nsection_minimizer_unique`, `clean_residual_ratio`, `joint_onManifold_unique`, `lineIntensity_linear_in_N`, `nlObjective_Nsection_decomposition`, `nlObjective_Nsection_lt_of_ne`, `nlObjective_eq_sq_sum`, `nlObjective_eq_zero_iff`, `nlObjective_onManifold_min`, `profiledDensity_denom_pos`, `profiledDensity_isMinOn_Nsection`, `profiledDensity_onManifold`, `profiledResidual_metric_bound`, `profiledResidual_minimizer_trapped`, `profiledResidual_nearManifold_bound`, `profiledResidual_of_orthogonal`, `profiledResidual_stability_in_obs`, `profiledResidual_true_strict_lt`, `profiledResidual_two_closed_form`, `profiledResidual_two_eq_ratio`, `profiledT_onManifold_unique`, `profiledT_two_offManifold_box_unique`, `profiledT_two_onManifold_unique`, `two_ratio_diff`
- **Alt.CSigma** (8) — **not** the twin of `csigma.py`: `Alt.CSigma` is a C-sigma-style *normalization* of the thin model; `csigma.py` builds the thick Cσ curve of growth with a λ²·g·A·e^{-E_i/kT}(1−e^{-ΔE/kT}) cross-section, which has no Lean counterpart (audit SPC-11, RF-10): `csigmaOffset_of_lineIntensity`, `csigma_agrees_classic`, `csigma_agrees_of_sound`, `csigma_cross_stage_collapse`, `csigma_saha_master_line`, `csigma_saha_universal_line`, `csigma_sound`, `csigma_temperature_cross_stage`
- **ProfiledTUniqueness** (8): `joint_twoLevel_box_isStrictMin`, `joint_twoLevel_box_minimizer_unique`, `joint_two_box_isStrictMin`, `joint_two_box_minimizer_unique`, `profiledResidual_eq_rayleigh`, `profiledResidual_twoLevel_Tstar_isStrictMin`, `profiledResidual_twoLevel_strictUnimodalOn`, `profiledResidual_twoLevel_strictUnimodal_onManifold`
- **DifferentialEstimator** (7) — certifies matched per-line ratios; `opc.py` (one-point calibration, per-element F at a pooled T*) is a different estimator with no Lean twin yet (audit RF-10 item 5): `classic_biased_differential_exact`, `differentialRatio_eq_density_ratio`, `differentialRatio_error_bound`, `differentialRatio_immune_to_atomicData`, `differentialSlope_eq_neg_dbeta`, `differentialSlope_two_lines`, `logDifferentialRatio_affine_in_E`
- **Identifiability** (7): `density_identifiability`, `electron_density_identifiability`, `lineIntensity_ratio_closed_form`, `temperature_degeneracy`, `temperature_identifiability`, `temperature_not_identifiable_of_degenerate`, `temperature_ratio_near_degenerate`
- **AtomicDataPerturbation** (6): `classicDensity_aliasing`, `classicDensity_aliasing_error`, `classicDensity_aliasing_error_channels`, `classicDensity_aliasing_error_energy`, `classicDensity_temperature_aliasing`, `classicDensity_temperature_aliasing_error`
- **Alt.NeutralityScale** (5): `closureEstimate_bias`, `lineIntensity_linear`, `lineIntensity_ratio`, `neutralityScale_eq_Fcal`, `neutralityScale_undetected`
- **MatrixEffects** (5) — `homologousPair_*` assume one shared U for both species (EXACT only under that; per-U forms are REDUCED; audit RF-06): `homologousPair_ratio_closed_form`, `homologousPair_ratio_perU_closed_form`, `homologousPair_ratio_perU_temperature_invariant`, `homologousPair_ratio_temperature_invariant`, `nonHomologousPair_ratio_temperature_dependent`
- **HeteroAtomicData** (5): `nvP_slope_bias_eq_log`, `olsSlope_aliasing_A`, `olsSlope_aliasing_A_global`, `olsSlope_aliasing_A_hetero`, `temp_rel_error_atomicData_hetero`
- **Alt.LeastSquares** (4): `leastSquares_agrees_classic`, `leastSquares_sound`, `olsDensity_recovers`, `olsIntercept_of_forward`
- **Classic** (4): `classicDensity_recovers`, `classic_sound`, `classic_sound_sum_one`, `classic_temperature_correct`
- **Alt.OLSAtomicDataPerturbation** (3): `olsDensity_aliasing_A`, `olsDensity_aliasing_A_error`, `olsDensity_aliasing_E_error`
- **ProfiledUnimodality** (3): `profiledResidual_two_Tstar_isStrictMin`, `profiledResidual_two_strictUnimodalOn`, `profiledResidual_two_strictUnimodal_onManifold`
- **Certificates** (2): `aliasBudget_certificate_sound`, `knownTau_certificate_sound`
- **OpticalDepthBridge** (2): `lteSourceStrength_ratio_calibration_free`, `thickLineIntensity_lt_lineIntensity_of_pos_density`
- **CompositionIdentifiability** (2): `eq_2`, `eq_3`
- **Inverse** (1): `general_identifiability`
- **SelfAbsorptionInverse** (1): `lineIntensity_smul_left`
- **NoiseToComposition** (1): `noise_to_density`

## Not acceptance material: loop results that do not model `iterative.py`

| Lean name | module | scope | why it is not acceptance material |
|---|---|---|---|
| `outerLoop_contracts_apriori` | SahaRangeEnclosure | REDUCED | Model-B outer-loop contraction; iterative.py runs a different loop (0.5-damped Gauss–Seidel, IP-shifted SB graph, sb_offset), see audit RF-11/RF-17/FT-01 |
| `neLeg_mapsTo` | SahaEquilibrium | REDUCED | density-leg interval invariance of the Model-B loop; not the leg the pipeline iterates (audit PS-04, RF-11) |

## Annex: model identities and conditional results, not acceptance fixtures

v1 listed these as “Tier 1b”. They are exact statements about a specific model (the flat,
line-centre self-absorption kernel; the McWhirter-conditioned Stark–Saha bundle), so a context that
reproduces them only reproduces the model. They are listed so M5 knows what exists, not as tests.

| Lean name | module | scope | why it is not acceptance material |
|---|---|---|---|
| `envelope_ionization_matrix_shift` | MatrixIonizationCoupling | REDUCED | the envelope’s “zero matrix effect” clause has unconstrained densities; the module’s own sahaNeutralDensity refutes zero for element totals read through neutral lines (audit PS-02) |
| `lineIntensity_div_opticalDepth` | OpticalDepth | REDUCED | flat-kernel (line-centre, rectangular-profile) optical-depth identities: exact in that model only; applied to integrated intensities they over-correct 1.4–3.5× (audit LF-01, RF-03) |
| `lineIntensity_eq_source_mul_opticalDepth` | OpticalDepth | REDUCED | flat-kernel (line-centre, rectangular-profile) optical-depth identities: exact in that model only; applied to integrated intensities they over-correct 1.4–3.5× (audit LF-01, RF-03) |
| `opticalDepth_div_lineIntensity` | OpticalDepth | REDUCED | flat-kernel (line-centre, rectangular-profile) optical-depth identities: exact in that model only; applied to integrated intensities they over-correct 1.4–3.5× (audit LF-01, RF-03) |
| `opticalDepth_div_lineIntensity_strictAntiOn_temperature` | OpticalDepth | REDUCED | flat-kernel (line-centre, rectangular-profile) optical-depth identities: exact in that model only; applied to integrated intensities they over-correct 1.4–3.5× (audit LF-01, RF-03) |
| `lineIntensity_eq_selfAbsorbedIntensity_div` | SelfAbsorption | EXACT | same flat-kernel model; the SA identities are model left-inverses, i.e. tautologies of the model, not acceptance fixtures (audit LF-03) |
| `selfAbsorbedIntensity_eq_slab` | SelfAbsorption | EXACT | same flat-kernel model; the SA identities are model left-inverses, i.e. tautologies of the model, not acceptance fixtures (audit LF-03) |
| `selfAbsorbedIntensity_le_lineIntensity` | SelfAbsorption | APPROXIMATION | same flat-kernel model; the SA identities are model left-inverses, i.e. tautologies of the model, not acceptance fixtures (audit LF-03) |
| `selfAbsorbedIntensity_lt_lineIntensity` | SelfAbsorption | APPROXIMATION | same flat-kernel model; the SA identities are model left-inverses, i.e. tautologies of the model, not acceptance fixtures (audit LF-03) |
| `stark_saha_lte_consistent` | StarkBroadening | EXACT | Stark–Saha consistency is a conditional bundling; its McWhirter leg is unit-bearing (n_e cm⁻³, T K, ΔE eV) and its equality premise needs error bars (audit RF-20) |
| `temporal_temperature_insitu` | TemporalEvolution | REDUCED | in-situ gate temperature; carries the McWhirter unit caveat |

## Changes from v1

| v1 | v2 | why (audit) |
|---|---|---|
| Condition 2: “an IPD-lowered χ − Δχ is fine provided forward and inverse use the same value” | per-stage `(χ_eff, level list)` pair; every T- or n_e-varying row only with Δχ frozen and the list fixed | Δχ depends on the n_e being solved for and moves the cutoff (RF-10a, PS-07) |
| `hEχ` treated as physically universal | condition 1: holds only after truncation at or below χ; 202/324 DB species violate it untruncated | RF-10b, PS-06 |
| “any consistent unit system” | McWhirter-bearing results named as unit-bearing exceptions | RF-10c, PS-11 |
| Tier 1 by constants mentioned (41 rows, incl. `outerLoop_contracts_apriori`, `saha_joint_identifiability`, `neLeg_mapsTo`, twin rows) | hand-assigned tiers; loop results moved out; identifiability to Tier 2; twins dropped; per-U family added | RF-10d, SPC-12, G-15 |
| `electronDensity_antitone`: “check on a T grid” | monotonicity in R at fixed T | RF-10d |
| Tier 1b self-absorption / optical-depth rows as acceptance | annex, not acceptance | LF-03, RF-03 |
| `envelope_ionization_matrix_shift` in Tier 1b | annex, with the overclaim flagged | PS-02 |
| Tier 2 lists `outerLoop_contracts`, `jointConvergence` for `iterative.py` | dropped: they model a different loop | RF-11 |
| (routing doc) `Alt.CSigma` as `csigma.py`’s twin | explicitly not a twin; `csigma.py` has no Lean counterpart | SPC-11, RF-10e |
| `DifferentialEstimator` implicitly `opc.py`’s twin | explicitly not; no per-element-F theorem yet | RF-10 item 5 |

## How the list was generated

```lean
import CflibsFormal
open Lean Elab Command Meta

#eval show CommandElabM Unit from do
  let env ← getEnv
  let targets : List Name := [``CflibsFormal.boltzmannFactor, ``CflibsFormal.partitionFunction,
    ``CflibsFormal.population, ``CflibsFormal.sahaFactor, ``CflibsFormal.thermalBracket,
    ``CflibsFormal.electronDensityFromRatio, ``CflibsFormal.lineIntensity]
  let mut names : Array Name := #[]
  for (n, ci) in env.constants.toList do
    unless ci matches .thmInfo _ do continue
    unless (`CflibsFormal).isPrefixOf n do continue
    if n.isInternal then continue
    if (targets.filter ci.type.getUsedConstants.contains).isEmpty then continue
    names := names.push n
  let mut out : Array Json := #[]
  for n in names.qsort (·.toString < ·.toString) do
    let ci := env.find? n |>.get!
    let mod := match env.getModuleIdxFor? n with
      | some i => env.header.moduleNames[i.toNat]!.toString | none => "?"
    let sig ← liftTermElabM <| PrettyPrinter.ppSignature n
    let doc ← findDocString? env n
    let uses := targets.filter ci.type.getUsedConstants.contains
    let (hyps, concl) ← liftTermElabM <| forallTelescope ci.type fun xs body => do
      let mut hs : Array Json := #[]
      for x in xs do
        let t ← inferType x
        if ← Meta.isProp t then
          let ln := (← x.fvarId!.getDecl).userName
          hs := hs.push (Json.str s!"{ln.eraseMacroScopes} : {← ppExpr t}")
      return (hs, toString (← ppExpr body))
    out := out.push <| Json.mkObj [("name", n.toString), ("module", mod),
      ("hyps", Json.arr hyps), ("concl", concl),
      ("sig", sig.fmt.pretty 100), ("doc", (doc.getD "")),
      ("uses", Json.arr (uses.map (fun u => Json.str u.getString!)).toArray)]
  IO.FS.writeFile "sigs.json" (Json.arr out).pretty
```

Run from a built `main` checkout with `lake env lean <file>`; it writes `sigs.json` (name, module,
signature, docstring, hypotheses, conclusion, constants used), from which the tables above were
rendered; the tier of each theorem is assigned by hand (a table in the renderer), not inferred from
the constants it mentions, because that filter put loop and estimator results in Tier 1. Re-run after any change to `Boltzmann.lean`, `Saha.lean` or `ForwardMap.lean`.
