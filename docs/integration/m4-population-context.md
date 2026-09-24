# Population-layer theorems for a single `PopulationContext` (CF-LIBS-improved M4)

Acceptance criteria requested by the CF-LIBS-improved overhaul session (M4: one context for
Saha/Boltzmann/partition functions). Generated on 2026-09-24 from cflibs-formal `main` at
`fb1681d` by a Lean metaprogram (below) that lists every theorem in `CflibsFormal` whose
*statement* mentions `boltzmannFactor`, `partitionFunction`, `population`, `thermalBracket`,
`sahaFactor`, `electronDensityFromRatio` or `lineIntensity`: **150 theorems** (equation
lemmas dropped). Hypotheses and conclusions are printed by Lean, not paraphrased. Full signatures:
[`population-layer-signatures.md`](population-layer-signatures.md).

## When a theorem applies to the pipeline verbatim

A theorem transfers to the pipeline only if the context computes **the same functions**:

| spec definition (`CflibsFormal`) | formula | what the context must match |
|---|---|---|
| `boltzmannFactor kB T E` | `exp(-E / (kB·T))` | same sign and units of `E/(kB·T)` |
| `partitionFunction kB T g E` | `∑ₖ gₖ · boltzmannFactor kB T Eₖ` over a **finite, non-empty** level list | a literal level sum. A clamped, tabulated or polynomial (Irwin-type) `U(T)` is a different object: no `partitionFunction` theorem transfers to it automatically. Properties a fit happens to have (positivity on its range) must be checked on the fit itself, and the monotonicity, Lipschitz and growth results (`partitionFunction_mono_temp`, `partitionFunction_lipschitz_temp`, `partitionFunction_upper_growth`, …) can fail outright for a fit or a clamp |
| `population kB T N g E k` | `N · gₖ · boltzmannFactor / U(T)` | the **same** level list in numerator and `U` |
| `thermalBracket kB T me h` | `2π·me·kB·T / h²` | consistent units for `me`, `kB`, `T`, `h` |
| `sahaFactor kB T me h χ gZ EZ gZ1 EZ1` | `2 · (U_{Z+1}/U_Z) · thermalBracket^(3/2) · exp(-χ/(kB·T))` | `U`s from the same context; `g_e = 2` explicit |
| `electronDensityFromRatio … R` | `sahaFactor / R` | same `χ` as the forward model (see IPD below) |
| `lineIntensity kB T N Fcal g E A k` | `Fcal · Aₖ · population` (photon-rate convention, Ciucci 1999) | energy-flux form is `ForwardMapEnergy.lineIntensityEnergy`, proven to reduce |

Three cross-cutting conditions:

1. **Units.** The spec core is dimensionless `ℝ`. Every identity holds in any consistent unit
   system, so a fixture check must evaluate both sides in one system (e.g. SI with `kB` in J/K,
   or eV with `kB = 8.617e-5`). Mixing (energies in cm⁻¹, `kB` in eV/K) breaks every identity.
2. **One `χ`, forward and inverse.** Every Saha result is stated for one ionization energy `χ`.
   An IPD-lowered `χ − Δχ` is fine, **provided forward and inverse use the same value**.
   `saha_relation` is an `↔` at fixed `χ`: forward with IPD and inversion without it (the current
   `apply_ipd=False` default on the inverse side) fail its round-trip check by a factor
   `exp(Δχ/(kB·T))`.
3. **Hypotheses are real.** Positivity of `kB`, `T`, `me`, `h`, statistical weights and densities
   is required where listed. A context that admits `T ≤ 0` or `g = 0` is outside every theorem.

## Tier 1 — invariants of the context itself (M4 acceptance criteria)

Each row can be checked numerically against the new context: evaluate both sides at fixture
points drawn inside the hypotheses (and at `T` pairs for monotonicity and Lipschitz rows).

| Lean name | module | scope | hypotheses | conclusion | fixture check |
|---|---|---|---|---|---|
| `boltzmannFactor_pos` | Boltzmann | PURE-MATH | — | `0 < CflibsFormal.boltzmannFactor kB T E` | inequality: check at sample points |
| `boltzmann_plot` | Boltzmann | EXACT | [Nonempty ι]; hg : ∀ (k : ι), 0 < g k; hN : 0 < N | `Real.log (CflibsFormal.population kB T N g E k / g k) =   Real.log (N / CflibsFormal.partitionFunction kB T g E) - E k / (kB * T)` | identity: |lhs − rhs| ≤ tol |
| `partitionFunction_pos` | Boltzmann | PURE-MATH | [Nonempty ι]; hg : ∀ (k : ι), 0 < g k | `0 < CflibsFormal.partitionFunction kB T g E` | inequality: check at sample points |
| `population_sum` | Boltzmann | EXACT | [Nonempty ι]; hg : ∀ (k : ι), 0 < g k | `∑ k, CflibsFormal.population kB T N g E k = N` | identity: |lhs − rhs| ≤ tol |
| `temperature_from_two_levels` | Boltzmann | EXACT | [Nonempty ι]; hg : ∀ (k : ι), 0 < g k; hN : 0 < N; hE : E i ≠ E j | `(Real.log (CflibsFormal.population kB T N g E j / g j) - Real.log (CflibsFormal.population kB T N g E i / g i)) /     (E i - E j) =   1 / (kB * T)` | identity: |lhs − rhs| ≤ tol |
| `electronDensity_antitone` | Saha | PURE-MATH | [Nonempty ι]; [Nonempty κ]; hkB : 0 < kB; hT : 0 < T; hme : 0 < me; hh : 0 < h; hgZ : ∀ (k : ι), 0 < gZ k; hgZ1 : ∀ (k : κ), 0 < gZ1 k | `StrictAntiOn (CflibsFormal.electronDensityFromRatio kB T me h chi gZ EZ gZ1 EZ1) (Set.Ioi 0)` | monotonicity: check on a T grid |
| `log_sahaFactor` | Saha | EXACT | [Nonempty ι]; [Nonempty κ]; hkB : 0 < kB; hT : 0 < T; hme : 0 < me; hh : 0 < h; hgZ : ∀ (k : ι), 0 < gZ k; hgZ1 : ∀ (k : κ), 0 < gZ1 k | `Real.log (CflibsFormal.sahaFactor kB T me h chi gZ EZ gZ1 EZ1) =   Real.log 2 +         (Real.log (CflibsFormal.partitionFunction kB T gZ1 EZ1) -           Real.log (CflibsFormal.partitionFunction kB T gZ EZ)) +       3 / 2 * Real.log (CflibsFormal.thermalBracket kB T me h) -     chi / (kB * T)` | identity: |lhs − rhs| ≤ tol |
| `sahaFactor_pos` | Saha | PURE-MATH | [Nonempty ι]; [Nonempty κ]; hkB : 0 < kB; hT : 0 < T; hme : 0 < me; hh : 0 < h; hgZ : ∀ (k : ι), 0 < gZ k; hgZ1 : ∀ (k : κ), 0 < gZ1 k | `0 < CflibsFormal.sahaFactor kB T me h chi gZ EZ gZ1 EZ1` | inequality: check at sample points |
| `saha_relation` | Saha | EXACT | hR : R ≠ 0 | `ne = CflibsFormal.electronDensityFromRatio kB T me h chi gZ EZ gZ1 EZ1 R ↔   R * ne = CflibsFormal.sahaFactor kB T me h chi gZ EZ gZ1 EZ1` | round trip: forward then invert |
| `thermalBracket_pos` | Saha | PURE-MATH | hkB : 0 < kB; hT : 0 < T; hme : 0 < me; hh : 0 < h | `0 < CflibsFormal.thermalBracket kB T me h` | inequality: check at sample points |
| `electronDensityFromRatio_lipschitz_temp` | SahaStability | REDUCED | [Nonempty ι]; [Nonempty κ]; hkB : 0 < kB; hme : 0 < me; hh : 0 < h; hchi : 0 ≤ chi; hTmin : 0 < Tmin; hT1 : Tmin ≤ T1; hT2 : Tmin ≤ T2; hT1M : T1 ≤ Tmax; hT2M : T2 ≤ Tmax; hgZ : ∀ (k : ι), 0 < gZ k; hEZ : ∀ (k : ι), 0 ≤ EZ k; hgZ1 : ∀ (k : κ), 0 < gZ1 k; hEZ1 : ∀ (k : κ), 0 ≤ EZ1 k; hR0 : 0 < R0; hR : R0 ≤ R | `\|CflibsFormal.electronDensityFromRatio kB T1 me h chi gZ EZ gZ1 EZ1 R -       CflibsFormal.electronDensityFromRatio kB T2 me h chi gZ EZ gZ1 EZ1 R\| ≤   CflibsFormal.sahaFactorLipConst kB Tmin Tmax me h chi gZ EZ gZ1 EZ1 / R0 * \|T1 - T2\|` | inequality: check at sample points |
| `electronDensityFromRatio_strictMonoOn_temp` | SahaStability | EXACT | [Nonempty ι]; [Nonempty κ]; hkB : 0 < kB; hme : 0 < me; hh : 0 < h; hchi : 0 ≤ chi; hgZ : ∀ (k : ι), 0 < gZ k; hEZ : ∀ (k : ι), 0 ≤ EZ k; hgZ1 : ∀ (k : κ), 0 < gZ1 k; hEZ1 : ∀ (k : κ), 0 ≤ EZ1 k; hEχ : ∀ (k : ι), EZ k ≤ chi; hR : 0 < R | `StrictMonoOn (fun T => CflibsFormal.electronDensityFromRatio kB T me h chi gZ EZ gZ1 EZ1 R) (Set.Ioi 0)` | monotonicity: check on a T grid |
| `electronDensity_lipschitz` | SahaStability | EXACT | [Nonempty ι]; [Nonempty κ]; hkB : 0 < kB; hT : 0 < T; hme : 0 < me; hh : 0 < h; hgZ : ∀ (k : ι), 0 < gZ k; hgZ1 : ∀ (k : κ), 0 < gZ1 k; hR₀ : 0 < R₀; hR₁ : R₀ ≤ R₁; hR₂ : R₀ ≤ R₂ | `\|CflibsFormal.electronDensityFromRatio kB T me h chi gZ EZ gZ1 EZ1 R₁ -       CflibsFormal.electronDensityFromRatio kB T me h chi gZ EZ gZ1 EZ1 R₂\| ≤   CflibsFormal.sahaFactor kB T me h chi gZ EZ gZ1 EZ1 / R₀ ^ 2 * \|R₁ - R₂\|` | inequality: check at sample points |
| `electronDensity_relativeError` | SahaStability | EXACT | [Nonempty ι]; [Nonempty κ]; hkB : 0 < kB; hT : 0 < T; hme : 0 < me; hh : 0 < h; hgZ : ∀ (k : ι), 0 < gZ k; hgZ1 : ∀ (k : κ), 0 < gZ1 k; hR₁ : 0 < R₁; hR₂ : 0 < R₂ | `CflibsFormal.electronDensityFromRatio kB T me h chi gZ EZ gZ1 EZ1 R₁ /     CflibsFormal.electronDensityFromRatio kB T me h chi gZ EZ gZ1 EZ1 R₂ =   R₂ / R₁` | identity: |lhs − rhs| ≤ tol |
| `partitionFunction_mono_temp` | SahaStability | PURE-MATH | hkB : 0 < kB; hT1 : 0 < T1; hT12 : T1 ≤ T2; hg : ∀ (k : ι), 0 < g k; hE : ∀ (k : ι), 0 ≤ E k | `CflibsFormal.partitionFunction kB T1 g E ≤ CflibsFormal.partitionFunction kB T2 g E` | inequality: check at sample points |
| `partitionFunction_upper_growth` | SahaStability | PURE-MATH | hkB : 0 < kB; hT1 : 0 < T1; hT12 : T1 ≤ T2; hg : ∀ (k : ι), 0 < g k; hEχ : ∀ (k : ι), E k ≤ chi | `CflibsFormal.partitionFunction kB T2 g E ≤   Real.exp (chi * (1 / (kB * T1) - 1 / (kB * T2))) * CflibsFormal.partitionFunction kB T1 g E` | inequality: check at sample points |
| `sahaFactor_lipschitz_temp` | SahaStability | REDUCED | [Nonempty ι]; [Nonempty κ]; hkB : 0 < kB; hme : 0 < me; hh : 0 < h; hchi : 0 ≤ chi; hTmin : 0 < Tmin; hT1 : Tmin ≤ T1; hT2 : Tmin ≤ T2; hT1M : T1 ≤ Tmax; hT2M : T2 ≤ Tmax; hgZ : ∀ (k : ι), 0 < gZ k; hEZ : ∀ (k : ι), 0 ≤ EZ k; hgZ1 : ∀ (k : κ), 0 < gZ1 k; hEZ1 : ∀ (k : κ), 0 ≤ EZ1 k | `\|CflibsFormal.sahaFactor kB T1 me h chi gZ EZ gZ1 EZ1 - CflibsFormal.sahaFactor kB T2 me h chi gZ EZ gZ1 EZ1\| ≤   CflibsFormal.sahaFactorLipConst kB Tmin Tmax me h chi gZ EZ gZ1 EZ1 * \|T1 - T2\|` | inequality: check at sample points |
| `sahaFactor_strictMonoOn_temp` | SahaStability | EXACT | [Nonempty ι]; [Nonempty κ]; hkB : 0 < kB; hme : 0 < me; hh : 0 < h; _hchi : 0 ≤ chi; hgZ : ∀ (k : ι), 0 < gZ k; _hEZ : ∀ (k : ι), 0 ≤ EZ k; hgZ1 : ∀ (k : κ), 0 < gZ1 k; hEZ1 : ∀ (k : κ), 0 ≤ EZ1 k; hEχ : ∀ (k : ι), EZ k ≤ chi | `StrictMonoOn (fun T => CflibsFormal.sahaFactor kB T me h chi gZ EZ gZ1 EZ1) (Set.Ioi 0)` | monotonicity: check on a T grid |
| `thermalBracket_strictMono` | SahaStability | PURE-MATH | hkB : 0 < kB; hme : 0 < me; hh : 0 < h; hab : Ta < Tb | `CflibsFormal.thermalBracket kB Ta me h < CflibsFormal.thermalBracket kB Tb me h` | inequality: check at sample points |
| `partitionFunction_lipschitz_temp` | PartitionLipschitz | REDUCED | hkB : 0 < kB; hTmin : 0 < Tmin; hT1 : Tmin ≤ T1; hT2 : Tmin ≤ T2; hg : ∀ (k : ι), 0 < g k; hE : ∀ (k : ι), 0 ≤ E k | `\|CflibsFormal.partitionFunction kB T1 g E - CflibsFormal.partitionFunction kB T2 g E\| ≤   (∑ k, g k * E k) / (kB * Tmin ^ 2) * \|T1 - T2\|` | inequality: check at sample points |
| `partitionFunction_relative_error_temp` | PartitionLipschitz | REDUCED | [Nonempty ι]; hkB : 0 < kB; hTmin : 0 < Tmin; hT1 : Tmin ≤ T1; hT2 : Tmin ≤ T2; hg : ∀ (k : ι), 0 < g k; hE : ∀ (k : ι), 0 ≤ E k | `\|CflibsFormal.partitionFunction kB T1 g E - CflibsFormal.partitionFunction kB T2 g E\| /     CflibsFormal.partitionFunction kB T2 g E ≤   (∑ k, g k * E k) / (kB * Tmin ^ 2) * \|T1 - T2\| / CflibsFormal.partitionFunction kB T2 g E` | inequality: check at sample points |
| `partitionFunction_two_point_bound` | PartitionLipschitz | REDUCED | hkB : 0 < kB; hT1 : 0 < T1; hT2 : 0 < T2; hg : ∀ (k : ι), 0 < g k; hE : ∀ (k : ι), 0 ≤ E k | `\|CflibsFormal.partitionFunction kB T1 g E - CflibsFormal.partitionFunction kB T2 g E\| ≤   (∑ k, g k * E k) * \|1 / (kB * T1) - 1 / (kB * T2)\|` | inequality: check at sample points |
| `electronDensityFromRatio_mem_Icc` | SahaRangeEnclosure | EXACT | [Nonempty ι]; [Nonempty κ]; hkB : 0 < kB; hme : 0 < me; hh : 0 < h; hchi : 0 ≤ chi; hgZ : ∀ (k : ι), 0 < gZ k; hEZ : ∀ (k : ι), 0 ≤ EZ k; hgZ1 : ∀ (k : κ), 0 < gZ1 k; hEZ1 : ∀ (k : κ), 0 ≤ EZ1 k; hEχ : ∀ (k : ι), EZ k ≤ chi; hTmin : 0 < Tmin; hR : 0 < R; hT : T ∈ Set.Icc Tmin Tmax | `CflibsFormal.electronDensityFromRatio kB T me h chi gZ EZ gZ1 EZ1 R ∈   Set.Icc (CflibsFormal.electronDensityFromRatio kB Tmin me h chi gZ EZ gZ1 EZ1 R)     (CflibsFormal.electronDensityFromRatio kB Tmax me h chi gZ EZ gZ1 EZ1 R)` | enclosure: value lies in the stated interval |
| `outerLoop_contracts_apriori` | SahaRangeEnclosure | REDUCED | [Nonempty ιe]; [Nonempty κe]; [Nonempty ιl]; hTle : Tmin ≤ Tmax; hkB : 0 < kB; hme : 0 < me; hh : 0 < h; hchi : 0 ≤ chi; hTmin : 0 < Tmin; hgZ : ∀ (k : ιe), 0 < gZ k; hEZ : ∀ (k : ιe), 0 ≤ EZ k; hgZ1 : ∀ (k : κe), 0 < gZ1 k; hEZ1 : ∀ (k : κe), 0 ≤ EZ1 k; hEχ : ∀ (k : ιe), EZ k ≤ chi; hR0 : 0 < R0; hR : R0 ≤ R; hvar : 0 < ∑ k, (E k - CflibsFormal.mean E) ^ 2; hnemin : 0 < nemin; hsmin : 0 < smin; hnelo : nemin ≤ CflibsFormal.electronDensityFromRatio kB Tmin me h chi gZ EZ gZ1 EZ1 R; hnehi : CflibsFormal.electronDensityFromRatio kB Tmax me h chi gZ EZ gZ1 EZ1 R ≤ nemax; hmapsT : ∀ ne ∈ Set.Icc nemin nemax, CflibsFormal.combinedSlopeTempUpdate kB E yb svec offConst ne ∈ Set.Icc Tmin Tmax; hslopeFloor : ∀ ne ∈ Set.Icc nemin nemax, smin ≤ CflibsFormal.combinedSahaBoltzmannSlope E yb svec offConst ne; hL1nn : 0 ≤ CflibsFormal.sahaFactorLipConst kB Tmin Tmax me h chi gZ EZ gZ1 EZ1 / R0; hgate : CflibsFormal.sahaFactorLipConst kB Tmin Tmax me h chi gZ EZ gZ1 EZ1 / R0 *     ((\|∑ k, (E k - CflibsFormal.mean E) * svec k\| / ∑ k, (E k - CflibsFormal.mean E) ^ 2) / (kB * smin ^ 2 * nemin)) <   1 | `∃ Tstar ∈ Set.Icc Tmin Tmax,   CflibsFormal.outerMap (fun T => CflibsFormal.electronDensityFromRatio kB T me h chi gZ EZ gZ1 EZ1 R)         (fun ne => CflibsFormal.combinedSlopeTempUpdate kB E yb svec offConst ne) Tstar =       Tstar ∧     (∀ T ∈ Set.Icc Tmin Tmax,         CflibsFormal.outerMap (fun T => CflibsFormal.electronDensityFromRatio kB T me h chi gZ EZ gZ1 EZ1 R)               (fun ne => CflibsFormal.combinedSlopeTempUpdate kB E yb svec offConst ne) T =             T →           T = Tstar) ∧       ∀ T0 ∈ Set.Icc Tmin Tmax,         Filter.Tendsto           (fun n =>             (CflibsFormal.outerMap (fun T => CflibsFormal.electronDensityFromRatio kB T me h chi gZ EZ gZ1 EZ1 R)                   fun ne => CflibsFormal.combinedSlopeTempUpdate kB E yb svec offConst ne)^[n]               T0)           Filter.atTop (nhds Tstar)` | enclosure: value lies in the stated interval |
| `sahaFactor_mem_Icc` | SahaRangeEnclosure | EXACT | [Nonempty ι]; [Nonempty κ]; hkB : 0 < kB; hme : 0 < me; hh : 0 < h; hchi : 0 ≤ chi; hgZ : ∀ (k : ι), 0 < gZ k; hEZ : ∀ (k : ι), 0 ≤ EZ k; hgZ1 : ∀ (k : κ), 0 < gZ1 k; hEZ1 : ∀ (k : κ), 0 ≤ EZ1 k; hEχ : ∀ (k : ι), EZ k ≤ chi; hTmin : 0 < Tmin; hT : T ∈ Set.Icc Tmin Tmax | `CflibsFormal.sahaFactor kB T me h chi gZ EZ gZ1 EZ1 ∈   Set.Icc (CflibsFormal.sahaFactor kB Tmin me h chi gZ EZ gZ1 EZ1)     (CflibsFormal.sahaFactor kB Tmax me h chi gZ EZ gZ1 EZ1)` | enclosure: value lies in the stated interval |
| `sahaBoltzmann_plot` | SahaInverse | REDUCED | [Nonempty ι]; [Nonempty κ]; hgZ : ∀ (k : ι), 0 < gZ k; hgZ1 : ∀ (k : κ), 0 < gZ1 k; hNz : 0 < Nz; hNz1 : 0 < Nz1; hFcal : 0 < Fcal; hAZ : ∀ (k : ι), 0 < AZ k; hAZ1 : ∀ (k : κ), 0 < AZ1 k | `CflibsFormal.sahaBoltzmannOrdinate kB T Nz Fcal gZ EZ AZ kz =     CflibsFormal.stageIntercept kB T Nz Fcal gZ EZ - EZ kz / (kB * T) ∧   CflibsFormal.sahaBoltzmannOrdinate kB T Nz1 Fcal gZ1 EZ1 AZ1 kz1 =       CflibsFormal.stageIntercept kB T Nz1 Fcal gZ1 EZ1 - EZ1 kz1 / (kB * T) ∧     CflibsFormal.stageIntercept kB T Nz1 Fcal gZ1 EZ1 - CflibsFormal.stageIntercept kB T Nz Fcal gZ EZ =       Real.log (Nz1 / Nz) +         (Real.log (CflibsFormal.partitionFunction kB T gZ EZ) - Real.log (CflibsFormal.partitionFunction kB T gZ1 EZ1))` | identity: |lhs − rhs| ≤ tol |
| `sahaBoltzmann_shift_eq_log_saha` | SahaInverse | EXACT | [Nonempty ι]; [Nonempty κ]; hkB : 0 < kB; hT : 0 < T; hme : 0 < me; hh : 0 < h; hgZ : ∀ (k : ι), 0 < gZ k; hgZ1 : ∀ (k : κ), 0 < gZ1 k; hNz : 0 < Nz; hNz1 : 0 < Nz1; hFcal : 0 < Fcal; hne : 0 < ne; hsaha : Nz1 * ne / Nz = CflibsFormal.sahaFactor kB T me h chi gZ EZ gZ1 EZ1 | `CflibsFormal.stageIntercept kB T Nz1 Fcal gZ1 EZ1 - CflibsFormal.stageIntercept kB T Nz Fcal gZ EZ =   Real.log (CflibsFormal.sahaFactor kB T me h chi gZ EZ gZ1 EZ1) - Real.log ne +     (Real.log (CflibsFormal.partitionFunction kB T gZ EZ) - Real.log (CflibsFormal.partitionFunction kB T gZ1 EZ1))` | identity: |lhs − rhs| ≤ tol |
| `saha_joint_identifiability` | SahaInverse | EXACT | [Nonempty ι]; [Nonempty κ]; hkB : 0 < kB; _hme : 0 < me; _hh : 0 < h; hT₁ : 0 < T₁; hT₂ : 0 < T₂; hgZ : ∀ (k : ι), 0 < gZ k; hgZ1 : ∀ (k : κ), 0 < gZ1 k; hAZ : ∀ (k : ι), 0 < AZ k; hAZ1 : ∀ (k : κ), 0 < AZ1 k; hNz₁ : 0 < Nz₁; hNz₂ : 0 < Nz₂; hNz1₁ : 0 < Nz1₁; _hNz1₂ : 0 < Nz1₂; hFcal : 0 < Fcal; _hne₁ : 0 < ne₁; _hne₂ : 0 < ne₂; hE : EZ i ≠ EZ j; hslope : CflibsFormal.lineIntensity kB T₁ Nz₁ Fcal gZ EZ AZ j / CflibsFormal.lineIntensity kB T₁ Nz₁ Fcal gZ EZ AZ i =   CflibsFormal.lineIntensity kB T₂ Nz₂ Fcal gZ EZ AZ j / CflibsFormal.lineIntensity kB T₂ Nz₂ Fcal gZ EZ AZ i; hNeutObs : CflibsFormal.lineIntensity kB T₁ Nz₁ Fcal gZ EZ AZ uz = CflibsFormal.lineIntensity kB T₂ Nz₂ Fcal gZ EZ AZ uz; hIonObs : CflibsFormal.lineIntensity kB T₁ Nz1₁ Fcal gZ1 EZ1 AZ1 uz1 = CflibsFormal.lineIntensity kB T₂ Nz1₂ Fcal gZ1 EZ1 AZ1 uz1; hsaha₁ : Nz1₁ * ne₁ / Nz₁ = CflibsFormal.sahaFactor kB T₁ me h chi gZ EZ gZ1 EZ1; hsaha₂ : Nz1₂ * ne₂ / Nz₂ = CflibsFormal.sahaFactor kB T₂ me h chi gZ EZ gZ1 EZ1 | `T₁ = T₂ ∧ ne₁ = ne₂` | identity: |lhs − rhs| ≤ tol |
| `neLeg_mapsTo` | SahaEquilibrium | REDUCED | hR : 0 < R; hSlo : ∀ T ∈ Set.Icc Tmin Tmax, Slo ≤ CflibsFormal.sahaFactor kB T me h chi gZ EZ gZ1 EZ1; hShi : ∀ T ∈ Set.Icc Tmin Tmax, CflibsFormal.sahaFactor kB T me h chi gZ EZ gZ1 EZ1 ≤ Shi; hnemin : nemin ≤ Slo / R; hnemax : Shi / R ≤ nemax; a : T ∈ Set.Icc Tmin Tmax | `CflibsFormal.electronDensityFromRatio kB T me h chi gZ EZ gZ1 EZ1 R ∈ Set.Icc nemin nemax` | enclosure: value lies in the stated interval |
| `boltzmann_plot_intensity` | ForwardMap | REDUCED | [Nonempty ι]; hg : ∀ (k : ι), 0 < g k; hN : 0 < N; hFcal : 0 < Fcal; hA : ∀ (k : ι), 0 < A k | `Real.log (CflibsFormal.lineIntensity kB T N Fcal g E A k / (g k * A k)) =   Real.log (Fcal * N / CflibsFormal.partitionFunction kB T g E) - E k / (kB * T)` | identity: |lhs − rhs| ≤ tol |
| `lineIntensity_pos` | ForwardMap | PURE-MATH | [Nonempty ι]; hg : ∀ (k : ι), 0 < g k; hN : 0 < N; hFcal : 0 < Fcal; hA : ∀ (k : ι), 0 < A k | `0 < CflibsFormal.lineIntensity kB T N Fcal g E A k` | inequality: check at sample points |
| `temperature_from_two_lines` | ForwardMap | REDUCED | [Nonempty ι]; hg : ∀ (k : ι), 0 < g k; hN : 0 < N; hFcal : 0 < Fcal; hA : ∀ (k : ι), 0 < A k; hE : E i ≠ E j | `(Real.log (CflibsFormal.lineIntensity kB T N Fcal g E A j / (g j * A j)) -       Real.log (CflibsFormal.lineIntensity kB T N Fcal g E A i / (g i * A i))) /     (E i - E j) =   1 / (kB * T)` | identity: |lhs − rhs| ≤ tol |
| `boltzmann_plot_intensity_wavelength` | ForwardMapEnergy | EXACT | [Nonempty ι]; hg : ∀ (k : ι), 0 < g k; hN : 0 < N; hhc : 0 < hc; hfp : 0 < fourPi; hFgeo : 0 < Fgeo; hA : ∀ (k : ι), 0 < A k; hlam : ∀ (k : ι), 0 < lam k | `Real.log (CflibsFormal.lineIntensityEnergy hc fourPi kB T N Fgeo g E A lam k * lam k / (g k * A k)) =   Real.log (hc * Fgeo * N / (fourPi * CflibsFormal.partitionFunction kB T g E)) - E k / (kB * T)` | identity: |lhs − rhs| ≤ tol |
| `lineIntensityEnergy_eq_lineIntensity` | ForwardMapEnergy | REDUCED | — | `CflibsFormal.lineIntensityEnergy hc fourPi kB T N Fgeo g E A lam k =   CflibsFormal.lineIntensity kB T N (hc * Fgeo / (fourPi * lam k)) g E A k` | identity: |lhs − rhs| ≤ tol |
| `lineIntensityEnergy_mul_lam` | ForwardMapEnergy | REDUCED | hlam : lam k ≠ 0 | `CflibsFormal.lineIntensityEnergy hc fourPi kB T N Fgeo g E A lam k * lam k =   CflibsFormal.lineIntensity kB T N (hc * Fgeo / fourPi) g E A k` | identity: |lhs − rhs| ≤ tol |
| `deNormalizedDensity_eq_deNormalizedDensityPerU` | MultiSpecies | PURE-MATH | — | `CflibsFormal.deNormalizedDensity kB T Fcal g E A s I =   CflibsFormal.deNormalizedDensityPerU kB T Fcal (CflibsFormal.partitionFunction kB T g E) g E A s I` | identity: |lhs − rhs| ≤ tol |
| `deNormalized_lineIntensity` | MultiSpecies | EXACT | [Nonempty ι]; hg : ∀ (k : ι), 0 < g k; hN : 0 < N; hFcal : 0 < Fcal; hA : ∀ (k : ι), 0 < A k | `CflibsFormal.deNormalizedDensity kB T Fcal g E A s (CflibsFormal.lineIntensity kB T N Fcal g E A s) = N` | identity: |lhs − rhs| ≤ tol |
| `deNormalized_lineIntensity_ofPerU` | MultiSpecies | EXACT | [Nonempty ι]; hg : ∀ (k : ι), 0 < g k; hFcal : 0 < Fcal; hA : ∀ (k : ι), 0 < A k | `CflibsFormal.deNormalizedDensity kB T Fcal g E A s (CflibsFormal.lineIntensity kB T N Fcal g E A s) = N` | identity: |lhs − rhs| ≤ tol |
| `density_ratio_from_intensities` | MultiSpecies | EXACT | [Nonempty ι]; hg : ∀ (k : ι), 0 < g k; hNs : 0 < Ns; hNt : 0 < Nt; hFcal : 0 < Fcal; hA : ∀ (k : ι), 0 < A k | `CflibsFormal.deNormalizedDensity kB T Fcal g E A s (CflibsFormal.lineIntensity kB T Ns Fcal g E A s) /     CflibsFormal.deNormalizedDensity kB T Fcal g E A t (CflibsFormal.lineIntensity kB T Nt Fcal g E A t) =   Ns / Nt` | identity: |lhs − rhs| ≤ tol |
| `density_ratio_from_intensities_ofPerU` | MultiSpecies | EXACT | [Nonempty ι]; hg : ∀ (k : ι), 0 < g k; hFcal : 0 < Fcal; hA : ∀ (k : ι), 0 < A k | `CflibsFormal.deNormalizedDensity kB T Fcal g E A s (CflibsFormal.lineIntensity kB T Ns Fcal g E A s) /     CflibsFormal.deNormalizedDensity kB T Fcal g E A t (CflibsFormal.lineIntensity kB T Nt Fcal g E A t) =   Ns / Nt` | identity: |lhs − rhs| ≤ tol |
| `lineIntensity_eq_lineIntensityPerU` | MultiSpecies | PURE-MATH | — | `CflibsFormal.lineIntensity kB T N Fcal g E A s =   CflibsFormal.lineIntensityPerU kB T N Fcal (CflibsFormal.partitionFunction kB T g E) g E A s` | identity: |lhs − rhs| ≤ tol |

## Tier 1b — context plus one extra model (optical depth, self-absorption, Stark, temporal gating)

These need a second definition beyond the population layer (`opticalDepth`,
`selfAbsorbedIntensity`, the Stark and temporal models). They apply once those stages read `U`
and populations from the same context (M5's explicit emission/transport stages).

| Lean name | module | scope | hypotheses | conclusion | fixture check |
|---|---|---|---|---|---|
| `lineIntensity_div_opticalDepth` | OpticalDepth | REDUCED | [Nonempty ι]; hg : ∀ (k : ι), 0 < g k; hN : 0 < N; hsig : 0 < sigma0; hell : 0 < ell | `CflibsFormal.lineIntensity kB T N Fcal g E A u / CflibsFormal.opticalDepth kB T N sigma0 ell g E l =   CflibsFormal.lteSourceStrength kB T Fcal sigma0 ell g E A u l` | identity: |lhs − rhs| ≤ tol |
| `lineIntensity_eq_source_mul_opticalDepth` | OpticalDepth | REDUCED | [Nonempty ι]; hg : ∀ (k : ι), 0 < g k; hsig : 0 < sigma0; hell : 0 < ell | `CflibsFormal.lineIntensity kB T N Fcal g E A u =   CflibsFormal.lteSourceStrength kB T Fcal sigma0 ell g E A u l * CflibsFormal.opticalDepth kB T N sigma0 ell g E l` | identity: |lhs − rhs| ≤ tol |
| `opticalDepth_div_lineIntensity` | OpticalDepth | REDUCED | [Nonempty ι]; hg : ∀ (k : ι), 0 < g k; hN : 0 < N; hFcal : 0 < Fcal; hA : ∀ (k : ι), 0 < A k; hsig : 0 < sigma0; hell : 0 < ell | `CflibsFormal.opticalDepth kB T N sigma0 ell g E l / CflibsFormal.lineIntensity kB T N Fcal g E A u =   sigma0 * ell * g l / (Fcal * A u * g u) * Real.exp ((E u - E l) / (kB * T))` | identity: |lhs − rhs| ≤ tol |
| `opticalDepth_div_lineIntensity_strictAntiOn_temperature` | OpticalDepth | REDUCED | [Nonempty ι]; hg : ∀ (k : ι), 0 < g k; hN : 0 < N; hFcal : 0 < Fcal; hA : ∀ (k : ι), 0 < A k; hsig : 0 < sigma0; hell : 0 < ell; hkB : 0 < kB; hE : E l < E u | `StrictAntiOn   (fun T => CflibsFormal.opticalDepth kB T N sigma0 ell g E l / CflibsFormal.lineIntensity kB T N Fcal g E A u)   (Set.Ioi 0)` | monotonicity: check on a T grid |
| `lineIntensity_eq_selfAbsorbedIntensity_div` | SelfAbsorption | EXACT | htau : 0 ≤ tau | `CflibsFormal.lineIntensity kB T N Fcal g E A k =   CflibsFormal.selfAbsorbedIntensity kB T N Fcal g E A k tau / CflibsFormal.selfAbsorptionFactor tau` | identity: |lhs − rhs| ≤ tol |
| `selfAbsorbedIntensity_eq_slab` | SelfAbsorption | EXACT | htau : 0 < tau | `CflibsFormal.selfAbsorbedIntensity kB T N Fcal g E A k tau =   CflibsFormal.slabIntensity (CflibsFormal.lineIntensity kB T N Fcal g E A k / tau) tau` | identity: |lhs − rhs| ≤ tol |
| `selfAbsorbedIntensity_le_lineIntensity` | SelfAbsorption | APPROXIMATION | [Nonempty ι]; hg : ∀ (k : ι), 0 < g k; hN : 0 < N; hFcal : 0 < Fcal; hA : ∀ (k : ι), 0 < A k; htau : 0 ≤ tau | `CflibsFormal.selfAbsorbedIntensity kB T N Fcal g E A k tau ≤ CflibsFormal.lineIntensity kB T N Fcal g E A k` | inequality: check at sample points |
| `selfAbsorbedIntensity_lt_lineIntensity` | SelfAbsorption | APPROXIMATION | [Nonempty ι]; hg : ∀ (k : ι), 0 < g k; hN : 0 < N; hFcal : 0 < Fcal; hA : ∀ (k : ι), 0 < A k; htau : 0 < tau | `CflibsFormal.selfAbsorbedIntensity kB T N Fcal g E A k tau < CflibsFormal.lineIntensity kB T N Fcal g E A k` | inequality: check at sample points |
| `stark_saha_lte_consistent` | StarkBroadening | EXACT | hw : w ≠ 0; hnRef : nRef ≠ 0; hR : R ≠ 0; hagree : CflibsFormal.starkDensity w nRef width = CflibsFormal.electronDensityFromRatio kB T me h chi gZ EZ gZ1 EZ1 R; hlte : CflibsFormal.lteValid T dE (CflibsFormal.starkDensity w nRef width) | `∃ ne,   ne = CflibsFormal.starkDensity w nRef width ∧     ne = CflibsFormal.electronDensityFromRatio kB T me h chi gZ EZ gZ1 EZ1 R ∧       CflibsFormal.mcWhirterBound T dE ≤ ne ∧         width = CflibsFormal.starkFWHM w nRef ne ∧ R * ne = CflibsFormal.sahaFactor kB T me h chi gZ EZ gZ1 EZ1` | inequality: check at sample points |
| `temporal_temperature_insitu` | TemporalEvolution | REDUCED | [Nonempty ι]; hg : ∀ (s : σ) (k : ι), 0 < g s k; hN0 : ∀ (s : σ), 0 < N0 s; hFcal : 0 < Fcal; hA : ∀ (s : σ) (k : ι), 0 < A s k; hρ : 0 < ρ t; hE : E s i ≠ E s j | `(Real.log (CflibsFormal.lineIntensity kB (T t) (ρ t * N0 s) Fcal (g s) (E s) (A s) j / (g s j * A s j)) -       Real.log (CflibsFormal.lineIntensity kB (T t) (ρ t * N0 s) Fcal (g s) (E s) (A s) i / (g s i * A s i))) /     (E s i - E s j) =   1 / (kB * T t)` | identity: |lhs − rhs| ≤ tol |
| `envelope_ionization_matrix_shift` | MatrixIonizationCoupling | REDUCED | [Nonempty ι]; hS : ∀ (s : ι), 0 < S s; hS' : ∀ (s : ι), 0 < S' s; hN : ∀ (s : ι), 0 < Ntot s; hmono : ∀ (s : ι), S s ≤ S' s; hs0 : S s0 < S' s0; hx : 0 < x; hy : 0 < y; hxeq : x = CflibsFormal.multiElementIonized S Ntot x; hyeq : y = CflibsFormal.multiElementIonized S' Ntot y; hSspec : 0 < Sspec; hNspec : 0 < Nspec; [Nonempty μ]; hg : ∀ (k : μ), 0 < g k; hNt : 0 < Nt; hFcal : 0 < Fcal; hA : ∀ (k : μ), 0 < A k; hE : E a = E b | `x < y ∧   CflibsFormal.sahaIonDensity Sspec Nspec y < CflibsFormal.sahaIonDensity Sspec Nspec x ∧     CflibsFormal.lineIntensity kB Told Ns Fcal g E A a / CflibsFormal.lineIntensity kB Told Nt Fcal g E A b =       CflibsFormal.lineIntensity kB Tnew Ns Fcal g E A a / CflibsFormal.lineIntensity kB Tnew Nt Fcal g E A b` | inequality: check at sample points |

## Tier 2 — estimator results that consume the context (not M4 acceptance)

These are statements about estimators built **on top of** the population layer (classic
closure, C-sigma, least squares, identifiability, error transfer). They apply to a pipeline
estimator only when that estimator implements the same formula on the context (M6), so they are
acceptance material for M6 rather than M4. By module:

- **NonlinearLeastSquares** (24): `Nsection_minimizer_unique`, `clean_residual_ratio`, `joint_onManifold_unique`, `lineIntensity_linear_in_N`, `nlObjective_Nsection_decomposition`, `nlObjective_Nsection_lt_of_ne`, `nlObjective_eq_sq_sum`, `nlObjective_eq_zero_iff`, `nlObjective_onManifold_min`, `profiledDensity_denom_pos`, `profiledDensity_isMinOn_Nsection`, `profiledDensity_onManifold`, `profiledResidual_metric_bound`, `profiledResidual_minimizer_trapped`, `profiledResidual_nearManifold_bound`, `profiledResidual_of_orthogonal`, `profiledResidual_stability_in_obs`, `profiledResidual_true_strict_lt`, `profiledResidual_two_closed_form`, `profiledResidual_two_eq_ratio`, `profiledT_onManifold_unique`, `profiledT_two_offManifold_box_unique`, `profiledT_two_onManifold_unique`, `two_ratio_diff`
- **Alt.CSigma** (8): `csigmaOffset_of_lineIntensity`, `csigma_agrees_classic`, `csigma_agrees_of_sound`, `csigma_cross_stage_collapse`, `csigma_saha_master_line`, `csigma_saha_universal_line`, `csigma_sound`, `csigma_temperature_cross_stage`
- **ProfiledTUniqueness** (8): `joint_twoLevel_box_isStrictMin`, `joint_twoLevel_box_minimizer_unique`, `joint_two_box_isStrictMin`, `joint_two_box_minimizer_unique`, `profiledResidual_eq_rayleigh`, `profiledResidual_twoLevel_Tstar_isStrictMin`, `profiledResidual_twoLevel_strictUnimodalOn`, `profiledResidual_twoLevel_strictUnimodal_onManifold`
- **DifferentialEstimator** (7): `classic_biased_differential_exact`, `differentialRatio_eq_density_ratio`, `differentialRatio_error_bound`, `differentialRatio_immune_to_atomicData`, `differentialSlope_eq_neg_dbeta`, `differentialSlope_two_lines`, `logDifferentialRatio_affine_in_E`
- **Identifiability** (7): `density_identifiability`, `electron_density_identifiability`, `lineIntensity_ratio_closed_form`, `temperature_degeneracy`, `temperature_identifiability`, `temperature_not_identifiable_of_degenerate`, `temperature_ratio_near_degenerate`
- **AtomicDataPerturbation** (6): `classicDensity_aliasing`, `classicDensity_aliasing_error`, `classicDensity_aliasing_error_channels`, `classicDensity_aliasing_error_energy`, `classicDensity_temperature_aliasing`, `classicDensity_temperature_aliasing_error`
- **Alt.NeutralityScale** (5): `closureEstimate_bias`, `lineIntensity_linear`, `lineIntensity_ratio`, `neutralityScale_eq_Fcal`, `neutralityScale_undetected`
- **HeteroAtomicData** (5): `nvP_slope_bias_eq_log`, `olsSlope_aliasing_A`, `olsSlope_aliasing_A_global`, `olsSlope_aliasing_A_hetero`, `temp_rel_error_atomicData_hetero`
- **Alt.LeastSquares** (4): `leastSquares_agrees_classic`, `leastSquares_sound`, `olsDensity_recovers`, `olsIntercept_of_forward`
- **Classic** (4): `classicDensity_recovers`, `classic_sound`, `classic_sound_sum_one`, `classic_temperature_correct`
- **Alt.OLSAtomicDataPerturbation** (3): `olsDensity_aliasing_A`, `olsDensity_aliasing_A_error`, `olsDensity_aliasing_E_error`
- **MatrixEffects** (3): `homologousPair_ratio_closed_form`, `homologousPair_ratio_temperature_invariant`, `nonHomologousPair_ratio_temperature_dependent`
- **ProfiledUnimodality** (3): `profiledResidual_two_Tstar_isStrictMin`, `profiledResidual_two_strictUnimodalOn`, `profiledResidual_two_strictUnimodal_onManifold`
- **Certificates** (2): `aliasBudget_certificate_sound`, `knownTau_certificate_sound`
- **OpticalDepthBridge** (2): `lteSourceStrength_ratio_calibration_free`, `thickLineIntensity_lt_lineIntensity_of_pos_density`
- **CompositionIdentifiability** (2): `eq_2`, `eq_3`
- **Inverse** (1): `general_identifiability`
- **JointConvergence** (1): `jointConvergence`
- **SelfAbsorptionInverse** (1): `lineIntensity_smul_left`
- **NoiseToComposition** (1): `noise_to_density`
- **OuterLoopModelB** (1): `outerLoop_contracts`

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
rendered. Re-run after any change to `Boltzmann.lean`, `Saha.lean` or `ForwardMap.lean`.
