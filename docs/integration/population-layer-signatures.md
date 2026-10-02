# Population-layer theorems: full signatures

Companion to `m4-population-context.md` (v2); generated from `main` at `fb1681d`, one entry per theorem (155).

### `CflibsFormal.Alt.csigmaOffset_of_lineIntensity`

Module `CflibsFormal.Alt.CSigma` · scope `EXACT`

```lean
CflibsFormal.Alt.csigmaOffset_of_lineIntensity.{u_1} {ι : Type u_1} [Fintype ι] [Nonempty ι]
  {kB T N Fcal : ℝ} {g E A : ι → ℝ} (hg : ∀ (k : ι), 0 < g k) (hN : 0 < N) (hFcal : 0 < Fcal)
  (u : ι) (hA : 0 < A u) :
  CflibsFormal.Alt.csigmaOffsetOfIntensity kB T g E A u
      (CflibsFormal.lineIntensity kB T N Fcal g E A u) =
    CflibsFormal.Alt.csigmaOffset kB T Fcal N g E
```

> **The measurement step recovers the true offset.** Feeding a genuine forward-model
> line intensity into the C-sigma offset reader `csigmaOffsetOfIntensity` returns exactly the
> analytic offset `q_s = csigmaOffset … = log(Fcal·N_s/U_s)`. This is the non-tautological
> link between the OBSERVED spectrum and the composition-bearing offset: it reduces to the
> intensity Boltzmann-plot intercept, the `E_u/(k_B T)` terms cancelling. Only positivity at
> the single measured line `u` is needed. 

### `CflibsFormal.Alt.csigma_agrees_classic`

Module `CflibsFormal.Alt.CSigma` · scope `PURE-MATH`

```lean
CflibsFormal.Alt.csigma_agrees_classic.{u_1, u_2} {ι : Type u_1} [Fintype ι] {κ : Type u_2}
  [Fintype κ] [Nonempty ι] {kB T Fcal : ℝ} {N : κ → ℝ} {g E A : κ → ι → ℝ} {u : κ → ι}
  (hg : ∀ (s : κ) (k : ι), 0 < g s k) (hN : ∀ (s : κ), 0 < N s) (hFcal : 0 < Fcal)
  (hA : ∀ (s : κ), 0 < A s (u s)) (s : κ) :
  CflibsFormal.Alt.csigmaComposition kB T Fcal g E A u
      (fun t => CflibsFormal.lineIntensity kB T (N t) Fcal (g t) (E t) (A t) (u t)) s =
    CflibsFormal.Classic.classicComposition kB T Fcal g E A u
      (fun t => CflibsFormal.lineIntensity kB T (N t) Fcal (g t) (E t) (A t) (u t)) s
```

> **Cross-method agreement on a measured spectrum (forward-data instance).** Fed the SAME
> measured line intensities `I_t = lineIntensity …`, `csigmaComposition` and
> `Classic.classicComposition` return the SAME composition. Honest framing: this is NOT two
> independent procedures coinciding "because both are sound" — by
> `csigmaComposition_eq_classicComposition` they are the IDENTICAL function on all positive
> intensities (the C-sigma offset-inversion is the classic density inverse in `log/exp`
> packaging). This theorem is just that unconditional identity applied to the (positive)
> forward spectrum. The genuine same-spectrum agreement between *structurally different*
> estimators is the OLS-vs-classic one (`Alt.leastSquares_agrees_classic`), where the two
> differ off the noise-free fixpoint. 

### `CflibsFormal.Alt.csigma_agrees_of_sound`

Module `CflibsFormal.Alt.CSigma` · scope `PURE-MATH`

```lean
CflibsFormal.Alt.csigma_agrees_of_sound.{u_1, u_2} {ι : Type u_1} [Fintype ι] {κ : Type u_2}
  [Fintype κ] [Nonempty ι] {kB T Fcal : ℝ} {N : κ → ℝ} {g E A : κ → ι → ℝ} {u : κ → ι}
  (hg : ∀ (s : κ) (k : ι), 0 < g s k) (hN : ∀ (s : κ), 0 < N s) (hFcal : 0 < Fcal)
  (hA : ∀ (s : κ), 0 < A s (u s)) {classicEst : κ → ℝ}
  (hclassic : ∀ (s : κ), classicEst s = CflibsFormal.composition N s) (s : κ) :
  CflibsFormal.Alt.csigmaComposition kB T Fcal g E A u
      (fun t => CflibsFormal.lineIntensity kB T (N t) Fcal (g t) (E t) (A t) (u t)) s =
    classicEst s
```

> **Agreement via shared soundness (abstract classic estimator).** Given any
> estimator `classicEst` that is sound (`hclassic : ∀ s, classicEst s = composition N s`),
> the C-sigma estimator — run on the genuine forward-model spectrum — agrees with it. This
> routes agreement through both sides equalling the true composition `composition N`; the
> *literal* identity against `CflibsFormal.Classic.classicComposition` on the same observed
> spectrum is `csigma_agrees_classic` below. 

### `CflibsFormal.Alt.csigma_cross_stage_collapse`

Module `CflibsFormal.Alt.CSigma` · scope `EXACT`

```lean
CflibsFormal.Alt.csigma_cross_stage_collapse.{u_1, u_2} {ι : Type u_1} [Fintype ι] {κ : Type u_2}
  [Fintype κ] [Nonempty ι] [Nonempty κ] {kB T me h chi ne NI NII Fcal : ℝ} {gI EI AI : ι → ℝ}
  {gII EII AII : κ → ℝ} (hkB : 0 < kB) (hT : 0 < T) (hme : 0 < me) (hh : 0 < h) (hne : 0 < ne)
  (hgI : ∀ (j : ι), 0 < gI j) (hNI : 0 < NI) (hFcal : 0 < Fcal) (hAI : ∀ (j : ι), 0 < AI j)
  (hgII : ∀ (j : κ), 0 < gII j) (hNII : 0 < NII) (hAII : ∀ (j : κ), 0 < AII j)
  (hsaha : NII * ne = NI * CflibsFormal.sahaFactor kB T me h chi gI EI gII EII) (i : ι) (k : κ)
  (hshift : EI i = EII k + chi) :
  CflibsFormal.Alt.csigmaOrdinate kB T NI Fcal gI EI AI i =
    CflibsFormal.Alt.csigmaSahaOrdinate kB T me h ne NI NII Fcal gI EI gII EII AII k
```

> **Neutral and ionic lines share one line.** A neutral line `i` and an ionic line `k` with the
> same ionization-shifted abscissa (`E_I i = E_II k + χ`) produce the SAME Cσ ordinate: the neutral
> master ordinate (`csigma_master_line`) and the ionic Saha-corrected ordinate
> (`csigma_saha_master_line`) coincide. The cross-stage analogue of
> `csigma_master_line_indep_species` — "all points, both stages, collapse onto one line." 

### `CflibsFormal.Alt.csigma_saha_master_line`

Module `CflibsFormal.Alt.CSigma` · scope `EXACT`

```lean
CflibsFormal.Alt.csigma_saha_master_line.{u_1, u_2} {ι : Type u_1} [Fintype ι] {κ : Type u_2}
  [Fintype κ] [Nonempty ι] [Nonempty κ] {kB T me h chi ne NI NII Fcal : ℝ} {gI EI : ι → ℝ}
  {gII EII AII : κ → ℝ} (hkB : 0 < kB) (hT : 0 < T) (hme : 0 < me) (hh : 0 < h) (hne : 0 < ne)
  (hgI : ∀ (j : ι), 0 < gI j) (hNI : 0 < NI) (hFcal : 0 < Fcal) (hgII : ∀ (j : κ), 0 < gII j)
  (hNII : 0 < NII) (hAII : ∀ (j : κ), 0 < AII j)
  (hsaha : NII * ne = NI * CflibsFormal.sahaFactor kB T me h chi gI EI gII EII) (k : κ) :
  CflibsFormal.Alt.csigmaSahaOrdinate kB T me h ne NI NII Fcal gI EI gII EII AII k =
    -(EII k + chi) / (kB * T)
```

> **Cσ cross-stage master line (the Saha-coupled collapse).** An ionic (stage `Z+1`) line whose
> density satisfies Saha ionization equilibrium with the neutral stage
> (`hsaha : N_II·n_e = N_I · S(T)`, i.e. `n_{z+1} n_e / n_z = sahaFactor`, the `Saha.saha_relation`)
> has Saha-corrected ordinate exactly `−(E_k + χ)/(k_B T)` — the neutral master line
> `Y = −E*/(k_B T)` evaluated at the **ionization-shifted** abscissa `E* = E_k + χ`. So neutral and
> ionic lines of an element fall on ONE straight line of slope `−1/(k_B T)` and common intercept
> `q_I = ln(F·N_I/U_I)`. Reduces the ionic Boltzmann plot (`boltzmann_plot_intensity`) through the
> Saha log-identity (`log_sahaFactor`); the partition functions, `n_e`, the `log 2` and the
> `(3/2)·log` bracket all cancel, leaving only the ionization shift `χ`. 

### `CflibsFormal.Alt.csigma_saha_universal_line`

Module `CflibsFormal.Alt.CSigma` · scope `EXACT`

```lean
CflibsFormal.Alt.csigma_saha_universal_line.{u_1, u_2} {ι : Type u_1} [Fintype ι] {κ : Type u_2}
  [Fintype κ] [Nonempty ι] [Nonempty κ] {kB T me h chi ne NI NII Fcal : ℝ} {gI EI : ι → ℝ}
  {gII EII AII : κ → ℝ} (hkB : 0 < kB) (hT : 0 < T) (hme : 0 < me) (hh : 0 < h) (hne : 0 < ne)
  (hgI : ∀ (j : ι), 0 < gI j) (hNI : 0 < NI) (hFcal : 0 < Fcal) (hgII : ∀ (j : κ), 0 < gII j)
  (hNII : 0 < NII) (hAII : ∀ (j : κ), 0 < AII j)
  (hsaha : NII * ne = NI * CflibsFormal.sahaFactor kB T me h chi gI EI gII EII) (k : κ) :
  CflibsFormal.Alt.csigmaSahaUniversalOrdinate kB T me h ne NI NII Fcal gI EI gII EII AII k =
    Real.log Fcal - (EII k + chi) / (kB * T)
```

> **The universal line spans both stages.** An ionic (stage `Z+1`) line in Saha equilibrium with
> the neutral stage has universal ordinate `ln F − (E_k + χ)/(k_B T)` — the SAME universal line
> (slope `−1/(k_B T)`, intercept `ln F`) as the neutral lines, at the ionization-shifted abscissa. So
> ALL lines of ALL elements and BOTH stages collapse onto one line. (`csigmaSahaUniversalOrdinate`
> differs from `csigmaSahaOrdinate` by exactly `ln F`, the offset minus the concentration norm.) 

### `CflibsFormal.Alt.csigma_sound`

Module `CflibsFormal.Alt.CSigma` · scope `EXACT`

```lean
CflibsFormal.Alt.csigma_sound.{u_1, u_2} {ι : Type u_1} [Fintype ι] {κ : Type u_2} [Fintype κ]
  [Nonempty ι] {kB T Fcal : ℝ} {N : κ → ℝ} {g E A : κ → ι → ℝ} {u : κ → ι}
  (hg : ∀ (s : κ) (k : ι), 0 < g s k) (hN : ∀ (s : κ), 0 < N s) (hFcal : 0 < Fcal)
  (hA : ∀ (s : κ), 0 < A s (u s)) (s : κ) :
  CflibsFormal.Alt.csigmaComposition kB T Fcal g E A u
      (fun t => CflibsFormal.lineIntensity kB T (N t) Fcal (g t) (E t) (A t) (u t)) s =
    CflibsFormal.composition N s
```

> **Soundness of the C-sigma estimator.** On the genuine forward-model spectrum
> (`I_t = lineIntensity …` at the true densities `N_t`), `csigmaComposition` returns the TRUE
> composition `C_s = N_s / ∑ N`. The measurement step recovers each offset
> (`csigmaOffset_of_lineIntensity`) and `csigmaDensity` inverts it
> (`csigma_density_offset`), so the recovered density vector equals `N` pointwise. The
> estimator never sees `N` — only the intensities. 

### `CflibsFormal.Alt.csigma_temperature_cross_stage`

Module `CflibsFormal.Alt.CSigma` · scope `EXACT`

```lean
CflibsFormal.Alt.csigma_temperature_cross_stage.{u_1, u_2} {ι : Type u_1} [Fintype ι] {κ : Type u_2}
  [Fintype κ] [Nonempty ι] [Nonempty κ] {kB T me h chi ne NI NII Fcal : ℝ} {gI EI AI : ι → ℝ}
  {gII EII AII : κ → ℝ} (hkB : 0 < kB) (hT : 0 < T) (hme : 0 < me) (hh : 0 < h) (hne : 0 < ne)
  (hgI : ∀ (j : ι), 0 < gI j) (hNI : 0 < NI) (hFcal : 0 < Fcal) (hAI : ∀ (j : ι), 0 < AI j)
  (hgII : ∀ (j : κ), 0 < gII j) (hNII : 0 < NII) (hAII : ∀ (j : κ), 0 < AII j)
  (hsaha : NII * ne = NI * CflibsFormal.sahaFactor kB T me h chi gI EI gII EII) (i : ι) (k : κ)
  (hx : EI i ≠ EII k + chi) :
  (CflibsFormal.Alt.csigmaOrdinate kB T NI Fcal gI EI AI i -
        CflibsFormal.Alt.csigmaSahaOrdinate kB T me h ne NI NII Fcal gI EI gII EII AII k) /
      (EI i - (EII k + chi)) =
    -1 / (kB * T)
```

> **Cross-stage two-line temperature (the Saha–Boltzmann diagnostic).** A *neutral* line `i` and
> an *ionic* line `k` together yield the temperature: the slope of the Cσ master line through the
> neutral point `(E_I i, ·)` and the ionization-shifted ionic point `(E_II k + χ, ·)` is exactly
> `−1/(k_B T)`. This is the practical value of the Saha-coupled collapse — a single-species Boltzmann
> plot **cannot** combine an atomic and an ionic line, but the Saha–Boltzmann / Cσ graph can. Reduces
> to
> `csigma_master_line` (neutral) and `csigma_saha_master_line` (ionic). 

### `CflibsFormal.Alt.leastSquares_agrees_classic`

Module `CflibsFormal.Alt.LeastSquares` · scope `REDUCED`

```lean
CflibsFormal.Alt.leastSquares_agrees_classic.{u_1, u_2} {ι : Type u_1} [Fintype ι] {κ : Type u_2}
  [Fintype κ] [Nonempty ι] {kB T Fcal : ℝ} {N : κ → ℝ} {g E A : κ → ι → ℝ} {u : κ → ι}
  (hg : ∀ (s : κ) (k : ι), 0 < g s k) (hN : ∀ (s : κ), 0 < N s) (hFcal : 0 < Fcal)
  (hA : ∀ (s : κ) (k : ι), 0 < A s k) (hNtot : 0 < CflibsFormal.totalDensity N)
  (hvar : ∀ (s : κ), 0 < ∑ k, (E s k - CflibsFormal.mean (E s)) ^ 2) (s : κ) :
  CflibsFormal.Alt.leastSquaresComposition kB T Fcal g E A
      (fun t k => CflibsFormal.lineIntensity kB T (N t) Fcal (g t) (E t) (A t) k) s =
    CflibsFormal.Classic.classicComposition kB T Fcal g E A u
      (fun t => CflibsFormal.lineIntensity kB T (N t) Fcal (g t) (E t) (A t) (u t)) s
```

> **Same-spectrum agreement on the noise-free forward fixpoint.** Fed the SAME underlying
> forward spectrum (the classic input `fun t => lineIntensity … (u t)` is literally the
> `u t`-slice of the OLS input `fun t k => lineIntensity … k`), the OLS estimator and the
> classic two-line estimator return the SAME composition. Neither side ingests `N` or
> `composition N`, and the two procedures are genuinely different (OLS = regression intercept
> over `n` lines via `olsDensity`; classic = single-line inversion via `classicDensity`).
> 
> Honest content: this is a COROLLARY OF JOINT SOUNDNESS — the proof rewrites both sides to
> `composition N` (`leastSquares_sound` and `Classic.classic_sound`), so it holds precisely
> because both are exact ON the noise-free forward fixpoint. It is NOT an observation-level
> identity and is NOT claimed off the fixpoint: on noisy/perturbed intensities the two
> estimators genuinely DISAGREE — OLS averages all lines while classic uses one — and that
> robustness-to-noise is the entire reason to prefer the OLS variant. (`hNtot` is forwarded to
> `classic_sound`, whose total-density hypothesis is unused.) 

### `CflibsFormal.Alt.leastSquares_sound`

Module `CflibsFormal.Alt.LeastSquares` · scope `REDUCED`

```lean
CflibsFormal.Alt.leastSquares_sound.{u_1, u_2} {ι : Type u_1} [Fintype ι] {κ : Type u_2} [Fintype κ]
  [Nonempty ι] {kB T Fcal : ℝ} {N : κ → ℝ} {g E A : κ → ι → ℝ} (hg : ∀ (s : κ) (k : ι), 0 < g s k)
  (hN : ∀ (s : κ), 0 < N s) (hFcal : 0 < Fcal) (hA : ∀ (s : κ) (k : ι), 0 < A s k)
  (hvar : ∀ (s : κ), 0 < ∑ k, (E s k - CflibsFormal.mean (E s)) ^ 2) (s : κ) :
  CflibsFormal.Alt.leastSquaresComposition kB T Fcal g E A
      (fun t k => CflibsFormal.lineIntensity kB T (N t) Fcal (g t) (E t) (A t) k) s =
    CflibsFormal.composition N s
```

> **MAIN soundness.** Run on the genuine multi-line forward-model spectrum (full
> per-species line vector, no `N` input), the OLS estimator returns the TRUE composition
> `C_s = N_s / ∑ N`. Assembles `olsDensity_recovers` pointwise then `Closure.composition`;
> soundness is the assembly. Realizes the multi-line least-squares CF-LIBS intercept method of
> Tognoni et al. (2010). 

### `CflibsFormal.Alt.olsDensity_recovers`

Module `CflibsFormal.Alt.LeastSquares` · scope `REDUCED`

```lean
CflibsFormal.Alt.olsDensity_recovers.{u_1} {ι : Type u_1} [Fintype ι] [Nonempty ι] {kB T N Fcal : ℝ}
  {g E A : ι → ℝ} (hg : ∀ (k : ι), 0 < g k) (hN : 0 < N) (hFcal : 0 < Fcal)
  (hA : ∀ (k : ι), 0 < A k) (hvar : 0 < ∑ k, (E k - CflibsFormal.mean E) ^ 2) :
  (CflibsFormal.Alt.olsDensity kB T Fcal g E A fun k =>
      CflibsFormal.lineIntensity kB T N Fcal g E A k) =
    N
```

> **Per-species soundness core.** Feeding the FULL forward-model spectrum of a species
> through the OLS density reader recovers the true density `N`. The OLS intercept recovers
> `q_s` (`olsIntercept_of_forward`) and `exp(q_s)·U/Fcal` inverts it. Engine of soundness; the
> estimator sees only intensities, never `N`. 

### `CflibsFormal.Alt.olsIntercept_of_forward`

Module `CflibsFormal.Alt.LeastSquares` · scope `REDUCED`

```lean
CflibsFormal.Alt.olsIntercept_of_forward.{u_1} {ι : Type u_1} [Fintype ι] [Nonempty ι]
  {kB T N Fcal : ℝ} {g E A : ι → ℝ} (hg : ∀ (k : ι), 0 < g k) (hN : 0 < N) (hFcal : 0 < Fcal)
  (hA : ∀ (k : ι), 0 < A k) (hvar : 0 < ∑ k, (E k - CflibsFormal.mean E) ^ 2) :
  (CflibsFormal.olsIntercept E fun k => CflibsFormal.Alt.olsBoltzmannOrdinate kB T N Fcal g E A k) =
    Real.log (Fcal * N / CflibsFormal.partitionFunction kB T g E)
```

> **Links OLS recovery to the physics.** The OLS intercept of the FORWARD-MODEL
> Boltzmann-plot ordinates equals the composition-bearing offset `q_s = log (Fcal·N/U)` —
> exactly the Ciucci et al. (1999) claim that the Boltzmann-plot intercept gives the
> concentration, now via a least-squares fit over all lines. Reduces to `ols_recovers_line`
> with `m0 = −1/(k_B T)`, `b0 = log (Fcal·N/U)` supplied by
> `ForwardMap.boltzmann_plot_intensity` (reused, not reproven). 

### `CflibsFormal.Alt.closureEstimate_bias`

Module `CflibsFormal.Alt.NeutralityScale` · scope `?`

```lean
CflibsFormal.Alt.closureEstimate_bias.{u_1, u_2} {κ : Type u_1} {ι : Type u_2} [Fintype κ]
  [Fintype ι] {kB T Fcal Nu : ℝ} {g E A : ι → ℝ} {N : κ → ℝ} {emit : κ → ι} (hFcal : 0 < Fcal)
  (hNu : 0 ≤ Nu) (hsum : 0 < ∑ t, N t)
  (hunit : ∀ (s : κ), 0 < CflibsFormal.lineIntensity kB T 1 1 g E A (emit s)) (s : κ) :
  CflibsFormal.Alt.closureEstimate
      (fun s => CflibsFormal.lineIntensity kB T (N s) Fcal g E A (emit s))
      (fun s => CflibsFormal.lineIntensity kB T 1 1 g E A (emit s)) s =
    N s / (∑ t, N t + Nu) / (1 - Nu / (∑ t, N t + Nu))
```

> **Closure bias from an undetected species.** With an undetected species of neutral density
> `Nu ≥ 0` outside the observed set, the closure estimate of an observed species equals its true
> composition over all species, `N s / (∑ t, N t + Nu)`, divided by `1 - Cu` where
> `Cu = Nu / (∑ t, N t + Nu)` is the undetected species' true fraction: closure silently
> redistributes the missing fraction over the observed species (Tognoni et al. 2010). Load-bearing
> guards: `Fcal ≠ 0`, `unitI s ≠ 0` and `∑ N + Nu ≠ 0` (the last is what `hNu` and `hsum` jointly
> supply; neither alone can be dropped — `Nu = −∑ N` breaks the identity); `∑ N ≠ 0` additionally
> keeps the left side away from `0/0`. `N` is the *neutral* density, so this is elemental composition
> only where ionization is negligible or uniform across species. See the module docstring for the
> identity's `Nu`-invariance and its relation to `MatrixEffects.recoveredComposition_eq_inflation`. 

### `CflibsFormal.Alt.lineIntensity_linear`

Module `CflibsFormal.Alt.NeutralityScale` · scope `?`

```lean
CflibsFormal.Alt.lineIntensity_linear.{u_2} {ι : Type u_2} [Fintype ι] (kB T N Fcal : ℝ)
  (g E A : ι → ℝ) (k : ι) :
  CflibsFormal.lineIntensity kB T N Fcal g E A k =
    Fcal * N * CflibsFormal.lineIntensity kB T 1 1 g E A k
```

> **Linearity of the line intensity in density and calibration.** `lineIntensity` at density `N`
> and calibration `Fcal` is `Fcal * N` times its value at the unit point `(N = 1, Fcal = 1)` — a pure
> algebraic identity (the shared `partitionFunction` denominator cancels), holding unconditionally. 

### `CflibsFormal.Alt.lineIntensity_ratio`

Module `CflibsFormal.Alt.NeutralityScale` · scope `?`

```lean
CflibsFormal.Alt.lineIntensity_ratio.{u_1, u_2} {κ : Type u_1} {ι : Type u_2} [Fintype ι]
  (kB T Fcal : ℝ) (g E A : ι → ℝ) (N : κ → ℝ) (emit : κ → ι) (t : κ)
  (hunit : 0 < CflibsFormal.lineIntensity kB T 1 1 g E A (emit t)) :
  CflibsFormal.lineIntensity kB T (N t) Fcal g E A (emit t) /
      CflibsFormal.lineIntensity kB T 1 1 g E A (emit t) =
    Fcal * N t
```

> The ratio form of `lineIntensity_linear`, guarded by positivity of the unit-point intensity. 

### `CflibsFormal.Alt.neutralityScale_eq_Fcal`

Module `CflibsFormal.Alt.NeutralityScale` · scope `?`

```lean
CflibsFormal.Alt.neutralityScale_eq_Fcal.{u_1, u_2} {κ : Type u_1} {ι : Type u_2} [Fintype κ]
  [Fintype ι] {kB T Fcal ne : ℝ} {g E A : ι → ℝ} {N R : κ → ℝ} {emit : κ → ι} (hne : 0 < ne)
  (hunit : ∀ (s : κ), 0 < CflibsFormal.lineIntensity kB T 1 1 g E A (emit s))
  (hneut : CflibsFormal.chargeNeutrality (fun x => 1) (fun s => N s * R s) ne) :
  CflibsFormal.Alt.neutralityScale
      (fun s => CflibsFormal.lineIntensity kB T (N s) Fcal g E A (emit s))
      (fun s => CflibsFormal.lineIntensity kB T 1 1 g E A (emit s)) R ne =
    Fcal
```

> **Exact recovery.** If every species' neutral line is observed, the stage ratios are the true
> ones, and charge neutrality `ne = ∑ s, N s * R s` holds (`chargeNeutrality` with unit charge and
> ion densities `N s * R s`), then the neutrality scale estimator returns `Fcal` exactly — no closure
> hypothesis `∑ C = 1` is used. `ne ≠ 0` and `unitI s ≠ 0` are load-bearing (division); their signs
> are physical decoration. The stage ratios `R` are unconstrained: they enter only through the
> neutrality hypothesis. 

### `CflibsFormal.Alt.neutralityScale_undetected`

Module `CflibsFormal.Alt.NeutralityScale` · scope `?`

```lean
CflibsFormal.Alt.neutralityScale_undetected.{u_1, u_2} {κ : Type u_1} {ι : Type u_2} [Fintype κ]
  [Fintype ι] {kB T Fcal ne Nu Ru : ℝ} {g E A : ι → ℝ} {N R : κ → ℝ} {emit : κ → ι} (hne : 0 < ne)
  (hunit : ∀ (s : κ), 0 < CflibsFormal.lineIntensity kB T 1 1 g E A (emit s))
  (hneut : ne = ∑ s, N s * R s + Nu * Ru) :
  CflibsFormal.Alt.neutralityScale
      (fun s => CflibsFormal.lineIntensity kB T (N s) Fcal g E A (emit s))
      (fun s => CflibsFormal.lineIntensity kB T 1 1 g E A (emit s)) R ne =
    Fcal * (1 - Nu * Ru / ne)
```

> **Undetected species.** If one species (neutral density `Nu`, stage ratio `Ru`) is absent from
> the observed set `κ`, but charge neutrality holds over *all* species,
> `ne = (∑ s, N s * R s) + Nu * Ru`, then the neutrality scale computed over the observed species
> returns `Fcal` scaled by one minus the undetected species' **charge share** `Nu * Ru / ne`. The
> estimator is therefore blind to an undetected species exactly to the extent that it is neutral
> (`Ru → 0`), which is the case for the high-ionization-energy elements (H, O, N, C) that CF-LIBS
> typically fails to observe: the charge share, not the mass share, controls the bias. The reading as
> a fraction in `[0, 1]` presupposes `0 ≤ Nu * Ru ≤ ne`, which is not assumed; the identity itself
> holds for any sign. `Nu * Ru` may also stand for the net ion density of several undetected
> species. 

### `CflibsFormal.Alt.olsDensity_aliasing_A`

Module `CflibsFormal.Alt.OLSAtomicDataPerturbation` · scope `EXACT`

```lean
CflibsFormal.Alt.olsDensity_aliasing_A.{u_1} {ι : Type u_1} [Fintype ι] [Nonempty ι]
  {kB T N Fcal : ℝ} {g E A A' : ι → ℝ} (hg : ∀ (k : ι), 0 < g k) (hN : 0 < N) (hFcal : 0 < Fcal)
  (hA : ∀ (k : ι), 0 < A k) (hA' : ∀ (k : ι), 0 < A' k)
  (hvar : 0 < ∑ k, (E k - CflibsFormal.mean E) ^ 2) :
  (CflibsFormal.Alt.olsDensity kB T Fcal g E A' fun k =>
      CflibsFormal.lineIntensity kB T N Fcal g E A k) =
    N * Real.exp (CflibsFormal.olsIntercept E fun k => Real.log (A k / A' k))
```

> **EXACT aliasing identity, OLS density reader, A-channel.** The spectrum is emitted with
> the TRUE transition probabilities `A` (correct `g`, `E`) at density `N`; the analyst inverts
> ALL lines with the WRONG `A'` via the multi-line OLS Boltzmann-plot fit. The recovered
> density is exactly the true density scaled by the exponential of the OLS INTERCEPT of the
> per-line log-ratios `log(A_k/A'_k)`:
>   `N̂ = N · exp(olsIntercept E (fun k => log(A_k/A'_k)))`.
> This is the OLS mirror of `classicDensity_aliasing`: the single-line reader carries the raw
> ratio of response factors, the multi-line OLS reader carries its intercept — the log-domain
> (geometric-mean, in the centered convention) AVERAGE of the per-line data ratios. Proof: the
> observed ordinate splits as `ŷ_k = y_k^true + log(A_k/A'_k)` (via `Real.log_mul` on
> `I_k/(g_k A'_k) = (I_k/(g_k A_k))·(A_k/A'_k)`, all factors positive), `olsIntercept` is linear
> in the ordinate (`olsIntercept_add`), the true-ordinate intercept is `log(Fcal·N/U)`
> (`olsIntercept_of_forward`), and `Real.exp_add` + `Real.exp_log` repackage the sum of
> intercepts into `N · exp(...)`. `U` is untouched (`partitionFunction` does not depend on `A`),
> so no `g`/`U`-channel factor appears — this is the clean single-channel EXACT identity. 

### `CflibsFormal.Alt.olsDensity_aliasing_A_error`

Module `CflibsFormal.Alt.OLSAtomicDataPerturbation` · scope `REDUCED`

```lean
CflibsFormal.Alt.olsDensity_aliasing_A_error.{u_1} {ι : Type u_1} [Fintype ι] [Nonempty ι]
  {kB T N Fcal : ℝ} {g E A A' δ : ι → ℝ} (hg : ∀ (k : ι), 0 < g k) (hN : 0 < N) (hFcal : 0 < Fcal)
  (hA : ∀ (k : ι), 0 < A k) (hA' : ∀ (k : ι), 0 < A' k)
  (hvar : 0 < ∑ k, (E k - CflibsFormal.mean E) ^ 2) (hcent : CflibsFormal.mean E = 0)
  (hδ1 : ∀ (k : ι), δ k < 1) (hpert : ∀ (k : ι), |A' k - A k| ≤ δ k * A k) :
  |(CflibsFormal.Alt.olsDensity kB T Fcal g E A' fun k =>
          CflibsFormal.lineIntensity kB T N Fcal g E A k) -
        N| ≤
    N * (Real.exp ((∑ k, δ k / (1 - δ k)) / ↑(Fintype.card ι)) - 1)
```

> **REDUCED closed-form density-error bound, OLS reader, A-channel.** In the centered
> Boltzmann-plot convention (`mean E = 0`) with a per-line RELATIVE transition-probability
> error `|A'_k − A_k| ≤ δ_k·A_k` (`δ_k < 1`), the recovered density obeys
>   `|N̂ − N| ≤ N·(exp(η) − 1)`,   `η = (∑_k δ_k/(1−δ_k)) / card ι`.
> Derivation: `olsDensity_aliasing_A` gives the EXACT `N̂ − N = N·(exp(olsIntercept E δlog) − 1)`
> with `δlog_k = log(A_k/A'_k)`; `abs_log_ratio_le` bounds each `|δlog_k| ≤ δ_k/(1−δ_k)`;
> `olsIntercept_stable_hetero` (centered convention) bounds the intercept of `δlog` against the
> zero ordinate by the AVERAGE `η` of those per-line bounds; `abs_exp_sub_one_le` closes the
> exponential step. REDUCED because the per-line `δ_k` are lumped into the single average `η`
> (rather than kept fully per-line downstream) and the centered convention (`mean E = 0`) is
> assumed. **Honest scope — bias, not variance**: `η` is the worst-case average of a SYSTEMATIC
> per-line error, not a statistical standard error; a uniformly-signed `δ_k` does not shrink as
> `card ι` grows (`exp η − 1` does not vanish as `n → ∞` unless the signed average `η → 0`). 

### `CflibsFormal.Alt.olsDensity_aliasing_E_error`

Module `CflibsFormal.Alt.OLSAtomicDataPerturbation` · scope `REDUCED`

```lean
CflibsFormal.Alt.olsDensity_aliasing_E_error.{u_1} {ι : Type u_1} [Fintype ι] [Nonempty ι]
  {kB T N Fcal : ℝ} {g E E' A : ι → ℝ} (hg : ∀ (k : ι), 0 < g k) (hN : 0 < N) (hFcal : 0 < Fcal)
  (hA : ∀ (k : ι), 0 < A k) (hkT : 0 < kB * T) (hcent' : CflibsFormal.mean E' = 0) :
  |(CflibsFormal.olsIntercept E' fun k =>
          Real.log (CflibsFormal.lineIntensity kB T N Fcal g E A k / (g k * A k))) -
        Real.log (Fcal * N / CflibsFormal.partitionFunction kB T g E)| ≤
    1 / (kB * T) * ((∑ k, |E k - E' k|) / ↑(Fintype.card ι))
```

> **(M6c) REDUCED intercept-channel log-density error under a wrong abscissa.** The analyst
> reads the density off the OLS intercept; the intercept is `log(Fcal·N/U)`, so its error is the
> LOG-density bias. In the standard analyst-centered Boltzmann-plot convention `mean E' = 0`
> (energies referenced to the analyst's own — wrong — mean), the intercept collapses to the mean
> ordinate and is therefore INSENSITIVE to the slope/tilt distortion `regCoef` (M6b); the residual
> intercept bias is exactly `−m·Ē = −m·mean(E − E')` and is cleanly bounded:
>   `|olsIntercept E' ŷ − log(Fcal·N/U(E))| ≤ (1/(k_B T))·(∑ₖ |Eₖ − E'ₖ|)/card ι`
> with `ŷₖ = log(Iₖ/(gₖ Aₖ))` the true intensity ordinate and `m = 1/(k_B T) > 0`. REDUCED, and
> honestly partial in two ways: (i) it bounds ONLY the intercept/abscissa-projection channel — the
> recovered *density* additionally carries the partition-function factor `U(T;g,E')/U(T;g,E)` (the
> `E`-channel perturbs `U` too), a SEPARATE bias not included here; (ii) the centering `mean E' = 0`
> is load-bearing — the *uncentered* intercept bias is conditioning-dependent (it scales with
> `regCoef`, which blows up as `E'` degenerates), so no bound in `maxₖ|E'ₖ − Eₖ|` alone exists off
> the centered convention (the projection artifact, dossier §5). **Bias, not variance:** a fixed
> wrong abscissa, worst case; no line-count / averaging claim. 

### `CflibsFormal.classicDensity_aliasing`

Module `CflibsFormal.AtomicDataPerturbation` · scope `EXACT`

```lean
CflibsFormal.classicDensity_aliasing.{u_1} {ι : Type u_1} [Fintype ι] [Nonempty ι] {kB T N Fcal : ℝ}
  {g E A g' E' A' : ι → ℝ} (hg : ∀ (k : ι), 0 < g k) (hg' : ∀ (k : ι), 0 < g' k) (hFcal : 0 < Fcal)
  (u : ι) (hA' : 0 < A' u) :
  CflibsFormal.Classic.classicDensity kB T Fcal g' E' A' u
      (CflibsFormal.lineIntensity kB T N Fcal g E A u) =
    N * CflibsFormal.responseFactor kB T g E A u / CflibsFormal.responseFactor kB T g' E' A' u
```

> **EXACT aliasing identity.** The spectrum is emitted with the TRUE atomic data `(g, E, A)`
> at density `N` and shared calibration `Fcal`; the analyst inverts the same line with the WRONG
> data `(g', E', A')`. The recovered density is exactly the true density scaled by the ratio of
> response factors:
>   `N̂ = N · responseFactor(g,E,A) / responseFactor(g',E',A')`
>     `= N · (g_u·A_u·bf(E_u)/U) / (g'_u·A'_u·bf(E'_u)/U')`.
> Pure cancellation on `classicDensity ∘ lineIntensity`: the calibration `Fcal` and every
> partition-function / Boltzmann factor cancel, leaving the multiplicative atomic-data bias. This
> is the algebraic substrate of the CF-LIBS atomic-data accuracy floor (Tognoni et al. 2010): with
> correct data (`g'=g, E'=E, A'=A`) the ratio is `1` and `N̂ = N` (`Classic.classicDensity_recovers`);
> any mismatch biases `N̂` multiplicatively, with no self-diagnosing signature. 

### `CflibsFormal.classicDensity_aliasing_error`

Module `CflibsFormal.AtomicDataPerturbation` · scope `REDUCED`

```lean
CflibsFormal.classicDensity_aliasing_error.{u_1} {ι : Type u_1} [Fintype ι] [Nonempty ι]
  {kB T N Fcal δ : ℝ} {g E A g' E' A' : ι → ℝ} (hg : ∀ (k : ι), 0 < g k) (hg' : ∀ (k : ι), 0 < g' k)
  (hFcal : 0 < Fcal) (u : ι) (hA : 0 < A u) (hA' : 0 < A' u) (hN : 0 < N) (hδ0 : 0 ≤ δ)
  (hδ1 : δ < 1)
  (hpert :
    |CflibsFormal.responseFactor kB T g' E' A' u - CflibsFormal.responseFactor kB T g E A u| ≤
      δ * CflibsFormal.responseFactor kB T g E A u) :
  |CflibsFormal.Classic.classicDensity kB T Fcal g' E' A' u
          (CflibsFormal.lineIntensity kB T N Fcal g E A u) -
        N| ≤
    N * (δ / (1 - δ))
```

> **REDUCED lumped relative-error bound.** Lumping all atomic-data error into a single relative
> response error `|ρ' − ρ| ≤ δ·ρ` (`0 ≤ δ < 1`), the recovered density obeys
> `|N̂ − N| ≤ N · δ/(1 − δ)`. Immediate from the `EXACT` aliasing identity plus the elementary
> scaled-ratio bound. This single channel absorbs an `E`-channel automatically, because the
> response factor `ρ` carries the Boltzmann factor `exp(−E_u/(k_B T))` — an `E' ≠ E` perturbation
> simply enters `|ρ' − ρ|`. Reduction: the per-symbol errors in `g`, `A`, `E`, `U` are collapsed
> into the one scalar `δ`; the algebra itself is exact (Tognoni et al. 2010, accuracy budget). 

### `CflibsFormal.classicDensity_aliasing_error_channels`

Module `CflibsFormal.AtomicDataPerturbation` · scope `REDUCED`

```lean
CflibsFormal.classicDensity_aliasing_error_channels.{u_1} {ι : Type u_1} [Fintype ι] [Nonempty ι]
  {kB T N Fcal δgA δU : ℝ} {g E A g' A' : ι → ℝ} (hg : ∀ (k : ι), 0 < g k)
  (hg' : ∀ (k : ι), 0 < g' k) (hFcal : 0 < Fcal) (u : ι) (hA : 0 < A u) (hA' : 0 < A' u)
  (hN : 0 < N) (hδgA0 : 0 ≤ δgA) (hδgA1 : δgA < 1) (hδU0 : 0 ≤ δU)
  (hpertGA : |g' u * A' u - g u * A u| ≤ δgA * (g u * A u))
  (hpertU :
    |CflibsFormal.partitionFunction kB T g' E - CflibsFormal.partitionFunction kB T g E| ≤
      δU * CflibsFormal.partitionFunction kB T g E) :
  |CflibsFormal.Classic.classicDensity kB T Fcal g' E A' u
          (CflibsFormal.lineIntensity kB T N Fcal g E A u) -
        N| ≤
    N * ((δgA + δU) / (1 - δgA))
```

> **REDUCED two-channel relative-error bound (`E' = E`).** With the same level energies but
> perturbed `gA` and partition function, split the atomic-data error into a line-strength channel
> `|g'_u·A'_u − g_u·A_u| ≤ δ_gA·(g_u·A_u)` (`0 ≤ δ_gA < 1`) and a partition-function channel
> `|U' − U| ≤ δ_U·U` (`0 ≤ δ_U`). Then
>   `|N̂ − N| ≤ N · (δ_gA + δ_U)/(1 − δ_gA)`.
> Derivation: with `E' = E` the aliasing identity collapses to `N̂ = N · (U'/U)/(g'A'/gA)`, and the
> two relative bounds give `|U'/U − 1| ≤ δ_U`, `|g'A'/gA − 1| ≤ δ_gA`; the two-factor ratio bound
> finishes. Reduction: `E' = E` (the energy channel is carried separately by
> `classicDensity_aliasing_error`) and the per-symbol `g`,`A`,`U` errors are lumped into
> `δ_gA`, `δ_U`; the algebra is exact (Tognoni et al. 2010). 

### `CflibsFormal.classicDensity_aliasing_error_energy`

Module `CflibsFormal.AtomicDataPerturbation` · scope `REDUCED`

```lean
CflibsFormal.classicDensity_aliasing_error_energy.{u_1} {ι : Type u_1} [Fintype ι] [Nonempty ι]
  {kB Tmin T N Fcal : ℝ} {g E A g' E' A' : ι → ℝ} (hkB : 0 < kB) (hTmin : 0 < Tmin) (hT : Tmin ≤ T)
  (hg : ∀ (k : ι), 0 < g k) (hg' : ∀ (k : ι), 0 < g' k) (hFcal : 0 < Fcal) (u : ι) (hA : 0 < A u)
  (hA' : 0 < A' u) (hN : 0 < N) (hgA : g' u * A' u = g u * A u)
  (hUeq : CflibsFormal.partitionFunction kB T g' E' = CflibsFormal.partitionFunction kB T g E) :
  |CflibsFormal.Classic.classicDensity kB T Fcal g' E' A' u
          (CflibsFormal.lineIntensity kB T N Fcal g E A u) -
        N| ≤
    N * (Real.exp (|E' u - E u| / (kB * Tmin)) - 1)
```

> **REDUCED energy-channel isolation (gap #2 residual).** In the wrong-DATA aliasing at the SAME
> temperature `T`, isolate the pure energy channel: with matched line strength `g'_u·A'_u = g_u·A_u`
> and matched partition function `U(T; g', E') = U(T; g, E)` but a shifted upper-level energy
> `E'_u ≠ E_u`, the aliasing identity collapses to `N̂ = N · bf(E_u; T)/bf(E'_u; T)
> = N · exp((E'_u − E_u)/(k_B T))`, and on a floor `Tmin ≤ T`:
>   `|N̂ − N| ≤ N · (exp(|E'_u − E_u|/(k_B·Tmin)) − 1)`.
> Derivation: `|exp w − 1| ≤ exp|w| − 1` (the two-point `|exp − 1|` bound) with
> `|w| = |E'_u − E_u|/(k_B T) ≤ |E'_u − E_u|/(k_B·Tmin)` (from `Tmin ≤ T`). Reduction: `Tmin` floors
> the temperature; the matched-`gA`/matched-`U` hypotheses isolate the single line's Boltzmann factor
> (Tognoni et al. 2010, the energy-parameter channel). Explicit constant, not sharp. 

### `CflibsFormal.classicDensity_temperature_aliasing`

Module `CflibsFormal.AtomicDataPerturbation` · scope `EXACT`

```lean
CflibsFormal.classicDensity_temperature_aliasing.{u_1} {ι : Type u_1} [Fintype ι] [Nonempty ι]
  {kB T That N Fcal : ℝ} {g E A : ι → ℝ} (hg : ∀ (k : ι), 0 < g k) (hFcal : 0 < Fcal) (u : ι)
  (hA : 0 < A u) :
  CflibsFormal.Classic.classicDensity kB That Fcal g E A u
      (CflibsFormal.lineIntensity kB T N Fcal g E A u) =
    N * CflibsFormal.responseFactor kB T g E A u / CflibsFormal.responseFactor kB That g E A u
```

> **EXACT temperature-aliasing identity.** The spectrum is emitted with atomic data `(g, E, A)`
> at the TRUE temperature `T` and shared calibration `Fcal`; the analyst inverts the SAME line with
> the SAME atomic data but at a WRONG temperature `T̂`. The recovered density is exactly the true
> density scaled by the ratio of response factors *at the two temperatures*:
>   `N̂ = N · responseFactor(T) / responseFactor(T̂)`
>     `= N · (bf(E_u; T)/U(T)) / (bf(E_u; T̂)/U(T̂))`.
> Pure cancellation on `classicDensity ∘ lineIntensity`: `Fcal`, `g_u`, `A_u` cancel, leaving the
> temperature bias carried by the Boltzmann factor and the partition function. With `T̂ = T` the ratio
> is `1` and `N̂ = N` (`Classic.classicDensity_recovers`); any temperature mis-estimate biases `N̂`
> multiplicatively (Tognoni et al. 2010, the `U_s(T)`/Boltzmann temperature channel of the accuracy
> budget). 

### `CflibsFormal.classicDensity_temperature_aliasing_error`

Module `CflibsFormal.AtomicDataPerturbation` · scope `REDUCED`

```lean
CflibsFormal.classicDensity_temperature_aliasing_error.{u_1} {ι : Type u_1} [Fintype ι] [Nonempty ι]
  {kB Tmin T That N Fcal : ℝ} {g E A : ι → ℝ} (hkB : 0 < kB) (hTmin : 0 < Tmin) (hT : Tmin ≤ T)
  (hThat : Tmin ≤ That) (hg : ∀ (k : ι), 0 < g k) (hE : ∀ (k : ι), 0 ≤ E k) (hFcal : 0 < Fcal)
  (u k0 : ι) (hA : 0 < A u) (hN : 0 < N)
  (hδp1 : Real.exp (E u * |That - T| / (kB * Tmin ^ 2)) - 1 < 1) :
  |CflibsFormal.Classic.classicDensity kB That Fcal g E A u
          (CflibsFormal.lineIntensity kB T N Fcal g E A u) -
        N| ≤
    N * CflibsFormal.tempResponseErrorBound kB Tmin T That g E u k0
```

> **REDUCED temperature-error bound.** On a box `Tmin ≤ T, T̂` (`0 < Tmin`), with `gₖ > 0`,
> `Eₖ ≥ 0`, and the exp-channel smallness `delta_exp < 1`, the temperature-aliased recovered density
> obeys
>   `|N̂ − N| ≤ N · tempResponseErrorBound k_B Tmin T T̂ g E u k0`.
> Proof: rewrite `N̂ = N · v/u` with `v = U(T̂)/U(T)` (`U` channel) and `u = bf(E_u; T̂)/bf(E_u; T)`
> (exp channel), then bound `|u − 1| ≤ delta_exp` via the two-point `|exp − 1|` bound and the
> inverse-temperature gap, and `|v − 1| ≤ delta_U` via
> `PartitionLipschitz.partitionFunction_two_point_bound` + the single-term `U`-floor
> `partitionFunction_floor` (level `k0`); the two-factor ratio helper `abs_two_ratio_sub_le` closes.
> Reduction: the constants are honest over-estimates (`exp ≤ 1`, `T₁T₂ ≥ Tmin²`, single-term floor),
> not sharp; the algebra is exact (Tognoni et al. 2010, temperature→density channel). 

### `CflibsFormal.boltzmannFactor_pos`

Module `CflibsFormal.Boltzmann` · scope `PURE-MATH`

```lean
CflibsFormal.boltzmannFactor_pos (kB T E : ℝ) : 0 < CflibsFormal.boltzmannFactor kB T E
```

### `CflibsFormal.boltzmann_plot`

Module `CflibsFormal.Boltzmann` · scope `EXACT`

```lean
CflibsFormal.boltzmann_plot.{u_1} {ι : Type u_1} [Fintype ι] [Nonempty ι] {kB T N : ℝ} {g E : ι → ℝ}
  (hg : ∀ (k : ι), 0 < g k) (hN : 0 < N) (k : ι) :
  Real.log (CflibsFormal.population kB T N g E k / g k) =
    Real.log (N / CflibsFormal.partitionFunction kB T g E) - E k / (kB * T)
```

> **Boltzmann-plot identity.** `log (nₖ / gₖ) = log (N / U) - Eₖ / (k_B T)`,
> i.e. affine in the level energy `E k` with slope `-1 / (k_B T)`. This is the
> mathematical content of the classical "temperature from the Boltzmann-plot slope"
> step. 

### `CflibsFormal.partitionFunction_pos`

Module `CflibsFormal.Boltzmann` · scope `PURE-MATH`

```lean
CflibsFormal.partitionFunction_pos.{u_1} {ι : Type u_1} [Fintype ι] [Nonempty ι] {kB T : ℝ}
  {g E : ι → ℝ} (hg : ∀ (k : ι), 0 < g k) : 0 < CflibsFormal.partitionFunction kB T g E
```

### `CflibsFormal.population_sum`

Module `CflibsFormal.Boltzmann` · scope `EXACT`

```lean
CflibsFormal.population_sum.{u_1} {ι : Type u_1} [Fintype ι] [Nonempty ι] {kB T N : ℝ} {g E : ι → ℝ}
  (hg : ∀ (k : ι), 0 < g k) : ∑ k, CflibsFormal.population kB T N g E k = N
```

> **Normalization.** The level populations sum to the total number density `N`. 

### `CflibsFormal.temperature_from_two_levels`

Module `CflibsFormal.Boltzmann` · scope `EXACT`

```lean
CflibsFormal.temperature_from_two_levels.{u_1} {ι : Type u_1} [Fintype ι] [Nonempty ι] {kB T N : ℝ}
  {g E : ι → ℝ} (hg : ∀ (k : ι), 0 < g k) (hN : 0 < N) (i j : ι) (hE : E i ≠ E j) :
  (Real.log (CflibsFormal.population kB T N g E j / g j) -
        Real.log (CflibsFormal.population kB T N g E i / g i)) /
      (E i - E j) =
    1 / (kB * T)
```

> **Temperature from two levels.** The Boltzmann-plot slope between any two
> distinct-energy levels recovers `1 / (k_B T)` exactly — independent of `N`, the
> partition function, and the degeneracies. 

### `CflibsFormal.aliasBudget_certificate_sound`

Module `CflibsFormal.Certificates` · scope `REDUCED`

```lean
CflibsFormal.aliasBudget_certificate_sound.{u_1} {ι : Type u_1} [Fintype ι] [Nonempty ι]
  {kB T N Fcal delta : ℝ} {g E A g' E' A' : ι → ℝ} (hg : ∀ (k : ι), 0 < g k)
  (hg' : ∀ (k : ι), 0 < g' k) (hFcal : 0 < Fcal) (u : ι) (hA : 0 < A u) (hA' : 0 < A' u)
  (hN : 0 < N)
  (hpert :
    |CflibsFormal.responseFactor kB T g' E' A' u - CflibsFormal.responseFactor kB T g E A u| ≤
      delta * CflibsFormal.responseFactor kB T g E A u)
  (hcert : CflibsFormal.aliasBudgetCert delta) :
  |CflibsFormal.Classic.classicDensity kB T Fcal g' E' A' u
          (CflibsFormal.lineIntensity kB T N Fcal g E A u) -
        N| ≤
    N * (delta / (1 - delta))
```

> **C14 soundness** (thin re-export of `classicDensity_aliasing_error`,
> `AtomicDataPerturbation.lean:213`). Given an assumed relative atomic-data error bound `δ` (R2) and
> `δ < 1`, the recovered density obeys `|N̂ − N| ≤ N·δ/(1 − δ)`. 

### `CflibsFormal.knownTau_certificate_sound`

Module `CflibsFormal.Certificates` · scope `EXACT`

```lean
CflibsFormal.knownTau_certificate_sound.{u_1} {ι : Type u_1} [Fintype ι] {kB T N Fcal : ℝ}
  {g E A : ι → ℝ} (k : ι) {tau : ℝ} (hcert : CflibsFormal.knownTauCert tau) :
  CflibsFormal.lineIntensity kB T N Fcal g E A k =
    CflibsFormal.selfAbsorbedIntensity kB T N Fcal g E A k tau /
      CflibsFormal.selfAbsorptionFactor tau
```

> **C12 soundness** (thin re-export of `lineIntensity_eq_selfAbsorbedIntensity_div`,
> `SelfAbsorption.lean:237`). A known `τ ≥ 0` certifies exact optically-thin recovery
> `I_thin = I_meas / SA(τ)`. 

### `CflibsFormal.Classic.classicDensity_recovers`

Module `CflibsFormal.Classic` · scope `EXACT`

```lean
CflibsFormal.Classic.classicDensity_recovers.{u_1} {ι : Type u_1} [Fintype ι] [Nonempty ι]
  {kB T N Fcal : ℝ} {g E A : ι → ℝ} (hg : ∀ (k : ι), 0 < g k) (hFcal : 0 < Fcal) (u : ι)
  (hA : 0 < A u) :
  CflibsFormal.Classic.classicDensity kB T Fcal g E A u
      (CflibsFormal.lineIntensity kB T N Fcal g E A u) =
    N
```

> **Per-species soundness core.** The exact inverse of the forward line-emission
> step: feeding the forward intensity `lineIntensity kB T N Fcal g E A u` back through
> `classicDensity` recovers the true total density `N`. The partition function `U`, the
> calibration `Fcal`, the Einstein coefficient `A_u`, the degeneracy `g_u`, and the
> Boltzmann factor `bf` all cancel. Everything downstream (composition soundness,
> calibration-free) is assembled from this single equality. 

### `CflibsFormal.Classic.classic_sound`

Module `CflibsFormal.Classic` · scope `EXACT`

```lean
CflibsFormal.Classic.classic_sound.{u_1, u_2} {ι : Type u_1} [Fintype ι] {κ : Type u_2} [Fintype κ]
  [Nonempty ι] {kB T Fcal : ℝ} {N : κ → ℝ} {g E A : κ → ι → ℝ} {u : κ → ι}
  (hg : ∀ (s : κ) (k : ι), 0 < g s k) (hFcal : 0 < Fcal) (hA : ∀ (s : κ), 0 < A s (u s))
  (_hN : 0 < CflibsFormal.totalDensity N) (s : κ) :
  CflibsFormal.Classic.classicComposition kB T Fcal g E A u
      (fun t => CflibsFormal.lineIntensity kB T (N t) Fcal (g t) (E t) (A t) (u t)) s =
    CflibsFormal.composition N s
```

> **Composition soundness of the classic algorithm (given the temperature).** When the
> intensities are generated by the forward model at true parameters `(T, N)` AND the estimator
> is evaluated at that same `T`, `classicComposition` returns exactly the true composition
> `C_s = N_s / Σ_t N_t`. The per-species recovery `classicDensity_recovers` fires for every
> species, so the recovered density vector equals `N` pointwise; feeding it into `composition`
> matches the true composition.
> 
> Honest scope: this is the DENSITY→CLOSURE leg, and `T` is shared between the data and the
> estimator (temperature-matching is load-bearing — unlike `Fcal`, which provably cancels by
> `classic_calibration_free`). The temperature itself is recovered separately, from the
> Boltzmann-plot slope on the same data, by `classic_temperature_correct`. The full
> slope→density→closure pipeline is `classic_temperature_correct` (slope ⇒ `T`) composed with
> this theorem (`T` ⇒ composition); they are not yet combined into a single statement. 

### `CflibsFormal.Classic.classic_sound_sum_one`

Module `CflibsFormal.Classic` · scope `PURE-MATH`

```lean
CflibsFormal.Classic.classic_sound_sum_one.{u_1, u_2} {ι : Type u_1} [Fintype ι] {κ : Type u_2}
  [Fintype κ] [Nonempty ι] {kB T Fcal : ℝ} {N : κ → ℝ} {g E A : κ → ι → ℝ} {u : κ → ι}
  (hg : ∀ (s : κ) (k : ι), 0 < g s k) (hFcal : 0 < Fcal) (hA : ∀ (s : κ), 0 < A s (u s))
  (hN : 0 < CflibsFormal.totalDensity N) :
  ∑ s,
      CflibsFormal.Classic.classicComposition kB T Fcal g E A u
        (fun t => CflibsFormal.lineIntensity kB T (N t) Fcal (g t) (E t) (A t) (u t)) s =
    1
```

> **Normalization corollary.** The recovered compositions sum to one, exercising
> the positivity of the total density through `composition_sum_one`. 

### `CflibsFormal.Classic.classic_temperature_correct`

Module `CflibsFormal.Classic` · scope `REDUCED`

```lean
CflibsFormal.Classic.classic_temperature_correct.{u_1} {ι : Type u_1} [Fintype ι] [Nonempty ι]
  {kB T N Fcal : ℝ} {g E A : ι → ℝ} (hg : ∀ (k : ι), 0 < g k) (hN : 0 < N) (hFcal : 0 < Fcal)
  (hA : ∀ (k : ι), 0 < A k) (i j : ι) (hE : E i ≠ E j) :
  (Real.log (CflibsFormal.lineIntensity kB T N Fcal g E A j / (g j * A j)) -
        Real.log (CflibsFormal.lineIntensity kB T N Fcal g E A i / (g i * A i))) /
      (E i - E j) =
    1 / (kB * T)
```

> **Temperature-correctness leg of soundness.** The slope of the intensity Boltzmann
> plot built from two measured lines of the same species recovers `1 / (k_B T)` exactly:
> the recovered temperature equals the true `T`. Pure reuse of
> `temperature_from_two_lines` from `ForwardMap.lean`, restated in the Classic namespace
> to articulate that STEP (1) of the classic algorithm is sound. 

### `CflibsFormal.observeMulti.eq_2`

Module `CflibsFormal.CompositionIdentifiability` · scope `?`

```lean
CflibsFormal.observeMulti.eq_2.{u_1, u_2} {species : Type u_1} {levelIndex : Type u_2}
  [Fintype levelIndex] (kB Fcal : ℝ) (emit : species → levelIndex) (s₀ : species) (i j : levelIndex)
  (p : CflibsFormal.PlasmaParams species levelIndex) :
  CflibsFormal.observeMulti kB Fcal emit s₀ i j p (Sum.inr false) =
    CflibsFormal.lineIntensity kB p.T (p.N s₀) Fcal p.g p.E p.A i
```

### `CflibsFormal.observeMulti.eq_3`

Module `CflibsFormal.CompositionIdentifiability` · scope `?`

```lean
CflibsFormal.observeMulti.eq_3.{u_1, u_2} {species : Type u_1} {levelIndex : Type u_2}
  [Fintype levelIndex] (kB Fcal : ℝ) (emit : species → levelIndex) (s₀ : species) (i j : levelIndex)
  (p : CflibsFormal.PlasmaParams species levelIndex) :
  CflibsFormal.observeMulti kB Fcal emit s₀ i j p (Sum.inr true) =
    CflibsFormal.lineIntensity kB p.T (p.N s₀) Fcal p.g p.E p.A j
```

### `CflibsFormal.classic_biased_differential_exact`

Module `CflibsFormal.DifferentialEstimator` · scope `EXACT`

```lean
CflibsFormal.classic_biased_differential_exact.{u_1} {ι : Type u_1} [Fintype ι] [Nonempty ι]
  {kB T Ns Nr Fcal : ℝ} {g E A g' E' A' : ι → ℝ} (hg : ∀ (k : ι), 0 < g k)
  (hg' : ∀ (k : ι), 0 < g' k) (hNs : 0 < Ns) (hNr : 0 < Nr) (hFcal : 0 < Fcal)
  (hA : ∀ (k : ι), 0 < A k) (k : ι) (hA' : 0 < A' k)
  (hρ : CflibsFormal.responseFactor kB T g' E' A' k ≠ CflibsFormal.responseFactor kB T g E A k) :
  CflibsFormal.Classic.classicDensity kB T Fcal g' E' A' k
        (CflibsFormal.lineIntensity kB T Ns Fcal g E A k) ≠
      Ns ∧
    CflibsFormal.differentialRatio (CflibsFormal.lineIntensity kB T Ns Fcal g E A)
        (CflibsFormal.lineIntensity kB T Nr Fcal g E A) k =
      Ns / Nr
```

> **EXACT: the classic reader is actually biased, the differential one is not.** Sharpening of
> `differentialRatio_immune_to_atomicData`: whenever the believed response factor differs from the
> true one (`ρ_wrong ≠ ρ_true` — e.g. any wrong `A'_k`), the classic recovered density is *not*
> `N_s`, while on the same spectrum the differential ratio is exactly `N_s/N_r`. 

### `CflibsFormal.differentialRatio_eq_density_ratio`

Module `CflibsFormal.DifferentialEstimator` · scope `EXACT`

```lean
CflibsFormal.differentialRatio_eq_density_ratio.{u_1} {ι : Type u_1} [Fintype ι] [Nonempty ι]
  {kB T Ns Nr Fcal : ℝ} {g E A : ι → ℝ} (hg : ∀ (k : ι), 0 < g k) (hNr : 0 < Nr) (hFcal : 0 < Fcal)
  (hA : ∀ (k : ι), 0 < A k) (k : ι) :
  CflibsFormal.differentialRatio (CflibsFormal.lineIntensity kB T Ns Fcal g E A)
      (CflibsFormal.lineIntensity kB T Nr Fcal g E A) k =
    Ns / Nr
```

> **EXACT line-by-line cancellation (matched `T`, `Fcal`).** For a sample of density `N_s` and
> a reference of density `N_r` of the same species, emitted at the same temperature with the same
> calibration and the same (true) atomic data, the differential ratio of EVERY line is `N_s / N_r`:
>   `(Fcal·A_k·N_s·g_k·bf_k/U) / (Fcal·A_k·N_r·g_k·bf_k/U) = N_s/N_r`.
> `Fcal`, `A_k`, `g_k`, the Boltzmann factor and the partition function all cancel *per line*
> (contrast `Identifiability.lineIntensity_ratio_closed_form`, the ratio *across* lines of one
> spectrum, where `g_j A_j/(g_i A_i)` survives). No positivity of `N_s` is needed; `N_r > 0` keeps
> the reference line nonzero. The forward model is that of Ciucci et al. 1999. 

### `CflibsFormal.differentialRatio_error_bound`

Module `CflibsFormal.DifferentialEstimator` · scope `REDUCED`

```lean
CflibsFormal.differentialRatio_error_bound.{u_1} {ι : Type u_1} [Fintype ι] [Nonempty ι]
  {kB Tmin Ts Tr Ns Nr Fcal δ : ℝ} {g E A : ι → ℝ} (hkB : 0 < kB) (hTmin : 0 < Tmin)
  (hTs : Tmin ≤ Ts) (hTr : Tmin ≤ Tr) (hg : ∀ (k : ι), 0 < g k) (hE : ∀ (k : ι), 0 ≤ E k)
  (hNs : 0 < Ns) (hNr : 0 < Nr) (hFcal : 0 < Fcal) (hA : ∀ (k : ι), 0 < A k) (hδ : |Ts - Tr| ≤ δ)
  (k : ι) :
  |Real.log
          (CflibsFormal.differentialRatio (CflibsFormal.lineIntensity kB Ts Ns Fcal g E A)
            (CflibsFormal.lineIntensity kB Tr Nr Fcal g E A) k) -
        Real.log (Ns / Nr)| ≤
    (|E k| + (∑ j, g j * E j) / CflibsFormal.partitionFunction kB Tmin g E) / (kB * Tmin ^ 2) * δ
```

> **REDUCED first-order error bound for an unmatched temperature.** On a temperature floor
> `0 < Tmin ≤ T_s, T_r`, with `k_B > 0`, `g_k > 0`, level energies `E_k ≥ 0` and
> `|T_s − T_r| ≤ δ`, the differential log-ratio deviates from `log (N_s/N_r)` by at most
>   `(|E_k| + (∑_j g_j E_j) / U(Tmin)) · δ / (k_B Tmin²)`.
> Derivation (all constants explicit): by `logDifferentialRatio_affine_in_E` the deviation is
> `log (U_r/U_s) − E_k (β_s − β_r)`; the inverse-temperature leg is `|β_s − β_r| ≤ δ/(k_B Tmin²)`
> (`Analysis.inv_kT_sub_le`, the mean-value bound on `1/(k_B T)`); the partition-function leg is
> `|log U_r − log U_s| ≤ |U_r − U_s|/U(Tmin) ≤ (∑ g_j E_j)/(k_B Tmin²) · δ / U(Tmin)`, using the
> Lipschitz constant of `PartitionLipschitz.partitionFunction_lipschitz_temp` and the floor
> `U(Tmin) ≤ U(T)` for `T ≥ Tmin` (`SahaStability.partitionFunction_mono_temp`, valid because
> `E_k ≥ 0`). Reduction: the bound is a first-order (Lipschitz) envelope in `|T_s − T_r|` with
> `Tmin`-floor over-estimates in both legs; the identity it starts from is exact. 

### `CflibsFormal.differentialRatio_immune_to_atomicData`

Module `CflibsFormal.DifferentialEstimator` · scope `EXACT`

```lean
CflibsFormal.differentialRatio_immune_to_atomicData.{u_1} {ι : Type u_1} [Fintype ι] [Nonempty ι]
  {kB T Ns Nr Fcal : ℝ} {g E A g' E' A' : ι → ℝ} (hg : ∀ (k : ι), 0 < g k)
  (hg' : ∀ (k : ι), 0 < g' k) (hNr : 0 < Nr) (hFcal : 0 < Fcal) (hA : ∀ (k : ι), 0 < A k) (k : ι)
  (hA' : 0 < A' k) :
  CflibsFormal.Classic.classicDensity kB T Fcal g' E' A' k
        (CflibsFormal.lineIntensity kB T Ns Fcal g E A k) =
      Ns * CflibsFormal.responseFactor kB T g E A k / CflibsFormal.responseFactor kB T g' E' A' k ∧
    CflibsFormal.differentialRatio (CflibsFormal.lineIntensity kB T Ns Fcal g E A)
        (CflibsFormal.lineIntensity kB T Nr Fcal g E A) k =
      Ns / Nr
```

> **EXACT immunity to atomic-data error — the contrast with `classicDensity_aliasing`.**
> One spectrum, emitted with the TRUE data `(g, E, A)` at density `N_s`; one analyst who BELIEVES
> the wrong data `(g', E', A')`. The classic single-line reader returns the aliased
> `N_s · ρ_true/ρ_wrong` (first conjunct — verbatim `classicDensity_aliasing`), while the
> differential ratio against a reference of density `N_r` returns `N_s/N_r` (second conjunct).
> 
> Why this is the whole result and not a triviality: the second conjunct literally does not
> mention `g'`, `E'`, or `A'`. The differential estimator has no slot for the believed data, so the
> aliasing factor `ρ_true/ρ_wrong` — an *arbitrary* multiplicative bias with no self-diagnosing
> signature in the classic method — cannot enter it at all. The immunity is structural (a property
> of the estimator's *inputs*), not a cancellation that happens to hold for correct data. What it
> does NOT buy is standardlessness: `N_r` must be known independently. 

### `CflibsFormal.differentialSlope_eq_neg_dbeta`

Module `CflibsFormal.DifferentialEstimator` · scope `EXACT`

```lean
CflibsFormal.differentialSlope_eq_neg_dbeta.{u_1} {ι : Type u_1} [Fintype ι] [Nonempty ι]
  {kB Ts Tr Ns Nr Fcal : ℝ} {g E A : ι → ℝ} (hg : ∀ (k : ι), 0 < g k) (hNs : 0 < Ns) (hNr : 0 < Nr)
  (hFcal : 0 < Fcal) (hA : ∀ (k : ι), 0 < A k) (hvar : 0 < ∑ k, (E k - CflibsFormal.mean E) ^ 2) :
  (CflibsFormal.olsSlope E fun k =>
        Real.log
          (CflibsFormal.differentialRatio (CflibsFormal.lineIntensity kB Ts Ns Fcal g E A)
            (CflibsFormal.lineIntensity kB Tr Nr Fcal g E A) k)) =
      -(1 / (kB * Ts) - 1 / (kB * Tr)) ∧
    (CflibsFormal.olsIntercept E fun k =>
        Real.log
          (CflibsFormal.differentialRatio (CflibsFormal.lineIntensity kB Ts Ns Fcal g E A)
            (CflibsFormal.lineIntensity kB Tr Nr Fcal g E A) k)) =
      Real.log (Ns / Nr) +
        Real.log
          (CflibsFormal.partitionFunction kB Tr g E / CflibsFormal.partitionFunction kB Ts g E)
```

> **EXACT: OLS on the differential Boltzmann plot recovers `−Δβ`.** Fitting
> `y_k := log (I_s k / I_r k)` against `E_k` by ordinary least squares over any line set with
> positive energy spread (`OLS.olsSlope`, `OLS.ols_recovers_line`) returns the slope
> `−(β_s − β_r) = −(1/(k_B T_s) − 1/(k_B T_r))` and the intercept
> `log (N_s/N_r) + log (U_r/U_s)` exactly — because `logDifferentialRatio_affine_in_E` makes the
> ordinates exactly collinear. No atomic data enter the ordinates. 

### `CflibsFormal.differentialSlope_two_lines`

Module `CflibsFormal.DifferentialEstimator` · scope `EXACT`

```lean
CflibsFormal.differentialSlope_two_lines {kB Ts Tr Ns Nr Fcal : ℝ} {g E A : Fin 2 → ℝ}
  (hg : ∀ (k : Fin 2), 0 < g k) (hNs : 0 < Ns) (hNr : 0 < Nr) (hFcal : 0 < Fcal)
  (hA : ∀ (k : Fin 2), 0 < A k) (hE : E 0 ≠ E 1) :
  (CflibsFormal.olsSlope E fun k =>
      Real.log
        (CflibsFormal.differentialRatio (CflibsFormal.lineIntensity kB Ts Ns Fcal g E A)
          (CflibsFormal.lineIntensity kB Tr Nr Fcal g E A) k)) =
    -(1 / (kB * Ts) - 1 / (kB * Tr))
```

> **EXACT two-line differential slope.** The two-line specialization of
> `differentialSlope_eq_neg_dbeta`: with exactly two lines of distinct energy (`E 0 ≠ E 1`, which
> is precisely the positive-spread condition for `Fin 2`), the OLS slope of the differential
> Boltzmann plot is `−(β_s − β_r)`. This is the differential analogue of
> `ForwardMap.temperature_from_two_lines`, with `Δβ` in place of `β`. 

### `CflibsFormal.logDifferentialRatio_affine_in_E`

Module `CflibsFormal.DifferentialEstimator` · scope `EXACT`

```lean
CflibsFormal.logDifferentialRatio_affine_in_E.{u_1} {ι : Type u_1} [Fintype ι] [Nonempty ι]
  {kB Ts Tr Ns Nr Fcal : ℝ} {g E A : ι → ℝ} (hg : ∀ (k : ι), 0 < g k) (hNs : 0 < Ns) (hNr : 0 < Nr)
  (hFcal : 0 < Fcal) (hA : ∀ (k : ι), 0 < A k) (k : ι) :
  Real.log
      (CflibsFormal.differentialRatio (CflibsFormal.lineIntensity kB Ts Ns Fcal g E A)
        (CflibsFormal.lineIntensity kB Tr Nr Fcal g E A) k) =
    Real.log (Ns / Nr) +
        Real.log
          (CflibsFormal.partitionFunction kB Tr g E / CflibsFormal.partitionFunction kB Ts g E) -
      E k * (1 / (kB * Ts) - 1 / (kB * Tr))
```

> **EXACT: the differential Boltzmann plot (unmatched temperatures).** With sample and
> reference at temperatures `T_s`, `T_r` and inverse temperatures `β_x := 1/(k_B T_x)`,
>   `log (I_s k / I_r k) = log (N_s/N_r) + log (U_r/U_s) − E_k · (β_s − β_r)`,
> where `U_x = partitionFunction kB T_x g E`. The log-ratio is *affine in the level energy* with
> slope `−(β_s − β_r)` and an intercept carrying the density ratio and the partition-function
> ratio. Still no `A_k`, `g_k`, or `Fcal` — those cancel line by line regardless of `T`. So a
> two-spectrum Boltzmann plot of `log (I_s/I_r)` against `E_k` reads off the temperature
> *mismatch*; at `T_s = T_r` the slope is `0` and the intercept collapses to `log (N_s/N_r)`
> (`differentialRatio_eq_density_ratio`). Forward model: Ciucci et al. 1999. 

### `CflibsFormal.boltzmann_plot_intensity`

Module `CflibsFormal.ForwardMap` · scope `REDUCED`

```lean
CflibsFormal.boltzmann_plot_intensity.{u_1} {ι : Type u_1} [Fintype ι] [Nonempty ι]
  {kB T N Fcal : ℝ} {g E A : ι → ℝ} (hg : ∀ (k : ι), 0 < g k) (hN : 0 < N) (hFcal : 0 < Fcal)
  (hA : ∀ (k : ι), 0 < A k) (k : ι) :
  Real.log (CflibsFormal.lineIntensity kB T N Fcal g E A k / (g k * A k)) =
    Real.log (Fcal * N / CflibsFormal.partitionFunction kB T g E) - E k / (kB * T)
```

> **Intensity Boltzmann-plot identity.** `log (I_{ki} / (g_k A)) = log (Fcal · N / U)
> - E_k / (k_B T)`, i.e. the Boltzmann plot built from *measured* line intensities is
> affine in the upper-level energy `E k` with slope `-1 / (k_B T)` and intercept
> `log (Fcal · N / U(T))`. This lifts `boltzmann_plot` from level populations to
> observables — the core of CF-LIBS temperature determination. 

### `CflibsFormal.lineIntensity_pos`

Module `CflibsFormal.ForwardMap` · scope `PURE-MATH`

```lean
CflibsFormal.lineIntensity_pos.{u_1} {ι : Type u_1} [Fintype ι] [Nonempty ι] {kB T N Fcal : ℝ}
  {g E A : ι → ℝ} (hg : ∀ (k : ι), 0 < g k) (hN : 0 < N) (hFcal : 0 < Fcal)
  (hA : ∀ (k : ι), 0 < A k) (k : ι) : 0 < CflibsFormal.lineIntensity kB T N Fcal g E A k
```

> **Positivity of the observable.** The line intensity is positive given positive
> calibration, density, Einstein coefficient, and degeneracies. Establishes the model is
> physically well-posed and is the precondition for taking `Real.log` below. 

### `CflibsFormal.temperature_from_two_lines`

Module `CflibsFormal.ForwardMap` · scope `REDUCED`

```lean
CflibsFormal.temperature_from_two_lines.{u_1} {ι : Type u_1} [Fintype ι] [Nonempty ι]
  {kB T N Fcal : ℝ} {g E A : ι → ℝ} (hg : ∀ (k : ι), 0 < g k) (hN : 0 < N) (hFcal : 0 < Fcal)
  (hA : ∀ (k : ι), 0 < A k) (i j : ι) (hE : E i ≠ E j) :
  (Real.log (CflibsFormal.lineIntensity kB T N Fcal g E A j / (g j * A j)) -
        Real.log (CflibsFormal.lineIntensity kB T N Fcal g E A i / (g i * A i))) /
      (E i - E j) =
    1 / (kB * T)
```

> **Temperature from two lines.** The slope of the intensity Boltzmann plot between
> any two distinct-energy lines of the same species recovers `1 / (k_B T)` exactly. The
> calibration `Fcal`, number density `N`, partition function `U`, degeneracies `g`, and
> Einstein coefficients `A` all cancel. (`hE` prevents division by zero; the identity is
> physically meaningful for `k_B T ≠ 0`.) 

### `CflibsFormal.boltzmann_plot_intensity_wavelength`

Module `CflibsFormal.ForwardMapEnergy` · scope `EXACT`

```lean
CflibsFormal.boltzmann_plot_intensity_wavelength.{u_1} {ι : Type u_1} [Fintype ι] [Nonempty ι]
  {hc fourPi kB T N Fgeo : ℝ} {g E A lam : ι → ℝ} (hg : ∀ (k : ι), 0 < g k) (hN : 0 < N)
  (hhc : 0 < hc) (hfp : 0 < fourPi) (hFgeo : 0 < Fgeo) (hA : ∀ (k : ι), 0 < A k)
  (hlam : ∀ (k : ι), 0 < lam k) (k : ι) :
  Real.log
      (CflibsFormal.lineIntensityEnergy hc fourPi kB T N Fgeo g E A lam k * lam k / (g k * A k)) =
    Real.log (hc * Fgeo * N / (fourPi * CflibsFormal.partitionFunction kB T g E)) - E k / (kB * T)
```

> **Wavelength-form Boltzmann plot.** `log(I·λ_k/(g_k A_k))` is affine in the upper-level energy
> `E_k` with slope `-1/(k_B T)` and intercept `log(h c · Fgeo · N /(4π U(T)))`. The explicit `λ_k`
> cancels the `1/λ_k` photon-energy factor, so the intercept is λ-INDEPENDENT and the slope is
> identical to the reduced `boltzmann_plot_intensity`. This is the energy ordinate of the companion
> numerical pipeline (`y = ln(I·λ/(g·A))`); its slope `-1/(k_B T)` is identical to the reduced
> `boltzmann_plot_intensity` (the intercepts coincide when `Fcal = h c · Fgeo / 4π`). 

### `CflibsFormal.lineIntensityEnergy_eq_lineIntensity`

Module `CflibsFormal.ForwardMapEnergy` · scope `REDUCED`

```lean
CflibsFormal.lineIntensityEnergy_eq_lineIntensity.{u_1} {ι : Type u_1} [Fintype ι]
  (hc fourPi kB T N Fgeo : ℝ) (g E A lam : ι → ℝ) (k : ι) :
  CflibsFormal.lineIntensityEnergy hc fourPi kB T N Fgeo g E A lam k =
    CflibsFormal.lineIntensity kB T N (hc * Fgeo / (fourPi * lam k)) g E A k
```

> **Reduction to the canonical map.** With the **per-line** calibration
> `Fcal := h c · Fgeo /(4π λ_k)` the energy forward map equals `ForwardMap.lineIntensity`. This is
> WHY the spec's `Fcal`-absorbed convention is not "missing λ": the per-line `λ_k` lives inside
> `Fcal` exactly. An unconditional algebraic identity (`ring`) — no positivity needed. 

### `CflibsFormal.lineIntensityEnergy_mul_lam`

Module `CflibsFormal.ForwardMapEnergy` · scope `REDUCED`

```lean
CflibsFormal.lineIntensityEnergy_mul_lam.{u_1} {ι : Type u_1} [Fintype ι]
  {hc fourPi kB T N Fgeo : ℝ} {g E A lam : ι → ℝ} (k : ι) (hlam : lam k ≠ 0) :
  CflibsFormal.lineIntensityEnergy hc fourPi kB T N Fgeo g E A lam k * lam k =
    CflibsFormal.lineIntensity kB T N (hc * Fgeo / fourPi) g E A k
```

> **The wavelength factor cancels the photon-energy factor.** `I · λ_k` equals
> `ForwardMap.lineIntensity` with the **λ-free** calibration `Fcal := h c · Fgeo / 4π`: multiplying
> the measured energy intensity by its own wavelength removes the per-line `1/λ_k`, recovering the
> photon-rate map. This is the crux of why `ln(I·λ/(g A))` (energy) and `ln(I/(g A))` (photon-rate)
> are the same Boltzmann plot. Needs only `λ_k ≠ 0`. 

### `CflibsFormal.nvP_slope_bias_eq_log`

Module `CflibsFormal.HeteroAtomicData` · scope `EXACT`

```lean
CflibsFormal.nvP_slope_bias_eq_log :
  (CflibsFormal.olsSlope CflibsFormal.nvHE✝ fun k =>
          Real.log
            (CflibsFormal.lineIntensity 1 1 2 1 CflibsFormal.nvPg✝ CflibsFormal.nvHE✝
                CflibsFormal.nvPA✝ k /
              (CflibsFormal.nvPg✝ k * CflibsFormal.nvPA'✝ k))) -
        -(1 / (1 * 1)) =
      Real.log (2 / 3) ∧
    Real.log (2 / 3) < 0
```

> **The physical witness's slope bias is NOT zero** — the `example` above is bracketed by two
> non-zero numbers, `0 < |Δβ| = |log (2/3)| ≤ 3/2`, not a `0 ≤ 3/2` collapse. On the witness data
> the fitted slope is displaced from the true `−1/(k_B T) = −1` by EXACTLY `log (2/3) < 0`: the
> wrong `A'₁ = 3` in place of `A₁ = 2` really does tilt the Boltzmann plot, so the recovered
> temperature really is biased. Together with `nvP_heteroSlopeBound_value` this certifies that
> `olsSlope_aliasing_A_hetero` is being exercised on a genuine perturbation. 

### `CflibsFormal.olsSlope_aliasing_A`

Module `CflibsFormal.HeteroAtomicData` · scope `EXACT`

```lean
CflibsFormal.olsSlope_aliasing_A.{u_1} {ι : Type u_1} [Fintype ι] [Nonempty ι] {kB T N Fcal : ℝ}
  {g E A A' : ι → ℝ} (hg : ∀ (k : ι), 0 < g k) (hN : 0 < N) (hFcal : 0 < Fcal)
  (hA : ∀ (k : ι), 0 < A k) (hA' : ∀ (k : ι), 0 < A' k)
  (hvar : 0 < ∑ k, (E k - CflibsFormal.mean E) ^ 2) :
  (CflibsFormal.olsSlope E fun k =>
      Real.log (CflibsFormal.lineIntensity kB T N Fcal g E A k / (g k * A' k))) =
    -(1 / (kB * T)) + CflibsFormal.olsSlope E fun k => Real.log (A k / A' k)
```

> **EXACT aliasing identity for the fitted SLOPE (A-channel).** The spectrum is emitted with the
> TRUE transition probabilities `A` (correct `g`, `E`) at density `N`; the analyst builds the
> Boltzmann-plot ordinate with the WRONG `A'`. Then the fitted slope is EXACTLY the true slope plus
> the OLS slope of the per-line log data-ratios:
>   `olsSlope E (log(Iₖ/(gₖA'ₖ))) = −1/(k_B T) + olsSlope E (log(Aₖ/A'ₖ))`.
> Proof: the observed ordinate splits additively, `ŷₖ = yₖ^true + log(Aₖ/A'ₖ)` (`Real.log_mul` on
> `Iₖ/(gₖA'ₖ) = (Iₖ/(gₖAₖ))·(Aₖ/A'ₖ)`, all factors positive); `olsSlope` is linear in the ordinate;
> and the true ordinate is affine in `Eₖ` with slope `−1/(k_B T)`
> (`ForwardMap.boltzmann_plot_intensity` + `OLS.ols_recovers_line`).
> EXACT: a cancellation identity, no approximation, no centering hypothesis. It is the SLOPE twin
> of `Alt.olsDensity_aliasing_A` (which is the intercept/density statement), and it is what makes
> the atomic-data error a *temperature* error, not only a density error. 

### `CflibsFormal.olsSlope_aliasing_A_global`

Module `CflibsFormal.HeteroAtomicData` · scope `REDUCED`

```lean
CflibsFormal.olsSlope_aliasing_A_global.{u_1} {ι : Type u_1} [Fintype ι] [Nonempty ι]
  {kB T N Fcal dmax : ℝ} {g E A A' δ : ι → ℝ} (hg : ∀ (k : ι), 0 < g k) (hN : 0 < N)
  (hFcal : 0 < Fcal) (hA : ∀ (k : ι), 0 < A k) (hA' : ∀ (k : ι), 0 < A' k)
  (hvar : 0 < ∑ k, (E k - CflibsFormal.mean E) ^ 2) (hδ1 : ∀ (k : ι), δ k < 1)
  (hpert : ∀ (k : ι), |A' k - A k| ≤ δ k * A k) (hδmax : ∀ (k : ι), δ k ≤ dmax) (hmax1 : dmax < 1) :
  |(CflibsFormal.olsSlope E fun k =>
          Real.log (CflibsFormal.lineIntensity kB T N Fcal g E A k / (g k * A' k))) -
        -(1 / (kB * T))| ≤
    CflibsFormal.globalSlopeBound E dmax
```

> **The GLOBAL lumped-`δ` bound, recovered as a corollary.** If every per-line budget is capped
> by one worst-case `δmax < 1`, the heterogeneous bound implies the familiar single-`δ` bound
> `|Δβ| ≤ (δmax/(1−δmax))·(∑ₖ |Eₖ − Ē|)/SS_E`. Together with the EQUALITY
> `heteroSlopeBound_const` (constant `δ` gives exactly `globalSlopeBound`), this certifies that the
> heterogeneous statement is a strict generalization of the lumped-`δ` model rather than a
> different quantity.
> REDUCED, for the same reasons as `olsSlope_aliasing_A_hetero`. 

### `CflibsFormal.olsSlope_aliasing_A_hetero`

Module `CflibsFormal.HeteroAtomicData` · scope `REDUCED`

```lean
CflibsFormal.olsSlope_aliasing_A_hetero.{u_1} {ι : Type u_1} [Fintype ι] [Nonempty ι]
  {kB T N Fcal : ℝ} {g E A A' δ : ι → ℝ} (hg : ∀ (k : ι), 0 < g k) (hN : 0 < N) (hFcal : 0 < Fcal)
  (hA : ∀ (k : ι), 0 < A k) (hA' : ∀ (k : ι), 0 < A' k)
  (hvar : 0 < ∑ k, (E k - CflibsFormal.mean E) ^ 2) (hδ1 : ∀ (k : ι), δ k < 1)
  (hpert : ∀ (k : ι), |A' k - A k| ≤ δ k * A k) :
  |(CflibsFormal.olsSlope E fun k =>
          Real.log (CflibsFormal.lineIntensity kB T N Fcal g E A k / (g k * A' k))) -
        -(1 / (kB * T))| ≤
    CflibsFormal.heteroSlopeBound E δ
```

> **HETEROGENEOUS atomic-data slope bound (the main result).** With a genuinely PER-LINE
> relative transition-probability error `|A'ₖ − Aₖ| ≤ δₖ·Aₖ` (`δₖ < 1`), the Boltzmann-plot slope
> recovered from the true spectrum with the wrong `A'` deviates from the true inverse temperature
> by at most `heteroSlopeBound E δ = (∑ₖ |Eₖ − Ē|·δₖ/(1−δₖ)) / SS_E`.
> Each line is charged its OWN budget, weighted by its OWN leverage: a line whose `A` is exact
> (`δₖ = 0`) contributes nothing at all, which no single-`δ` bound can express.
> Proof: the EXACT split `olsSlope_aliasing_A` reduces the claim to `|olsSlope E (log(A/A'))|`;
> `Analysis.abs_log_ratio_le` turns each relative data error into an ordinate budget
> `δₖ/(1−δₖ)`; `ErrorBudget.olsSlope_stable_hetero` (the per-line NOISE precedent, reused verbatim)
> closes it against the zero ordinate.
> REDUCED: it inherits the optically-thin single-temperature LTE forward map, and the two-sided
> `δ/(1−δ)` transfer constant is the worse of the two log sides. 

### `CflibsFormal.temp_rel_error_atomicData_hetero`

Module `CflibsFormal.HeteroAtomicData` · scope `REDUCED`

```lean
CflibsFormal.temp_rel_error_atomicData_hetero.{u_1} {ι : Type u_1} [Fintype ι] [Nonempty ι]
  {kB T THat N Fcal : ℝ} {g E A A' δ : ι → ℝ} (hkB : 0 < kB) (hT : 0 < T) (hTHat : 0 < THat)
  (hg : ∀ (k : ι), 0 < g k) (hN : 0 < N) (hFcal : 0 < Fcal) (hA : ∀ (k : ι), 0 < A k)
  (hA' : ∀ (k : ι), 0 < A' k) (hvar : 0 < ∑ k, (E k - CflibsFormal.mean E) ^ 2)
  (hδ1 : ∀ (k : ι), δ k < 1) (hpert : ∀ (k : ι), |A' k - A k| ≤ δ k * A k)
  (hslopeHat :
    (CflibsFormal.olsSlope E fun k =>
        Real.log (CflibsFormal.lineIntensity kB T N Fcal g E A k / (g k * A' k))) =
      -(1 / (kB * THat))) :
  |THat - T| / T ≤ kB * THat * CflibsFormal.heteroSlopeBound E δ
```

> **Per-line atomic-data error ⇒ relative TEMPERATURE error.** The physics payload: composing
> the heterogeneous slope bound with the exact temperature identity
> (`ErrorBudget.temp_rel_error_le`), a per-line transition-probability budget `δₖ` propagates to
>   `|T̂ − T|/T ≤ k_B·T̂·heteroSlopeBound E δ`.
> `hslopeHat` identifies the analyst's recovered temperature `T̂` with the fitted (wrong-`A'`) slope
> in the physical Boltzmann sign convention `slope = −1/(k_B T)`.
> REDUCED, and honestly partial: `T̂` is a HYPOTHESIS (this bounds the error of whatever temperature
> the analyst reads off the fitted slope; it does not construct `T̂` or prove one exists), the
> `g`/`E` channels are excluded, and the resulting temperature error is NOT fed back into the
> partition functions `U(T̂)` — that cross-channel coupling remains open (see `ErrorBudget.lean`). 

### `CflibsFormal.density_identifiability`

Module `CflibsFormal.Identifiability` · scope `EXACT`

```lean
CflibsFormal.density_identifiability.{u_1} {ι : Type u_1} [Fintype ι] [Nonempty ι] {kB T Fcal : ℝ}
  {g E A : ι → ℝ} {N₁ N₂ : ℝ} (hg : ∀ (k : ι), 0 < g k) (hFcal : 0 < Fcal) (u : ι) (hA : 0 < A u)
  (hI :
    CflibsFormal.lineIntensity kB T N₁ Fcal g E A u =
      CflibsFormal.lineIntensity kB T N₂ Fcal g E A u) :
  N₁ = N₂
```

> **Target 2 — relative-density / composition identifiability.**
> 
> With `T` and the atomic data (`Fcal`, `A`, `g`, `E`, `U`) fixed and nondegenerate
> (`Fcal > 0`, `A u > 0`, `g k > 0`), the species total number density `N` is uniquely
> recovered from a single line intensity: equal intensities ⇒ equal `N`. Since the
> composition `C_s` is `N_s` up to the closure normalization `∑ C_s = 1`
> (`composition_sum_one` in `Closure.lean`), equal `N` for every species gives equal
> composition; this lemma is the per-species core.
> 
> The map `N ↦ I` is multiplication by the strictly positive constant
> `c = Fcal · A_u · g u · exp(−E_u/(k_B T)) / U(T)`, so it is injective but not
> trivially so (the constant is genuine physics, so the proof needs
> `mul_left_cancel₀`, not `rfl`).
> 
> Non-vacuous: `ι = Fin 1`, `kB = T = Fcal = 1`, `g = A = fun _ => 1`,
> `E = fun _ => 0`, `u = 0`; then `I = c · N` with `c > 0`, so `N₁ = 3 ≠ N₂ = 5`
> give distinct intensities. `T` may be any real (positivity of `T` is *not* needed:
> `exp` and the partition function are positive regardless of `T`'s sign). 

### `CflibsFormal.electron_density_identifiability`

Module `CflibsFormal.Identifiability` · scope `EXACT`

```lean
CflibsFormal.electron_density_identifiability.{u_1, u_2} {ι : Type u_1} [Fintype ι] {κ : Type u_2}
  [Fintype κ] [Nonempty ι] [Nonempty κ] {kB T me h chi : ℝ} {gZ EZ : ι → ℝ} {gZ1 EZ1 : κ → ℝ}
  {R₁ R₂ : ℝ} (hkB : 0 < kB) (hT : 0 < T) (hme : 0 < me) (hh : 0 < h) (hgZ : ∀ (k : ι), 0 < gZ k)
  (hgZ1 : ∀ (k : κ), 0 < gZ1 k) (hR₁ : 0 < R₁) (hR₂ : 0 < R₂)
  (hne :
    CflibsFormal.electronDensityFromRatio kB T me h chi gZ EZ gZ1 EZ1 R₁ =
      CflibsFormal.electronDensityFromRatio kB T me h chi gZ EZ gZ1 EZ1 R₂) :
  R₁ = R₂
```

> **Target 3 — electron-density / stage-ratio identifiability via Saha.**
> 
> At fixed temperature `T` (hence fixed Saha factor `S = sahaFactor … > 0`), the Saha
> density diagnostic `R ↦ n_e = S/R = electronDensityFromRatio` is **injective** on
> positive stage ratios: if two positive ratios `R₁, R₂` yield the same inferred
> electron density, then `R₁ = R₂`. Equivalently, the diagnostic is invertible — a
> measured `n_e` back-determines the stage ratio `R` uniquely. (The forward reading
> `n_e = S/R` from a known `R` is, of course, mere function evaluation; the content
> here is the converse: no two distinct ratios alias to the same `n_e`.)
> 
> This is exactly the injectivity packaged from the proven strict antitonicity
> `electronDensity_antitone` (`R ↦ S/R` strictly decreasing on `(0,∞)`). It rests
> *only* on `S > 0`; identifiability does not — and need not — re-derive the Saha
> factor's internal structure: the exponent sign `−χ/(k_B T)`, the `(3/2)` thermal
> power, the spin weight `2`, and the partition-function ratio are certified
> separately by `sahaFactor_pos` and the closed form `log_sahaFactor`. (`S = 0` would
> make the map constantly `0`, destroying injectivity, so positivity is load-bearing.)
> 
> Non-vacuous: with `S > 0` (guaranteed by `sahaFactor_pos` under positive physical
> constants/weights) and `R₁ = R₂ = 2`, both sides equal `S/2`; the antitone map
> forces `R₁ = R₂`. 

### `CflibsFormal.lineIntensity_ratio_closed_form`

Module `CflibsFormal.Identifiability` · scope `EXACT`

```lean
CflibsFormal.lineIntensity_ratio_closed_form.{u_1} {ι : Type u_1} [Fintype ι] [Nonempty ι]
  {kB T N Fcal : ℝ} {g E A : ι → ℝ} (hg : ∀ (k : ι), 0 < g k) (hN : 0 < N) (hFcal : 0 < Fcal)
  (hA : ∀ (k : ι), 0 < A k) (i j : ι) :
  CflibsFormal.lineIntensity kB T N Fcal g E A j / CflibsFormal.lineIntensity kB T N Fcal g E A i =
    g j * A j / (g i * A i) * Real.exp ((E i - E j) / (kB * T))
```

> **Two-line intensity-ratio closed form.** Within one parameter set, the same-species
> two-line ratio is
>   `I_j / I_i = ((g_j·A_j)/(g_i·A_i)) · exp((E_i − E_j)/(k_B T))` —
> the calibration `Fcal`, density `N`, and partition function `U(T)` all cancel (Ciucci et al.
> 1999, the two-line Boltzmann ratio). This single identity carries BOTH directions of the
> temperature question: with `E i ≠ E j` the exponential factor genuinely varies with `T` and the
> temperature is identifiable (`temperature_identifiability`); with `E i = E j` it collapses to
> the `T`-independent constant `(g_j·A_j)/(g_i·A_i)` and the temperature is provably lost
> (`temperature_degeneracy`). No sign or positivity constraint on `T` is needed — the identity is
> total algebra over ℝ (at `T = 0` both sides read the same `exp(·/0) = exp 0` convention). 

### `CflibsFormal.temperature_degeneracy`

Module `CflibsFormal.Identifiability` · scope `EXACT`

```lean
CflibsFormal.temperature_degeneracy.{u_1} {ι : Type u_1} [Fintype ι] [Nonempty ι]
  {kB T₁ T₂ N₁ N₂ Fcal₁ Fcal₂ : ℝ} {g E A : ι → ℝ} (hg : ∀ (k : ι), 0 < g k) (hN₁ : 0 < N₁)
  (hN₂ : 0 < N₂) (hFcal₁ : 0 < Fcal₁) (hFcal₂ : 0 < Fcal₂) (hA : ∀ (k : ι), 0 < A k) (i j : ι)
  (hE : E i = E j) :
  CflibsFormal.lineIntensity kB T₁ N₁ Fcal₁ g E A j /
      CflibsFormal.lineIntensity kB T₁ N₁ Fcal₁ g E A i =
    CflibsFormal.lineIntensity kB T₂ N₂ Fcal₂ g E A j /
      CflibsFormal.lineIntensity kB T₂ N₂ Fcal₂ g E A i
```

> **Degeneracy converse — equal energies make the ratio `T`-independent.** If the two lines
> share the SAME upper-level energy (`E i = E j`), the two-line intensity ratio collapses to the
> constant `(g_j·A_j)/(g_i·A_i)` (`lineIntensity_ratio_closed_form` with a zero exponent) — the
> same value for EVERY temperature, density, and calibration on both sides. The ratio observation
> then carries no information about `T`: the ratio-equality antecedent of
> `temperature_identifiability` is satisfied by every pair `(T₁, T₂)` whatsoever, so its
> distinct-energy hypothesis `E i ≠ E j` is *necessary*, not merely convenient. Note the
> strength: no positivity of `kB`, `T₁`, `T₂` is needed — the collapse is total. 

### `CflibsFormal.temperature_identifiability`

Module `CflibsFormal.Identifiability` · scope `EXACT`

```lean
CflibsFormal.temperature_identifiability.{u_1} {ι : Type u_1} [Fintype ι] [Nonempty ι]
  {kB T₁ T₂ N₁ N₂ Fcal₁ Fcal₂ : ℝ} {g E A : ι → ℝ} (hkB : 0 < kB) (hT₁ : 0 < T₁) (hT₂ : 0 < T₂)
  (hg : ∀ (k : ι), 0 < g k) (hN₁ : 0 < N₁) (hN₂ : 0 < N₂) (hFcal₁ : 0 < Fcal₁) (hFcal₂ : 0 < Fcal₂)
  (hA : ∀ (k : ι), 0 < A k) (i j : ι) (hE : E i ≠ E j)
  (hratio :
    CflibsFormal.lineIntensity kB T₁ N₁ Fcal₁ g E A j /
        CflibsFormal.lineIntensity kB T₁ N₁ Fcal₁ g E A i =
      CflibsFormal.lineIntensity kB T₂ N₂ Fcal₂ g E A j /
        CflibsFormal.lineIntensity kB T₂ N₂ Fcal₂ g E A i) :
  T₁ = T₂
```

> **Target 1 — temperature identifiability.**
> 
> Two same-species lines with **distinct upper-level energies** `E i ≠ E j` fix the
> temperature uniquely. If two parameter sets (possibly differing in calibration
> `Fcal`, total density `N`, and temperature `T`) produce the *same intensity ratio*
> `I_j / I_i` on this line pair, and both temperatures are positive, then `T₁ = T₂`.
> 
> Inside one parameter set the ratio is
> `I_j/I_i = ((g_j·A_j)/(g_i·A_i)) · exp((E_i − E_j)/(k_B T))` — the common positive
> prefactor `(g_j·A_j)/(g_i·A_i)` (shared across both sides because `g`, `E`, `A`, the
> species, are the same) cancels *across* the two sides, after which `Real.exp` injectivity
> plus `E i ≠ E j` and `k_B > 0` force `T₁ = T₂`. `Fcal`, `N`, and the partition function
> `U` all cancel.
> 
> Non-vacuous: e.g. `ι = Fin 2`, `kB = 1`, `g = A = fun _ => 1`, `E = ![0,1]`
> (so `E 0 ≠ E 1`), `N = Fcal = 1`, any `T₁, T₂ > 0`. Then the ratio is
> `exp((E i − E j)/(kB·T))`, a non-constant function of `T`; equality genuinely
> forces `T₁ = T₂` (it depends on `Real.exp` injectivity, not `rfl`). 

### `CflibsFormal.temperature_not_identifiable_of_degenerate`

Module `CflibsFormal.Identifiability` · scope `EXACT`

```lean
CflibsFormal.temperature_not_identifiable_of_degenerate.{u_1} {ι : Type u_1} [Fintype ι]
  [Nonempty ι] {kB N Fcal : ℝ} {g E A : ι → ℝ} (hg : ∀ (k : ι), 0 < g k) (hN : 0 < N)
  (hFcal : 0 < Fcal) (hA : ∀ (k : ι), 0 < A k) (i j : ι) (hE : E i = E j) :
  ∃ T₁ T₂,
    0 < T₁ ∧
      0 < T₂ ∧
        T₁ ≠ T₂ ∧
          CflibsFormal.lineIntensity kB T₁ N Fcal g E A j /
              CflibsFormal.lineIntensity kB T₁ N Fcal g E A i =
            CflibsFormal.lineIntensity kB T₂ N Fcal g E A j /
              CflibsFormal.lineIntensity kB T₂ N Fcal g E A i
```

> **Degenerate pair ⇒ temperature NOT identifiable.** With a degenerate line pair
> (`E i = E j`), two genuinely different positive temperatures (here `T₁ = 1 ≠ 2 = T₂`, same
> density and calibration) produce the SAME two-line ratio observation — the formal converse of
> `temperature_identifiability`, exhibiting the non-injectivity directly. This grounds the
> runtime "small `ΔE` ⇒ refuse" gate of the strict-mode solver: at `ΔE = 0` the refusal is not
> heuristic caution but a theorem — NO algorithm can recover `T` from a degenerate pair's ratio,
> because the observation itself is constant in `T`. 

### `CflibsFormal.temperature_ratio_near_degenerate`

Module `CflibsFormal.Identifiability` · scope `EXACT`

```lean
CflibsFormal.temperature_ratio_near_degenerate.{u_1} {ι : Type u_1} [Fintype ι] [Nonempty ι]
  {kB T₁ T₂ N₁ N₂ Fcal₁ Fcal₂ : ℝ} {g E A : ι → ℝ} (hg : ∀ (k : ι), 0 < g k) (hN₁ : 0 < N₁)
  (hN₂ : 0 < N₂) (hFcal₁ : 0 < Fcal₁) (hFcal₂ : 0 < Fcal₂) (hA : ∀ (k : ι), 0 < A k) (i j : ι) :
  |CflibsFormal.lineIntensity kB T₁ N₁ Fcal₁ g E A j /
          CflibsFormal.lineIntensity kB T₁ N₁ Fcal₁ g E A i -
        CflibsFormal.lineIntensity kB T₂ N₂ Fcal₂ g E A j /
          CflibsFormal.lineIntensity kB T₂ N₂ Fcal₂ g E A i| ≤
    g j * A j / (g i * A i) *
          max (Real.exp ((E i - E j) / (kB * T₁))) (Real.exp ((E i - E j) / (kB * T₂))) *
        |E i - E j| *
      |1 / (kB * T₁) - 1 / (kB * T₂)|
```

> **Quantitative near-degeneracy — linear-in-`ΔE` temperature-conditioning bound.**
> 
> For positive atomic data (`g k > 0`, `A k > 0`), positive densities/calibrations, and any two
> temperatures `T₁, T₂` (via their inverse-temperature slots `1/(k_B·T_m)`), the two-line
> intensity ratio differs between the two parameter sets by at most a quantity **linear in**
> `|E_i − E_j|`:
> 
> `|ratio(T₁) − ratio(T₂)| ≤ ((g_j·A_j)/(g_i·A_i)) · C · |E_i − E_j| · |1/(k_B·T₁) − 1/(k_B·T₂)|`,
> 
> with the explicit constant `C = max(exp x₁, exp x₂)`, `x_m = (E_i − E_j)/(k_B·T_m)`.
> 
> Derivation (all steps EXACT, no approximation of the forward model): by
> `lineIntensity_ratio_closed_form` the difference is `(g_j·A_j)/(g_i·A_i)·(exp x₁ − exp x₂)`;
> `abs_exp_sub_le` gives `|exp x₁ − exp x₂| ≤ max(exp x₁, exp x₂)·|x₁ − x₂|`; and
> `x₁ − x₂ = (E_i − E_j)·(1/(k_B·T₁) − 1/(k_B·T₂))` factors the energy gap out of the argument
> difference. Everything (`Fcal`, `N`, the partition function `U`) cancels, exactly as in the
> identifiability theorems.
> 
> Physics reading: as `ΔE = E_i − E_j → 0` the right-hand side vanishes *linearly* in `ΔE`, so the
> temperature-dependence of the observed ratio — the entire signal a two-line thermometer has to
> work with — shrinks to zero at a controlled rate. Any measurement noise `ε` of fixed size then
> swamps the `O(ΔE)` signal, so `T` inference is ill-conditioned: this is the quantitative,
> finite-`ΔE` form of `temperature_degeneracy` (the `ΔE = 0` collapse), and it grounds the strict
> solver's *"small `ΔE` ⇒ refuse"* gate in a bound rather than a heuristic threshold. At `E_i = E_j`
> the factor `|E_i − E_j|` is `0`, so the bound forces `ratio(T₁) = ratio(T₂)`, recovering
> `temperature_degeneracy` as the exact limit (see the witness below). (Ciucci et al. 1999, the
> two-line Boltzmann ratio.) 

### `CflibsFormal.general_identifiability`

Module `CflibsFormal.Inverse` · scope `EXACT`

```lean
CflibsFormal.general_identifiability.{u_1, u_2} {species : Type u_1} {levelIndex : Type u_2}
  [Fintype species] [Fintype levelIndex] [Nonempty levelIndex] {kB Fcal₁ Fcal₂ : ℝ}
  {emit : species → levelIndex} {p₁ p₂ : CflibsFormal.PlasmaParams species levelIndex}
  (s₀ : species) (hkB : 0 < kB) (hFcal₁ : 0 < Fcal₁) (hFcal₂ : 0 < Fcal₂) (ha₁ : p₁.Admissible)
  (ha₂ : p₂.Admissible) (i j : levelIndex) (hE₁ : p₁.E i ≠ p₁.E j) (hEeq : p₁.E = p₂.E)
  (hgeq : p₁.g = p₂.g) (hAeq : p₁.A = p₂.A) (hFeq : Fcal₁ = Fcal₂)
  (hTratio :
    CflibsFormal.lineIntensity kB p₁.T (p₁.N s₀) Fcal₁ p₁.g p₁.E p₁.A j /
        CflibsFormal.lineIntensity kB p₁.T (p₁.N s₀) Fcal₁ p₁.g p₁.E p₁.A i =
      CflibsFormal.lineIntensity kB p₂.T (p₂.N s₀) Fcal₂ p₂.g p₂.E p₂.A j /
        CflibsFormal.lineIntensity kB p₂.T (p₂.N s₀) Fcal₂ p₂.g p₂.E p₂.A i)
  (hObs : CflibsFormal.observe kB Fcal₁ emit p₁ = CflibsFormal.observe kB Fcal₂ emit p₂) :
  p₁.T = p₂.T ∧
    ∀ (s : species), CflibsFormal.trueComposition p₁ s = CflibsFormal.trueComposition p₂ s
```

> **General identifiability — the central theorem.**
> 
> Under explicit nondegeneracy (positive `T`, `N`, `g`, `A` via `Admissible`; one
> emitting line per species via `emit`; an additional assumed two-line Boltzmann ratio
> `hTratio` on a distinct-energy pair `(i,j)` that fixes `T`), if two admissible
> parameter sets produce **equal observations** `hObs`, share calibration (`hFeq`) and
> atomic data (`hgeq`, `hEeq`, `hAeq`), then they have **equal temperature** and
> **equal composition**.
> 
> *Honest scoping.* The temperature equality is delivered by `hTratio` — an additional
> assumed two-line Boltzmann ratio on a distinct-energy pair — **not** by `hObs`. The
> one-line-per-species observation map `observe` constrains only the emitting lines
> `emit s`; the distinct-energy pair `(i,j)` that pins `T` need not be observed. The
> composition equality is then extracted from `hObs` **once the temperatures are matched**:
> the proof first uses `hT` (derived from `hTratio`) to bring the two per-species line
> intensities to a common temperature, and only then does `density_identifiability` force
> equal `N s` for every species (hence equal closure composition). So composition rests on
> `hObs` PLUS the matched temperature (from `hTratio`), matched calibration, and atomic
> data — not on `hObs` alone.
> 
> Assembled strictly from the already-proven `temperature_identifiability` and
> `density_identifiability` (neither reproven), plus `Closure.composition`.
> 
> Non-vacuous: take `species = Fin 1`, `levelIndex = Fin 2`, `kB = Fcal₁ = Fcal₂ = 1`,
> `emit = fun _ => 0`, `p₁ = p₂` with `T = 1`, `N = g = A = fun _ => 1`, `E = ![0,1]`.
> Then `E i ≠ E j` (`0 ≠ 1`), `Admissible` holds, the ratio and observation equalities
> are reflexive, and the conclusion holds; the content (for differing parameter sets) is
> that `hTratio` forces `T₁ = T₂` via `Real.exp` injectivity and `hObs` forces equal
> composition via positive-constant cancellation — neither is `rfl`. 

### `CflibsFormal.jointConvergence`

Module `CflibsFormal.JointConvergence` · scope `REDUCED`

```lean
CflibsFormal.jointConvergence.{u_1, u_2, u_3} {ιe : Type u_1} [Fintype ιe] [Nonempty ιe]
  {κe : Type u_2} [Fintype κe] [Nonempty κe] {ιl : Type u_3} [Fintype ιl] [Nonempty ιl]
  {kB me h chi R0 R : ℝ} {gZ EZ : ιe → ℝ} {gZ1 EZ1 : κe → ℝ} {E yb svec : ιl → ℝ}
  {offConst Tmin Tmax nemin nemax smin : ℝ} (hTle : Tmin ≤ Tmax) (hnele : nemin ≤ nemax)
  (hkB : 0 < kB) (hme : 0 < me) (hh : 0 < h) (hchi : 0 ≤ chi) (hTmin : 0 < Tmin)
  (hgZ : ∀ (k : ιe), 0 < gZ k) (hEZ : ∀ (k : ιe), 0 ≤ EZ k) (hgZ1 : ∀ (k : κe), 0 < gZ1 k)
  (hEZ1 : ∀ (k : κe), 0 ≤ EZ1 k) (hEχ : ∀ (k : ιe), EZ k ≤ chi) (hR0 : 0 < R0) (hR : R0 ≤ R)
  (hvar : 0 < ∑ k, (E k - CflibsFormal.mean E) ^ 2) (hnemin : 0 < nemin) (hsmin : 0 < smin)
  (hnelo : nemin ≤ CflibsFormal.electronDensityFromRatio kB Tmin me h chi gZ EZ gZ1 EZ1 R)
  (hnehi : CflibsFormal.electronDensityFromRatio kB Tmax me h chi gZ EZ gZ1 EZ1 R ≤ nemax)
  (hmapsT :
    ∀ ne ∈ Set.Icc nemin nemax,
      CflibsFormal.combinedSlopeTempUpdate kB E yb svec offConst ne ∈ Set.Icc Tmin Tmax)
  (hslopeFloor :
    ∀ ne ∈ Set.Icc nemin nemax,
      smin ≤ CflibsFormal.combinedSahaBoltzmannSlope E yb svec offConst ne)
  (hL1nn : 0 ≤ CflibsFormal.sahaFactorLipConst kB Tmin Tmax me h chi gZ EZ gZ1 EZ1 / R0)
  (hgate :
    max
        ((|∑ k, (E k - CflibsFormal.mean E) * svec k| / ∑ k, (E k - CflibsFormal.mean E) ^ 2) /
          (kB * smin ^ 2 * nemin))
        (CflibsFormal.sahaFactorLipConst kB Tmin Tmax me h chi gZ EZ gZ1 EZ1 / R0) <
      1) :
  ∃ pstar ∈ Set.Icc Tmin Tmax ×ˢ Set.Icc nemin nemax,
    CflibsFormal.jointOuterMap
          (fun x ne => CflibsFormal.combinedSlopeTempUpdate kB E yb svec offConst ne)
          (fun T x => CflibsFormal.electronDensityFromRatio kB T me h chi gZ EZ gZ1 EZ1 R) pstar =
        pstar ∧
      (∀ p ∈ Set.Icc Tmin Tmax ×ˢ Set.Icc nemin nemax,
          CflibsFormal.jointOuterMap
                (fun x ne => CflibsFormal.combinedSlopeTempUpdate kB E yb svec offConst ne)
                (fun T x => CflibsFormal.electronDensityFromRatio kB T me h chi gZ EZ gZ1 EZ1 R) p =
              p →
            p = pstar) ∧
        ∀ p0 ∈ Set.Icc Tmin Tmax ×ˢ Set.Icc nemin nemax,
          Filter.Tendsto
            (fun n =>
              (CflibsFormal.jointOuterMap
                    (fun x ne => CflibsFormal.combinedSlopeTempUpdate kB E yb svec offConst ne)
                    fun T x =>
                    CflibsFormal.electronDensityFromRatio kB T me h chi gZ EZ gZ1 EZ1 R)^[n]
                p0)
            Filter.atTop (nhds pstar)
```

> **The CF-LIBS joint `(T, n_e)` outer loop contracts** (`REDUCED`; Aguilera & Aragón 2007,
> Model B; Saha–Eggert (Griem)). Instantiating the abstract 2-D box Banach theorem
> `jointOuterContraction_box` at the anti-diagonal CF-LIBS legs `fT (T,n_e) =
> combinedSlopeTempUpdate … n_e` and `fNe (T,n_e) = electronDensityFromRatio … T … R`: the joint
> sweep `Φ (T,n_e) = (fT T n_e, fNe T n_e)` on the box `[Tmin,Tmax] ×ˢ [nemin,nemax]` has a
> **unique** self-consistent fixed point `pstar`, and the iterates `Φ^[n] p0` converge to `pstar`
> jointly in both coordinates (product metric) from every start in the box. The density
> interval-invariance is discharged a-priori from the endpoint containments `hnelo`/`hnehi`; the
> gate `max L₂ L₁ < 1` is the carried convergence certificate. 

### `CflibsFormal.homologousPair_ratio_closed_form`

Module `CflibsFormal.MatrixEffects` · scope `EXACT`

```lean
CflibsFormal.homologousPair_ratio_closed_form.{u_2} {ι : Type u_2} [Fintype ι] [Nonempty ι]
  {kB T Ns Nt Fcal : ℝ} {g E A : ι → ℝ} (hg : ∀ (k : ι), 0 < g k) (hNt : 0 < Nt) (hFcal : 0 < Fcal)
  (hA : ∀ (k : ι), 0 < A k) (s t : ι) :
  CflibsFormal.lineIntensity kB T Ns Fcal g E A s /
      CflibsFormal.lineIntensity kB T Nt Fcal g E A t =
    Ns * g s * A s / (Nt * g t * A t) * Real.exp ((E t - E s) / (kB * T))
```

> **Cross-species two-line ratio — closed form (shared partition function).** For two species
> with designated-line densities `N_s, N_t` emitting from a COMMON atomic-data family `(g, E, A)` at
> one temperature `T`, the intensity ratio is
> `I_s/I_t = ((N_s·g_s·A_s)/(N_t·g_t·A_t)) · exp((E_t − E_s)/(k_B T))`:
> the calibration `Fcal` and the shared partition function `U(T)` cancel EXACTLY. The whole
> temperature dependence of the ratio is the single Boltzmann exponential in the energy GAP
> `E_t − E_s`. (Ciucci et al. 1999, the two-line Boltzmann ratio; here across two species.) 

### `CflibsFormal.homologousPair_ratio_perU_closed_form`

Module `CflibsFormal.MatrixEffects` · scope `EXACT`

```lean
CflibsFormal.homologousPair_ratio_perU_closed_form.{u_2} {ι : Type u_2} {kB T Ns Nt Fcal Us Ut : ℝ}
  {g E A : ι → ℝ} (hg : ∀ (k : ι), 0 < g k) (hNt : 0 < Nt) (hFcal : 0 < Fcal)
  (hA : ∀ (k : ι), 0 < A k) (hUs : 0 < Us) (hUt : 0 < Ut) (s t : ι) :
  CflibsFormal.lineIntensityPerU kB T Ns Fcal Us g E A s /
      CflibsFormal.lineIntensityPerU kB T Nt Fcal Ut g E A t =
    Ns * g s * A s * Ut / (Nt * g t * A t * Us) * Real.exp ((E t - E s) / (kB * T))
```

> **Per-species-`U` two-line ratio — closed form with the `U`-residual explicit.** With
> GENUINELY per-species partition functions `U_s, U_t` (each summed over its own species' internal
> manifold, carried as `MultiSpecies.lineIntensityPerU` scalars) and per-species designated-line data
> `(g_s, E_s, A_s)`, `(g_t, E_t, A_t)`, the intensity ratio is
> `I_s/I_t = ((N_s·g_s·A_s·U_t)/(N_t·g_t·A_t·U_s)) · exp((E_t − E_s)/(k_B T))`.
> Energy matching `E_s = E_t` collapses the exponential to `1`, leaving the ratio's ENTIRE residual
> equal to the partition-function ratio `U_t/U_s` — the honest per-species form of the
> homologous-pair identity (the shared-`U` `homologousPair_ratio_closed_form` is the case
> `U_s = U_t`). **Scope EXACT** for the fixed-`T` identity; `U_s, U_t` are free positive inputs. 

### `CflibsFormal.homologousPair_ratio_perU_temperature_invariant`

Module `CflibsFormal.MatrixEffects` · scope `REDUCED`

```lean
CflibsFormal.homologousPair_ratio_perU_temperature_invariant.{u_2} {ι : Type u_2}
  {kB T T' Ns Nt Fcal Us Ut : ℝ} {g E A : ι → ℝ} (hg : ∀ (k : ι), 0 < g k) (hNt : 0 < Nt)
  (hFcal : 0 < Fcal) (hA : ∀ (k : ι), 0 < A k) (hUs : 0 < Us) (hUt : 0 < Ut) (s t : ι)
  (hE : E s = E t) :
  CflibsFormal.lineIntensityPerU kB T Ns Fcal Us g E A s /
      CflibsFormal.lineIntensityPerU kB T Nt Fcal Ut g E A t =
    CflibsFormal.lineIntensityPerU kB T' Ns Fcal Us g E A s /
      CflibsFormal.lineIntensityPerU kB T' Nt Fcal Ut g E A t
```

> **Per-species-`U` homologous-pair temperature invariance (REDUCED).** In the per-species-`U`
> forward model, a homologous pair (`E_s = E_t`) has a temperature-invariant intensity ratio
> `I_s(T)/I_t(T) = I_s(T')/I_t(T')`, its common value the residual
> `(N_s·g_s·A_s·U_t)/(N_t·g_t·A_t·U_s)`.
> **REDUCED**, not EXACT: `MultiSpecies.lineIntensityPerU` carries each `U_s` as a per-shot scalar
> INPUT, so varying `T` here holds `U_s, U_t` fixed. It therefore isolates the Boltzmann/exponential
> temperature channel (killed exactly by energy matching) from the genuine per-species drift
> `U_s(T)/U_t(T)`, which is the physical residual left OUT of scope (the shared-`U`
> `homologousPair_ratio_temperature_invariant` is EXACT because there the single `U(T)` cancels
> regardless of its `T`-dependence). 

### `CflibsFormal.homologousPair_ratio_temperature_invariant`

Module `CflibsFormal.MatrixEffects` · scope `EXACT`

```lean
CflibsFormal.homologousPair_ratio_temperature_invariant.{u_2} {ι : Type u_2} [Fintype ι]
  [Nonempty ι] {kB T T' Ns Nt Fcal : ℝ} {g E A : ι → ℝ} (hg : ∀ (k : ι), 0 < g k) (hNt : 0 < Nt)
  (hFcal : 0 < Fcal) (hA : ∀ (k : ι), 0 < A k) (s t : ι) (hE : E s = E t) :
  CflibsFormal.lineIntensity kB T Ns Fcal g E A s /
      CflibsFormal.lineIntensity kB T Nt Fcal g E A t =
    CflibsFormal.lineIntensity kB T' Ns Fcal g E A s /
      CflibsFormal.lineIntensity kB T' Nt Fcal g E A t
```

> **THE per-shot-`T` deliverable — homologous-pair exact temperature invariance.** For a
> homologous pair (two species' designated lines with EQUAL upper-level energies `E_s = E_t`, drawn
> from a common partition-function manifold), the two-species intensity ratio is the SAME at ANY two
> temperatures `T`, `T'`:
> `I_s(T)/I_t(T) = I_s(T')/I_t(T')`.
> The Boltzmann exponentials cancel identically at the matched energy and the shared `U(T)` cancels,
> so per-shot temperature jitter leaves the ratio invariant — the exact ground of the
> homologous-line-pair technique. No positivity of `T`, `T'` is needed: the collapse is total (both
> sides equal the `T`-free constant `(N_s·g_s·A_s)/(N_t·g_t·A_t)`). This is the CROSS-species
> (`N_s ≠ N_t`) form; the same-species sibling is `Identifiability.temperature_degeneracy`. 

### `CflibsFormal.nonHomologousPair_ratio_temperature_dependent`

Module `CflibsFormal.MatrixEffects` · scope `EXACT`

```lean
CflibsFormal.nonHomologousPair_ratio_temperature_dependent.{u_2} {ι : Type u_2} [Fintype ι]
  [Nonempty ι] {kB T T' Ns Nt Fcal : ℝ} {g E A : ι → ℝ} (hkB : 0 < kB) (hT : 0 < T) (hT' : 0 < T')
  (hTT' : T ≠ T') (hg : ∀ (k : ι), 0 < g k) (hNs : 0 < Ns) (hNt : 0 < Nt) (hFcal : 0 < Fcal)
  (hA : ∀ (k : ι), 0 < A k) (s t : ι) (hE : E s ≠ E t) :
  CflibsFormal.lineIntensity kB T Ns Fcal g E A s /
      CflibsFormal.lineIntensity kB T Nt Fcal g E A t ≠
    CflibsFormal.lineIntensity kB T' Ns Fcal g E A s /
      CflibsFormal.lineIntensity kB T' Nt Fcal g E A t
```

> **Contrast — invariance is a property OF the energy matching.** With DISTINCT upper-level
> energies `E_s ≠ E_t` the two-species intensity ratio genuinely varies with temperature: at two
> distinct positive temperatures `T ≠ T'` (with `k_B > 0`) the ratios differ. The surviving
> Boltzmann factor `exp((E_t − E_s)/(k_B T))` is a non-constant function of `T` once `ΔE ≠ 0`, so
> `homologousPair_ratio_temperature_invariant` genuinely requires the homologous (`E_s = E_t`)
> hypothesis. (Ciucci et al. 1999, the two-line Boltzmann ratio.) 

### `CflibsFormal.envelope_ionization_matrix_shift`

Module `CflibsFormal.MatrixIonizationCoupling` · scope `REDUCED`

```lean
CflibsFormal.envelope_ionization_matrix_shift.{u_1, u_2} {ι : Type u_1} [Fintype ι] [Nonempty ι]
  (S S' Ntot : ι → ℝ) (hS : ∀ (s : ι), 0 < S s) (hS' : ∀ (s : ι), 0 < S' s)
  (hN : ∀ (s : ι), 0 < Ntot s) (hmono : ∀ (s : ι), S s ≤ S' s) {s0 : ι} (hs0 : S s0 < S' s0)
  {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hxeq : x = CflibsFormal.multiElementIonized S Ntot x)
  (hyeq : y = CflibsFormal.multiElementIonized S' Ntot y) {Sspec Nspec : ℝ} (hSspec : 0 < Sspec)
  (hNspec : 0 < Nspec) {μ : Type u_2} [Fintype μ] [Nonempty μ] {kB Told Tnew Ns Nt Fcal : ℝ}
  {g E A : μ → ℝ} (hg : ∀ (k : μ), 0 < g k) (hNt : 0 < Nt) (hFcal : 0 < Fcal)
  (hA : ∀ (k : μ), 0 < A k) (a b : μ) (hE : E a = E b) :
  x < y ∧
    CflibsFormal.sahaIonDensity Sspec Nspec y < CflibsFormal.sahaIonDensity Sspec Nspec x ∧
      CflibsFormal.lineIntensity kB Told Ns Fcal g E A a /
          CflibsFormal.lineIntensity kB Told Nt Fcal g E A b =
        CflibsFormal.lineIntensity kB Tnew Ns Fcal g E A a /
          CflibsFormal.lineIntensity kB Tnew Nt Fcal g E A b
```

> **Ionization-suppression matrix-shift envelope (`REDUCED` comparative statics + `EXACT`
> homologous invariance; Saha–Eggert/Griem, Aguilera & Aragón 2007, Ciucci et al. 1999).**
> Making one species strictly more easily ionized simultaneously yields:
> 
> * `x < y` — the shared coupled electron density strictly increases;
> * `sahaIonDensity Sspec Nspec y < sahaIonDensity Sspec Nspec x` — a spectator element's ion
>   density strictly **drops**: its ionization is suppressed by exactly the induced `n_e`
>   shift (`sahaIonDensity_antitone` at `x < y`); this is the genuine, nonzero matrix effect,
>   whose sign is fixed by the comparative statics;
> * the **homologous-line-pair** intensity ratio (matched upper-level energies `E a = E b`,
>   shared partition-function manifold) is invariant across the box temperatures
>   `Told, Tnew` (`homologousPair_ratio_temperature_invariant`).
> 
> In this Boltzmann-only intensity encoding the homologous ratio depends on neither `T` nor
> `n_e`, so the induced `n_e` shift leaves the reported homologous subcomposition ratio exactly
> unchanged (matrix effect zero, a fortiori bounded by the `n_e` shift); the physical residual
> lives entirely in the spectator ionization suppression above. 

### `CflibsFormal.deNormalizedDensity_eq_deNormalizedDensityPerU`

Module `CflibsFormal.MultiSpecies` · scope `PURE-MATH`

```lean
CflibsFormal.deNormalizedDensity_eq_deNormalizedDensityPerU.{u_1} {ι : Type u_1} [Fintype ι]
  (kB T Fcal : ℝ) (g E A : ι → ℝ) (s : ι) (I : ℝ) :
  CflibsFormal.deNormalizedDensity kB T Fcal g E A s I =
    CflibsFormal.deNormalizedDensityPerU kB T Fcal (CflibsFormal.partitionFunction kB T g E) g E A s
      I
```

> **Shared-`U` reader is the per-`U` reader at `Us = partitionFunction kB T g E`.**
> Definitional bridge (`rfl`) making `deNormalizedDensity` a special case of
> `deNormalizedDensityPerU`. 

### `CflibsFormal.deNormalized_lineIntensity`

Module `CflibsFormal.MultiSpecies` · scope `EXACT`

```lean
CflibsFormal.deNormalized_lineIntensity.{u_1} {ι : Type u_1} [Fintype ι] [Nonempty ι]
  {kB T N Fcal : ℝ} {g E A : ι → ℝ} (hg : ∀ (k : ι), 0 < g k) (hN : 0 < N) (hFcal : 0 < Fcal)
  (hA : ∀ (k : ι), 0 < A k) (s : ι) :
  CflibsFormal.deNormalizedDensity kB T Fcal g E A s
      (CflibsFormal.lineIntensity kB T N Fcal g E A s) =
    N
```

> **Inversion identity.** De-normalizing the forward line intensity of species `s`
> (divide out `Fcal`, `A s`, `g s`, the Boltzmann factor, multiply by `U`) recovers the
> species number density `N` exactly. This is the per-species half of the
> density-from-intensity bridge and the lemma the ratio theorem rests on. 

### `CflibsFormal.deNormalized_lineIntensity_ofPerU`

Module `CflibsFormal.MultiSpecies` · scope `EXACT`

```lean
CflibsFormal.deNormalized_lineIntensity_ofPerU.{u_1} {ι : Type u_1} [Fintype ι] [Nonempty ι]
  {kB T N Fcal : ℝ} {g E A : ι → ℝ} (hg : ∀ (k : ι), 0 < g k) (hFcal : 0 < Fcal)
  (hA : ∀ (k : ι), 0 < A k) (s : ι) :
  CflibsFormal.deNormalizedDensity kB T Fcal g E A s
      (CflibsFormal.lineIntensity kB T N Fcal g E A s) =
    N
```

> **Shared-`U` inversion identity as a special case of the per-`U` one.** Re-derives the
> `deNormalized_lineIntensity` statement by specializing `deNormalized_lineIntensity_perU` to
> `Us = partitionFunction kB T g E` via the `rfl`-bridges — witnessing that the shared-`U`
> inversion is not an independent claim. (The original `deNormalized_lineIntensity` above is
> retained verbatim for downstream importers.) 

### `CflibsFormal.deNormalized_lineIntensity_perU`

Module `CflibsFormal.MultiSpecies` · scope `EXACT`

```lean
CflibsFormal.deNormalized_lineIntensity_perU.{u_1} {ι : Type u_1} {kB T N Fcal Us : ℝ}
  {g E A : ι → ℝ} (hg : ∀ (k : ι), 0 < g k) (hFcal : 0 < Fcal) (hA : ∀ (k : ι), 0 < A k)
  (hUs : 0 < Us) (s : ι) :
  CflibsFormal.deNormalizedDensityPerU kB T Fcal Us g E A s
      (CflibsFormal.lineIntensityPerU kB T N Fcal Us g E A s) =
    N
```

> **Per-species inversion identity.** De-normalizing species `s`'s per-`U` forward line
> intensity recovers its number density `N` exactly, using the species' own partition function
> `Us`. Genuine multi-element generalization of `deNormalized_lineIntensity`; note the proof
> needs only `0 < Us` (a per-species positivity), and — unlike the shared-`U` version — no
> `Nonempty ι` and no `0 < N`. 

### `CflibsFormal.density_ratio_from_intensities`

Module `CflibsFormal.MultiSpecies` · scope `EXACT`

```lean
CflibsFormal.density_ratio_from_intensities.{u_1} {ι : Type u_1} [Fintype ι] [Nonempty ι]
  {kB T Ns Nt Fcal : ℝ} {g E A : ι → ℝ} (hg : ∀ (k : ι), 0 < g k) (hNs : 0 < Ns) (hNt : 0 < Nt)
  (hFcal : 0 < Fcal) (hA : ∀ (k : ι), 0 < A k) (s t : ι) :
  CflibsFormal.deNormalizedDensity kB T Fcal g E A s
        (CflibsFormal.lineIntensity kB T Ns Fcal g E A s) /
      CflibsFormal.deNormalizedDensity kB T Fcal g E A t
        (CflibsFormal.lineIntensity kB T Nt Fcal g E A t) =
    Ns / Nt
```

> **Density-from-intensity bridge.** At a common temperature `T` and common
> calibration `Fcal`, with one designated emitting level per species, the ratio of two
> species' partition-function-and-degeneracy-de-normalized line intensities equals the
> ratio `N_s / N_t` of their number densities. Hence relative composition is fixed by the
> measured intensities and atomic data at known `T`. The two intensities carry different
> densities `Ns`, `Nt` but share `kB, T, Fcal, g, E, A` — two species emitting under the
> same plasma conditions and (single-family) atomic data. 

### `CflibsFormal.density_ratio_from_intensities_ofPerU`

Module `CflibsFormal.MultiSpecies` · scope `EXACT`

```lean
CflibsFormal.density_ratio_from_intensities_ofPerU.{u_1} {ι : Type u_1} [Fintype ι] [Nonempty ι]
  {kB T Ns Nt Fcal : ℝ} {g E A : ι → ℝ} (hg : ∀ (k : ι), 0 < g k) (hFcal : 0 < Fcal)
  (hA : ∀ (k : ι), 0 < A k) (s t : ι) :
  CflibsFormal.deNormalizedDensity kB T Fcal g E A s
        (CflibsFormal.lineIntensity kB T Ns Fcal g E A s) /
      CflibsFormal.deNormalizedDensity kB T Fcal g E A t
        (CflibsFormal.lineIntensity kB T Nt Fcal g E A t) =
    Ns / Nt
```

> **Shared-`U` ratio theorem as a special case of the per-`U` one.** Re-derives
> `density_ratio_from_intensities` by specializing `density_ratio_from_intensities_perU` to
> `Us = Ut = partitionFunction kB T g E`. Notably it needs neither `0 < Ns` nor `0 < Nt`,
> which the per-`U` inversion made unnecessary. 

### `CflibsFormal.density_ratio_from_intensities_perU`

Module `CflibsFormal.MultiSpecies` · scope `EXACT`

```lean
CflibsFormal.density_ratio_from_intensities_perU.{u_1} {ι : Type u_1} {kB T Ns Nt Fcal Us Ut : ℝ}
  {g E A : ι → ℝ} (hg : ∀ (k : ι), 0 < g k) (hFcal : 0 < Fcal) (hA : ∀ (k : ι), 0 < A k)
  (hUs : 0 < Us) (hUt : 0 < Ut) (s t : ι) :
  CflibsFormal.deNormalizedDensityPerU kB T Fcal Us g E A s
        (CflibsFormal.lineIntensityPerU kB T Ns Fcal Us g E A s) /
      CflibsFormal.deNormalizedDensityPerU kB T Fcal Ut g E A t
        (CflibsFormal.lineIntensityPerU kB T Nt Fcal Ut g E A t) =
    Ns / Nt
```

> **Per-species density-from-intensity bridge.** With *genuinely per-species* partition
> functions `Us, Ut` (each summed over its own species' level manifold) and per-species
> designated-line data `(g s, E s, A s)` / `(g t, E t, A t)`, at a common temperature `T` and
> calibration `Fcal`, the ratio of the two species' `U`-de-normalized line intensities equals
> the true density ratio `N_s / N_t`. Hence relative composition is fixed by the measured
> intensities and per-species atomic data at known `T`, with no shared-`U` assumption. The
> shared-`U` `density_ratio_from_intensities` is the special case `Us = Ut =
> partitionFunction kB T g E` (`density_ratio_from_intensities_ofPerU`). 

### `CflibsFormal.lineIntensity_eq_lineIntensityPerU`

Module `CflibsFormal.MultiSpecies` · scope `PURE-MATH`

```lean
CflibsFormal.lineIntensity_eq_lineIntensityPerU.{u_1} {ι : Type u_1} [Fintype ι] (kB T N Fcal : ℝ)
  (g E A : ι → ℝ) (s : ι) :
  CflibsFormal.lineIntensity kB T N Fcal g E A s =
    CflibsFormal.lineIntensityPerU kB T N Fcal (CflibsFormal.partitionFunction kB T g E) g E A s
```

> **Shared-`U` forward map is the per-`U` forward map at `Us = partitionFunction kB T g E`.**
> Definitional bridge (`rfl`) making `lineIntensity` a special case of `lineIntensityPerU`. 

### `CflibsFormal.speciesComposition_ratio_from_intensities_perU`

Module `CflibsFormal.MultiSpecies` · scope `EXACT`

```lean
CflibsFormal.speciesComposition_ratio_from_intensities_perU.{u_1} {ι : Type u_1} [Fintype ι]
  {kB T Fcal Us Ut : ℝ} {g E A N : ι → ℝ} (hg : ∀ (k : ι), 0 < g k) (hFcal : 0 < Fcal)
  (hA : ∀ (k : ι), 0 < A k) (hUs : 0 < Us) (hUt : 0 < Ut) (hD : CflibsFormal.totalDensity N ≠ 0)
  (s t : ι) :
  CflibsFormal.deNormalizedDensityPerU kB T Fcal Us g E A s
        (CflibsFormal.lineIntensityPerU kB T (N s) Fcal Us g E A s) /
      CflibsFormal.deNormalizedDensityPerU kB T Fcal Ut g E A t
        (CflibsFormal.lineIntensityPerU kB T (N t) Fcal Ut g E A t) =
    CflibsFormal.speciesComposition N s / CflibsFormal.speciesComposition N t
```

> **Relative composition from intensities (per-species `U`).** The elemental
> number-fraction ratio `C_s / C_t` of two species equals the ratio of their per-`U`
> de-normalized designated-line intensities — relative composition is fixed by the measured
> intensities and per-species atomic data at known `T`, with genuinely per-species partition
> functions `Us, Ut`. Combines `density_ratio_from_intensities_perU` with
> `speciesComposition_ratio`. 

### `CflibsFormal.noise_to_density`

Module `CflibsFormal.NoiseToComposition` · scope `REDUCED`

```lean
CflibsFormal.noise_to_density.{u_1, u_3} {ι : Type u_1} [Fintype ι] {ιT : Type u_3} [Fintype ιT]
  [Nonempty ι] [Nonempty ιT] {kB Tmin Tmax T That Fcal N : ℝ} {ET yT yHatT epsT : ιT → ℝ}
  {g E A : ι → ℝ} {u k0 : ι} (hkB : 0 < kB) (hTmin : 0 < Tmin) (hT : Tmin ≤ T) (hThat : Tmin ≤ That)
  (hTmaxT : T ≤ Tmax) (hTmaxThat : That ≤ Tmax) (hg : ∀ (k : ι), 0 < g k) (hE : ∀ (k : ι), 0 ≤ E k)
  (hFcal : 0 < Fcal) (hA : 0 < A u) (hN : 0 < N)
  (hvarT : 0 < ∑ k, (ET k - CflibsFormal.mean ET) ^ 2) (hδT : ∀ (k : ιT), |yHatT k - yT k| ≤ epsT k)
  (hβ : CflibsFormal.olsSlope ET yT = 1 / (kB * T))
  (hβHat : CflibsFormal.olsSlope ET yHatT = 1 / (kB * That))
  (hsmall :
    Real.exp (E u * CflibsFormal.noiseTempGapBound kB Tmax ET epsT / (kB * Tmin ^ 2)) - 1 < 1) :
  |CflibsFormal.Classic.classicDensity kB That Fcal g E A u
          (CflibsFormal.lineIntensity kB T N Fcal g E A u) -
        N| ≤
    N *
      CflibsFormal.tempResponseErrorBoundOfGap kB Tmin
        (CflibsFormal.noiseTempGapBound kB Tmax ET epsT) g E u k0
```

> **Noise ⇒ per-species recovered-density error (REDUCED, Tognoni 2010).** The single-species
> composition of two reused legs. The temperature gap is bounded by the noise
> (`noise_to_temperatureGap`), fed into the temperature-density bound
> `AtomicDataPerturbation.classicDensity_temperature_aliasing_error`, and the exact gap `|T̂ − T|` is
> replaced by the noise-derived worst-case gap `dmax = noiseTempGapBound kB Tmax E ε` via
> `tempResponseErrorBoundOfGap_mono`:
>   `|N̂ − N| ≤ N · tempResponseErrorBoundOfGap kB Tmin dmax g E u k0`.
> The exp-channel smallness `hsmall` is required at `dmax` (the worst case), whence it holds at the
> actual gap. Reduction: inherits the temperature and density legs' reductions (worst-case slope,
> `Tmax` over-estimate, non-sharp response constants). 

### `CflibsFormal.Nsection_minimizer_unique`

Module `CflibsFormal.NonlinearLeastSquares` · scope `REDUCED`

```lean
CflibsFormal.Nsection_minimizer_unique.{u_1} {ι : Type u_1} [Fintype ι] (kB Fcal T : ℝ)
  (g E A obs : ι → ℝ) (hc : 0 < ∑ k, CflibsFormal.lineIntensity kB T 1 Fcal g E A k ^ 2) {N : ℝ}
  (hmin :
    ∀ (N' : ℝ),
      CflibsFormal.nlObjective kB Fcal g E A obs (T, N) ≤
        CflibsFormal.nlObjective kB Fcal g E A obs (T, N')) :
  N = CflibsFormal.profiledDensity kB Fcal g E A obs T
```

> **Uniqueness of the `N`-section minimizer (headline, REDUCED).** For a fixed `T` with
> `0 < ∑ₖ c_k²`, any density `N` that minimizes the `N`-section — `nlObjective … (T, N) ≤
> nlObjective … (T, N')` for all `N'` — must equal the profiled density `N̂(T)`. If it did not,
> `nlObjective_Nsection_lt_of_ne` would make `N̂(T)` strictly better, contradicting minimality of `N`.
> So the `N`-coordinate of every joint minimizer is *pinned* to `N̂(T̂)` by its `T`-coordinate: the
> joint 2-D CF-LIBS fit is provably 1-D in `T`. This is the variable-projection reduction the solver
> exploits (Tognoni et al. 2010); `T`-uniqueness stays open (non-convex objective). 

### `CflibsFormal.clean_residual_ratio`

Module `CflibsFormal.NonlinearLeastSquares` · scope `EXACT`

```lean
CflibsFormal.clean_residual_ratio {kB Fcal T0 N0 T : ℝ} {g E A obs : Fin 2 → ℝ}
  (hg : ∀ (k : Fin 2), 0 < g k) (hFcal : 0 < Fcal) (hA : ∀ (k : Fin 2), 0 < A k)
  (hobs : ∀ (k : Fin 2), obs k = CflibsFormal.lineIntensity kB T0 N0 Fcal g E A k) :
  CflibsFormal.nlObjective kB Fcal g E A obs (T, CflibsFormal.profiledDensity kB Fcal g E A obs T) =
    N0 ^ 2 * CflibsFormal.lineIntensity kB T0 1 Fcal g E A 0 ^ 2 *
        (CflibsFormal.lineIntensity kB T 1 Fcal g E A 1 /
              CflibsFormal.lineIntensity kB T 1 Fcal g E A 0 -
            CflibsFormal.lineIntensity kB T0 1 Fcal g E A 1 /
              CflibsFormal.lineIntensity kB T0 1 Fcal g E A 0) ^
          2 /
      (1 +
        (CflibsFormal.lineIntensity kB T 1 Fcal g E A 1 /
            CflibsFormal.lineIntensity kB T 1 Fcal g E A 0) ^
          2)
```

> On-manifold, the two-line profiled residual in the intensity-ratio coordinate. 

### `CflibsFormal.joint_onManifold_unique`

Module `CflibsFormal.NonlinearLeastSquares` · scope `EXACT`

```lean
CflibsFormal.joint_onManifold_unique.{u_1} {ι : Type u_1} [Fintype ι] [Nonempty ι]
  {kB Fcal T0 N0 : ℝ} {g E A obs : ι → ℝ} (hkB : 0 < kB) (hg : ∀ (k : ι), 0 < g k)
  (hFcal : 0 < Fcal) (hA : ∀ (k : ι), 0 < A k) (hN0 : 0 < N0) (hT0 : 0 < T0) (i j : ι)
  (hE : E i ≠ E j) (hobs : ∀ (k : ι), obs k = CflibsFormal.lineIntensity kB T0 N0 Fcal g E A k)
  {p : ℝ × ℝ} (hp : 0 < p.1) : CflibsFormal.nlObjective kB Fcal g E A obs p = 0 ↔ p = (T0, N0)
```

> **Joint `(T, N)` on-manifold uniqueness (EXACT, Ciucci 1999).** For any parameter pair `p` with
> positive temperature `0 < p.1`, the joint objective vanishes **iff** `p` is exactly the true
> parameters: `nlObjective … p = 0 ↔ p = (T₀, N₀)`, given one distinct-energy pair. This is the full
> argmin uniqueness that the `N`-VARPRO reduction and `profiledT_onManifold_unique` combine to give:
> a zero residual forces an exact fit at every line, which pins `T = T₀` (the ratio argument) and then
> `N = N₀` (cancel `c_i(T₀) > 0`). Upgrades `nlObjective_onManifold_min` from "value `0` at the true
> parameters" to "`(T₀, N₀)` is the *only* zero of the residual among positive temperatures". 

### `CflibsFormal.lineIntensity_linear_in_N`

Module `CflibsFormal.NonlinearLeastSquares` · scope `EXACT`

```lean
CflibsFormal.lineIntensity_linear_in_N.{u_1} {ι : Type u_1} [Fintype ι] (kB T N Fcal : ℝ)
  (g E A : ι → ℝ) (k : ι) :
  CflibsFormal.lineIntensity kB T N Fcal g E A k =
    N * CflibsFormal.lineIntensity kB T 1 Fcal g E A k
```

> **Linearity of the forward map in the density `N` (EXACT).**
> `lineIntensity kB T N Fcal g E A k = N · lineIntensity kB T 1 Fcal g E A k`. The CF-LIBS
> optically-thin line intensity `I_k = Fcal · A_k · N · g_k · exp(−E_k/(k_B T)) / U(T)` carries the
> number density `N` as a bare scalar multiplier: only the `population` numerator contains `N`, and it
> enters linearly, while `Fcal`, `A_k`, `g_k`, the Boltzmann factor and the partition function `U(T)`
> are all independent of `N`. Pure algebra through `population`; the enabling structural fact behind
> variable projection (the `N`-section is exactly quadratic). (Ciucci et al. 1999 forward map.) 

### `CflibsFormal.nlObjective_Nsection_decomposition`

Module `CflibsFormal.NonlinearLeastSquares` · scope `PURE-MATH`

```lean
CflibsFormal.nlObjective_Nsection_decomposition.{u_1} {ι : Type u_1} [Fintype ι] (kB Fcal T : ℝ)
  (g E A obs : ι → ℝ) (hc : 0 < ∑ k, CflibsFormal.lineIntensity kB T 1 Fcal g E A k ^ 2) (N : ℝ) :
  CflibsFormal.nlObjective kB Fcal g E A obs (T, N) =
    CflibsFormal.nlObjective kB Fcal g E A obs
        (T, CflibsFormal.profiledDensity kB Fcal g E A obs T) +
      (N - CflibsFormal.profiledDensity kB Fcal g E A obs T) ^ 2 *
        ∑ k, CflibsFormal.lineIntensity kB T 1 Fcal g E A k ^ 2
```

> **`N`-section decomposition (PURE-MATH).** For a fixed `T` with nondegenerate regressor energy
> `0 < ∑ₖ c_k²` (`c_k = lineIntensity kB T 1 Fcal g E A k`), for every density `N`:
> `nlObjective … (T, N) = nlObjective … (T, N̂(T)) + (N − N̂(T))² · ∑ₖ c_k²`, where
> `N̂(T) = profiledDensity … T`. The nonlinear objective, rewritten through
> `lineIntensity_linear_in_N` into the 1-D least squares `∑ₖ (N·c_k − obs_k)²`, decomposes
> orthogonally: any `N`'s excess residual over the profiled minimum is exactly `(N − N̂)² · ∑ c²`.
> The 2-D nonlinear analogue of `LeastSquaresFit.rss_decomposition`. 

### `CflibsFormal.nlObjective_Nsection_lt_of_ne`

Module `CflibsFormal.NonlinearLeastSquares` · scope `REDUCED`

```lean
CflibsFormal.nlObjective_Nsection_lt_of_ne.{u_1} {ι : Type u_1} [Fintype ι] (kB Fcal T : ℝ)
  (g E A obs : ι → ℝ) (hc : 0 < ∑ k, CflibsFormal.lineIntensity kB T 1 Fcal g E A k ^ 2) {N : ℝ}
  (hN : N ≠ CflibsFormal.profiledDensity kB Fcal g E A obs T) :
  CflibsFormal.nlObjective kB Fcal g E A obs (T, CflibsFormal.profiledDensity kB Fcal g E A obs T) <
    CflibsFormal.nlObjective kB Fcal g E A obs (T, N)
```

> **Strict excess off the profiled density (uniqueness core, REDUCED).** For a fixed `T` with
> `0 < ∑ₖ c_k²`, every density `N ≠ N̂(T)` gives *strictly* larger `N`-section residual:
> `nlObjective … (T, N̂(T)) < nlObjective … (T, N)`. The excess `(N − N̂)² · ∑ c²` is a positive times
> a positive, using `sq_pos_of_ne_zero`. This is what makes `N̂(T)` the *unique* `N`-section
> minimizer (`Nsection_minimizer_unique`). (Tognoni et al. 2010 VARPRO reduction.) 

### `CflibsFormal.nlObjective_eq_sq_sum`

Module `CflibsFormal.NonlinearLeastSquares` · scope `PURE-MATH`

```lean
CflibsFormal.nlObjective_eq_sq_sum.{u_1} {ι : Type u_1} [Fintype ι] (kB Fcal T N : ℝ)
  (g E A obs : ι → ℝ) :
  CflibsFormal.nlObjective kB Fcal g E A obs (T, N) =
    ∑ k, (N * CflibsFormal.lineIntensity kB T 1 Fcal g E A k - obs k) ^ 2
```

> The joint objective at any `(T, N)`, rewritten through linearity in `N`:
> `nlObjective … (T, N) = ∑ₖ (N·c_k(T) − obs_k)²`, `c_k(T) = lineIntensity kB T 1 Fcal g E A k`.
> Shared expansion behind the two-line closed form and the exact-fit characterization. 

### `CflibsFormal.nlObjective_eq_zero_iff`

Module `CflibsFormal.NonlinearLeastSquares` · scope `PURE-MATH`

```lean
CflibsFormal.nlObjective_eq_zero_iff.{u_1} {ι : Type u_1} [Fintype ι] (kB Fcal T N : ℝ)
  (g E A obs : ι → ℝ) :
  CflibsFormal.nlObjective kB Fcal g E A obs (T, N) = 0 ↔
    ∀ (k : ι), N * CflibsFormal.lineIntensity kB T 1 Fcal g E A k = obs k
```

> **Exact-fit characterization of a zero residual.** The joint objective vanishes at `(T, N)` iff
> `N` reproduces every line exactly: `nlObjective … (T, N) = 0 ↔ ∀ k, N·c_k(T) = obs_k`. A sum of
> squares is zero iff every summand is (`Finset.sum_eq_zero_iff_of_nonneg`). This is the engine behind
> on-manifold `T`- and joint uniqueness: a perfect fit forces the intensity ratios, hence `T`. 

### `CflibsFormal.nlObjective_onManifold_min`

Module `CflibsFormal.NonlinearLeastSquares` · scope `EXACT`

```lean
CflibsFormal.nlObjective_onManifold_min.{u_1} {ι : Type u_1} [Fintype ι] {kB Fcal : ℝ}
  {g E A : ι → ℝ} {T0 N0 : ℝ} {obs : ι → ℝ} {S : Set (ℝ × ℝ)}
  (hobs : ∀ (k : ι), obs k = CflibsFormal.lineIntensity kB T0 N0 Fcal g E A k)
  (hmem : (T0, N0) ∈ S) :
  (T0, N0) ∈ S ∧
    CflibsFormal.nlObjective kB Fcal g E A obs (T0, N0) = 0 ∧
      IsMinOn (CflibsFormal.nlObjective kB Fcal g E A obs) S (T0, N0)
```

> **On-manifold anchor.** If `obs` is exactly the forward spectrum of a parameter pair
> `(T0, N0)` lying in a set `S` — the noise-free case `obs_k = lineIntensity kB T0 N0 Fcal g E A k`
> — then `nlObjective` attains its global minimum value `0` at `(T0, N0)`, so `(T0, N0)` is a
> minimizer over `S`. The objective is a sum of squares, hence `≥ 0` everywhere, and each summand
> `(I_k(T0,N0) − obs_k)²` vanishes at the true parameters; so the true parameters are a zero-residual
> global optimum. For a genuine physical box `S = Icc Tmin Tmax ×ˢ Icc Nmin Nmax` with `(T0, N0)`
> inside, this identifies the minimizer of `nlObjective_exists_min` as having minimal value `0`. Off
> the manifold (noisy `obs`) the minimal value is positive and this anchor does not apply. 

### `CflibsFormal.profiledDensity_denom_pos`

Module `CflibsFormal.NonlinearLeastSquares` · scope `PURE-MATH`

```lean
CflibsFormal.profiledDensity_denom_pos.{u_1} {ι : Type u_1} [Fintype ι] [Nonempty ι] {kB T Fcal : ℝ}
  {g E A : ι → ℝ} (hg : ∀ (k : ι), 0 < g k) (hFcal : 0 < Fcal) (hA : ∀ (k : ι), 0 < A k) :
  0 < ∑ k, CflibsFormal.lineIntensity kB T 1 Fcal g E A k ^ 2
```

> **Nondegeneracy of the profiled least squares.** For any temperature `T`, under positive
> degeneracies `g`, calibration `Fcal`, and Einstein coefficients `A`, the regressor energy
> `∑ₖ (lineIntensity kB T 1 Fcal g E A k)²` is strictly positive: each `c_k` is a positive observable
> at unit density (`lineIntensity_pos`; the Boltzmann factor is positive for *any* `T`, so no lower
> bound on `T` is needed), and a sum over the nonempty level set of positive squares is positive. This
> is the hypothesis `0 < ∑ c²` of the decomposition and minimality theorems, so they are never
> vacuous. 

### `CflibsFormal.profiledDensity_isMinOn_Nsection`

Module `CflibsFormal.NonlinearLeastSquares` · scope `REDUCED`

```lean
CflibsFormal.profiledDensity_isMinOn_Nsection.{u_1} {ι : Type u_1} [Fintype ι] (kB Fcal T : ℝ)
  (g E A obs : ι → ℝ) (hc : 0 < ∑ k, CflibsFormal.lineIntensity kB T 1 Fcal g E A k ^ 2) (N : ℝ) :
  CflibsFormal.nlObjective kB Fcal g E A obs (T, CflibsFormal.profiledDensity kB Fcal g E A obs T) ≤
    CflibsFormal.nlObjective kB Fcal g E A obs (T, N)
```

> **`N`-section global minimality (headline, REDUCED).** For a fixed `T` with `0 < ∑ₖ c_k²`, the
> profiled density `N̂(T) = profiledDensity … T` minimizes the `N`-section of the joint objective:
> `nlObjective … (T, N̂(T)) ≤ nlObjective … (T, N)` for every `N`. Immediate from
> `nlObjective_Nsection_decomposition` — the excess `(N − N̂)² · ∑ c²` is a nonnegative sum of
> squares. Reduces the joint 2-D fit's `N`-direction to the closed-form VARPRO estimate (Tognoni et
> al. 2010); the `T`-direction remains open (non-convex). 

### `CflibsFormal.profiledDensity_onManifold`

Module `CflibsFormal.NonlinearLeastSquares` · scope `PURE-MATH`

```lean
CflibsFormal.profiledDensity_onManifold.{u_1} {ι : Type u_1} [Fintype ι] {kB Fcal T0 N0 : ℝ}
  {g E A obs : ι → ℝ} (hc : 0 < ∑ k, CflibsFormal.lineIntensity kB T0 1 Fcal g E A k ^ 2)
  (hobs : ∀ (k : ι), obs k = CflibsFormal.lineIntensity kB T0 N0 Fcal g E A k) :
  CflibsFormal.profiledDensity kB Fcal g E A obs T0 = N0
```

> **Profiled density recovers the true density on-manifold.** If `obs` is the exact forward
> spectrum of `(T₀, N₀)`, the variable-projection density at the true temperature is exactly `N₀`
> (`∑ c_k·obs_k = N₀·∑ c_k²`, then divide by the nondegeneracy). 

### `CflibsFormal.profiledResidual_metric_bound`

Module `CflibsFormal.NonlinearLeastSquares` · scope `REDUCED`

```lean
CflibsFormal.profiledResidual_metric_bound {kB Fcal Tmin Tmax T0 N0 T : ℝ} {g E A obs η : Fin 2 → ℝ}
  (hg : ∀ (k : Fin 2), 0 < g k) (hFcal : 0 < Fcal) (hA : ∀ (k : Fin 2), 0 < A k) (hN0 : 0 < N0)
  (hTmin : 0 < Tmin) (hT : Tmin ≤ T) (hTM : T ≤ Tmax) (hT0 : Tmin ≤ T0) (hT0M : T0 ≤ Tmax)
  (hobs : ∀ (k : Fin 2), obs k = CflibsFormal.lineIntensity kB T0 N0 Fcal g E A k + η k)
  (hle :
    CflibsFormal.nlObjective kB Fcal g E A obs
        (T, CflibsFormal.profiledDensity kB Fcal g E A obs T) ≤
      CflibsFormal.nlObjective kB Fcal g E A obs
        (T0, CflibsFormal.profiledDensity kB Fcal g E A obs T0)) :
  (N0 * CflibsFormal.lineIntensity kB T0 1 Fcal g E A 0 * (g 1 * A 1 / (g 0 * A 0)) *
          (Real.exp (-(|(E 0 - E 1) / kB| / Tmin)) * (|(E 0 - E 1) / kB| / Tmax ^ 2))) ^
        2 *
      (T - T0) ^ 2 ≤
    6 * (1 + (g 1 * A 1 / (g 0 * A 0) * Real.exp (|(E 0 - E 1) / kB| / Tmin)) ^ 2) * ∑ k, η k ^ 2
```

### `CflibsFormal.profiledResidual_minimizer_trapped`

Module `CflibsFormal.NonlinearLeastSquares` · scope `REDUCED`

```lean
CflibsFormal.profiledResidual_minimizer_trapped.{u_1} {ι : Type u_1} [Fintype ι]
  {kB Fcal T0 N0 T : ℝ} {g E A obs η : ι → ℝ}
  (hc0 : 0 < ∑ k, CflibsFormal.lineIntensity kB T0 1 Fcal g E A k ^ 2)
  (hcT : 0 < ∑ k, CflibsFormal.lineIntensity kB T 1 Fcal g E A k ^ 2)
  (hobs : ∀ (k : ι), obs k = CflibsFormal.lineIntensity kB T0 N0 Fcal g E A k + η k)
  (hle :
    CflibsFormal.nlObjective kB Fcal g E A obs
        (T, CflibsFormal.profiledDensity kB Fcal g E A obs T) ≤
      CflibsFormal.nlObjective kB Fcal g E A obs
        (T0, CflibsFormal.profiledDensity kB Fcal g E A obs T0)) :
  CflibsFormal.nlObjective kB Fcal g E A (fun k => CflibsFormal.lineIntensity kB T0 N0 Fcal g E A k)
      (T,
        CflibsFormal.profiledDensity kB Fcal g E A
          (fun k => CflibsFormal.lineIntensity kB T0 N0 Fcal g E A k) T) ≤
    6 * ∑ k, η k ^ 2
```

> **Near-manifold minimizer localization / trapping (REDUCED, Tognoni 2010).** The topological
> form of the near-manifold picture. For noisy data `obs = forward(T₀,N₀) + η`, any temperature `T`
> that fits the noisy data **at least as well as `T₀`** — in particular any minimizer of the profiled
> objective over a set containing `T₀` — has a small *clean* residual gap: `Φ_clean(T) ≤ 6·∑ηₖ²`. So
> every noisy near-optimizer is trapped in the clean sublevel set `{T : Φ_clean(T) ≤ 6·∑ηₖ²}`. This is
> a genuine neighborhood of `T₀` (it contains `T₀`, where `Φ_clean = 0`), and since `Φ_clean` vanishes
> **only** at `T₀` (`profiledT_onManifold_unique`), the trapping set collapses to `{T₀}` as the noise
> energy `∑ηₖ² → 0`: the solver's answer is provably pinned near the truth, with the closeness
> controlled by the noise. This is the argmin-localization face of `profiledResidual_true_strict_lt`
> (its contrapositive), from `profiledResidual_nearManifold_bound` +
> `profiledResidual_stability_in_obs` via `linarith`.
> 
> Honest scope — what this deliberately does **not** claim: (1) `T₀` is *not* asserted to be a strict
> local minimizer of the noisy `Φ_obs` — under generic noise the minimizer shifts off `T₀` by
> `O(‖η‖)`, so that statement is false; trapping localizes the *shifted* minimizer, which is correct.
> (2) The *metric* refinement `|T − T₀| ≤ C·√(∑ηₖ²)` and strict-convexity uniqueness of the minimizer
> *within* the neighborhood need the Rayleigh-quotient curvature/Hessian route (heavy, and flagged
> as a trap in the frontier dossier); they remain open. 

### `CflibsFormal.profiledResidual_nearManifold_bound`

Module `CflibsFormal.NonlinearLeastSquares` · scope `REDUCED`

```lean
CflibsFormal.profiledResidual_nearManifold_bound.{u_1} {ι : Type u_1} [Fintype ι]
  {kB Fcal T0 N0 : ℝ} {g E A obs η : ι → ℝ}
  (hc : 0 < ∑ k, CflibsFormal.lineIntensity kB T0 1 Fcal g E A k ^ 2)
  (hobs : ∀ (k : ι), obs k = CflibsFormal.lineIntensity kB T0 N0 Fcal g E A k + η k) :
  CflibsFormal.nlObjective kB Fcal g E A obs
      (T0, CflibsFormal.profiledDensity kB Fcal g E A obs T0) ≤
    2 * ∑ k, η k ^ 2
```

> **Near-manifold residual bound at the true temperature (REDUCED, Tognoni 2010).** If the data is
> the exact forward spectrum of `(T₀, N₀)` corrupted by additive noise `η` (`obs_k = c_k(T₀)·N₀ + η_k`
> via `lineIntensity`), the profiled residual at the *true* temperature is controlled by the noise
> energy: `Φ_obs(T₀) ≤ 2·∑ₖ η_k²`. Immediate instance of `profiledResidual_stability_in_obs` against
> the clean forward spectrum, whose profiled residual at `T₀` is exactly `0`
> (`profiledDensity_onManifold` + `nlObjective_eq_zero_iff`). This quantifies
> "small `L²` noise ⇒ small residual at the truth" — the *value* half of the near-manifold picture;
> the *argmin* half (that `T₀` strictly out-competes far temperatures) is
> `profiledResidual_true_strict_lt` below. 

### `CflibsFormal.profiledResidual_of_orthogonal`

Module `CflibsFormal.NonlinearLeastSquares` · scope `PURE-MATH`

```lean
CflibsFormal.profiledResidual_of_orthogonal.{u_1} {ι : Type u_1} [Fintype ι] (kB Fcal T : ℝ)
  (g E A obs : ι → ℝ) (horth : ∑ k, CflibsFormal.lineIntensity kB T 1 Fcal g E A k * obs k = 0) :
  CflibsFormal.nlObjective kB Fcal g E A obs (T, CflibsFormal.profiledDensity kB Fcal g E A obs T) =
    ∑ k, obs k ^ 2
```

> **Profiled residual at an orthogonal observation (PURE-MATH).** If the observation vector `obs`
> is orthogonal to the unit-density line-intensity vector `c(T)`, i.e.
> `∑ₖ lineIntensity kB T 1 Fcal g E A k · obs_k = 0`, then the variable-projection density profiles to
> zero and the profiled residual equals the full observation energy:
> `nlObjective … (T, N̂(T)) = ∑ₖ obs_k²`. The normal-equation numerator vanishes, so
> `N̂(T) = 0/‖c(T)‖² = 0`, and the residual is `∑ₖ (0·c_k − obs_k)² = ∑ₖ obs_k²`. Pure algebra — the
> worst-case fit at any temperature where `obs` has no component along the line-intensity ray. 

### `CflibsFormal.profiledResidual_stability_in_obs`

Module `CflibsFormal.NonlinearLeastSquares` · scope `REDUCED`

```lean
CflibsFormal.profiledResidual_stability_in_obs.{u_1} {ι : Type u_1} [Fintype ι] {kB Fcal T : ℝ}
  {g E A obs obs' : ι → ℝ} (hc : 0 < ∑ k, CflibsFormal.lineIntensity kB T 1 Fcal g E A k ^ 2) :
  CflibsFormal.nlObjective kB Fcal g E A obs (T, CflibsFormal.profiledDensity kB Fcal g E A obs T) ≤
    2 *
        CflibsFormal.nlObjective kB Fcal g E A obs'
          (T, CflibsFormal.profiledDensity kB Fcal g E A obs' T) +
      2 * ∑ k, (obs' k - obs k) ^ 2
```

> **Near-manifold stability of the profiled residual in the observation (REDUCED, Tognoni 2010).**
> For a fixed temperature `T` with nondegenerate regressor energy `0 < ∑ₖ c_k²`
> (`c_k = lineIntensity kB T 1 Fcal g E A k`), the density-profiled residual
> `Φ_obs(T) = nlObjective … obs (T, N̂_obs(T))` is stable under an `L²` perturbation of the data:
> `Φ_obs(T) ≤ 2·Φ_obs'(T) + 2·∑ₖ (obs'_k − obs_k)²` for any two observations `obs, obs'`. This is the
> honest analytic core a full perturbation/local-uniqueness argument rests on — a global quadratic
> *upper* stability estimate controlling how far the profiled residual can rise under an `L²` data
> perturbation. It is NOT a continuity statement
> (the factor `2` leaves `Φ ≤ 2Φ` slack at `obs = obs'`) and NOT a local-uniqueness theorem; its
> force is the near-manifold corollary below.
> Proof: variable-projection minimality (`profiledDensity_isMinOn_Nsection`) bounds `Φ_obs(T)` by the
> residual of `obs` measured at the *other* profiled density `N̂_obs'(T)`; the elementary split
> `(x−obs)² ≤ 2(x−obs')² + 2(obs'−obs)²` summed over lines finishes. No distinct-energy hypothesis is
> needed, so the bound holds for every line set. 

### `CflibsFormal.profiledResidual_true_strict_lt`

Module `CflibsFormal.NonlinearLeastSquares` · scope `REDUCED`

```lean
CflibsFormal.profiledResidual_true_strict_lt.{u_1} {ι : Type u_1} [Fintype ι] {kB Fcal T0 N0 T : ℝ}
  {g E A obs η : ι → ℝ} (hc0 : 0 < ∑ k, CflibsFormal.lineIntensity kB T0 1 Fcal g E A k ^ 2)
  (hcT : 0 < ∑ k, CflibsFormal.lineIntensity kB T 1 Fcal g E A k ^ 2)
  (hobs : ∀ (k : ι), obs k = CflibsFormal.lineIntensity kB T0 N0 Fcal g E A k + η k)
  (hgap :
    6 * ∑ k, η k ^ 2 <
      CflibsFormal.nlObjective kB Fcal g E A
        (fun k => CflibsFormal.lineIntensity kB T0 N0 Fcal g E A k)
        (T,
          CflibsFormal.profiledDensity kB Fcal g E A
            (fun k => CflibsFormal.lineIntensity kB T0 N0 Fcal g E A k) T)) :
  CflibsFormal.nlObjective kB Fcal g E A obs
      (T0, CflibsFormal.profiledDensity kB Fcal g E A obs T0) <
    CflibsFormal.nlObjective kB Fcal g E A obs (T, CflibsFormal.profiledDensity kB Fcal g E A obs T)
```

> **Near-manifold strict domination by the true temperature (REDUCED, Tognoni 2010).** The
> *argmin* half of the near-manifold picture. For noisy data `obs = forward(T₀,N₀) + η`, the true
> `T₀` gives a **strictly** smaller profiled residual than any temperature `T` whose *clean* residual
> gap exceeds six times the noise energy: `6·∑ηₖ² < Φ_clean(T) ⟹ Φ_obs(T₀) < Φ_obs(T)`. So every
> temperature the noise-free objective separates from `T₀` by more than `O(‖η‖²)` still loses to `T₀`
> on the noisy data — a quantitative local-minimizer statement. Honestly **not** a topological
> neighborhood-uniqueness theorem: temperatures with clean gap `≤ 6‖η‖²` are uncontrolled (that tail
> would need the heavy perturbation machinery). Proof: `profiledResidual_stability_in_obs`
> (clean vs noisy) gives `Φ_clean(T) ≤ 2·Φ_obs(T) + 2∑ηₖ²` and `profiledResidual_nearManifold_bound`
> gives `Φ_obs(T₀) ≤ 2∑ηₖ²`; the gap hypothesis closes the strict inequality by linear arithmetic. 

### `CflibsFormal.profiledResidual_two_closed_form`

Module `CflibsFormal.NonlinearLeastSquares` · scope `PURE-MATH`

```lean
CflibsFormal.profiledResidual_two_closed_form (kB Fcal T : ℝ) (g E A obs : Fin 2 → ℝ)
  (hc :
    0 <
      CflibsFormal.lineIntensity kB T 1 Fcal g E A 0 ^ 2 +
        CflibsFormal.lineIntensity kB T 1 Fcal g E A 1 ^ 2) :
  CflibsFormal.nlObjective kB Fcal g E A obs (T, CflibsFormal.profiledDensity kB Fcal g E A obs T) =
    (obs 1 * CflibsFormal.lineIntensity kB T 1 Fcal g E A 0 -
          obs 0 * CflibsFormal.lineIntensity kB T 1 Fcal g E A 1) ^
        2 /
      (CflibsFormal.lineIntensity kB T 1 Fcal g E A 0 ^ 2 +
        CflibsFormal.lineIntensity kB T 1 Fcal g E A 1 ^ 2)
```

> **Two-line profiled-residual closed form (PURE-MATH).** For two lines, evaluating the joint
> objective at the variable-projection density `N̂(T) = profiledDensity … T` yields the explicit
> projection residual
> `nlObjective … (T, N̂(T)) = (obs₁·c₀ − obs₀·c₁)² / (c₀² + c₁²)`,
> with `c_k = lineIntensity kB T 1 Fcal g E A k`. The calibration, density, and partition function all
> cancel out of the Rayleigh-quotient residual — only the two unit-density line intensities `c₀, c₁`
> survive. Pure algebra: expand `nlObjective` over `Fin 2`, substitute `profiledDensity`, then apply
> the Lagrange identity `residual_two_cross`. Needs only the nondegeneracy `0 < c₀² + c₁²`
> (`profiledDensity_denom_pos`). This is the closed form the two-line `T`-uniqueness rests on. 

### `CflibsFormal.profiledResidual_two_eq_ratio`

Module `CflibsFormal.NonlinearLeastSquares` · scope `PURE-MATH`

```lean
CflibsFormal.profiledResidual_two_eq_ratio {kB Fcal T : ℝ} {g E A obs : Fin 2 → ℝ}
  (hc0 : 0 < CflibsFormal.lineIntensity kB T 1 Fcal g E A 0) :
  CflibsFormal.nlObjective kB Fcal g E A obs (T, CflibsFormal.profiledDensity kB Fcal g E A obs T) =
    CflibsFormal.profiledRatioResidual (obs 0) (obs 1)
      (CflibsFormal.lineIntensity kB T 1 Fcal g E A 1 /
        CflibsFormal.lineIntensity kB T 1 Fcal g E A 0)
```

> **The off-manifold two-line profiled residual equals the ratio residual (PURE-MATH).** For
> arbitrary observations, the density-profiled two-line residual equals `profiledRatioResidual` at the
> intensity ratio `t = c₁(T)/c₀(T)`. The cross form of `profiledResidual_two_closed_form` divided
> through by `c₀² > 0`; the partition function has already cancelled. 

### `CflibsFormal.profiledT_onManifold_unique`

Module `CflibsFormal.NonlinearLeastSquares` · scope `EXACT`

```lean
CflibsFormal.profiledT_onManifold_unique.{u_1} {ι : Type u_1} [Fintype ι] [Nonempty ι]
  {kB Fcal T0 N0 T : ℝ} {g E A obs : ι → ℝ} (hkB : 0 < kB) (hg : ∀ (k : ι), 0 < g k)
  (hFcal : 0 < Fcal) (hA : ∀ (k : ι), 0 < A k) (hN0 : 0 < N0) (hT0 : 0 < T0) (hT : 0 < T) (i j : ι)
  (hE : E i ≠ E j) (hobs : ∀ (k : ι), obs k = CflibsFormal.lineIntensity kB T0 N0 Fcal g E A k) :
  CflibsFormal.nlObjective kB Fcal g E A obs (T, CflibsFormal.profiledDensity kB Fcal g E A obs T) =
      0 ↔
    T = T0
```

> **On-manifold `T`-uniqueness for `m` lines (EXACT, Ciucci 1999).** With `obs` the exact forward
> spectrum of `(T₀, N₀)` and **one** distinct-energy pair `E i ≠ E j`, the profiled residual
> `Φ(T) = nlObjective … (T, N̂(T))` vanishes **iff** `T = T₀`, for any finite line set. So the true
> temperature is the unique global minimizer of the density-profiled objective — the general-`m`
> strengthening of `nlObjective_onManifold_min` (min *value* `0` → unique *argmin*), and the
> least-squares analogue of `temperature_identifiability`. Forward: `Φ(T) = 0` forces an exact fit
> (`nlObjective_eq_zero_iff`), so `c_j(T)/c_i(T) = obs_j/obs_i = c_j(T₀)/c_i(T₀)`, and distinct
> energies force `T = T₀`. Reverse: at `T₀` the profiled density is exactly `N₀`
> (`profiledDensity_onManifold`), a perfect fit. The `m ≥ 3` off-manifold case is genuinely multimodal
> and is not addressed. 

### `CflibsFormal.profiledT_two_offManifold_box_unique`

Module `CflibsFormal.NonlinearLeastSquares` · scope `REDUCED`

```lean
CflibsFormal.profiledT_two_offManifold_box_unique {kB Fcal Tmin Tmax T1 T2 : ℝ}
  {g E A obs : Fin 2 → ℝ} (hkB : 0 < kB) (hg : ∀ (k : Fin 2), 0 < g k) (hFcal : 0 < Fcal)
  (hA : ∀ (k : Fin 2), 0 < A k) (hTmin : 0 < Tmin) (hE : E 0 ≠ E 1)
  (hpos :
    ∀ T ∈ Set.Icc Tmin Tmax,
      0 <
        obs 0 * CflibsFormal.lineIntensity kB T 1 Fcal g E A 0 +
          obs 1 * CflibsFormal.lineIntensity kB T 1 Fcal g E A 1)
  (hT1 : T1 ∈ Set.Icc Tmin Tmax) (hT2 : T2 ∈ Set.Icc Tmin Tmax)
  (hmin1 :
    ∀ T ∈ Set.Icc Tmin Tmax,
      CflibsFormal.nlObjective kB Fcal g E A obs
          (T1, CflibsFormal.profiledDensity kB Fcal g E A obs T1) ≤
        CflibsFormal.nlObjective kB Fcal g E A obs
          (T, CflibsFormal.profiledDensity kB Fcal g E A obs T))
  (hmin2 :
    ∀ T ∈ Set.Icc Tmin Tmax,
      CflibsFormal.nlObjective kB Fcal g E A obs
          (T2, CflibsFormal.profiledDensity kB Fcal g E A obs T2) ≤
        CflibsFormal.nlObjective kB Fcal g E A obs
          (T, CflibsFormal.profiledDensity kB Fcal g E A obs T)) :
  T1 = T2
```

> **Two-line OFF-manifold box-uniqueness of the profiled temperature (REDUCED, Ciucci 1999).** The
> first genuinely off-manifold `T`-*minimizer* uniqueness for two lines. For **arbitrary** data
> `obs` (no on-manifold hypothesis), on a temperature box `[Tmin,Tmax]` with distinct upper-level
> energies `E 0 ≠ E 1` and where the antipode is avoided —
> `0 < obs₀·c₀(T) + obs₁·c₁(T)` for every `T` in the box, i.e. `obs` keeps a positive projection onto
> the line-intensity ray (automatic for any nonzero physical spectrum, `obs ≥ 0`) — any two
> temperatures that both minimize the density-profiled residual over the box are **equal**.
> 
> Mechanism, entirely algebraic (no Hessian/curvature): the profiled residual is
> `Φ(T) = profiledRatioResidual obs₀ obs₁ (c₁(T)/c₀(T))` (`profiledResidual_two_eq_ratio`), the ratio
> `c₁/c₀ = K·exp((E₀−E₁)/(k_B T))` is strictly monotone in `T` (`lineIntensity_ratio_closed_form` +
> `Real.exp` strict monotonicity, `E₀ ≠ E₁`), and the ratio residual is strictly *unimodal* on the
> antipode-free region (`profiledRatioResidual_strict_between`): were there two distinct box
> minimizers, their midpoint temperature would give a strictly smaller residual, contradicting
> minimality. Honest scope: uniqueness of the **minimizer** over the box (REDUCED — two lines, box,
> antipode-avoidance hypothesis); the general `m ≥ 3` off-manifold problem is genuinely multimodal
> (`profiledResidual_not_injective_m3`) and is not addressed. 

### `CflibsFormal.profiledT_two_onManifold_unique`

Module `CflibsFormal.NonlinearLeastSquares` · scope `EXACT`

```lean
CflibsFormal.profiledT_two_onManifold_unique {kB Fcal T0 N0 T : ℝ} {g E A obs : Fin 2 → ℝ}
  (hkB : 0 < kB) (hg : ∀ (k : Fin 2), 0 < g k) (hFcal : 0 < Fcal) (hA : ∀ (k : Fin 2), 0 < A k)
  (hN0 : 0 < N0) (hE : E 0 ≠ E 1) (hT0 : 0 < T0) (hT : 0 < T)
  (hobs : ∀ (k : Fin 2), obs k = CflibsFormal.lineIntensity kB T0 N0 Fcal g E A k) :
  CflibsFormal.nlObjective kB Fcal g E A obs (T, CflibsFormal.profiledDensity kB Fcal g E A obs T) =
      0 ↔
    T = T0
```

> **Two-line on-manifold `T`-uniqueness (EXACT, Ciucci 1999).** The `Fin 2`, distinct-energy
> `E 0 ≠ E 1` instance of `profiledT_onManifold_unique`: on-manifold, `Φ₂(T) = 0 ↔ T = T₀`. The
> original two-line milestone, now a corollary of the general-`m` result. 

### `CflibsFormal.two_ratio_diff`

Module `CflibsFormal.NonlinearLeastSquares` · scope `EXACT`

```lean
CflibsFormal.two_ratio_diff {kB Fcal T T0 : ℝ} {g E A : Fin 2 → ℝ} (hg : ∀ (k : Fin 2), 0 < g k)
  (hFcal : 0 < Fcal) (hA : ∀ (k : Fin 2), 0 < A k) :
  CflibsFormal.lineIntensity kB T 1 Fcal g E A 1 / CflibsFormal.lineIntensity kB T 1 Fcal g E A 0 -
      CflibsFormal.lineIntensity kB T0 1 Fcal g E A 1 /
        CflibsFormal.lineIntensity kB T0 1 Fcal g E A 0 =
    g 1 * A 1 / (g 0 * A 0) *
      (Real.exp ((E 0 - E 1) / (kB * T)) - Real.exp ((E 0 - E 1) / (kB * T0)))
```

> The two-line intensity-ratio difference is a scaled `Real.exp` difference. 

### `CflibsFormal.lineIntensity_div_opticalDepth`

Module `CflibsFormal.OpticalDepth` · scope `REDUCED`

```lean
CflibsFormal.lineIntensity_div_opticalDepth.{u_1} {ι : Type u_1} [Fintype ι] [Nonempty ι]
  {kB T N Fcal sigma0 ell : ℝ} {g E A : ι → ℝ} (hg : ∀ (k : ι), 0 < g k) (hN : 0 < N)
  (hsig : 0 < sigma0) (hell : 0 < ell) (u l : ι) :
  CflibsFormal.lineIntensity kB T N Fcal g E A u /
      CflibsFormal.opticalDepth kB T N sigma0 ell g E l =
    CflibsFormal.lteSourceStrength kB T Fcal sigma0 ell g E A u l
```

> **The source strength is the measured ratio `I_thin / τ`.** Dividing the thin emission by
> the state-bound optical depth returns a quantity free of `N` and of `U(T)`.
> 
> REDUCED: homogeneous single-temperature slab, flat line-center cross-section. 

### `CflibsFormal.lineIntensity_eq_source_mul_opticalDepth`

Module `CflibsFormal.OpticalDepth` · scope `REDUCED`

```lean
CflibsFormal.lineIntensity_eq_source_mul_opticalDepth.{u_1} {ι : Type u_1} [Fintype ι] [Nonempty ι]
  {kB T N Fcal sigma0 ell : ℝ} {g E A : ι → ℝ} (hg : ∀ (k : ι), 0 < g k) (hsig : 0 < sigma0)
  (hell : 0 < ell) (u l : ι) :
  CflibsFormal.lineIntensity kB T N Fcal g E A u =
    CflibsFormal.lteSourceStrength kB T Fcal sigma0 ell g E A u l *
      CflibsFormal.opticalDepth kB T N sigma0 ell g E l
```

> **Emission = source × optical depth.** The optically-thin upper-level emission factors
> EXACTLY as `I_thin = S · τ`, where `S = lteSourceStrength` contains no `N` and no `U(T)`.
> Holds for every `N` (no positivity needed): both sides are linear in `N`, and the partition
> function cancels between the upper-level population and the lower-level column. This single
> identity is the algebraic hinge of the module — the two ratio laws below are read off it.
> 
> REDUCED: homogeneous single-temperature slab, flat line-center cross-section. 

### `CflibsFormal.opticalDepth_div_lineIntensity`

Module `CflibsFormal.OpticalDepth` · scope `REDUCED`

```lean
CflibsFormal.opticalDepth_div_lineIntensity.{u_1} {ι : Type u_1} [Fintype ι] [Nonempty ι]
  {kB T N Fcal sigma0 ell : ℝ} {g E A : ι → ℝ} (hg : ∀ (k : ι), 0 < g k) (hN : 0 < N)
  (hFcal : 0 < Fcal) (hA : ∀ (k : ι), 0 < A k) (hsig : 0 < sigma0) (hell : 0 < ell) (u l : ι) :
  CflibsFormal.opticalDepth kB T N sigma0 ell g E l /
      CflibsFormal.lineIntensity kB T N Fcal g E A u =
    sigma0 * ell * g l / (Fcal * A u * g u) * Real.exp ((E u - E l) / (kB * T))
```

> **The temperature law of the absorption channel.** The ratio of optical depth to thin
> emission is
>   `τ / I_thin = (σ₀ ℓ g_l)/(Fcal A_u g_u) · exp((E_u − E_l)/(k_B T))`,
> in which the total density `N` and the partition function `U(T)` have cancelled COMPLETELY.
> So `τ/I` is a function of `T` and known constants alone — a second, structurally different
> equation on the same state than the Boltzmann plot supplies.
> 
> REDUCED: homogeneous single-temperature slab, flat line-center cross-section. 

### `CflibsFormal.opticalDepth_div_lineIntensity_strictAntiOn_temperature`

Module `CflibsFormal.OpticalDepth` · scope `REDUCED`

```lean
CflibsFormal.opticalDepth_div_lineIntensity_strictAntiOn_temperature.{u_1} {ι : Type u_1}
  [Fintype ι] [Nonempty ι] {kB N Fcal sigma0 ell : ℝ} {g E A : ι → ℝ} (hg : ∀ (k : ι), 0 < g k)
  (hN : 0 < N) (hFcal : 0 < Fcal) (hA : ∀ (k : ι), 0 < A k) (hsig : 0 < sigma0) (hell : 0 < ell)
  (hkB : 0 < kB) (u l : ι) (hE : E l < E u) :
  StrictAntiOn
    (fun T =>
      CflibsFormal.opticalDepth kB T N sigma0 ell g E l /
        CflibsFormal.lineIntensity kB T N Fcal g E A u)
    (Set.Ioi 0)
```

> **Hotter plasmas self-absorb less, relative to what they emit.** For a genuine
> bound-bound transition (`E_l < E_u`) and `k_B > 0`, the ratio `τ / I_thin` is STRICTLY
> ANTITONE in `T` on `(0, ∞)`. Proof: the ratio identity above turns the claim into strict
> antitonicity of `T ↦ exp((E_u − E_l)/(k_B T))`, i.e. of `T ↦ (E_u − E_l)/(k_B T)`.
> 
> Note the careful statement: `opticalDepth` itself is NOT monotone in `T` (the partition
> function `U(T)` redistributes population), so the temperature content of the absorption
> channel lives in this ratio, not in `τ` alone.
> 
> REDUCED: homogeneous single-temperature slab, flat line-center cross-section. 

### `CflibsFormal.lteSourceStrength_ratio_calibration_free`

Module `CflibsFormal.OpticalDepthBridge` · scope `PURE-MATH`

```lean
CflibsFormal.lteSourceStrength_ratio_calibration_free.{u_1} {ι : Type u_1}
  {kB T Fcal sigma0 ell : ℝ} {g E A : ι → ℝ} (hg : ∀ (k : ι), 0 < g k) (hFcal : 0 < Fcal)
  (hA : ∀ (k : ι), 0 < A k) (hsig : 0 < sigma0) (hell : 0 < ell) (u₁ l₁ u₂ l₂ : ι) :
  CflibsFormal.lteSourceStrength kB T Fcal sigma0 ell g E A u₁ l₁ /
      CflibsFormal.lteSourceStrength kB T Fcal sigma0 ell g E A u₂ l₂ =
    A u₁ * g u₁ * CflibsFormal.boltzmannFactor kB T (E u₁) *
        (g l₂ * CflibsFormal.boltzmannFactor kB T (E l₂)) /
      (A u₂ * g u₂ * CflibsFormal.boltzmannFactor kB T (E u₂) *
        (g l₁ * CflibsFormal.boltzmannFactor kB T (E l₁)))
```

> **The source-strength ratio is calibration- and opacity-free.** Both `lteSourceStrength`
> factors carry the same `Fcal` and the same `σ₀ · ℓ`, so in their ratio these cancel EXACTLY:
> what survives depends only on `T` and the atomic data `(A, g, E)` of the four levels. This is
> the algebraic fact that makes the two-line ratio route below independent of the absolute
> calibration; it is proved here rather than asserted in prose. Pure algebra.
> 
> The `σ₀ · ℓ` cancellation is CONDITIONAL on the two lines sharing one `σ₀` — a single
> `sigma0` argument serves both. `Fcal` cancels unconditionally; `σ₀` cancels only because it
> was assumed common (see the module's `## Honest limitations`). 

### `CflibsFormal.thickLineIntensity_lt_lineIntensity_of_pos_density`

Module `CflibsFormal.OpticalDepthBridge` · scope `APPROXIMATION`

```lean
CflibsFormal.thickLineIntensity_lt_lineIntensity_of_pos_density.{u_1} {ι : Type u_1} [Fintype ι]
  [Nonempty ι] {kB T N Fcal sigma0 ell : ℝ} {g E A : ι → ℝ} (hg : ∀ (k : ι), 0 < g k) (hN : 0 < N)
  (hFcal : 0 < Fcal) (hA : ∀ (k : ι), 0 < A k) (hsig : 0 < sigma0) (hell : 0 < ell) (u l : ι) :
  CflibsFormal.thickLineIntensity kB T N Fcal sigma0 ell g E A u l <
    CflibsFormal.lineIntensity kB T N Fcal g E A u
```

> **The bias-direction theorem, at the bound `τ`.** `SelfAbsorption`'s strict dimming law
> needs a free hypothesis `0 < τ`; with `τ` bound to the state that hypothesis is DERIVED from
> `0 < N`. So: at any positive density the measured (self-absorbed) line lies strictly below
> its optically-thin value, and neglecting self-absorption biases the inferred upper-level
> population downward.
> 
> REDUCED: homogeneous single-temperature slab, flat line-center cross-section; inherits the
> `APPROXIMATION` scope of `selfAbsorbedIntensity_lt_lineIntensity`. 

### `CflibsFormal.outerLoop_contracts`

Module `CflibsFormal.OuterLoopModelB` · scope `REDUCED`

```lean
CflibsFormal.outerLoop_contracts.{u_1, u_2, u_3} {ιe : Type u_1} [Fintype ιe] [Nonempty ιe]
  {κe : Type u_2} [Fintype κe] [Nonempty κe] {ιl : Type u_3} [Fintype ιl] [Nonempty ιl]
  {kB me h chi R0 R : ℝ} {gZ EZ : ιe → ℝ} {gZ1 EZ1 : κe → ℝ} {E yb svec : ιl → ℝ}
  {offConst Tmin Tmax nemin nemax smin : ℝ} (hTle : Tmin ≤ Tmax) (hkB : 0 < kB) (hme : 0 < me)
  (hh : 0 < h) (hchi : 0 ≤ chi) (hTmin : 0 < Tmin) (hgZ : ∀ (k : ιe), 0 < gZ k)
  (hEZ : ∀ (k : ιe), 0 ≤ EZ k) (hgZ1 : ∀ (k : κe), 0 < gZ1 k) (hEZ1 : ∀ (k : κe), 0 ≤ EZ1 k)
  (hR0 : 0 < R0) (hR : R0 ≤ R) (hvar : 0 < ∑ k, (E k - CflibsFormal.mean E) ^ 2)
  (hnemin : 0 < nemin) (hsmin : 0 < smin)
  (hmapsNe :
    ∀ T ∈ Set.Icc Tmin Tmax,
      CflibsFormal.electronDensityFromRatio kB T me h chi gZ EZ gZ1 EZ1 R ∈ Set.Icc nemin nemax)
  (hmapsT :
    ∀ ne ∈ Set.Icc nemin nemax,
      CflibsFormal.combinedSlopeTempUpdate kB E yb svec offConst ne ∈ Set.Icc Tmin Tmax)
  (hslopeFloor :
    ∀ ne ∈ Set.Icc nemin nemax,
      smin ≤ CflibsFormal.combinedSahaBoltzmannSlope E yb svec offConst ne)
  (hL1nn : 0 ≤ CflibsFormal.sahaFactorLipConst kB Tmin Tmax me h chi gZ EZ gZ1 EZ1 / R0)
  (hgate :
    CflibsFormal.sahaFactorLipConst kB Tmin Tmax me h chi gZ EZ gZ1 EZ1 / R0 *
        ((|∑ k, (E k - CflibsFormal.mean E) * svec k| / ∑ k, (E k - CflibsFormal.mean E) ^ 2) /
          (kB * smin ^ 2 * nemin)) <
      1) :
  ∃ Tstar ∈ Set.Icc Tmin Tmax,
    CflibsFormal.outerMap
          (fun T => CflibsFormal.electronDensityFromRatio kB T me h chi gZ EZ gZ1 EZ1 R)
          (fun ne => CflibsFormal.combinedSlopeTempUpdate kB E yb svec offConst ne) Tstar =
        Tstar ∧
      (∀ T ∈ Set.Icc Tmin Tmax,
          CflibsFormal.outerMap
                (fun T => CflibsFormal.electronDensityFromRatio kB T me h chi gZ EZ gZ1 EZ1 R)
                (fun ne => CflibsFormal.combinedSlopeTempUpdate kB E yb svec offConst ne) T =
              T →
            T = Tstar) ∧
        ∀ T0 ∈ Set.Icc Tmin Tmax,
          Filter.Tendsto
            (fun n =>
              (CflibsFormal.outerMap
                    (fun T => CflibsFormal.electronDensityFromRatio kB T me h chi gZ EZ gZ1 EZ1 R)
                    fun ne => CflibsFormal.combinedSlopeTempUpdate kB E yb svec offConst ne)^[n]
                T0)
            Filter.atTop (nhds Tstar)
```

> **The CF-LIBS outer temperature loop contracts** (`REDUCED`; Aguilera & Aragón 2007,
> Model B). Instantiating the abstract two-leg spine `outerContraction_box` with the concrete
> CF-LIBS legs — the Saha density reader `legNe T = electronDensityFromRatio … T … R` and the
> combined-slope temperature update `legT ne = combinedSlopeTempUpdate … ne` — the outer sweep
> `Φ = legT ∘ legNe` on `[Tmin,Tmax]` has a **unique** self-consistent fixed point `T⋆` and the
> iterates `Φ^[n] T₀` converge to `T⋆` from every start in the box.
> 
> The density leg's `T`-Lipschitz constant is `L₁ = sahaFactorLipConst/R₀`
> (`electronDensityFromRatio_lipschitz_temp`); the temperature leg's `n_e`-Lipschitz constant is
> `L₂ = (|∑ₖ (Eₖ − Ē)·sₖ|/SS_E)/(k_B·smin²·nemin)` (`combinedSlopeTempUpdate_lipschitz`). The
> hypothesis `hgate : L₁·L₂ < 1` is the runtime-checkable convergence certificate the solver
> flag gates on; `hmapsNe`, `hmapsT` are the two interval invariances and `hslopeFloor` the
> combined-slope floor (genuine side conditions, cf. `sahaIter_mapsTo`). Non-degenerate via the
> combined Saha–Boltzmann slope (contrast the composition-independent two-line temperature). 

### `CflibsFormal.partitionFunction_lipschitz_temp`

Module `CflibsFormal.PartitionLipschitz` · scope `REDUCED`

```lean
CflibsFormal.partitionFunction_lipschitz_temp.{u_1} {ι : Type u_1} [Fintype ι] {kB Tmin T1 T2 : ℝ}
  {g E : ι → ℝ} (hkB : 0 < kB) (hTmin : 0 < Tmin) (hT1 : Tmin ≤ T1) (hT2 : Tmin ≤ T2)
  (hg : ∀ (k : ι), 0 < g k) (hE : ∀ (k : ι), 0 ≤ E k) :
  |CflibsFormal.partitionFunction kB T1 g E - CflibsFormal.partitionFunction kB T2 g E| ≤
    (∑ k, g k * E k) / (kB * Tmin ^ 2) * |T1 - T2|
```

> **Lipschitz-in-`T` partition-function bound (`REDUCED`, Tognoni 2010).**
> 
> On a temperature floor `Tmin ≤ T₁, T₂` (`0 < Tmin`), with `k_B > 0`, `gₖ > 0`, `Eₖ ≥ 0`, the
> partition function is Lipschitz in `T` with the explicit constant `L = (∑ₖ gₖ·Eₖ)/(k_B·Tmin²)`:
> 
> `|U(T₁) − U(T₂)| ≤ (∑ₖ gₖ·Eₖ)/(k_B·Tmin²) · |T₁ − T₂|`.
> 
> Immediate from `partitionFunction_two_point_bound` and the inverse-temperature gap bound
> `|1/(k_B T₁) − 1/(k_B T₂)| ≤ |T₁ − T₂|/(k_B·Tmin²)`. Reduction: the floor `Tmin` supplies the
> `T₁ T₂ ≥ Tmin²` over-estimate on top of the two-point bound's `exp ≤ 1` over-estimate. This is the
> `U_s(T)` sensitivity leg of the CF-LIBS temperature→composition error budget. 

### `CflibsFormal.partitionFunction_relative_error_temp`

Module `CflibsFormal.PartitionLipschitz` · scope `REDUCED`

```lean
CflibsFormal.partitionFunction_relative_error_temp.{u_1} {ι : Type u_1} [Fintype ι] [Nonempty ι]
  {kB Tmin T1 T2 : ℝ} {g E : ι → ℝ} (hkB : 0 < kB) (hTmin : 0 < Tmin) (hT1 : Tmin ≤ T1)
  (hT2 : Tmin ≤ T2) (hg : ∀ (k : ι), 0 < g k) (hE : ∀ (k : ι), 0 ≤ E k) :
  |CflibsFormal.partitionFunction kB T1 g E - CflibsFormal.partitionFunction kB T2 g E| /
      CflibsFormal.partitionFunction kB T2 g E ≤
    (∑ k, g k * E k) / (kB * Tmin ^ 2) * |T1 - T2| / CflibsFormal.partitionFunction kB T2 g E
```

> **Relative partition-function error from a temperature error (`REDUCED`, Tognoni 2010).**
> 
> Dividing the Lipschitz bound by `U(T₂) > 0` (`partitionFunction_pos`) yields the *relative*
> partition-function error induced by a temperature error:
> 
> `|U(T₁) − U(T₂)|/U(T₂) ≤ (∑ₖ gₖ·Eₖ)/(k_B·Tmin²)·|T₁ − T₂| / U(T₂)`.
> 
> The right-hand side is the scalar `δ_U` that a `U`-channel density bound consumes (e.g. the `δ_U`
> slot of `AtomicDataPerturbation.classicDensity_aliasing_error_channels`): a recovered-temperature
> error `|T̂ − T|` becomes a bounded relative `U`-error. Reduction: same over-estimates as
> `partitionFunction_lipschitz_temp`. See the module's Honest-scope note for why the composition into
> the density channel is stated as a handoff (the density channel models a same-`T` atomic-data
> `U`-mismatch, not the same-`g` temperature `U`-shift) rather than a literal Lean corollary. 

### `CflibsFormal.partitionFunction_two_point_bound`

Module `CflibsFormal.PartitionLipschitz` · scope `REDUCED`

```lean
CflibsFormal.partitionFunction_two_point_bound.{u_1} {ι : Type u_1} [Fintype ι] {kB T1 T2 : ℝ}
  {g E : ι → ℝ} (hkB : 0 < kB) (hT1 : 0 < T1) (hT2 : 0 < T2) (hg : ∀ (k : ι), 0 < g k)
  (hE : ∀ (k : ι), 0 ≤ E k) :
  |CflibsFormal.partitionFunction kB T1 g E - CflibsFormal.partitionFunction kB T2 g E| ≤
    (∑ k, g k * E k) * |1 / (kB * T1) - 1 / (kB * T2)|
```

> **Two-point partition-function bound — the `U_s(T)` sensitivity leg (`REDUCED`, Tognoni 2010).**
> 
> For `k_B > 0`, `0 < T₁, T₂`, positive degeneracies `gₖ > 0`, and non-negative level energies
> `Eₖ ≥ 0` (measured from the ground state), the partition function's sensitivity to a change of
> inverse temperature is bounded by
> 
> `|U(T₁) − U(T₂)| ≤ (∑ₖ gₖ·Eₖ)·|1/(k_B T₁) − 1/(k_B T₂)|`.
> 
> Reduction: the exact sensitivity of the `k`-th term is `gₖ·Eₖ·exp(−Eₖ/(k_B T))`; the constant
> `∑ₖ gₖ·Eₖ` upper-bounds it by discarding `exp(−Eₖ/(k_B T)) ≤ 1`, which holds precisely because
> `Eₖ ≥ 0` makes both exponents `≤ 0` (so `max(exp aₖ, exp bₖ) ≤ 1`). The forward model is exact;
> only the constant is an honest over-estimate. 

### `CflibsFormal.joint_twoLevel_box_isStrictMin`

Module `CflibsFormal.ProfiledTUniqueness` · scope `REDUCED`

```lean
CflibsFormal.joint_twoLevel_box_isStrictMin.{u_1} {ι : Type u_1} [Fintype ι] [DecidableEq ι]
  [Nonempty ι] {kB Fcal Tmin Tmax Tstar Ea Eb : ℝ} {g E A obs : ι → ℝ} {S : Finset ι} (hkB : 0 < kB)
  (hg : ∀ (k : ι), 0 < g k) (hFcal : 0 < Fcal) (hA : ∀ (k : ι), 0 < A k) (hSmem : ∀ k ∈ S, E k = Ea)
  (hScom : ∀ k ∉ S, E k = Eb) (hEne : Ea ≠ Eb) (i : ι) (hi : i ∈ S) (j : ι) (hj : j ∉ S)
  (hP : 0 < ∑ k ∈ S, A k * g k * obs k) (hTmin : 0 < Tmin) (hTsL : Tmin ≤ Tstar)
  (hTsR : Tstar ≤ Tmax)
  (hstar :
    ((∑ k ∈ Finset.univ \ S, (A k * g k) ^ 2) * ∑ k ∈ S, A k * g k * obs k) *
        CflibsFormal.boltzmannFactor kB Tstar Eb =
      ((∑ k ∈ S, (A k * g k) ^ 2) * ∑ k ∈ Finset.univ \ S, A k * g k * obs k) *
        CflibsFormal.boltzmannFactor kB Tstar Ea)
  {p : ℝ × ℝ} (hp : p.1 ∈ Set.Icc Tmin Tmax)
  (hne : p ≠ (Tstar, CflibsFormal.profiledDensity kB Fcal g E A obs Tstar)) :
  CflibsFormal.nlObjective kB Fcal g E A obs
      (Tstar, CflibsFormal.profiledDensity kB Fcal g E A obs Tstar) <
    CflibsFormal.nlObjective kB Fcal g E A obs p
```

> **Strict joint `(T, N)` minimum (`m` lines, two energies; REDUCED, Tognoni 2010).** Under the
> hypotheses of `profiledResidual_twoLevel_strictUnimodalOn`, the pair `(Tstar, N̂(Tstar))` strictly
> beats **every** other parameter pair whose temperature lies in the box — the density being
> completely unconstrained. Two ingredients: strict unimodality pins the temperature, and the
> `N`-section of `nlObjective` is a strictly convex quadratic whose unique minimizer is the profiled
> density (`nlObjective_Nsection_lt_of_ne`). 

### `CflibsFormal.joint_twoLevel_box_minimizer_unique`

Module `CflibsFormal.ProfiledTUniqueness` · scope `REDUCED`

```lean
CflibsFormal.joint_twoLevel_box_minimizer_unique.{u_1} {ι : Type u_1} [Fintype ι] [DecidableEq ι]
  [Nonempty ι] {kB Fcal Tmin Tmax Tstar Ea Eb : ℝ} {g E A obs : ι → ℝ} {S : Finset ι} (hkB : 0 < kB)
  (hg : ∀ (k : ι), 0 < g k) (hFcal : 0 < Fcal) (hA : ∀ (k : ι), 0 < A k) (hSmem : ∀ k ∈ S, E k = Ea)
  (hScom : ∀ k ∉ S, E k = Eb) (hEne : Ea ≠ Eb) (i : ι) (hi : i ∈ S) (j : ι) (hj : j ∉ S)
  (hP : 0 < ∑ k ∈ S, A k * g k * obs k) (hTmin : 0 < Tmin) (hTsL : Tmin ≤ Tstar)
  (hTsR : Tstar ≤ Tmax)
  (hstar :
    ((∑ k ∈ Finset.univ \ S, (A k * g k) ^ 2) * ∑ k ∈ S, A k * g k * obs k) *
        CflibsFormal.boltzmannFactor kB Tstar Eb =
      ((∑ k ∈ S, (A k * g k) ^ 2) * ∑ k ∈ Finset.univ \ S, A k * g k * obs k) *
        CflibsFormal.boltzmannFactor kB Tstar Ea)
  {p : ℝ × ℝ} (hp : p ∈ Set.Icc Tmin Tmax ×ˢ Set.univ)
  (hmin : IsMinOn (CflibsFormal.nlObjective kB Fcal g E A obs) (Set.Icc Tmin Tmax ×ˢ Set.univ) p) :
  p = (Tstar, CflibsFormal.profiledDensity kB Fcal g E A obs Tstar)
```

> **Uniqueness of the joint `(T, N)` minimizer (`m` lines, two energies; REDUCED, Tognoni 2010).**
> Under the hypotheses of `profiledResidual_twoLevel_strictUnimodalOn`, ANY minimizer of the joint
> nonlinear least-squares objective over `[Tmin, Tmax] ×ˢ ℝ` equals `(Tstar, N̂(Tstar))` — the
> `T`-direction uniqueness that VARPRO alone could not supply, now for arbitrarily many lines at two
> upper-level energies. Scope note: `NonlinearLeastSquares.nlObjective_exists_min` gives existence on
> a compact box `[Tmin,Tmax] ×ˢ [Nmin,Nmax]`, a DIFFERENT region; the two do not compose into a
> single existence-and-uniqueness statement unless `N̂(Tstar)` lies in that density box, which is not
> proved here. 

### `CflibsFormal.joint_two_box_isStrictMin`

Module `CflibsFormal.ProfiledTUniqueness` · scope `REDUCED`

```lean
CflibsFormal.joint_two_box_isStrictMin {kB Fcal Tmin Tmax Tstar : ℝ} {g E A obs : Fin 2 → ℝ}
  (hkB : 0 < kB) (hg : ∀ (k : Fin 2), 0 < g k) (hFcal : 0 < Fcal) (hA : ∀ (k : Fin 2), 0 < A k)
  (ho0 : 0 < obs 0) (ho1 : 0 < obs 1) (hE : E 0 ≠ E 1) (hTmin : 0 < Tmin) (hTsL : Tmin ≤ Tstar)
  (hTsR : Tstar ≤ Tmax)
  (hstar :
    obs 1 * CflibsFormal.lineIntensity kB Tstar 1 Fcal g E A 0 =
      obs 0 * CflibsFormal.lineIntensity kB Tstar 1 Fcal g E A 1)
  {p : ℝ × ℝ} (hp : p.1 ∈ Set.Icc Tmin Tmax)
  (hne : p ≠ (Tstar, CflibsFormal.profiledDensity kB Fcal g E A obs Tstar)) :
  CflibsFormal.nlObjective kB Fcal g E A obs
      (Tstar, CflibsFormal.profiledDensity kB Fcal g E A obs Tstar) <
    CflibsFormal.nlObjective kB Fcal g E A obs p
```

> **Strict joint `(T, N)` minimum, two lines (REDUCED, Tognoni 2010).** The explicit corollary of
> `ProfiledUnimodality.profiledResidual_two_Tstar_isStrictMin` that was implicit but never stated:
> strict unimodality of the profiled residual on the box, plus the VARPRO fact that the `N`-section
> has the profiled density as its unique minimizer, makes `(Tstar, N̂(Tstar))` a strict global
> minimizer of the joint objective over `[Tmin, Tmax] ×ˢ ℝ`. This is bookkeeping over landed results,
> not new mathematics. 

### `CflibsFormal.joint_two_box_minimizer_unique`

Module `CflibsFormal.ProfiledTUniqueness` · scope `REDUCED`

```lean
CflibsFormal.joint_two_box_minimizer_unique {kB Fcal Tmin Tmax Tstar : ℝ} {g E A obs : Fin 2 → ℝ}
  (hkB : 0 < kB) (hg : ∀ (k : Fin 2), 0 < g k) (hFcal : 0 < Fcal) (hA : ∀ (k : Fin 2), 0 < A k)
  (ho0 : 0 < obs 0) (ho1 : 0 < obs 1) (hE : E 0 ≠ E 1) (hTmin : 0 < Tmin) (hTsL : Tmin ≤ Tstar)
  (hTsR : Tstar ≤ Tmax)
  (hstar :
    obs 1 * CflibsFormal.lineIntensity kB Tstar 1 Fcal g E A 0 =
      obs 0 * CflibsFormal.lineIntensity kB Tstar 1 Fcal g E A 1)
  {p : ℝ × ℝ} (hp : p ∈ Set.Icc Tmin Tmax ×ˢ Set.univ)
  (hmin : IsMinOn (CflibsFormal.nlObjective kB Fcal g E A obs) (Set.Icc Tmin Tmax ×ˢ Set.univ) p) :
  p = (Tstar, CflibsFormal.profiledDensity kB Fcal g E A obs Tstar)
```

> **Uniqueness of the joint `(T, N)` minimizer, two lines (REDUCED, Tognoni 2010).** Any minimizer
> of the joint objective over `[Tmin, Tmax] ×ˢ ℝ` equals `(Tstar, N̂(Tstar))`. The statement the
> `ProfiledUnimodality` module's `V`-shape always implied; recorded here so that "a joint minimizer
> of the two-line CF-LIBS fit over this region, **if one exists**, is unique and equals
> `(Tstar, N̂(Tstar))`" is an actual theorem rather than a reading of one. This is a *conditional*
> uniqueness statement, not an existence-and-uniqueness statement: the minimizer is supplied by the
> hypothesis `hmin`, and existence over this non-compact region is not proved anywhere here. 

### `CflibsFormal.profiledResidual_eq_rayleigh`

Module `CflibsFormal.ProfiledTUniqueness` · scope `PURE-MATH`

```lean
CflibsFormal.profiledResidual_eq_rayleigh.{u_1} {ι : Type u_1} [Fintype ι] {kB Fcal T : ℝ}
  {g E A obs : ι → ℝ} (hc : 0 < ∑ k, CflibsFormal.lineIntensity kB T 1 Fcal g E A k ^ 2) :
  CflibsFormal.nlObjective kB Fcal g E A obs (T, CflibsFormal.profiledDensity kB Fcal g E A obs T) =
    ∑ k, obs k ^ 2 -
      (∑ k, CflibsFormal.lineIntensity kB T 1 Fcal g E A k * obs k) ^ 2 /
        ∑ k, CflibsFormal.lineIntensity kB T 1 Fcal g E A k ^ 2
```

> **VARPRO residual in Rayleigh form (PURE-MATH).** Evaluating the joint objective at the
> variable-projection density `N̂(T)` gives, for *any* finite line set and *any* observation,
> `nlObjective … (T, N̂(T)) = ‖obs‖² − ⟨c(T), obs⟩² / ‖c(T)‖²`,
> where `c_k(T) = lineIntensity kB T 1 Fcal g E A k` is the unit-density intensity vector. Pure
> algebra: expand the `N`-section `∑ₖ (N·c_k − obs_k)²` as `N²‖c‖² − 2N⟨c,obs⟩ + ‖obs‖²` and
> substitute `N = ⟨c,obs⟩/‖c‖²`. This is the general-`m` sibling of the `Fin 2`-only
> `profiledResidual_two_closed_form`, and the form in which the residual is manifestly **invariant
> under rescaling `c`** — which is why the calibration `Fcal` and the whole partition function `U(T)`
> drop out downstream. 

### `CflibsFormal.profiledResidual_twoLevel_Tstar_isStrictMin`

Module `CflibsFormal.ProfiledTUniqueness` · scope `REDUCED`

```lean
CflibsFormal.profiledResidual_twoLevel_Tstar_isStrictMin.{u_1} {ι : Type u_1} [Fintype ι]
  [DecidableEq ι] [Nonempty ι] {kB Fcal Tmin Tmax Tstar Ea Eb : ℝ} {g E A obs : ι → ℝ}
  {S : Finset ι} (hkB : 0 < kB) (hg : ∀ (k : ι), 0 < g k) (hFcal : 0 < Fcal)
  (hA : ∀ (k : ι), 0 < A k) (hSmem : ∀ k ∈ S, E k = Ea) (hScom : ∀ k ∉ S, E k = Eb) (hEne : Ea ≠ Eb)
  (i : ι) (hi : i ∈ S) (j : ι) (hj : j ∉ S) (hP : 0 < ∑ k ∈ S, A k * g k * obs k) (hTmin : 0 < Tmin)
  (hTsL : Tmin ≤ Tstar) (hTsR : Tstar ≤ Tmax)
  (hstar :
    ((∑ k ∈ Finset.univ \ S, (A k * g k) ^ 2) * ∑ k ∈ S, A k * g k * obs k) *
        CflibsFormal.boltzmannFactor kB Tstar Eb =
      ((∑ k ∈ S, (A k * g k) ^ 2) * ∑ k ∈ Finset.univ \ S, A k * g k * obs k) *
        CflibsFormal.boltzmannFactor kB Tstar Ea)
  {T : ℝ} (hT : T ∈ Set.Icc Tmin Tmax) (hne : T ≠ Tstar) :
  CflibsFormal.nlObjective kB Fcal g E A obs
      (Tstar, CflibsFormal.profiledDensity kB Fcal g E A obs Tstar) <
    CflibsFormal.nlObjective kB Fcal g E A obs (T, CflibsFormal.profiledDensity kB Fcal g E A obs T)
```

> **`Tstar` is the strict profiled-`T` minimizer on the box (`m` lines, two energies; REDUCED,
> Ciucci 1999).** Under the hypotheses of `profiledResidual_twoLevel_strictUnimodalOn`, every box
> temperature other than the apex gives a strictly larger density-profiled residual. Hence the
> profiled `T`-minimizer on `[Tmin, Tmax]` is **unique** and equals `Tstar`; there is no spurious
> local minimum in the box. 

### `CflibsFormal.profiledResidual_twoLevel_strictUnimodalOn`

Module `CflibsFormal.ProfiledTUniqueness` · scope `REDUCED`

```lean
CflibsFormal.profiledResidual_twoLevel_strictUnimodalOn.{u_1} {ι : Type u_1} [Fintype ι]
  [DecidableEq ι] [Nonempty ι] {kB Fcal Tmin Tmax Tstar Ea Eb : ℝ} {g E A obs : ι → ℝ}
  {S : Finset ι} (hkB : 0 < kB) (hg : ∀ (k : ι), 0 < g k) (hFcal : 0 < Fcal)
  (hA : ∀ (k : ι), 0 < A k) (hSmem : ∀ k ∈ S, E k = Ea) (hScom : ∀ k ∉ S, E k = Eb) (hEne : Ea ≠ Eb)
  (i : ι) (hi : i ∈ S) (j : ι) (hj : j ∉ S) (hP : 0 < ∑ k ∈ S, A k * g k * obs k) (hTmin : 0 < Tmin)
  (hTsL : Tmin ≤ Tstar) (_hTsR : Tstar ≤ Tmax)
  (hstar :
    ((∑ k ∈ Finset.univ \ S, (A k * g k) ^ 2) * ∑ k ∈ S, A k * g k * obs k) *
        CflibsFormal.boltzmannFactor kB Tstar Eb =
      ((∑ k ∈ S, (A k * g k) ^ 2) * ∑ k ∈ Finset.univ \ S, A k * g k * obs k) *
        CflibsFormal.boltzmannFactor kB Tstar Ea) :
  StrictAntiOn
      (fun T =>
        CflibsFormal.nlObjective kB Fcal g E A obs
          (T, CflibsFormal.profiledDensity kB Fcal g E A obs T))
      (Set.Icc Tmin Tstar) ∧
    StrictMonoOn
      (fun T =>
        CflibsFormal.nlObjective kB Fcal g E A obs
          (T, CflibsFormal.profiledDensity kB Fcal g E A obs T))
      (Set.Icc Tstar Tmax)
```

> **Strict unimodality of the profiled objective in `T`, `m` lines at two energies (REDUCED,
> Ciucci 1999).** Let the upper-level energies take exactly two distinct values, `E k = E_a` on a
> line subset `S` and `E k = E_b` off it, with at least one line in each group (`i ∈ S`, `j ∉ S`) and
> `E_a ≠ E_b`. Let the group-`S` projection be positive, `P = ∑_{k∈S} A_k g_k obs_k > 0` (automatic
> for a nonnegative, not-identically-zero spectrum on those lines). Let `Tstar ∈ [Tmin, Tmax]` with
> `Tmin > 0` satisfy the **apex** condition
> `S_B·P·exp(−E_b/(k_B Tstar)) = S_A·Q·exp(−E_a/(k_B Tstar))`,
> i.e. the group-aggregated observed level ratio `(Q/S_B)/(P/S_A)` equals the Boltzmann ratio at
> `Tstar`. Then the density-profiled objective `T ↦ nlObjective … (T, N̂(T))` is **strictly
> decreasing** on `[Tmin, Tstar]` and **strictly increasing** on `[Tstar, Tmax]`.
> 
> This is a genuine widening of `ProfiledUnimodality.profiledResidual_two_strictUnimodalOn`: the
> number of lines `m` is arbitrary, and the component of `obs` orthogonal to the two-dimensional
> group plane — which can only exist once `m ≥ 3` — is carried through the argument as a
> `T`-independent offset rather than assumed away. It is NOT a general `m`-line result: three or
> more *distinct* energies are outside the argument. 

### `CflibsFormal.profiledResidual_twoLevel_strictUnimodal_onManifold`

Module `CflibsFormal.ProfiledTUniqueness` · scope `REDUCED`

```lean
CflibsFormal.profiledResidual_twoLevel_strictUnimodal_onManifold.{u_1} {ι : Type u_1} [Fintype ι]
  [Nonempty ι] {kB Fcal Tmin Tmax T0 N0 Ea Eb : ℝ} {g E A obs : ι → ℝ} {S : Finset ι} (hkB : 0 < kB)
  (hg : ∀ (k : ι), 0 < g k) (hFcal : 0 < Fcal) (hA : ∀ (k : ι), 0 < A k) (hN0 : 0 < N0)
  (hSmem : ∀ k ∈ S, E k = Ea) (hScom : ∀ k ∉ S, E k = Eb) (hEne : Ea ≠ Eb) (i : ι) (hi : i ∈ S)
  (j : ι) (hj : j ∉ S) (hTmin : 0 < Tmin) (hTL : Tmin ≤ T0) (hTR : T0 ≤ Tmax)
  (hobs : ∀ (k : ι), obs k = CflibsFormal.lineIntensity kB T0 N0 Fcal g E A k) :
  StrictAntiOn
      (fun T =>
        CflibsFormal.nlObjective kB Fcal g E A obs
          (T, CflibsFormal.profiledDensity kB Fcal g E A obs T))
      (Set.Icc Tmin T0) ∧
    StrictMonoOn
      (fun T =>
        CflibsFormal.nlObjective kB Fcal g E A obs
          (T, CflibsFormal.profiledDensity kB Fcal g E A obs T))
      (Set.Icc T0 Tmax)
```

> **On-manifold strict unimodality about the true temperature (`m` lines, two energies; REDUCED,
> Ciucci 1999).** In the noise-free case `obs = forward(T₀, N₀)` with `N₀ > 0`, the apex is `T₀`
> itself, so the density-profiled objective is strictly decreasing on `[Tmin, T₀]` and strictly
> increasing on `[T₀, Tmax]` for a line set with arbitrarily many lines at exactly two distinct upper
> level energies. This upgrades `NonlinearLeastSquares.profiledT_onManifold_unique` (which shows the
> residual VANISHES only at `T₀`) to a local shape statement, and widens
> `ProfiledUnimodality.profiledResidual_two_strictUnimodal_onManifold` past two lines. 

### `CflibsFormal.profiledResidual_two_Tstar_isStrictMin`

Module `CflibsFormal.ProfiledUnimodality` · scope `REDUCED`

```lean
CflibsFormal.profiledResidual_two_Tstar_isStrictMin {kB Fcal Tmin Tmax Tstar : ℝ}
  {g E A obs : Fin 2 → ℝ} (hkB : 0 < kB) (hg : ∀ (k : Fin 2), 0 < g k) (hFcal : 0 < Fcal)
  (hA : ∀ (k : Fin 2), 0 < A k) (ho0 : 0 < obs 0) (ho1 : 0 < obs 1) (hE : E 0 ≠ E 1)
  (hTmin : 0 < Tmin) (hTsL : Tmin ≤ Tstar) (hTsR : Tstar ≤ Tmax)
  (hstar :
    obs 1 * CflibsFormal.lineIntensity kB Tstar 1 Fcal g E A 0 =
      obs 0 * CflibsFormal.lineIntensity kB Tstar 1 Fcal g E A 1)
  {T : ℝ} (hT : T ∈ Set.Icc Tmin Tmax) (hne : T ≠ Tstar) :
  CflibsFormal.nlObjective kB Fcal g E A obs
      (Tstar, CflibsFormal.profiledDensity kB Fcal g E A obs Tstar) <
    CflibsFormal.nlObjective kB Fcal g E A obs (T, CflibsFormal.profiledDensity kB Fcal g E A obs T)
```

> **Unique minimizer / no spurious local minimum (REDUCED, Ciucci 1999).** Under the hypotheses of
> `profiledResidual_two_strictUnimodalOn`, the apex temperature `Tstar` is the **strict** global
> minimizer of the density-profiled objective on the box `[Tmin, Tmax]`: every other box temperature
> gives a strictly larger profiled residual — the objective strictly decreases toward `Tstar` on each
> side, so there is no spurious local minimum in the region of attraction. (The reading "a descent
> solver cannot stall away from `Tstar`" is the intended consequence, not a formalized solver
> theorem.) 

### `CflibsFormal.profiledResidual_two_strictUnimodalOn`

Module `CflibsFormal.ProfiledUnimodality` · scope `REDUCED`

```lean
CflibsFormal.profiledResidual_two_strictUnimodalOn {kB Fcal Tmin Tmax Tstar : ℝ}
  {g E A obs : Fin 2 → ℝ} (hkB : 0 < kB) (hg : ∀ (k : Fin 2), 0 < g k) (hFcal : 0 < Fcal)
  (hA : ∀ (k : Fin 2), 0 < A k) (ho0 : 0 < obs 0) (ho1 : 0 < obs 1) (hE : E 0 ≠ E 1)
  (hTmin : 0 < Tmin) (hTsL : Tmin ≤ Tstar) (_hTsR : Tstar ≤ Tmax)
  (hstar :
    obs 1 * CflibsFormal.lineIntensity kB Tstar 1 Fcal g E A 0 =
      obs 0 * CflibsFormal.lineIntensity kB Tstar 1 Fcal g E A 1) :
  StrictAntiOn
      (fun T =>
        CflibsFormal.nlObjective kB Fcal g E A obs
          (T, CflibsFormal.profiledDensity kB Fcal g E A obs T))
      (Set.Icc Tmin Tstar) ∧
    StrictMonoOn
      (fun T =>
        CflibsFormal.nlObjective kB Fcal g E A obs
          (T, CflibsFormal.profiledDensity kB Fcal g E A obs T))
      (Set.Icc Tstar Tmax)
```

> **Two-line strict unimodality of the profiled objective in `T` (REDUCED, Ciucci 1999).** For a
> positive two-line spectrum `obs 0, obs 1 > 0`, distinct upper-level energies `E 0 ≠ E 1`, and an
> apex temperature `Tstar ∈ [Tmin, Tmax]` (with `Tmin > 0`) at which the intensity ratio matches the
> observed ratio — `obs 1 · c₀(Tstar) = obs 0 · c₁(Tstar)`, `c_k(T) = lineIntensity kB T 1 Fcal g E A
> k` — the density-profiled objective `g(T) = nlObjective … (T, N̂(T))` is **strictly unimodal**
> on the box: strictly decreasing on `[Tmin, Tstar]` and strictly increasing on `[Tstar, Tmax]`.
> 
> Mechanism: `g(T) = profiledRatioResidual (obs 0) (obs 1) (t(T))` (`profiledResidual_two_eq_ratio`),
> `t(T) = c₁(T)/c₀(T)` is strictly monotone in `T` (`lineIntensityRatio_{lt,gt}_of_lt`, distinct
> energies), and `profiledRatioResidual` is strictly decreasing below the apex `t(Tstar) = obs₁/obs₀`
> and strictly increasing above it (`ratioResidual_lt_{below,above}`; the antipode `v = obs₀ + obs₁·t
> > 0` is automatic since `obs, t > 0`). No Hessian/curvature computation. 

### `CflibsFormal.profiledResidual_two_strictUnimodal_onManifold`

Module `CflibsFormal.ProfiledUnimodality` · scope `REDUCED`

```lean
CflibsFormal.profiledResidual_two_strictUnimodal_onManifold {kB Fcal Tmin Tmax T0 N0 : ℝ}
  {g E A obs : Fin 2 → ℝ} (hkB : 0 < kB) (hg : ∀ (k : Fin 2), 0 < g k) (hFcal : 0 < Fcal)
  (hA : ∀ (k : Fin 2), 0 < A k) (hN0 : 0 < N0) (hE : E 0 ≠ E 1) (hTmin : 0 < Tmin) (hTL : Tmin ≤ T0)
  (hTR : T0 ≤ Tmax)
  (hobs : ∀ (k : Fin 2), obs k = CflibsFormal.lineIntensity kB T0 N0 Fcal g E A k) :
  StrictAntiOn
      (fun T =>
        CflibsFormal.nlObjective kB Fcal g E A obs
          (T, CflibsFormal.profiledDensity kB Fcal g E A obs T))
      (Set.Icc Tmin T0) ∧
    StrictMonoOn
      (fun T =>
        CflibsFormal.nlObjective kB Fcal g E A obs
          (T, CflibsFormal.profiledDensity kB Fcal g E A obs T))
      (Set.Icc T0 Tmax)
```

> **On-manifold strict unimodality about the true temperature `T₀` (REDUCED, Ciucci 1999).**
> noise-free case `obs = forward(T₀, N₀)` (with `N₀ > 0`), the apex is `Tstar = T₀`, so the profiled
> objective `g` is strictly decreasing on `[Tmin, T₀]`, strictly increasing on `[T₀, Tmax]`, so `T₀`
> is the unique box minimizer (a descent solver's convergence to it is the informal consequence, not
> formalized). This upgrades the
> existence/zero-value anchor `nlObjective_onManifold_min` to a full local *shape* statement. The apex
> identity `obs 1 · c₀(T₀) = obs 0 · c₁(T₀)` holds since both sides equal `N₀·c₁(T₀)·c₀(T₀)` (forward
> map linear in `N`). 

### `CflibsFormal.electronDensity_antitone`

Module `CflibsFormal.Saha` · scope `PURE-MATH`

```lean
CflibsFormal.electronDensity_antitone.{u_1, u_2} {ι : Type u_1} [Fintype ι] {κ : Type u_2}
  [Fintype κ] [Nonempty ι] [Nonempty κ] {kB T me h chi : ℝ} {gZ EZ : ι → ℝ} {gZ1 EZ1 : κ → ℝ}
  (hkB : 0 < kB) (hT : 0 < T) (hme : 0 < me) (hh : 0 < h) (hgZ : ∀ (k : ι), 0 < gZ k)
  (hgZ1 : ∀ (k : κ), 0 < gZ1 k) :
  StrictAntiOn (CflibsFormal.electronDensityFromRatio kB T me h chi gZ EZ gZ1 EZ1) (Set.Ioi 0)
```

> **Density diagnostic is injective.** The map `R ↦ n_e = S(T)/R` is strictly
> antitone on the positive reals: a larger measured stage ratio yields a strictly
> smaller inferred electron density, so a measured ratio determines `n_e` uniquely.
> This relies on `S(T) > 0`. 

### `CflibsFormal.log_sahaFactor`

Module `CflibsFormal.Saha` · scope `EXACT`

```lean
CflibsFormal.log_sahaFactor.{u_1, u_2} {ι : Type u_1} [Fintype ι] {κ : Type u_2} [Fintype κ]
  [Nonempty ι] [Nonempty κ] {kB T me h chi : ℝ} {gZ EZ : ι → ℝ} {gZ1 EZ1 : κ → ℝ} (hkB : 0 < kB)
  (hT : 0 < T) (hme : 0 < me) (hh : 0 < h) (hgZ : ∀ (k : ι), 0 < gZ k)
  (hgZ1 : ∀ (k : κ), 0 < gZ1 k) :
  Real.log (CflibsFormal.sahaFactor kB T me h chi gZ EZ gZ1 EZ1) =
    Real.log 2 +
          (Real.log (CflibsFormal.partitionFunction kB T gZ1 EZ1) -
            Real.log (CflibsFormal.partitionFunction kB T gZ EZ)) +
        3 / 2 * Real.log (CflibsFormal.thermalBracket kB T me h) -
      chi / (kB * T)
```

> **Saha-plot log identity.** The closed form of `log S(T)`: it is affine in
> `1/(k_B T)` with slope `−χ` (the `−χ/(k_B T)` term), plus a `(3/2)·log(bracket)`
> term (which contains `(3/2)·log T`), plus the constant `log 2` and the
> partition-function difference `log U_{z+1} − log U_z`.  This is the ionization
> analogue of `boltzmann_plot`, underlying linearized Saha-plot fitting. 

### `CflibsFormal.sahaFactor_pos`

Module `CflibsFormal.Saha` · scope `PURE-MATH`

```lean
CflibsFormal.sahaFactor_pos.{u_1, u_2} {ι : Type u_1} [Fintype ι] {κ : Type u_2} [Fintype κ]
  [Nonempty ι] [Nonempty κ] {kB T me h chi : ℝ} {gZ EZ : ι → ℝ} {gZ1 EZ1 : κ → ℝ} (hkB : 0 < kB)
  (hT : 0 < T) (hme : 0 < me) (hh : 0 < h) (hgZ : ∀ (k : ι), 0 < gZ k)
  (hgZ1 : ∀ (k : κ), 0 < gZ1 k) : 0 < CflibsFormal.sahaFactor kB T me h chi gZ EZ gZ1 EZ1
```

> **Positivity of the Saha factor.** Given positive physical constants and
> temperature, and positive statistical weights for both stages, `S(T) > 0`.  The
> ionization energy `χ` is unconstrained: `exp(−χ/(k_B T))` is positive for any
> sign of `χ`. 

### `CflibsFormal.saha_relation`

Module `CflibsFormal.Saha` · scope `EXACT`

```lean
CflibsFormal.saha_relation.{u_1, u_2} {ι : Type u_1} [Fintype ι] {κ : Type u_2} [Fintype κ]
  {kB T me h chi : ℝ} {gZ EZ : ι → ℝ} {gZ1 EZ1 : κ → ℝ} {R ne : ℝ} (hR : R ≠ 0) :
  ne = CflibsFormal.electronDensityFromRatio kB T me h chi gZ EZ gZ1 EZ1 R ↔
    R * ne = CflibsFormal.sahaFactor kB T me h chi gZ EZ gZ1 EZ1
```

> **Saha law ⇔ density inversion.** For a nonzero stage ratio `R`, the
> diagnostic form `n_e = S/R` is equivalent to the structural Saha law
> `R · n_e = S`.  The hypothesis `R ≠ 0` is load-bearing (otherwise `S/R` is
> ill-posed). 

### `CflibsFormal.thermalBracket_pos`

Module `CflibsFormal.Saha` · scope `PURE-MATH`

```lean
CflibsFormal.thermalBracket_pos {kB T me h : ℝ} (hkB : 0 < kB) (hT : 0 < T) (hme : 0 < me)
  (hh : 0 < h) : 0 < CflibsFormal.thermalBracket kB T me h
```

> The thermal-de-Broglie bracket is strictly positive when the physical
> constants and temperature are positive (`h ≠ 0` suffices, here via `h > 0`). 

### `CflibsFormal.neLeg_mapsTo`

Module `CflibsFormal.SahaEquilibrium` · scope `REDUCED`

```lean
CflibsFormal.neLeg_mapsTo.{u_1, u_2} {Tmin Tmax nemin nemax : ℝ} {ι : Type u_1} {κ : Type u_2}
  [Fintype ι] [Fintype κ] {kB me h chi Slo Shi R : ℝ} {gZ EZ : ι → ℝ} {gZ1 EZ1 : κ → ℝ} (hR : 0 < R)
  (hSlo : ∀ T ∈ Set.Icc Tmin Tmax, Slo ≤ CflibsFormal.sahaFactor kB T me h chi gZ EZ gZ1 EZ1)
  (hShi : ∀ T ∈ Set.Icc Tmin Tmax, CflibsFormal.sahaFactor kB T me h chi gZ EZ gZ1 EZ1 ≤ Shi)
  (hnemin : nemin ≤ Slo / R) (hnemax : Shi / R ≤ nemax) (T : ℝ) :
  T ∈ Set.Icc Tmin Tmax →
    CflibsFormal.electronDensityFromRatio kB T me h chi gZ EZ gZ1 EZ1 R ∈ Set.Icc nemin nemax
```

> **`n_e`-leg interval invariance** (`REDUCED`; Saha–Eggert (Griem)).  The density reader
> `legNe T = electronDensityFromRatio … T … R = S(T)/R` maps the temperature box `[Tmin,Tmax]`
> into the density box `[nemin,nemax]`, *provided* the Saha factor `S(T)` is boxed by
> `[Slo,Shi]` on `[Tmin,Tmax]`, `R > 0`, `nemin ≤ Slo/R` and `Shi/R ≤ nemax`.  This is the
> concrete `hmapsNe` hypothesis of `outerContraction_box`/`outerLoop_contracts` for the Saha
> density leg — a genuine side condition carried exactly as the inner loop's `sahaIter_mapsTo`
> carries `√(S·Ntot) ≤ b`.  The Saha-factor box bounds `hSlo`/`hShi` are inputs here (they are
> discharged downstream from the partition-function floor/ceiling of `SahaStability`,
> `partitionFunction_ge_floor`/`partitionFunction_le_sum`, in a module that imports it).  Proof:
> division is monotone in a positive denominator, so `Slo/R ≤ S(T)/R ≤ Shi/R`. 

### `CflibsFormal.sahaBoltzmann_plot`

Module `CflibsFormal.SahaInverse` · scope `REDUCED`

```lean
CflibsFormal.sahaBoltzmann_plot.{u_1, u_2} {ι : Type u_1} [Fintype ι] {κ : Type u_2} [Fintype κ]
  [Nonempty ι] [Nonempty κ] {kB T Nz Nz1 Fcal : ℝ} {gZ EZ AZ : ι → ℝ} {gZ1 EZ1 AZ1 : κ → ℝ}
  (hgZ : ∀ (k : ι), 0 < gZ k) (hgZ1 : ∀ (k : κ), 0 < gZ1 k) (hNz : 0 < Nz) (hNz1 : 0 < Nz1)
  (hFcal : 0 < Fcal) (hAZ : ∀ (k : ι), 0 < AZ k) (hAZ1 : ∀ (k : κ), 0 < AZ1 k) (kz : ι) (kz1 : κ) :
  CflibsFormal.sahaBoltzmannOrdinate kB T Nz Fcal gZ EZ AZ kz =
      CflibsFormal.stageIntercept kB T Nz Fcal gZ EZ - EZ kz / (kB * T) ∧
    CflibsFormal.sahaBoltzmannOrdinate kB T Nz1 Fcal gZ1 EZ1 AZ1 kz1 =
        CflibsFormal.stageIntercept kB T Nz1 Fcal gZ1 EZ1 - EZ1 kz1 / (kB * T) ∧
      CflibsFormal.stageIntercept kB T Nz1 Fcal gZ1 EZ1 -
          CflibsFormal.stageIntercept kB T Nz Fcal gZ EZ =
        Real.log (Nz1 / Nz) +
          (Real.log (CflibsFormal.partitionFunction kB T gZ EZ) -
            Real.log (CflibsFormal.partitionFunction kB T gZ1 EZ1))
```

> **Saha–Boltzmann plot.** Establishes that the neutral-stage and ion-stage lines
> BOTH lie on a single straight line of common slope `-1/(k_B T)` (parts 1 and 2, one
> per stage), and computes the inter-stage vertical shift between the two stage
> intercepts in closed form (part 3). This is the Saha–Boltzmann plot construction of
> Yalcin et al. and Aguilera & Aragón: a shared slope across stages with a
> stage-dependent ordinate offset. The shift formula
> `log(Nz1/Nz) + (log U_z − log U_{z+1})` is the bridge to the Saha relation:
> combined with the Saha law `Nz1/Nz = S/n_e`, the shift carries `n_e` (made explicit
> in `sahaBoltzmann_shift_eq_log_saha`). 

### `CflibsFormal.sahaBoltzmann_shift_eq_log_saha`

Module `CflibsFormal.SahaInverse` · scope `EXACT`

```lean
CflibsFormal.sahaBoltzmann_shift_eq_log_saha.{u_1, u_2} {ι : Type u_1} [Fintype ι] {κ : Type u_2}
  [Fintype κ] [Nonempty ι] [Nonempty κ] {kB T me h chi Nz Nz1 ne Fcal : ℝ} {gZ EZ : ι → ℝ}
  {gZ1 EZ1 : κ → ℝ} (hkB : 0 < kB) (hT : 0 < T) (hme : 0 < me) (hh : 0 < h)
  (hgZ : ∀ (k : ι), 0 < gZ k) (hgZ1 : ∀ (k : κ), 0 < gZ1 k) (hNz : 0 < Nz) (hNz1 : 0 < Nz1)
  (hFcal : 0 < Fcal) (hne : 0 < ne)
  (hsaha : Nz1 * ne / Nz = CflibsFormal.sahaFactor kB T me h chi gZ EZ gZ1 EZ1) :
  CflibsFormal.stageIntercept kB T Nz1 Fcal gZ1 EZ1 -
      CflibsFormal.stageIntercept kB T Nz Fcal gZ EZ =
    Real.log (CflibsFormal.sahaFactor kB T me h chi gZ EZ gZ1 EZ1) - Real.log ne +
      (Real.log (CflibsFormal.partitionFunction kB T gZ EZ) -
        Real.log (CflibsFormal.partitionFunction kB T gZ1 EZ1))
```

> **Saha–Boltzmann shift equals the log Saha factor.** Couples the Saha equation
> into the inter-stage shift: under the structural Saha law `Nz1·n_e/Nz = S(T)` (so
> `Nz1/Nz = S/n_e`), the Saha–Boltzmann intercept shift equals
> `log S − log n_e + (log U_z − log U_{z+1})`. Because `log S` is itself the closed
> form of `log_sahaFactor` (affine in `1/(k_B T)`), the shift is an explicit function
> of `n_e` and `T`: this is the precise sense in which the vertical offset between
> neutral and ion lines on the Saha–Boltzmann plot encodes the electron density. 

### `CflibsFormal.saha_joint_identifiability`

Module `CflibsFormal.SahaInverse` · scope `EXACT`

```lean
CflibsFormal.saha_joint_identifiability.{u_1, u_2} {ι : Type u_1} [Fintype ι] {κ : Type u_2}
  [Fintype κ] [Nonempty ι] [Nonempty κ] {kB me h chi T₁ T₂ Nz₁ Nz₂ Nz1₁ Nz1₂ Fcal ne₁ ne₂ : ℝ}
  {gZ EZ AZ : ι → ℝ} {gZ1 EZ1 AZ1 : κ → ℝ} (hkB : 0 < kB) (_hme : 0 < me) (_hh : 0 < h)
  (hT₁ : 0 < T₁) (hT₂ : 0 < T₂) (hgZ : ∀ (k : ι), 0 < gZ k) (hgZ1 : ∀ (k : κ), 0 < gZ1 k)
  (hAZ : ∀ (k : ι), 0 < AZ k) (hAZ1 : ∀ (k : κ), 0 < AZ1 k) (hNz₁ : 0 < Nz₁) (hNz₂ : 0 < Nz₂)
  (hNz1₁ : 0 < Nz1₁) (_hNz1₂ : 0 < Nz1₂) (hFcal : 0 < Fcal) (_hne₁ : 0 < ne₁) (_hne₂ : 0 < ne₂)
  (i j : ι) (hE : EZ i ≠ EZ j) (uz : ι) (uz1 : κ)
  (hslope :
    CflibsFormal.lineIntensity kB T₁ Nz₁ Fcal gZ EZ AZ j /
        CflibsFormal.lineIntensity kB T₁ Nz₁ Fcal gZ EZ AZ i =
      CflibsFormal.lineIntensity kB T₂ Nz₂ Fcal gZ EZ AZ j /
        CflibsFormal.lineIntensity kB T₂ Nz₂ Fcal gZ EZ AZ i)
  (hNeutObs :
    CflibsFormal.lineIntensity kB T₁ Nz₁ Fcal gZ EZ AZ uz =
      CflibsFormal.lineIntensity kB T₂ Nz₂ Fcal gZ EZ AZ uz)
  (hIonObs :
    CflibsFormal.lineIntensity kB T₁ Nz1₁ Fcal gZ1 EZ1 AZ1 uz1 =
      CflibsFormal.lineIntensity kB T₂ Nz1₂ Fcal gZ1 EZ1 AZ1 uz1)
  (hsaha₁ : Nz1₁ * ne₁ / Nz₁ = CflibsFormal.sahaFactor kB T₁ me h chi gZ EZ gZ1 EZ1)
  (hsaha₂ : Nz1₂ * ne₂ / Nz₂ = CflibsFormal.sahaFactor kB T₂ me h chi gZ EZ gZ1 EZ1) :
  T₁ = T₂ ∧ ne₁ = ne₂
```

> **Joint identifiability of `(T, n_e)` from the Saha–Boltzmann plot.** THE genuine
> coupling theorem. The observations are line INTENSITIES from both ionization stages:
> a distinct-energy neutral-line pair `(i,j)` (`hslope`), one further neutral line `uz`
> (`hNeutObs`), and one ION line `uz1` (`hIonObs`), all at a shared (matched) calibration
> `Fcal`. From these, BOTH the temperature `T` AND the electron density `n_e` are uniquely
> determined:
> 
> * `T` from the neutral-line Boltzmann-plot slope (`temperature_identifiability`);
> * the neutral density `Nz` and the ION density `Nz1` are each recovered from their
>   observed line intensities at the now-common `T` (`density_identifiability`, applied to
>   the ion stage too — the ion stage is genuinely observed);
> * hence the stage ratio `Nz1/Nz` is *derived* (not assumed), and the Saha law then forces
>   `n_e` to agree.
> 
> The electron density `n_e` is recovered from the observed neutral- AND ion-line
> intensities, never taken as input and never via a smuggled stage-ratio hypothesis. This
> is the joint `(T, n_e)` recovery that Yalcin et al. and Aguilera & Aragón obtain from a
> multi-element Saha–Boltzmann plot, and the new content beyond prior modules (which proved
> `T` and `n_e` identifiability separately). The atomic data and calibration are shared
> across the two candidate states, so the two Saha factors coincide after `T₁ = T₂`. 

### `CflibsFormal.electronDensityFromRatio_mem_Icc`

Module `CflibsFormal.SahaRangeEnclosure` · scope `EXACT`

```lean
CflibsFormal.electronDensityFromRatio_mem_Icc.{u_1, u_2} {ι : Type u_1} {κ : Type u_2} [Fintype ι]
  [Fintype κ] [Nonempty ι] [Nonempty κ] {kB me h chi Tmin Tmax T R : ℝ} {gZ EZ : ι → ℝ}
  {gZ1 EZ1 : κ → ℝ} (hkB : 0 < kB) (hme : 0 < me) (hh : 0 < h) (hchi : 0 ≤ chi)
  (hgZ : ∀ (k : ι), 0 < gZ k) (hEZ : ∀ (k : ι), 0 ≤ EZ k) (hgZ1 : ∀ (k : κ), 0 < gZ1 k)
  (hEZ1 : ∀ (k : κ), 0 ≤ EZ1 k) (hEχ : ∀ (k : ι), EZ k ≤ chi) (hTmin : 0 < Tmin) (hR : 0 < R)
  (hT : T ∈ Set.Icc Tmin Tmax) :
  CflibsFormal.electronDensityFromRatio kB T me h chi gZ EZ gZ1 EZ1 R ∈
    Set.Icc (CflibsFormal.electronDensityFromRatio kB Tmin me h chi gZ EZ gZ1 EZ1 R)
      (CflibsFormal.electronDensityFromRatio kB Tmax me h chi gZ EZ gZ1 EZ1 R)
```

> **Density-reader range enclosure (EXACT, Saha–Eggert (Griem)).** The Saha density diagnostic
> `n_e(T) = S(T)/R` inherits the endpoint enclosure of `S`: for a fixed measured stage ratio
> `R > 0`, dividing the `sahaFactor_mem_Icc` bracket by `R` (order-preserving on `ℝ` since
> `0 ≤ R`) traps `n_e(T)` between `n_e(Tmin)` and `n_e(Tmax)`. Uses that
> `electronDensityFromRatio … R` is *defeq* to `sahaFactor … / R`. 

### `CflibsFormal.outerLoop_contracts_apriori`

Module `CflibsFormal.SahaRangeEnclosure` · scope `REDUCED`

```lean
CflibsFormal.outerLoop_contracts_apriori.{u_1, u_2, u_3} {ιe : Type u_1} [Fintype ιe] [Nonempty ιe]
  {κe : Type u_2} [Fintype κe] [Nonempty κe] {ιl : Type u_3} [Fintype ιl] [Nonempty ιl]
  {kB me h chi R0 R : ℝ} {gZ EZ : ιe → ℝ} {gZ1 EZ1 : κe → ℝ} {E yb svec : ιl → ℝ}
  {offConst Tmin Tmax nemin nemax smin : ℝ} (hTle : Tmin ≤ Tmax) (hkB : 0 < kB) (hme : 0 < me)
  (hh : 0 < h) (hchi : 0 ≤ chi) (hTmin : 0 < Tmin) (hgZ : ∀ (k : ιe), 0 < gZ k)
  (hEZ : ∀ (k : ιe), 0 ≤ EZ k) (hgZ1 : ∀ (k : κe), 0 < gZ1 k) (hEZ1 : ∀ (k : κe), 0 ≤ EZ1 k)
  (hEχ : ∀ (k : ιe), EZ k ≤ chi) (hR0 : 0 < R0) (hR : R0 ≤ R)
  (hvar : 0 < ∑ k, (E k - CflibsFormal.mean E) ^ 2) (hnemin : 0 < nemin) (hsmin : 0 < smin)
  (hnelo : nemin ≤ CflibsFormal.electronDensityFromRatio kB Tmin me h chi gZ EZ gZ1 EZ1 R)
  (hnehi : CflibsFormal.electronDensityFromRatio kB Tmax me h chi gZ EZ gZ1 EZ1 R ≤ nemax)
  (hmapsT :
    ∀ ne ∈ Set.Icc nemin nemax,
      CflibsFormal.combinedSlopeTempUpdate kB E yb svec offConst ne ∈ Set.Icc Tmin Tmax)
  (hslopeFloor :
    ∀ ne ∈ Set.Icc nemin nemax,
      smin ≤ CflibsFormal.combinedSahaBoltzmannSlope E yb svec offConst ne)
  (hL1nn : 0 ≤ CflibsFormal.sahaFactorLipConst kB Tmin Tmax me h chi gZ EZ gZ1 EZ1 / R0)
  (hgate :
    CflibsFormal.sahaFactorLipConst kB Tmin Tmax me h chi gZ EZ gZ1 EZ1 / R0 *
        ((|∑ k, (E k - CflibsFormal.mean E) * svec k| / ∑ k, (E k - CflibsFormal.mean E) ^ 2) /
          (kB * smin ^ 2 * nemin)) <
      1) :
  ∃ Tstar ∈ Set.Icc Tmin Tmax,
    CflibsFormal.outerMap
          (fun T => CflibsFormal.electronDensityFromRatio kB T me h chi gZ EZ gZ1 EZ1 R)
          (fun ne => CflibsFormal.combinedSlopeTempUpdate kB E yb svec offConst ne) Tstar =
        Tstar ∧
      (∀ T ∈ Set.Icc Tmin Tmax,
          CflibsFormal.outerMap
                (fun T => CflibsFormal.electronDensityFromRatio kB T me h chi gZ EZ gZ1 EZ1 R)
                (fun ne => CflibsFormal.combinedSlopeTempUpdate kB E yb svec offConst ne) T =
              T →
            T = Tstar) ∧
        ∀ T0 ∈ Set.Icc Tmin Tmax,
          Filter.Tendsto
            (fun n =>
              (CflibsFormal.outerMap
                    (fun T => CflibsFormal.electronDensityFromRatio kB T me h chi gZ EZ gZ1 EZ1 R)
                    fun ne => CflibsFormal.combinedSlopeTempUpdate kB E yb svec offConst ne)^[n]
                T0)
            Filter.atTop (nhds Tstar)
```

> **The CF-LIBS outer temperature loop contracts — a-priori density invariance** (`REDUCED`;
> Aguilera & Aragón 2007, Model B; Saha–Eggert (Griem)). Identical conclusion to
> `outerLoop_contracts`, but the carried interval-invariance side condition `hmapsNe` is **dropped**
> and replaced by the two endpoint containments `hnelo : nemin ≤ n_e(Tmin)` and
> `hnehi : n_e(Tmax) ≤ nemax` (plus `[Nonempty ιe] [Nonempty κe]` and the level-ceiling monotonicity
> premise `hEχ : ∀ k, EZ k ≤ chi`). The full box invariance is then *proven* inside the theorem:
> `electronDensityFromRatio_mem_Icc` traps each `n_e(T)` in `[n_e(Tmin), n_e(Tmax)]`, and
> `Set.Icc_subset_Icc hnelo hnehi` sends that sub-box into `[nemin,nemax]`. This is a genuine
> a-priori discharge — the density interval invariance is no longer assumed but derived from the
> box endpoints — after which the parent `outerLoop_contracts` is forwarded verbatim. 

### `CflibsFormal.sahaFactor_mem_Icc`

Module `CflibsFormal.SahaRangeEnclosure` · scope `EXACT`

```lean
CflibsFormal.sahaFactor_mem_Icc.{u_1, u_2} {ι : Type u_1} {κ : Type u_2} [Fintype ι] [Fintype κ]
  [Nonempty ι] [Nonempty κ] {kB me h chi Tmin Tmax T : ℝ} {gZ EZ : ι → ℝ} {gZ1 EZ1 : κ → ℝ}
  (hkB : 0 < kB) (hme : 0 < me) (hh : 0 < h) (hchi : 0 ≤ chi) (hgZ : ∀ (k : ι), 0 < gZ k)
  (hEZ : ∀ (k : ι), 0 ≤ EZ k) (hgZ1 : ∀ (k : κ), 0 < gZ1 k) (hEZ1 : ∀ (k : κ), 0 ≤ EZ1 k)
  (hEχ : ∀ (k : ι), EZ k ≤ chi) (hTmin : 0 < Tmin) (hT : T ∈ Set.Icc Tmin Tmax) :
  CflibsFormal.sahaFactor kB T me h chi gZ EZ gZ1 EZ1 ∈
    Set.Icc (CflibsFormal.sahaFactor kB Tmin me h chi gZ EZ gZ1 EZ1)
      (CflibsFormal.sahaFactor kB Tmax me h chi gZ EZ gZ1 EZ1)
```

> **Saha-factor range enclosure (EXACT, Saha–Eggert (Griem)).** On a positive temperature box
> `[Tmin,Tmax]` (with `0 < Tmin`), the Saha factor `S(T)` at any interior/boundary temperature is
> trapped between its two endpoint values. Immediate from the strict monotonicity of `S(·)` on
> `(0,∞)` (`sahaFactor_strictMonoOn_temp`, M4) demoted to `MonotoneOn`: all three of `Tmin`, `T`,
> `Tmax` lie in `Set.Ioi 0` (from `0 < Tmin ≤ T ≤ Tmax`), so `S Tmin ≤ S T ≤ S Tmax`. 

### `CflibsFormal.electronDensityFromRatio_lipschitz_temp`

Module `CflibsFormal.SahaStability` · scope `REDUCED`

```lean
CflibsFormal.electronDensityFromRatio_lipschitz_temp.{u_1, u_2} {ι : Type u_1} [Fintype ι]
  {κ : Type u_2} [Fintype κ] [Nonempty ι] [Nonempty κ] {kB Tmin Tmax me h chi : ℝ} {gZ EZ : ι → ℝ}
  {gZ1 EZ1 : κ → ℝ} {R0 R T1 T2 : ℝ} (hkB : 0 < kB) (hme : 0 < me) (hh : 0 < h) (hchi : 0 ≤ chi)
  (hTmin : 0 < Tmin) (hT1 : Tmin ≤ T1) (hT2 : Tmin ≤ T2) (hT1M : T1 ≤ Tmax) (hT2M : T2 ≤ Tmax)
  (hgZ : ∀ (k : ι), 0 < gZ k) (hEZ : ∀ (k : ι), 0 ≤ EZ k) (hgZ1 : ∀ (k : κ), 0 < gZ1 k)
  (hEZ1 : ∀ (k : κ), 0 ≤ EZ1 k) (hR0 : 0 < R0) (hR : R0 ≤ R) :
  |CflibsFormal.electronDensityFromRatio kB T1 me h chi gZ EZ gZ1 EZ1 R -
        CflibsFormal.electronDensityFromRatio kB T2 me h chi gZ EZ gZ1 EZ1 R| ≤
    CflibsFormal.sahaFactorLipConst kB Tmin Tmax me h chi gZ EZ gZ1 EZ1 / R0 * |T1 - T2|
```

> **Electron-density `T`-sensitivity bound** (`REDUCED`, Saha–Eggert (Griem)).  For a
> fixed measured stage ratio `R ≥ R₀ > 0` and temperatures in the box `[Tmin, Tmax]`, the
> inferred electron density `n_e = S(T)/R` obeys the two-point Lipschitz estimate
> 
> `|n_e(T₁,R) − n_e(T₂,R)| ≤ (sahaFactorLipConst …/R₀)·|T₁ − T₂|`.
> 
> Together with `electronDensity_lipschitz` (the `R`-channel constant `S/R₀²`), this closes
> the `(δT, δR)` sensitivity budget for `n_e`: a recovered-temperature error and a
> stage-ratio error each map to a bounded `n_e` deviation.  Immediate from
> `sahaFactor_lipschitz_temp` and `n_e(T,R) = S(T)/R`; the constant is the worst-case
> `R = R₀` reciprocal of the Saha-factor Lipschitz constant.  `REDUCED` for the same reason
> as the headline (the constant lumps the channel over-estimates). 

### `CflibsFormal.electronDensityFromRatio_strictMonoOn_temp`

Module `CflibsFormal.SahaStability` · scope `EXACT`

```lean
CflibsFormal.electronDensityFromRatio_strictMonoOn_temp.{u_1, u_2} {ι : Type u_1} [Fintype ι]
  {κ : Type u_2} [Fintype κ] [Nonempty ι] [Nonempty κ] {kB me h chi : ℝ} {gZ EZ : ι → ℝ}
  {gZ1 EZ1 : κ → ℝ} {R : ℝ} (hkB : 0 < kB) (hme : 0 < me) (hh : 0 < h) (hchi : 0 ≤ chi)
  (hgZ : ∀ (k : ι), 0 < gZ k) (hEZ : ∀ (k : ι), 0 ≤ EZ k) (hgZ1 : ∀ (k : κ), 0 < gZ1 k)
  (hEZ1 : ∀ (k : κ), 0 ≤ EZ1 k) (hEχ : ∀ (k : ι), EZ k ≤ chi) (hR : 0 < R) :
  StrictMonoOn (fun T => CflibsFormal.electronDensityFromRatio kB T me h chi gZ EZ gZ1 EZ1 R)
    (Set.Ioi 0)
```

> **Electron-density `n_e = S(T)/R` strict monotonicity in temperature (M5, EXACT,
> Saha–Eggert (Griem)).** For a fixed positive measured stage ratio `R`, the density reader
> inherits the strict monotonicity of `S`: dividing a strictly increasing function by a
> fixed positive constant preserves strict monotonicity. 

### `CflibsFormal.electronDensity_lipschitz`

Module `CflibsFormal.SahaStability` · scope `EXACT`

```lean
CflibsFormal.electronDensity_lipschitz.{u_1, u_2} {ι : Type u_1} [Fintype ι] {κ : Type u_2}
  [Fintype κ] [Nonempty ι] [Nonempty κ] {kB T me h chi : ℝ} {gZ EZ : ι → ℝ} {gZ1 EZ1 : κ → ℝ}
  {R₀ R₁ R₂ : ℝ} (hkB : 0 < kB) (hT : 0 < T) (hme : 0 < me) (hh : 0 < h) (hgZ : ∀ (k : ι), 0 < gZ k)
  (hgZ1 : ∀ (k : κ), 0 < gZ1 k) (hR₀ : 0 < R₀) (hR₁ : R₀ ≤ R₁) (hR₂ : R₀ ≤ R₂) :
  |CflibsFormal.electronDensityFromRatio kB T me h chi gZ EZ gZ1 EZ1 R₁ -
        CflibsFormal.electronDensityFromRatio kB T me h chi gZ EZ gZ1 EZ1 R₂| ≤
    CflibsFormal.sahaFactor kB T me h chi gZ EZ gZ1 EZ1 / R₀ ^ 2 * |R₁ - R₂|
```

> **EXACT sensitivity bound for the `n_e` diagnostic.** For stage ratios
> `R₁, R₂ ≥ R₀ > 0` and fixed temperature, the inferred electron densities obey the
> explicit Lipschitz estimate `|n_e(R₁) − n_e(R₂)| ≤ (S/R₀²)·|R₁ − R₂|`, with
> `S = sahaFactor …`.  The constant `S/R₀²` is exactly `|d n_e/dR|` at the worst-case
> (smallest) ratio `R₀`; it is the sensitivity coefficient the runtime multiplies a
> stage-ratio error bar by to obtain an `n_e` error budget.  Rests on `S > 0`
> (`sahaFactor_pos`) and the pure-analysis core `saha_inv_lipschitz`. 

### `CflibsFormal.electronDensity_relativeError`

Module `CflibsFormal.SahaStability` · scope `EXACT`

```lean
CflibsFormal.electronDensity_relativeError.{u_1, u_2} {ι : Type u_1} [Fintype ι] {κ : Type u_2}
  [Fintype κ] [Nonempty ι] [Nonempty κ] {kB T me h chi : ℝ} {gZ EZ : ι → ℝ} {gZ1 EZ1 : κ → ℝ}
  {R₁ R₂ : ℝ} (hkB : 0 < kB) (hT : 0 < T) (hme : 0 < me) (hh : 0 < h) (hgZ : ∀ (k : ι), 0 < gZ k)
  (hgZ1 : ∀ (k : κ), 0 < gZ1 k) (hR₁ : 0 < R₁) (hR₂ : 0 < R₂) :
  CflibsFormal.electronDensityFromRatio kB T me h chi gZ EZ gZ1 EZ1 R₁ /
      CflibsFormal.electronDensityFromRatio kB T me h chi gZ EZ gZ1 EZ1 R₂ =
    R₂ / R₁
```

> **EXACT relative-error transfer for `n_e`.** At fixed temperature (hence fixed
> Saha factor `S = sahaFactor … > 0`), the ratio of two inferred electron densities
> is the inverse ratio of the stage ratios that produced them:
> `n_e(R₁)/n_e(R₂) = R₂/R₁`.  Equivalently, in logarithms,
> `ln n_e(R₁) − ln n_e(R₂) = −(ln R₁ − ln R₂)`: the diagnostic's log-derivative is
> exactly `−1`, so a relative stage-ratio measurement error maps one-to-one (unit
> gain, inverted sign) onto the relative error of `n_e`.  Positivity of the physical
> constants/weights is load-bearing only through `S ≠ 0` (via `sahaFactor_pos`); the
> identity is otherwise pure algebra. 

### `CflibsFormal.partitionFunction_mono_temp`

Module `CflibsFormal.SahaStability` · scope `PURE-MATH`

```lean
CflibsFormal.partitionFunction_mono_temp.{u_1} {ι : Type u_1} [Fintype ι] {kB T1 T2 : ℝ}
  {g E : ι → ℝ} (hkB : 0 < kB) (hT1 : 0 < T1) (hT12 : T1 ≤ T2) (hg : ∀ (k : ι), 0 < g k)
  (hE : ∀ (k : ι), 0 ≤ E k) :
  CflibsFormal.partitionFunction kB T1 g E ≤ CflibsFormal.partitionFunction kB T2 g E
```

> **Monotonicity of the partition function in `T` (PURE-MATH).**  For non-negative
> level energies (`∀ k, 0 ≤ E k`) and positive degeneracies, the partition function is
> nondecreasing in temperature: `T₁ ≤ T₂ ⇒ U(T₁) ≤ U(T₂)`.  Each Boltzmann factor
> `exp(−Eₖ/(k_B T))` is nondecreasing in `T` when `Eₖ ≥ 0` and `k_B > 0` (the exponent
> `−Eₖ/(k_B T)` rises toward `0` as `T` grows), and a sum of nondecreasing terms is
> nondecreasing.  Public restatement of the private `partitionFunction_ge_floor`, with the
> floor taken as the lower temperature `T₁`. 

### `CflibsFormal.partitionFunction_upper_growth`

Module `CflibsFormal.SahaStability` · scope `PURE-MATH`

```lean
CflibsFormal.partitionFunction_upper_growth.{u_1} {ι : Type u_1} [Fintype ι] {kB T1 T2 chi : ℝ}
  {g E : ι → ℝ} (hkB : 0 < kB) (hT1 : 0 < T1) (hT12 : T1 ≤ T2) (hg : ∀ (k : ι), 0 < g k)
  (hEχ : ∀ (k : ι), E k ≤ chi) :
  CflibsFormal.partitionFunction kB T2 g E ≤
    Real.exp (chi * (1 / (kB * T1) - 1 / (kB * T2))) * CflibsFormal.partitionFunction kB T1 g E
```

> **Partition-function upper growth against the ionization exponential (PURE-MATH).**
> The crux termwise bound.  If every level energy is capped by `chi` (`∀ k, E k ≤ chi`)
> and the degeneracies are positive, then raising the temperature from `T₁` to `T₂ ≥ T₁`
> inflates the partition function by at most the factor `exp(chi·(1/(k_B T₁) − 1/(k_B T₂)))`:
> 
> `U(T₂) ≤ exp(chi·(1/(k_B T₁) − 1/(k_B T₂)))·U(T₁)`.
> 
> Proved termwise: dividing by `gₖ > 0` and using `exp` monotonicity, the claim reduces to
> the scalar inequality `(E k − chi)·(1/(k_B T₁) − 1/(k_B T₂)) ≤ 0`, which holds because
> `1/(k_B T₁) ≥ 1/(k_B T₂) > 0` (temperature raises the inverse-temperature floor) and
> `E k − chi ≤ 0`.  This pairs `U`'s growth against the `exp(−chi/(k_B T))` Saha factor —
> it does **not** require `E k ≥ 0`. 

### `CflibsFormal.sahaFactor_lipschitz_temp`

Module `CflibsFormal.SahaStability` · scope `REDUCED`

```lean
CflibsFormal.sahaFactor_lipschitz_temp.{u_1, u_2} {ι : Type u_1} [Fintype ι] {κ : Type u_2}
  [Fintype κ] [Nonempty ι] [Nonempty κ] {kB Tmin Tmax me h chi : ℝ} {gZ EZ : ι → ℝ}
  {gZ1 EZ1 : κ → ℝ} {T1 T2 : ℝ} (hkB : 0 < kB) (hme : 0 < me) (hh : 0 < h) (hchi : 0 ≤ chi)
  (hTmin : 0 < Tmin) (hT1 : Tmin ≤ T1) (hT2 : Tmin ≤ T2) (hT1M : T1 ≤ Tmax) (hT2M : T2 ≤ Tmax)
  (hgZ : ∀ (k : ι), 0 < gZ k) (hEZ : ∀ (k : ι), 0 ≤ EZ k) (hgZ1 : ∀ (k : κ), 0 < gZ1 k)
  (hEZ1 : ∀ (k : κ), 0 ≤ EZ1 k) :
  |CflibsFormal.sahaFactor kB T1 me h chi gZ EZ gZ1 EZ1 -
        CflibsFormal.sahaFactor kB T2 me h chi gZ EZ gZ1 EZ1| ≤
    CflibsFormal.sahaFactorLipConst kB Tmin Tmax me h chi gZ EZ gZ1 EZ1 * |T1 - T2|
```

> **Saha-factor `T`-Lipschitz (two-sided sensitivity) bound** (`REDUCED`,
> Saha–Eggert (Griem)).  On a temperature box `[Tmin, Tmax]` (`0 < Tmin ≤ T₁, T₂ ≤ Tmax`),
> with positive constants/degeneracies, non-negative level energies and `χ ≥ 0`, the Saha
> factor is Lipschitz in `T`:
> 
> `|S(T₁) − S(T₂)| ≤ sahaFactorLipConst … · |T₁ − T₂|`.
> 
> This is the *sign-free* form of the T-channel: no monotonicity of `S` is claimed (the
> partition ratio `U_{z+1}/U_z` can run either way — see the scope note), only the two-point
> sensitivity the runtime error budget needs.  Proved channelwise — a two-point bound for
> each factor of `sahaFactor` (thermal bracket, partition ratio, exponential) — assembled by
> `mul3_two_point_bound`.  `REDUCED` (not `EXACT`): the constant lumps three channel
> over-estimates (box floor/ceiling for each sup, plus each channel's own reduction as in
> `PartitionLipschitz` / the thermal `√` split); the forward model `sahaFactor` is exact. 

### `CflibsFormal.sahaFactor_strictMonoOn_temp`

Module `CflibsFormal.SahaStability` · scope `EXACT`

```lean
CflibsFormal.sahaFactor_strictMonoOn_temp.{u_1, u_2} {ι : Type u_1} [Fintype ι] {κ : Type u_2}
  [Fintype κ] [Nonempty ι] [Nonempty κ] {kB me h chi : ℝ} {gZ EZ : ι → ℝ} {gZ1 EZ1 : κ → ℝ}
  (hkB : 0 < kB) (hme : 0 < me) (hh : 0 < h) (_hchi : 0 ≤ chi) (hgZ : ∀ (k : ι), 0 < gZ k)
  (_hEZ : ∀ (k : ι), 0 ≤ EZ k) (hgZ1 : ∀ (k : κ), 0 < gZ1 k) (hEZ1 : ∀ (k : κ), 0 ≤ EZ1 k)
  (hEχ : ∀ (k : ι), EZ k ≤ chi) :
  StrictMonoOn (fun T => CflibsFormal.sahaFactor kB T me h chi gZ EZ gZ1 EZ1) (Set.Ioi 0)
```

> **Saha-factor strict monotonicity in temperature (M4, EXACT, Saha–Eggert (Griem)).**
> On the whole positive temperature axis, under the physically universal hypothesis that
> every bound level of the lower (neutral) stage sits at or below the ionization limit
> (`∀ k, EZ k ≤ chi`), the Saha factor `S(T)` is *strictly* increasing in `T`. Proof:
> rewrite `log S(T₁) < log S(T₂)` via `log_sahaFactor` at both temperatures; the upper-stage
> partition term is nondecreasing (`partitionFunction_mono_temp`), the lower-stage growth is
> dominated by the same χ-weighted factor as the exponential channel
> (`partitionFunction_upper_growth`), and the thermal bracket is *strictly* increasing
> (`thermalBracket_strictMono`), which alone supplies strictness; assemble by `linarith`
> through `Real.log_lt_log_iff` using `sahaFactor_pos`. `hchi` and `hEZ` are carried for API
> parity with `sahaFactor_lipschitz_temp` but are not load-bearing in this proof. 

### `CflibsFormal.thermalBracket_strictMono`

Module `CflibsFormal.SahaStability` · scope `PURE-MATH`

```lean
CflibsFormal.thermalBracket_strictMono {kB me h Ta Tb : ℝ} (hkB : 0 < kB) (hme : 0 < me)
  (hh : 0 < h) (hab : Ta < Tb) :
  CflibsFormal.thermalBracket kB Ta me h < CflibsFormal.thermalBracket kB Tb me h
```

> **Strict monotonicity of the thermal-de-Broglie bracket in `T` (PURE-MATH).**
> `thermalBracket kB · me h = (2π m_e k_B/h²)·T` is *strictly* increasing in the
> temperature: for positive constants `k_B, m_e, h` and `Ta < Tb`,
> `thermalBracket kB Ta me h < thermalBracket kB Tb me h`.  Strict sibling of the
> existing `thermalBracket_mono`; the difference is the positive linear coefficient
> `(2π m_e k_B/h²)` times the positive gap `Tb − Ta`. 

### `CflibsFormal.lineIntensity_eq_selfAbsorbedIntensity_div`

Module `CflibsFormal.SelfAbsorption` · scope `EXACT`

```lean
CflibsFormal.lineIntensity_eq_selfAbsorbedIntensity_div.{u_1} {ι : Type u_1} [Fintype ι]
  {kB T N Fcal : ℝ} {g E A : ι → ℝ} (k : ι) {tau : ℝ} (htau : 0 ≤ tau) :
  CflibsFormal.lineIntensity kB T N Fcal g E A k =
    CflibsFormal.selfAbsorbedIntensity kB T N Fcal g E A k tau /
      CflibsFormal.selfAbsorptionFactor tau
```

> **Exact curve-of-growth correction (model left-inverse).** Dividing the self-absorbed
> measurement by the known `SA(τ)` recovers the optically-thin intensity exactly:
> `I_thin = I_meas / SA(τ)`. This is the left-inverse of the model
> `selfAbsorbedIntensity = lineIntensity · SA(τ)` — itself the genuine radiative-transfer
> slab solution (`slabIntensity_eq_thin_mul_SA` / `selfAbsorbedIntensity_eq_slab`), so the
> correction is physically derived, not merely definitional. It feeds the existing
> `boltzmann_plot_intensity` / `temperature_from_two_lines` inversion unchanged:
> self-absorption is exactly invertible given a known optical depth. Holds for all `τ ≥ 0`
> (at `τ = 0`, `SA = 1` and the correction is the identity). 

### `CflibsFormal.selfAbsorbedIntensity_eq_slab`

Module `CflibsFormal.SelfAbsorption` · scope `EXACT`

```lean
CflibsFormal.selfAbsorbedIntensity_eq_slab.{u_1} {ι : Type u_1} [Fintype ι] {kB T N Fcal : ℝ}
  {g E A : ι → ℝ} (k : ι) {tau : ℝ} (htau : 0 < tau) :
  CflibsFormal.selfAbsorbedIntensity kB T N Fcal g E A k tau =
    CflibsFormal.slabIntensity (CflibsFormal.lineIntensity kB T N Fcal g E A k / tau) tau
```

> **The model intensity IS a radiative-transfer slab intensity.** For `τ > 0`, the
> self-absorbed line `selfAbsorbedIntensity = lineIntensity · SA(τ)` equals the emergent
> slab intensity `slabIntensity` whose optically-thin emission `S · τ` is the thin line
> `lineIntensity` (effective source strength `S = lineIntensity / τ`). This closes the loop:
> the multiplicative model used here is exactly the radiative-transfer slab solution, so
> `SA` is derived, not assumed. 

### `CflibsFormal.selfAbsorbedIntensity_le_lineIntensity`

Module `CflibsFormal.SelfAbsorption` · scope `APPROXIMATION`

```lean
CflibsFormal.selfAbsorbedIntensity_le_lineIntensity.{u_1} {ι : Type u_1} [Fintype ι] [Nonempty ι]
  {kB T N Fcal : ℝ} {g E A : ι → ℝ} (hg : ∀ (k : ι), 0 < g k) (hN : 0 < N) (hFcal : 0 < Fcal)
  (hA : ∀ (k : ι), 0 < A k) (k : ι) {tau : ℝ} (htau : 0 ≤ tau) :
  CflibsFormal.selfAbsorbedIntensity kB T N Fcal g E A k tau ≤
    CflibsFormal.lineIntensity kB T N Fcal g E A k
```

> **Bias-direction theorem (non-strict).** A self-absorbed line is measured at or below
> its optically-thin value: `I_meas ≤ I_thin`. Hence neglecting self-absorption biases the
> inferred upper-level population DOWNWARD, and hence the extracted composition of any
> *differentially* self-absorbed species (a factor common to all species cancels in the
> scale-invariant closure) — the dominant failure mode for concentrated alloy /
> high-entropy-alloy lines. 

### `CflibsFormal.selfAbsorbedIntensity_lt_lineIntensity`

Module `CflibsFormal.SelfAbsorption` · scope `APPROXIMATION`

```lean
CflibsFormal.selfAbsorbedIntensity_lt_lineIntensity.{u_1} {ι : Type u_1} [Fintype ι] [Nonempty ι]
  {kB T N Fcal : ℝ} {g E A : ι → ℝ} (hg : ∀ (k : ι), 0 < g k) (hN : 0 < N) (hFcal : 0 < Fcal)
  (hA : ∀ (k : ι), 0 < A k) (k : ι) {tau : ℝ} (htau : 0 < tau) :
  CflibsFormal.selfAbsorbedIntensity kB T N Fcal g E A k tau <
    CflibsFormal.lineIntensity kB T N Fcal g E A k
```

> **Bias-direction theorem (strict).** For any *actually* optically-thick line
> (`τ > 0`) the downward bias is strict: `I_meas < I_thin`. Self-absorption is never
> benign — it always reduces the measured intensity and must be corrected, biasing the
> inferred upper-level population DOWNWARD, and hence the extracted composition of any
> *differentially* self-absorbed species (a factor common to all species cancels in the
> scale-invariant closure). 

### `CflibsFormal.lineIntensity_smul_left`

Module `CflibsFormal.SelfAbsorptionInverse` · scope `PURE-MATH`

```lean
CflibsFormal.lineIntensity_smul_left.{u_3} {ι : Type u_3} [Fintype ι] (kB T N Fcal c : ℝ)
  (g E A : ι → ℝ) (k : ι) :
  CflibsFormal.lineIntensity kB T (c * N) Fcal g E A k =
    c * CflibsFormal.lineIntensity kB T N Fcal g E A k
```

> **`N`-linearity of the optically-thin forward map.** Scaling the species density by a
> constant `c` scales the line intensity by the same `c`:
> `lineIntensity … (c · N) … = c · lineIntensity … N …`. This is the structural fact the
> LOST construction exploits — the measured intensity constrains only the product `N · SA(τ)`,
> so density and self-absorption cannot be separated from a single line. (`ForwardMap` proves
> positivity and the Boltzmann-plot identity, never this linearity, so this is a genuine new
> helper, not a reproof.) 

### `CflibsFormal.stark_saha_lte_consistent`

Module `CflibsFormal.StarkBroadening` · scope `EXACT`

```lean
CflibsFormal.stark_saha_lte_consistent.{u_1, u_2} {ι : Type u_1} [Fintype ι] {κ : Type u_2}
  [Fintype κ] {w nRef width kB T me h chi : ℝ} {gZ EZ : ι → ℝ} {gZ1 EZ1 : κ → ℝ} {R dE : ℝ}
  (hw : w ≠ 0) (hnRef : nRef ≠ 0) (hR : R ≠ 0)
  (hagree :
    CflibsFormal.starkDensity w nRef width =
      CflibsFormal.electronDensityFromRatio kB T me h chi gZ EZ gZ1 EZ1 R)
  (hlte : CflibsFormal.lteValid T dE (CflibsFormal.starkDensity w nRef width)) :
  ∃ ne,
    ne = CflibsFormal.starkDensity w nRef width ∧
      ne = CflibsFormal.electronDensityFromRatio kB T me h chi gZ EZ gZ1 EZ1 R ∧
        CflibsFormal.mcWhirterBound T dE ≤ ne ∧
          width = CflibsFormal.starkFWHM w nRef ne ∧
            R * ne = CflibsFormal.sahaFactor kB T me h chi gZ EZ gZ1 EZ1
```

> **Stark–Saha LTE cross-check (conditional bundling).** A genuine two-diagnostic
> consistency theorem. The Stark route recovers `n_e` from a measured line WIDTH
> (`starkDensity`), the Saha route recovers `n_e` from a measured stage-intensity
> RATIO `R` (`electronDensityFromRatio`, reused from `Saha.lean`) — two physically
> INDEPENDENT diagnostics consuming genuinely DIFFERENT observations. The theorem
> certifies: IF the two estimates agree (`hagree`) AND the common value clears the
> McWhirter bound (`hlte`), THEN there exists a single `n_e` that
> 
> * (1) equals the Stark estimate, (2) equals the Saha estimate, (3) is LTE-valid —
>   these three restate the hypotheses; and
> * (4) re-derives the observed width through the Griem forward map
>   `width = starkFWHM w nRef ne` (the inversion content, needs `hw`, `hnRef`), and
>   (5) satisfies the structural Saha law `R·n_e = sahaFactor` (via `saha_relation`,
>   needs `hR`).
> 
> Honest scoping: agreement (`hagree`) is *assumed*, not proven — the two
> diagnostics are NOT shown to necessarily coincide. The substance is that the two
> sides feed DIFFERENT observations (a WIDTH vs a stage RATIO `R`), so their
> equality is empirical evidence rather than a definitional identity, and clauses
> 4–5 tie the single recovered `n_e` back to both independent forward laws. 

### `CflibsFormal.temporal_temperature_insitu`

Module `CflibsFormal.TemporalEvolution` · scope `REDUCED`

```lean
CflibsFormal.temporal_temperature_insitu.{u_1, u_2} {σ : Type u_1} {ι : Type u_2} [Fintype ι]
  [Nonempty ι] {kB Fcal : ℝ} {T ρ : ℝ → ℝ} {N0 : σ → ℝ} {g E A : σ → ι → ℝ}
  (hg : ∀ (s : σ) (k : ι), 0 < g s k) (hN0 : ∀ (s : σ), 0 < N0 s) (hFcal : 0 < Fcal)
  (hA : ∀ (s : σ) (k : ι), 0 < A s k) (t : ℝ) (hρ : 0 < ρ t) (s : σ) (i j : ι)
  (hE : E s i ≠ E s j) :
  (Real.log
          (CflibsFormal.lineIntensity kB (T t) (ρ t * N0 s) Fcal (g s) (E s) (A s) j /
            (g s j * A s j)) -
        Real.log
          (CflibsFormal.lineIntensity kB (T t) (ρ t * N0 s) Fcal (g s) (E s) (A s) i /
            (g s i * A s i))) /
      (E s i - E s j) =
    1 / (kB * T t)
```

> **In-situ gate temperature (Boltzmann slope).** The slope of the intensity
> Boltzmann plot between two distinct-energy lines `i, j` of element `s`, built from
> the gate-`t` spectra at the gate state `(T t, ρ t · N0 s)`, recovers `1/(k_B·T t)`
> exactly. A direct specialization of `ForwardMap.temperature_from_two_lines` at the
> gate state (density `N := ρ t · N0 s`); this is the SEPARATE temperature leg that
> licenses feeding `T t` to the composition estimator, with no formal in-Lean
> fusion to the composition soundness below. 
