/-
Copyright (c) 2026 Brian Squires. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Squires
-/

/-!
# CF-LIBS numerical regression-oracle generator

A computable **`Float` mirror** of the verified `CflibsFormal` forward map, classic
inversion, and the alternative estimators, used to emit numerical regression fixtures for the
companion numerical pipeline (CF-LIBS-improved). It is NOT part of the verified spec: the
verified definitions in `CflibsFormal/` are `noncomputable` and ℝ-valued (so they cannot be
`#eval`'d). Here we re-implement the SAME formulas over `Float`; each def mirrors its ℝ
counterpart verbatim in formula.

The fixtures exercise the **multi-element** CF-LIBS problem (the whole point of the method) and
the alternative estimators the spec proves equivalent/sound. Two scenarios:

* a **ternary alloy** — 3 chemically distinct elements, each with its OWN atomic data and
  partition function `U_s`, 4 lines each — checked with the classic inversion, the multi-line
  **OLS** Boltzmann-plot estimator, per-element **temperature** recovery, and the
  **self-absorption** correction (optically-thick input + known `τ`);
* a **two-stage Saha–Boltzmann** element (neutral + ion) — recover `T` and the electron
  density `n_e` from the two stages.

Each check instantiates a **proven theorem** (see `oracle/README.md` for the map). `Float ≠ ℝ`,
so the *formula structure* and *invariants* are verified; numerical eval is IEEE-754 and checks
are tolerance-based (~1e-6). Dimensionless inputs, kept O(1)–O(30) so the 9-decimal formatter
is lossless.

Regenerate with:  `lake exe oracle-fixtures > oracle/fixtures.json`
-/

namespace Oracle

abbrev Vec := Array Float

/-! ## Float mirror of the verified definitions -/

/-- Mirror of `CflibsFormal.boltzmannFactor`: `exp(-E / (kB · T))`. -/
def boltzmannFactor (kB T E : Float) : Float := Float.exp (-E / (kB * T))

/-- Mirror of `CflibsFormal.partitionFunction`: `Σ_k g_k · exp(-E_k / (kB · T))`. -/
def partitionFunction (kB T : Float) (g E : Vec) : Float :=
  (g.zip E).foldl (fun acc ge => acc + ge.1 * boltzmannFactor kB T ge.2) 0.0

/-- Mirror of `CflibsFormal.population`: `N · g_k · bf_k / U(T)`. -/
def population (kB T N : Float) (g E : Vec) (k : Nat) : Float :=
  N * g[k]! * boltzmannFactor kB T E[k]! / partitionFunction kB T g E

/-- Mirror of `CflibsFormal.lineIntensity`: `Fcal · A_k · population`. -/
def lineIntensity (kB T N Fcal : Float) (g E A : Vec) (k : Nat) : Float :=
  Fcal * A[k]! * population kB T N g E k

/-- Mirror of `ForwardMapEnergy.lineIntensityEnergy`: the energy/wavelength forward map
`(hc/(4π·λ_k)) · A_k · population · Fgeo`, with the per-line wavelength `λ` explicit. -/
def lineIntensityEnergy (hc fourPi kB T N Fgeo : Float) (g E A lam : Vec) (k : Nat) : Float :=
  (hc / (fourPi * lam[k]!)) * A[k]! * population kB T N g E k * Fgeo

/-- Mirror of `CflibsFormal.Classic.classicDensity`: `I · U / (Fcal · A_u · g_u · bf_u)`. -/
def classicDensity (kB T Fcal : Float) (g E A : Vec) (u : Nat) (I : Float) : Float :=
  I * partitionFunction kB T g E / (Fcal * A[u]! * g[u]! * boltzmannFactor kB T E[u]!)

/-- Mirror of `CflibsFormal.composition`: `n_s / Σ_t n_t`. -/
def composition (n : Vec) (s : Nat) : Float := n[s]! / n.foldl (· + ·) 0.0

/-- Two-line Boltzmann-plot temperature recovery (mirror of `Classic.classic_temperature_correct`):
`T = (E_i − E_j) / (kB · (y_j − y_i))`, `y_k = log(I_k/(g_k A_k))`. -/
def recoverT (kB : Float) (g E A : Vec) (i j : Nat) (Ii Ij : Float) : Float :=
  let yi := Float.log (Ii / (g[i]! * A[i]!))
  let yj := Float.log (Ij / (g[j]! * A[j]!))
  (E[i]! - E[j]!) / (kB * (yj - yi))

-- ### Multi-line OLS Boltzmann plot (mirror of `Alt/LeastSquares.lean`)

/-- Mirror of `mean`: arithmetic mean over the lines. -/
def mean (f : Vec) : Float := f.foldl (· + ·) 0.0 / f.size.toFloat

/-- Mirror of `olsSlope`: covariance/variance of the Boltzmann-plot points. -/
def olsSlope (E y : Vec) : Float :=
  let eb := mean E
  let yb := mean y
  let num := (E.zip y).foldl (fun acc p => acc + (p.1 - eb) * (p.2 - yb)) 0.0
  let den := E.foldl (fun acc ek => acc + (ek - eb) * (ek - eb)) 0.0
  num / den

/-- Mirror of `olsIntercept`: `ȳ − slope · Ē`. -/
def olsIntercept (E y : Vec) : Float := mean y - olsSlope E y * mean E

/-- Mirror of `Alt.olsDensity`: density read off the OLS intercept of ALL lines' ordinates. -/
def olsDensity (kB T Fcal : Float) (g E A I : Vec) : Float :=
  let y := (Array.range I.size).map (fun k => Float.log (I[k]! / (g[k]! * A[k]!)))
  Float.exp (olsIntercept E y) * partitionFunction kB T g E / Fcal

-- ### Self-absorption correction (mirror of `SelfAbsorption.lean` / `Alt/SelfAbsorbed.lean`)

/-- Mirror of `CflibsFormal.selfAbsorptionFactor`: `(1 − exp(−τ))/τ` (`1` at `τ = 0`), in `(0,1]`. -/
def selfAbsorptionFactor (tau : Float) : Float :=
  if tau == 0.0 then 1.0 else (1.0 - Float.exp (-tau)) / tau

/-- Mirror of `Alt.selfAbsorbedComposition`'s per-line step: correct the thick intensity by
`SA(τ)`, then invert with classicDensity. -/
def selfAbsorbedDensity (kB T Fcal : Float) (g E A : Vec) (u : Nat) (tau Imeas : Float) : Float :=
  classicDensity kB T Fcal g E A u (Imeas / selfAbsorptionFactor tau)

-- ### Saha factor (mirror of `Saha.lean`)

def piF : Float := 3.141592653589793

/-- `x^p` for `x > 0` via `exp(p·log x)` (Float has no rpow). -/
def rpow (x p : Float) : Float := Float.exp (p * Float.log x)

/-- Mirror of `CflibsFormal.thermalBracket`: `(2π · me · kB · T) / h²`. -/
def thermalBracket (kB T me h : Float) : Float := 2.0 * piF * me * kB * T / (h * h)

/-- Mirror of `CflibsFormal.sahaFactor`:
`2 · (U_{z+1}/U_z) · thermalBracket^(3/2) · exp(−χ/(kB·T))`. -/
def sahaFactor (kB T me h chi : Float) (gZ EZ gZ1 EZ1 : Vec) : Float :=
  2.0 * (partitionFunction kB T gZ1 EZ1 / partitionFunction kB T gZ EZ)
    * rpow (thermalBracket kB T me h) 1.5
    * Float.exp (-chi / (kB * T))

/-- Mirror of `CflibsFormal.electronDensityFromRatio`: `n_e = S(T) / R`, `R = n_{z+1}/n_z`. -/
def electronDensityFromRatio (kB T me h chi : Float) (gZ EZ gZ1 EZ1 : Vec) (R : Float) : Float :=
  sahaFactor kB T me h chi gZ EZ gZ1 EZ1 / R

-- ### Error-budget thresholds (mirror of `ErrorBudget.lean`)

/-- Mirror of the ℓ² slope-sensitivity bound (`ErrorBudget.olsSlope_stable_l2`):
`|Δβ| ≤ snr · √n / √ssE` — the worst-case inverse-temperature (slope) error from a per-line
ordinate error `snr` over `n` lines of energy spread `ssE = Σ(Eₖ − Ē)²`. -/
def slopeErrorBound (snr n ssE : Float) : Float := snr * Float.sqrt n / Float.sqrt ssE

/-- Mirror of `ErrorBudget.requiredEnergySpread_sufficient`: the energy spread that GUARANTEES a
target slope error `tauBeta` at per-line error `snr` over `n` lines: `ssE ≥ snr²·n / tauBeta²`.
The DERIVED `min_energy_spread` (was a tuned magic number). -/
def requiredEnergySpread (tauBeta snr n : Float) : Float := snr * snr * n / (tauBeta * tauBeta)

/-- Mirror of `ErrorBudget.maxPerLineError_sufficient`: the largest per-line ordinate error
(smallest SNR) tolerable for a target slope error `tauBeta` at spread `ssE` over `n` lines:
`snr ≤ tauBeta · √(ssE / n)`. The DERIVED `min_snr`. -/
def maxPerLineError (tauBeta n ssE : Float) : Float := tauBeta * Float.sqrt (ssE / n)

/-- Mirror of the OLS slope NOISE GAIN (`ErrorBudget.olsSlope_noise_gain`): `∑ wₖ² = 1/ssE`.
Under independent ordinate noise of variance `snr²` the Gauss–Markov slope variance is
`snr²/ssE`; with `ssE = n·vPerLine` (per-line energy variance) the STATISTICAL `min_lines` for a
target slope std `tauBeta` is `n ≥ snr²/(vPerLine·tauBeta²)`. (Statistical route — see the
ErrorBudget module docstring on why the deterministic worst case does not give a line-count law.) -/
def requiredMinLinesStat (tauBeta snr vPerLine : Float) : Float :=
  snr * snr / (vPerLine * tauBeta * tauBeta)

/-- Mirror of the EXACT identity `ErrorBudget.temp_rel_error_eq` (`|ΔT|/T = kB·T·|Δβ|`): the
slope accuracy `tauBeta` required to hit a target RELATIVE temperature error `relTtarget` is
`tauBeta = relTtarget / (kB·T)`. -/
def slopeTargetFromTempRel (relTtarget kB T : Float) : Float := relTtarget / (kB * T)

/-- Mirror of `ErrorBudget.composition_target_sufficient`: the per-species absolute density-error
budget that GUARANTEES a target composition accuracy `tauC` for `card` species at total recovered
density `Shat`: `delta ≤ tauC·Shat / (card + 1)`. -/
def densityBudgetFromComposition (tauC Shat card : Float) : Float := tauC * Shat / (card + 1.0)

-- ### Stark broadening / McWhirter (mirror of `StarkBroadening.lean`)

/-- Mirror of `StarkBroadening.starkFWHM`: the Griem electron-impact linear width
`Δλ = 2·w·(ne/nRef)`. -/
def starkFWHM (w nRef ne : Float) : Float := 2.0 * w * (ne / nRef)

/-- Mirror of `StarkBroadening.starkDensity` (the inverse): `n_e = nRef·width/(2·w)`. -/
def starkDensity (w nRef width : Float) : Float := nRef * width / (2.0 * w)

/-- Mirror of the DIMENSIONLESS shape of `StarkBroadening.mcWhirterBound` (`1.6e12·√T·ΔE³`): the
`√T·ΔE³` part. The full bound is `mcWhirterConst · mcWhirterShape` with `mcWhirterConst = 1.6e12`;
the constant is kept out of the fixture so values stay in the lossless formatter range. -/
def mcWhirterShape (T dE : Float) : Float := Float.sqrt T * dE ^ 3

-- ### Runtime-certificate predicate mirrors (mirror of `CflibsFormal/Certificates.lean`)

/-- Centered sum of squares `SSₓ = Σ_k (x_k − x̄)²` (mirror of `∑ k, (E k − mean E)^2`, the
`OLS.designNormalMatrix` energy spread that gates C1/C3 and enters C2). -/
def ssq (x : Vec) : Float :=
  let xb := mean x
  x.foldl (fun acc xk => acc + (xk - xb) * (xk - xb)) 0.0

/-- Centered cross term `S_xy = Σ_k (x_k − x̄)(y_k − ȳ)` (mirror of the joint-design off-diagonal
`∑ k, (E k − mean E)*(s k − mean s)` in C2). -/
def crossSum (x y : Vec) : Float :=
  let xb := mean x
  let yb := mean y
  (x.zip y).foldl (fun acc p => acc + (p.1 - xb) * (p.2 - yb)) 0.0

/-- Mirror of `CflibsFormal.sahaEquilibriumNe`: the closed-form single-element two-stage electron
density `(−S + √(S² + 4·S·Ntot))/2` — the fixed point the C9 iteration converges to. -/
def sahaEquilibriumNe (S Ntot : Float) : Float :=
  (-S + Float.sqrt (S * S + 4.0 * S * Ntot)) / 2.0

/-- C1/C3 `energySpreadCert`/`conditioningCert`: verdict `0 < SSₑ`, value `SSₑ`. -/
def certEnergySpread (E : Vec) : Bool × Float := let s := ssq E; (s > 0.0, s)

/-- C2 `jointRankCert`: verdict `0 < SSₑ·SSₛ − S_Es²`, value the joint Gram determinant. -/
def certJointRank (E s : Vec) : Bool × Float :=
  let ces := crossSum E s
  let det := ssq E * ssq s - ces * ces
  (det > 0.0, det)

/-- C4 `slopeBudgetCert`: verdict `eps²·n ≤ tauBeta²·SSₑ`, value the slack `rhs − lhs`. -/
def certSlopeBudget (eps tauBeta ssE n : Float) : Bool × Float :=
  let lhs := eps * eps * n
  let rhs := tauBeta * tauBeta * ssE
  (lhs <= rhs, rhs - lhs)

/-- C5 `tempBudgetCert`: verdict `kB·T̂·B ≤ tauT`, value the slack `tauT − lhs`. -/
def certTempBudget (kBv THat B tauT : Float) : Bool × Float :=
  let lhs := kBv * THat * B
  (lhs <= tauT, tauT - lhs)

/-- C6 `compBudgetCert`: verdict `(n+1)·delta ≤ tauC·Ŝ`, value the slack `rhs − lhs`. -/
def certCompBudget (delta tauC shat n : Float) : Bool × Float :=
  let lhs := (n + 1.0) * delta
  let rhs := tauC * shat
  (lhs <= rhs, rhs - lhs)

/-- C7 `mcWhirterCert`: verdict `C·√T·ΔE³ ≤ nₑ`, value the McWhirter margin `nₑ − lhs`. -/
def certMcWhirter (cc t dE ne : Float) : Bool × Float :=
  let lhs := cc * Float.sqrt t * dE ^ 3
  (lhs <= ne, ne - lhs)

/-- C9 `sahaIterCert`: verdict = all four clauses (`b<Ntot ∧ root≤b ∧ rate<1 ∧ √(S·Ntot)≤b`),
value the contraction rate `√S/(2·√(Ntot−b))`. -/
def certSahaIter (S Ntot b : Float) : Bool × Float :=
  let root := sahaEquilibriumNe S Ntot
  let rate := if b < Ntot then Float.sqrt S / (2.0 * Float.sqrt (Ntot - b)) else 2.0
  let ok := (b < Ntot) && (root <= b) && (rate < 1.0) && (Float.sqrt (S * Ntot) <= b)
  (ok, rate)

/-- C10 `dampedIterCert`: verdict = all `Sₛ>0 ∧ Ntotₛ>0`, value the proven convergence rate
`1 − lam` with the canonical `lam = 1/(1 + Σ Ntotₛ/Sₛ)` (finite only when the verdict holds). -/
def certDampedIter (S Ntot : Vec) : Bool × Float :=
  let posS := S.foldl (fun acc s => acc && (s > 0.0)) true
  let posN := Ntot.foldl (fun acc nt => acc && (nt > 0.0)) true
  let ok := posS && posN
  let value := if ok then
      let sumRatio := (Ntot.zip S).foldl (fun acc p => acc + p.1 / p.2) 0.0
      1.0 - 1.0 / (1.0 + sumRatio)
    else 0.0
  (ok, value)

/-- C12 `knownTauCert`: verdict `0 ≤ tau`, value `tau`. -/
def certKnownTau (tau : Float) : Bool × Float := (tau >= 0.0, tau)

/-- C13 `saDistinctCert`: verdict `0 < w₂ ∧ w₂ < w₁`, value the width gap `w₁ − w₂`. -/
def certSaDistinct (w₁ w₂ : Float) : Bool × Float :=
  ((0.0 < w₂) && (w₂ < w₁), w₁ - w₂)

/-- C14 `aliasBudgetCert` (A*): verdict `0 ≤ delta ∧ delta < 1`, value the error amplification
`delta/(1 − delta)` (finite only when `delta < 1`). REFUSAL: `delta` is ASSUMED, not measured. -/
def certAliasBudget (delta : Float) : Bool × Float :=
  let ok := (0.0 <= delta) && (delta < 1.0)
  (ok, if delta < 1.0 then delta / (1.0 - delta) else 0.0)

/-! ## JSON emission -/

/-- 9-decimal fixed-point rendering via a scaled integer (Lean's `Float.toString` is lossy
`%.6f`). Assumes `|x|` is O(1)–O(few·10), keeping `|x|·1e9` in the exact-integer range. -/
def jNum (x : Float) : String :=
  let neg := x < 0.0
  let a := if neg then -x else x
  let n : Nat := (a * 1.0e9 + 0.5).floor.toUInt64.toNat
  let intPart := n / 1000000000
  let frac := n % 1000000000
  let fs := toString frac
  let fracStr := String.ofList (List.replicate (9 - fs.length) '0') ++ fs
  (if neg then "-" else "") ++ toString intPart ++ "." ++ fracStr
def jVec (xs : Vec) : String := "[" ++ String.intercalate ", " (xs.toList.map jNum) ++ "]"
def jField (k : String) (v : String) : String := "\"" ++ k ++ "\": " ++ v
def jStr (s : String) : String := "\"" ++ s ++ "\""
def jBool (b : Bool) : String := if b then "true" else "false"
def jArrayOf (xs : Array String) : String := "[" ++ String.intercalate ", " xs.toList ++ "]"

/-! ## Scenario 1 — ternary alloy -/

/-- One chemical element with its OWN atomic-data family, true density, designated line, and
(for the self-absorption check) the optical depth `tau` of its designated line. -/
structure Element where
  sym : String
  g : Vec
  E : Vec
  A : Vec
  N : Float
  u : Nat
  tau : Float
  deriving Inhabited

-- DIMENSIONLESS constants (the spec is dimensionless — see CONTEXT.md). Feed the pipeline these.
def kB : Float := 1.0
def T  : Float := 1.0
def Fcal : Float := 1.0

/-- Ternary "alloy": 3 chemically-distinct elements, distinct atomic data + `U_s`, 4 lines each,
distinct optical depths. True densities 5/3/2 ⇒ composition [0.5, 0.3, 0.2]. (Synthetic
dimensionless atomic data; swap in NIST values.) -/
def alloy : Array Element :=
  #[{ sym := "El-A", g := #[2.0, 4.0, 6.0, 8.0], E := #[0.0, 1.2, 2.5, 3.8],
      A := #[1.0, 0.7, 0.5, 0.3], N := 5.0, u := 0, tau := 0.5 },
    { sym := "El-B", g := #[1.0, 3.0, 5.0, 7.0], E := #[0.0, 0.9, 2.1, 3.3],
      A := #[0.9, 0.6, 0.4, 0.2], N := 3.0, u := 1, tau := 1.0 },
    { sym := "El-C", g := #[3.0, 5.0, 7.0, 9.0], E := #[0.0, 1.5, 2.8, 4.0],
      A := #[0.8, 0.5, 0.35, 0.25], N := 2.0, u := 2, tau := 1.5 }]

def forwardLines (el : Element) : Vec :=
  (Array.range el.g.size).map (fun k => lineIntensity kB T el.N Fcal el.g el.E el.A k)

def recoveredDensityOf (el : Element) (fc : Float) : Float :=
  classicDensity kB T fc el.g el.E el.A el.u (lineIntensity kB T el.N fc el.g el.E el.A el.u)

/-- OLS-recovered density: regress over ALL the element's lines (not just one). -/
def olsDensityOf (el : Element) : Float :=
  olsDensity kB T Fcal el.g el.E el.A (forwardLines el)

/-- Self-absorption-corrected density: optically-thick measured intensity = thin · SA(τ),
then correct + invert. Recovers the true `N` (the SA factor cancels). -/
def selfAbsorbedDensityOf (el : Element) : Float :=
  let thin := lineIntensity kB T el.N Fcal el.g el.E el.A el.u
  let thick := thin * selfAbsorptionFactor el.tau
  selfAbsorbedDensity kB T Fcal el.g el.E el.A el.u el.tau thick

def recoveredComposition (densFn : Element → Float) : Vec :=
  let dens : Vec := alloy.map densFn
  (Array.range alloy.size).map (fun i => composition dens i)

def trueComposition : Vec :=
  let N : Vec := alloy.map (·.N)
  (Array.range N.size).map (fun i => composition N i)

def recoveredTOf (el : Element) : Float :=
  recoverT kB el.g el.E el.A 0 1
    (lineIntensity kB T el.N Fcal el.g el.E el.A 0)
    (lineIntensity kB T el.N Fcal el.g el.E el.A 1)

def jElement (el : Element) : String :=
  "{" ++ jField "sym" (jStr el.sym) ++ ", " ++ jField "g" (jVec el.g) ++ ", "
    ++ jField "E" (jVec el.E) ++ ", " ++ jField "A" (jVec el.A) ++ ", "
    ++ jField "N" (jNum el.N) ++ ", " ++ jField "u" (toString el.u) ++ ", "
    ++ jField "tau" (jNum el.tau) ++ ", "
    ++ jField "partitionFunction" (jNum (partitionFunction kB T el.g el.E)) ++ ", "
    ++ jField "intensities" (jVec (forwardLines el)) ++ "}"

def alloyScenario : String :=
  let elems := jArrayOf (alloy.map jElement)
  let trueDen := jVec (alloy.map (·.N))
  let recDen := jVec (alloy.map (fun el => recoveredDensityOf el Fcal))
  let trueT := jVec (alloy.map (fun _ => T))
  let recT := jVec (alloy.map recoveredTOf)
  let comp := jVec (recoveredComposition (fun el => recoveredDensityOf el Fcal))
  let compScaled := jVec (recoveredComposition (fun el => recoveredDensityOf el (1000.0 * Fcal)))
  let olsDen := jVec (alloy.map olsDensityOf)
  let olsComp := jVec (recoveredComposition olsDensityOf)
  let saComp := jVec (recoveredComposition selfAbsorbedDensityOf)
  let fwd := "{" ++ jField "theorem" (jStr "ForwardMap.lineIntensity / boltzmann_plot_intensity")
    ++ ", " ++ jField "must" (jStr "lineIntensity(element.g,E,A, N, k) == element.intensities[k]") ++ "}"
  let rt := "{" ++ jField "theorem" (jStr "Classic.classicDensity_recovers / classic_sound")
    ++ ", " ++ jField "true_densities" trueDen ++ ", " ++ jField "recovered_densities" recDen
    ++ ", " ++ jField "must" (jStr "classicDensity(lineIntensity(N)) == N per element (own U_s)") ++ "}"
  let tmp := "{" ++ jField "theorem" (jStr "Classic.classic_temperature_correct")
    ++ ", " ++ jField "true_T" trueT ++ ", " ++ jField "recovered_T" recT
    ++ ", " ++ jField "must" (jStr "2-line Boltzmann slope recovers T per element") ++ "}"
  let ols := "{" ++ jField "theorem" (jStr "Alt.olsDensity_recovers / leastSquares_sound / leastSquares_agrees_classic")
    ++ ", " ++ jField "ols_densities" olsDen ++ ", " ++ jField "ols_composition" olsComp
    ++ ", " ++ jField "must" (jStr "OLS over ALL lines recovers N per element AND ols_composition == true composition (agrees with classic)") ++ "}"
  let sa := "{" ++ jField "theorem" (jStr "Alt.selfAbsorbed_sound")
    ++ ", " ++ jField "self_absorbed_composition" saComp
    ++ ", " ++ jField "must" (jStr "from optically-thick intensities (thin*SA(tau)) + known tau, the corrected estimator recovers the true composition") ++ "}"
  let cl := "{" ++ jField "theorem" (jStr "Closure.composition_sum_one / classic_sound")
    ++ ", " ++ jField "true_composition" (jVec trueComposition) ++ ", " ++ jField "recovered_composition" comp
    ++ ", " ++ jField "must" (jStr "recovered == true mole fractions AND sum == 1 (heterogeneous elements)") ++ "}"
  let cf := "{" ++ jField "theorem" (jStr "Classic.classic_calibration_free")
    ++ ", " ++ jField "Fcal_scale" (jNum 1000.0) ++ ", " ++ jField "composition_base" comp
    ++ ", " ++ jField "composition_scaled" compScaled
    ++ ", " ++ jField "must" (jStr "composition_scaled == composition_base (Fcal cancels)") ++ "}"
  let checks := "{" ++ jField "forward" fwd ++ ", " ++ jField "round_trip" rt ++ ", "
    ++ jField "temperature" tmp ++ ", " ++ jField "ols" ols ++ ", "
    ++ jField "self_absorbed" sa ++ ", " ++ jField "closure" cl ++ ", "
    ++ jField "calibration_free" cf ++ "}"
  "{" ++ jField "name" (jStr ("ternary alloy — 3 chemically-distinct elements, distinct atomic "
    ++ "data + partition functions, 4 lines each; classic + OLS + self-absorbed estimators"))
    ++ ", " ++ jField "kind" (jStr "multi-element-composition")
    ++ ", " ++ jField "true_composition" (jVec trueComposition)
    ++ ", " ++ jField "elements" elems ++ ", " ++ jField "checks" checks ++ "}"

/-! ## Scenario 2 — two-stage Saha–Boltzmann (electron density) -/

/-- A single element in two adjacent ionization stages (neutral `z`, ion `z+1`), each with its
own atomic data. `Nz1` is fixed by the Saha law `Nz1·ne/Nz = S(T)` (so the recovery is genuine,
not assumed). Shared physical constants `me = h = 1`. -/
structure TwoStage where
  gZ : Vec      -- neutral stage statistical weights
  EZ : Vec
  AZ : Vec
  gZ1 : Vec     -- ion stage
  EZ1 : Vec
  AZ1 : Vec
  Nz : Float    -- true neutral density
  ne : Float    -- true electron density
  chi : Float   -- ionization energy
  uz : Nat      -- designated neutral line
  uz1 : Nat     -- designated ion line
  deriving Inhabited

def me : Float := 1.0
def hPlanck : Float := 1.0

def twoStage : TwoStage :=
  { gZ := #[2.0, 4.0, 6.0], EZ := #[0.0, 1.0, 2.0], AZ := #[1.0, 0.7, 0.4]
    gZ1 := #[1.0, 3.0, 5.0], EZ1 := #[0.0, 1.5, 3.0], AZ1 := #[0.8, 0.5, 0.3]
    Nz := 5.0, ne := 4.0, chi := 2.0, uz := 0, uz1 := 0 }

/-- Saha factor `S(T)` for the two-stage element. -/
def twoStageS (ts : TwoStage) : Float :=
  sahaFactor kB T me hPlanck ts.chi ts.gZ ts.EZ ts.gZ1 ts.EZ1

/-- True ion density fixed by the Saha law: `Nz1 = S(T) · Nz / ne`. -/
def twoStageNz1 (ts : TwoStage) : Float := twoStageS ts * ts.Nz / ts.ne

def twoStageScenario : String :=
  let ts := twoStage
  let S := twoStageS ts
  let Nz1 := twoStageNz1 ts
  -- forward intensities for both stages
  let neutLines := (Array.range ts.gZ.size).map (fun k => lineIntensity kB T ts.Nz Fcal ts.gZ ts.EZ ts.AZ k)
  let ionLines := (Array.range ts.gZ1.size).map (fun k => lineIntensity kB T Nz1 Fcal ts.gZ1 ts.EZ1 ts.AZ1 k)
  -- recovery: T from neutral slope; Nz, Nz1 from designated lines; R; ne = S/R
  let Trec := recoverT kB ts.gZ ts.EZ ts.AZ 0 1 (neutLines[0]!) (neutLines[1]!)
  let NzRec := classicDensity kB T Fcal ts.gZ ts.EZ ts.AZ ts.uz (neutLines[ts.uz]!)
  let Nz1Rec := classicDensity kB T Fcal ts.gZ1 ts.EZ1 ts.AZ1 ts.uz1 (ionLines[ts.uz1]!)
  let Rrec := Nz1Rec / NzRec
  let neRec := electronDensityFromRatio kB T me hPlanck ts.chi ts.gZ ts.EZ ts.gZ1 ts.EZ1 Rrec
  let neutral := "{" ++ jField "g" (jVec ts.gZ) ++ ", " ++ jField "E" (jVec ts.EZ) ++ ", "
    ++ jField "A" (jVec ts.AZ) ++ ", " ++ jField "N" (jNum ts.Nz) ++ ", " ++ jField "u" (toString ts.uz)
    ++ ", " ++ jField "intensities" (jVec neutLines) ++ "}"
  let ion := "{" ++ jField "g" (jVec ts.gZ1) ++ ", " ++ jField "E" (jVec ts.EZ1) ++ ", "
    ++ jField "A" (jVec ts.AZ1) ++ ", " ++ jField "N" (jNum Nz1) ++ ", " ++ jField "u" (toString ts.uz1)
    ++ ", " ++ jField "intensities" (jVec ionLines) ++ "}"
  let temp := "{" ++ jField "theorem" (jStr "Classic.classic_temperature_correct")
    ++ ", " ++ jField "true_T" (jNum T) ++ ", " ++ jField "recovered_T" (jNum Trec)
    ++ ", " ++ jField "must" (jStr "neutral 2-line slope recovers T") ++ "}"
  let sahaC := "{" ++ jField "theorem" (jStr "Saha.electronDensityFromRatio / saha_relation / electronDensity_antitone / SahaInverse.saha_joint_identifiability")
    ++ ", " ++ jField "true_ne" (jNum ts.ne) ++ ", " ++ jField "recovered_ne" (jNum neRec)
    ++ ", " ++ jField "sahaFactor" (jNum S) ++ ", " ++ jField "stage_ratio" (jNum Rrec)
    ++ ", " ++ jField "must" (jStr "recover Nz and Nz1 from forward intensities; R = Nz1/Nz; ne = S(T)/R == true ne; and R*ne == S(T) (Saha law)") ++ "}"
  "{" ++ jField "name" (jStr "two-stage Saha–Boltzmann — neutral + ion stages, recover T and electron density n_e")
    ++ ", " ++ jField "kind" (jStr "saha-boltzmann")
    ++ ", " ++ jField "constants" ("{" ++ jField "me" (jNum me) ++ ", " ++ jField "h" (jNum hPlanck)
      ++ ", " ++ jField "chi" (jNum ts.chi) ++ "}")
    ++ ", " ++ jField "neutral" neutral ++ ", " ++ jField "ion" ion
    ++ ", " ++ jField "checks" ("{" ++ jField "temperature" temp ++ ", " ++ jField "saha" sahaC ++ "}") ++ "}"

/-! ## Scenario 3 — error-budget thresholds (DERIVED reliability knobs) -/

/-- A concrete dimensionless instance of the derived thresholds, with self-consistency invariants
that each instantiate a proven `ErrorBudget` theorem. The two "tight" checks witness that
`requiredEnergySpread` / `maxPerLineError` are exactly the values at which the slope-sensitivity
bound EQUALS the target — i.e. the sufficient thresholds are not loose. -/
def errorBudgetScenario : String :=
  let tauBeta : Float := 0.05    -- target inverse-temperature (slope) error
  let snr : Float := 0.02        -- per-line Boltzmann-plot ordinate error
  let n : Float := 6.0           -- number of lines
  let ssE : Float := 8.0         -- energy spread Σ(Eₖ − Ē)²
  let relTtarget : Float := 0.03 -- target relative temperature error
  let tauC : Float := 0.01       -- target composition accuracy
  let Shat : Float := 10.0       -- recovered total density
  let card : Float := 3.0        -- number of species
  let vPerLine : Float := 1.5    -- per-line energy variance (for the statistical line count)
  let reqSpread := requiredEnergySpread tauBeta snr n
  let maxErr := maxPerLineError tauBeta n ssE
  let reqLines := requiredMinLinesStat tauBeta snr vPerLine
  let slopeTgt := slopeTargetFromTempRel relTtarget kB T
  let densBudget := densityBudgetFromComposition tauC Shat card
  let noiseGain : Float := 1.0 / ssE
  let boundAtReqSpread := slopeErrorBound snr n reqSpread   -- == tauBeta (energy-spread tight)
  let boundAtMaxErr := slopeErrorBound maxErr n ssE         -- == tauBeta (SNR tight)
  let inputs := "{" ++ jField "tauBeta" (jNum tauBeta) ++ ", " ++ jField "snr" (jNum snr)
    ++ ", " ++ jField "n" (jNum n) ++ ", " ++ jField "ssE" (jNum ssE) ++ ", "
    ++ jField "kB" (jNum kB) ++ ", " ++ jField "T" (jNum T) ++ ", "
    ++ jField "relTtarget" (jNum relTtarget) ++ ", " ++ jField "tauC" (jNum tauC) ++ ", "
    ++ jField "Shat" (jNum Shat) ++ ", " ++ jField "card" (jNum card) ++ ", "
    ++ jField "vPerLine" (jNum vPerLine) ++ "}"
  let thresholds := "{" ++ jField "requiredEnergySpread" (jNum reqSpread) ++ ", "
    ++ jField "maxPerLineError" (jNum maxErr) ++ ", "
    ++ jField "requiredMinLinesStat" (jNum reqLines) ++ ", "
    ++ jField "slopeTargetFromTempRel" (jNum slopeTgt) ++ ", "
    ++ jField "densityBudgetFromComposition" (jNum densBudget) ++ ", "
    ++ jField "noiseGain" (jNum noiseGain) ++ "}"
  let cEnergy := "{" ++ jField "theorem" (jStr "ErrorBudget.requiredEnergySpread_sufficient")
    ++ ", " ++ jField "bound_at_threshold" (jNum boundAtReqSpread) ++ ", "
    ++ jField "tauBeta" (jNum tauBeta) ++ ", "
    ++ jField "must" (jStr "slopeErrorBound(snr, n, requiredEnergySpread(tauBeta,snr,n)) == tauBeta (threshold is tight)") ++ "}"
  let cSnr := "{" ++ jField "theorem" (jStr "ErrorBudget.maxPerLineError_sufficient")
    ++ ", " ++ jField "bound_at_threshold" (jNum boundAtMaxErr) ++ ", "
    ++ jField "tauBeta" (jNum tauBeta) ++ ", "
    ++ jField "must" (jStr "slopeErrorBound(maxPerLineError(tauBeta,n,ssE), n, ssE) == tauBeta (threshold is tight)") ++ "}"
  let cNoise := "{" ++ jField "theorem" (jStr "ErrorBudget.olsSlope_noise_gain")
    ++ ", " ++ jField "noiseGain" (jNum noiseGain) ++ ", " ++ jField "ssE" (jNum ssE) ++ ", "
    ++ jField "must" (jStr "noiseGain == 1/ssE (Gauss-Markov slope-variance multiplier)") ++ "}"
  let cTemp := "{" ++ jField "theorem" (jStr "ErrorBudget.temp_rel_error_eq")
    ++ ", " ++ jField "slopeTarget" (jNum slopeTgt) ++ ", " ++ jField "relTtarget" (jNum relTtarget)
    ++ ", " ++ jField "must" (jStr "slopeTargetFromTempRel(relTtarget,kB,T) * (kB*T) == relTtarget (exact)") ++ "}"
  let cComp := "{" ++ jField "theorem" (jStr "ErrorBudget.composition_target_sufficient")
    ++ ", " ++ jField "densityBudget" (jNum densBudget) ++ ", " ++ jField "tauC" (jNum tauC)
    ++ ", " ++ jField "Shat" (jNum Shat) ++ ", " ++ jField "card" (jNum card) ++ ", "
    ++ jField "must" (jStr "(card+1)*densityBudgetFromComposition(tauC,Shat,card) == tauC*Shat (budget saturates the target)") ++ "}"
  let checks := "{" ++ jField "energy_spread_tight" cEnergy ++ ", " ++ jField "snr_tight" cSnr
    ++ ", " ++ jField "noise_gain" cNoise ++ ", " ++ jField "temp_rel" cTemp ++ ", "
    ++ jField "composition_budget" cComp ++ "}"
  "{" ++ jField "name" (jStr ("error-budget thresholds — min energy spread, min SNR, and the "
    ++ "temperature / composition budgets DERIVED from the proven error-propagation chain"))
    ++ ", " ++ jField "kind" (jStr "error-budget")
    ++ ", " ++ jField "inputs" inputs ++ ", " ++ jField "thresholds" thresholds
    ++ ", " ++ jField "checks" checks ++ "}"

/-! ## Scenario 4 — energy/wavelength ordinate (convention equivalence, distinct per-line λ) -/

/-- One element fed through the ENERGY forward map `lineIntensityEnergy` with DISTINCT,
`E_k`-correlated per-line wavelengths `λ` (never `λ = 1` — uniform λ is blind to every λ-bug).
The checks instantiate `ForwardMapEnergy` theorems: the energy map reduces to the photon-rate
`lineIntensity` (per-line `Fcal`), `I·λ` recovers the λ-free reduced map, and the wavelength-form
ordinate `ln(I·λ/(g·A))` recovers the same temperature `T`. This is the proven λ-form bridge the
companion pipeline (`y = ln(I·λ/(g·A))`) regression-tests against. -/
def energyOrdinateScenario : String :=
  let g : Vec := #[2.0, 4.0, 6.0, 8.0]
  let E : Vec := #[0.0, 1.2, 2.5, 3.8]
  let A : Vec := #[1.0, 0.7, 0.5, 0.3]
  let lam : Vec := #[3.0, 2.6, 2.1, 1.7]   -- distinct, decreasing as E increases (E_k-correlated)
  let Nd : Float := 5.0
  let hc : Float := 2.0
  let fourPi : Float := 4.0
  let Fgeo : Float := 1.5
  let nlines := g.size
  let Ien := (Array.range nlines).map (fun k => lineIntensityEnergy hc fourPi kB T Nd Fgeo g E A lam k)
  let constants := "{" ++ jField "hc" (jNum hc) ++ ", " ++ jField "fourPi" (jNum fourPi)
    ++ ", " ++ jField "Fgeo" (jNum Fgeo) ++ "}"
  let elem := "{" ++ jField "g" (jVec g) ++ ", " ++ jField "E" (jVec E) ++ ", "
    ++ jField "A" (jVec A) ++ ", " ++ jField "lambda" (jVec lam) ++ ", "
    ++ jField "N" (jNum Nd) ++ ", " ++ jField "intensities" (jVec Ien) ++ "}"
  let fwd := "{" ++ jField "theorem" (jStr "ForwardMapEnergy.lineIntensityEnergy")
    ++ ", " ++ jField "must" (jStr "lineIntensityEnergy(hc,4pi,N,Fgeo, g,E,A,lambda, k) == element.intensities[k]") ++ "}"
  let red := "{" ++ jField "theorem" (jStr "ForwardMapEnergy.lineIntensityEnergy_eq_lineIntensity")
    ++ ", " ++ jField "must" (jStr "lineIntensityEnergy[k] == lineIntensity(Fcal = hc*Fgeo/(4pi*lambda[k]))[k] (per-line Fcal reduction)") ++ "}"
  let mulLam := "{" ++ jField "theorem" (jStr "ForwardMapEnergy.lineIntensityEnergy_mul_lam")
    ++ ", " ++ jField "must" (jStr "lineIntensityEnergy[k] * lambda[k] == lineIntensity(Fcal = hc*Fgeo/(4pi))[k] (lambda cancels the 1/lambda photon-energy factor)") ++ "}"
  let tmp := "{" ++ jField "theorem" (jStr "ForwardMapEnergy.temperature_from_two_lines_wavelength")
    ++ ", " ++ jField "true_T" (jNum T)
    ++ ", " ++ jField "must" (jStr "2-line slope of the wavelength ordinate ln(I*lambda/(g*A)) recovers T (distinct per-line lambda; lambda cancels)") ++ "}"
  let checks := "{" ++ jField "forward" fwd ++ ", " ++ jField "reduction" red ++ ", "
    ++ jField "mul_lam" mulLam ++ ", " ++ jField "temperature" tmp ++ "}"
  "{" ++ jField "name" (jStr ("energy/wavelength ordinate — one element through the energy forward "
    ++ "map with DISTINCT per-line lambda; proves the wavelength (ln(I*lambda/gA)) and photon-rate "
    ++ "(ln(I/gA)) conventions agree"))
    ++ ", " ++ jField "kind" (jStr "energy-ordinate")
    ++ ", " ++ jField "constants" constants ++ ", " ++ jField "element" elem
    ++ ", " ++ jField "checks" checks ++ "}"

/-! ## Scenario 5 — Stark broadening n_e diagnostic + McWhirter LTE bound -/

/-- The Griem linear Stark-width inverse (`n_e = nRef·width/(2w)`) and the `√T·ΔE³` McWhirter shape,
all DIMENSIONLESS (so the `1.6e12` / `REF_NE` physical constants stay out of the lossless
formatter; the Python checker applies them). Pins `StarkBroadening.starkDensity_recovers` and
`mcWhirterBound`. -/
def starkScenario : String :=
  let w : Float := 0.05    -- HWHM Stark coefficient (dimensionless)
  let nRef : Float := 1.0  -- reference density (dimensionless; pipeline uses REF_NE)
  let width : Float := 0.3 -- measured FWHM (dimensionless)
  let ne := starkDensity w nRef width      -- = 3.0 (Griem linear inverse)
  let widthRT := starkFWHM w nRef ne       -- = width (forward/inverse round trip)
  let tMc : Float := 4.0
  let dE : Float := 2.0
  let mcShape := mcWhirterShape tMc dE     -- = 16.0; full bound = 1.6e12 * shape
  let consts := "{" ++ jField "w" (jNum w) ++ ", " ++ jField "nRef" (jNum nRef) ++ ", "
    ++ jField "width" (jNum width) ++ ", " ++ jField "T" (jNum tMc) ++ ", " ++ jField "dE" (jNum dE)
    ++ "}"
  let cDensity := "{" ++ jField "theorem" (jStr "StarkBroadening.starkDensity_recovers")
    ++ ", " ++ jField "ne" (jNum ne) ++ ", "
    ++ jField "must" (jStr ("starkDensity(w,nRef,width) == nRef*width/(2w) == ne (Griem linear n_e "
      ++ "diagnostic); pipeline estimate_ne_from_stark(width, REF_T_K, stark_w_ref=2w) == REF_NE*ne/nRef")) ++ "}"
  let cRoundtrip := "{" ++ jField "theorem" (jStr "StarkBroadening.starkFWHM / starkDensity_recovers")
    ++ ", " ++ jField "width_roundtrip" (jNum widthRT) ++ ", "
    ++ jField "must" (jStr "starkFWHM(w,nRef, starkDensity(w,nRef,width)) == width (forward/inverse round trip)") ++ "}"
  let cMc := "{" ++ jField "theorem" (jStr "StarkBroadening.mcWhirterBound")
    ++ ", " ++ jField "shape" (jNum mcShape) ++ ", "
    ++ jField "must" (jStr "mcWhirterShape(T,dE) == sqrt(T)*dE^3 == shape; full McWhirter LTE bound = 1.6e12 * shape (pipeline MCWHIRTER_CONST)") ++ "}"
  let checks := "{" ++ jField "stark_density" cDensity ++ ", " ++ jField "stark_roundtrip" cRoundtrip
    ++ ", " ++ jField "mcwhirter" cMc ++ "}"
  "{" ++ jField "name" (jStr ("Stark broadening n_e diagnostic + McWhirter LTE bound -- dimensionless "
    ++ "Griem linear width inverse (n_e = nRef*width/(2w)) and the sqrt(T)*dE^3 McWhirter shape"))
    ++ ", " ++ jField "kind" (jStr "stark")
    ++ ", " ++ jField "constants" consts ++ ", " ++ jField "checks" checks ++ "}"

/-! ## Scenario 6 — runtime certificates (the typed bridge, `CflibsFormal/Certificates.lean`) -/

/-- Envelope for one certificate entry: id, name, wrapped guarantee theorem, the checkable
predicate (as prose), the concrete `inputs`, the expected boolean `verdict`, and the decisive
`value` (the number compared — a determinant, contraction rate, or budget margin). -/
def jCert (id nm thm pred inputs : String) (verdict : Bool) (value : Float) : String :=
  "{" ++ jField "id" (jStr id) ++ ", " ++ jField "name" (jStr nm) ++ ", "
    ++ jField "theorem" (jStr thm) ++ ", " ++ jField "predicate" (jStr pred) ++ ", "
    ++ jField "inputs" inputs ++ ", " ++ jField "verdict" (jBool verdict) ++ ", "
    ++ jField "value" (jNum value) ++ "}"

/-- The 12 certificate predicates of `Certificates.lean`, each on its non-vacuity witness data
(the exact inputs of the Lean `example`s), plus the reference mirror's four rejection tests. Each
entry mirrors its `def …Cert` 1:1 (same inequalities, same strictness); the Python checker
recomputes the verdict + decisive value and must agree. -/
def certificatesScenario : String :=
  -- ===== positive cases (12 predicates on their Lean non-vacuity witnesses) =====
  -- C1 — energy-spread rank gate; witness E = [0,1] ⇒ SSₑ = 1/2
  let c1E : Vec := #[0.0, 1.0]
  let (c1v, c1n) := certEnergySpread c1E
  let c1 := jCert "C1" "energy_spread" "designNormalMatrix_det_ne_zero_iff" "0 < SSe"
    ("{" ++ jField "E" (jVec c1E) ++ "}") c1v c1n
  -- C2 — joint Saha–Boltzmann rank gate; witness E=[0,1,2], s=[0,0,1] ⇒ det = 1/3
  let c2E : Vec := #[0.0, 1.0, 2.0]
  let c2s : Vec := #[0.0, 0.0, 1.0]
  let (c2v, c2n) := certJointRank c2E c2s
  let c2 := jCert "C2" "joint_rank" "jointDesign_det_pos_iff" "0 < SSe*SSs - S_Es^2"
    ("{" ++ jField "E" (jVec c2E) ++ ", " ++ jField "s" (jVec c2s) ++ "}") c2v c2n
  -- C3 — Boltzmann-plot conditioning; same predicate/witness as C1 (distinct guarantee)
  let (c3v, c3n) := certEnergySpread c1E
  let c3 := jCert "C3" "conditioning" "boltzmannConditionNumber_ge_one" "0 < SSe"
    ("{" ++ jField "E" (jVec c1E) ++ "}") c3v c3n
  -- C4 — slope / energy-spread budget; witness eps=1, tauBeta=2, SSₑ=1/2, n=2 (tight, 2≤2)
  let c4eps : Float := 1.0; let c4tb : Float := 2.0; let c4ss : Float := 0.5; let c4n : Float := 2.0
  let (c4v, c4n') := certSlopeBudget c4eps c4tb c4ss c4n
  let c4 := jCert "C4" "slope_budget" "maxPerLineError_sufficient" "eps^2 * n <= tauBeta^2 * SSe"
    ("{" ++ jField "eps" (jNum c4eps) ++ ", " ++ jField "tauBeta" (jNum c4tb) ++ ", "
      ++ jField "SSe" (jNum c4ss) ++ ", " ++ jField "n" (jNum c4n) ++ "}") c4v c4n'
  -- C5 — temperature-error budget; witness kB=1, T̂=2, B=1/2, tauT=1 (tight, 1≤1)
  let c5kB : Float := 1.0; let c5TH : Float := 2.0; let c5B : Float := 0.5; let c5tt : Float := 1.0
  let (c5v, c5n) := certTempBudget c5kB c5TH c5B c5tt
  let c5 := jCert "C5" "temp_budget" "temp_rel_error_le" "kB * THat * B <= tauT"
    ("{" ++ jField "kB" (jNum c5kB) ++ ", " ++ jField "THat" (jNum c5TH) ++ ", "
      ++ jField "B" (jNum c5B) ++ ", " ++ jField "tauT" (jNum c5tt) ++ "}") c5v c5n
  -- C6 — composition budget; witness delta=1, tauC=2, Ŝ=2, n=2 (3≤4)
  let c6d : Float := 1.0; let c6tc : Float := 2.0; let c6sh : Float := 2.0; let c6n : Float := 2.0
  let (c6v, c6n') := certCompBudget c6d c6tc c6sh c6n
  let c6 := jCert "C6" "comp_budget" "composition_target_sufficient" "(n+1)*delta <= tauC*Shat"
    ("{" ++ jField "delta" (jNum c6d) ++ ", " ++ jField "tauC" (jNum c6tc) ++ ", "
      ++ jField "Shat" (jNum c6sh) ++ ", " ++ jField "n" (jNum c6n) ++ "}") c6v c6n'
  -- C7 — McWhirter LTE admissibility; witness C=1, T=1, ΔE=1, nₑ=2 (1≤2)
  let c7C : Float := 1.0; let c7T : Float := 1.0; let c7dE : Float := 1.0; let c7ne : Float := 2.0
  let (c7v, c7n) := certMcWhirter c7C c7T c7dE c7ne
  let c7 := jCert "C7" "mcwhirter" "mcwhirter_iff_thermalizationLimit" "C * sqrt(T) * dE^3 <= ne"
    ("{" ++ jField "C" (jNum c7C) ++ ", " ++ jField "T" (jNum c7T) ++ ", "
      ++ jField "dE" (jNum c7dE) ++ ", " ++ jField "ne" (jNum c7ne) ++ "}") c7v c7n
  -- C9 — inner Saha-iteration contraction; witness S=1, Ntot=3, b=2 ⇒ rate=1/2
  let c9S : Float := 1.0; let c9Nt : Float := 3.0; let c9b : Float := 2.0
  let (c9v, c9n) := certSahaIter c9S c9Nt c9b
  let c9 := jCert "C9" "saha_iter" "sahaIter_tendsto"
    "b < Ntot & sahaEquilibriumNe(S,Ntot) <= b & sqrt(S)/(2 sqrt(Ntot-b)) < 1 & sqrt(S*Ntot) <= b"
    ("{" ++ jField "S" (jNum c9S) ++ ", " ++ jField "Ntot" (jNum c9Nt) ++ ", "
      ++ jField "b" (jNum c9b) ++ "}") c9v c9n
  -- C10 — damped multi-element contraction (UNCONDITIONAL); witness S=Ntot=[1,1] ⇒ rate 1−1/3
  let c10S : Vec := #[1.0, 1.0]; let c10Nt : Vec := #[1.0, 1.0]
  let (c10v, c10n) := certDampedIter c10S c10Nt
  let c10 := jCert "C10" "damped_iter" "dampedMultiElementIter_tendsto"
    "(all s, S[s] > 0) & (all s, Ntot[s] > 0)"
    ("{" ++ jField "S" (jVec c10S) ++ ", " ++ jField "Ntot" (jVec c10Nt) ++ "}") c10v c10n
  -- C12 — self-absorption exact correction (known τ); witness τ=1 (SA(1)=1−e⁻¹ ≠ 1)
  let c12t : Float := 1.0
  let (c12v, c12n) := certKnownTau c12t
  let c12 := jCert "C12" "known_tau" "lineIntensity_eq_selfAbsorbedIntensity_div" "0 <= tau"
    ("{" ++ jField "tau" (jNum c12t) ++ "}") c12v c12n
  -- C13 — self-absorption identifiability; witness w₁=2, w₂=1 ⇒ 0 < 1 < 2
  let c13w1 : Float := 2.0; let c13w2 : Float := 1.0
  let (c13v, c13n) := certSaDistinct c13w1 c13w2
  let c13 := jCert "C13" "sa_distinct" "cogRatio_injOn" "0 < w2 & w2 < w1"
    ("{" ++ jField "w1" (jNum c13w1) ++ ", " ++ jField "w2" (jNum c13w2) ++ "}") c13v c13n
  -- C14 — atomic-data aliasing budget (A*, REFUSAL: δ assumed not measured); witness δ=1/2
  let c14d : Float := 0.5
  let (c14v, c14n) := certAliasBudget c14d
  let c14 := jCert "C14" "alias_budget" "classicDensity_aliasing_error" "0 <= delta & delta < 1"
    ("{" ++ jField "delta" (jNum c14d) ++ "}") c14v c14n
  -- ===== negative cases (the reference mirror's four rejection tests, docs/integration) =====
  -- C1 flat energies ⇒ SSₑ = 0 ⇒ reject
  let n1E : Vec := #[1.0, 1.0]
  let (n1v, n1n) := certEnergySpread n1E
  let n1 := jCert "C1" "energy_spread (reject: flat energies)" "designNormalMatrix_det_ne_zero_iff"
    "0 < SSe" ("{" ++ jField "E" (jVec n1E) ++ "}") n1v n1n
  -- C2 collinear E,s ⇒ det = 0 ⇒ reject
  let n2E : Vec := #[0.0, 1.0]; let n2s : Vec := #[0.0, 2.0]
  let (n2v, n2n) := certJointRank n2E n2s
  let n2 := jCert "C2" "joint_rank (reject: collinear E,s)" "jointDesign_det_pos_iff"
    "0 < SSe*SSs - S_Es^2" ("{" ++ jField "E" (jVec n2E) ++ ", " ++ jField "s" (jVec n2s) ++ "}")
    n2v n2n
  -- C10 nonpositive Saha factor ⇒ reject (value forced 0; convergence rate undefined)
  let n10S : Vec := #[0.0, 1.0]; let n10Nt : Vec := #[1.0, 1.0]
  let (n10v, n10n) := certDampedIter n10S n10Nt
  let n10 := jCert "C10" "damped_iter (reject: nonpositive S)" "dampedMultiElementIter_tendsto"
    "(all s, S[s] > 0) & (all s, Ntot[s] > 0)"
    ("{" ++ jField "S" (jVec n10S) ++ ", " ++ jField "Ntot" (jVec n10Nt) ++ "}") n10v n10n
  -- C14 δ=1 ⇒ reject (amplification would diverge; value forced 0)
  let n14d : Float := 1.0
  let (n14v, n14n) := certAliasBudget n14d
  let n14 := jCert "C14" "alias_budget (reject: delta = 1)" "classicDensity_aliasing_error"
    "0 <= delta & delta < 1" ("{" ++ jField "delta" (jNum n14d) ++ "}") n14v n14n
  let certs := jArrayOf #[c1, c2, c3, c4, c5, c6, c7, c9, c10, c12, c13, c14, n1, n2, n10, n14]
  "{" ++ jField "name" (jStr ("runtime certificates — the 12 predicates of CflibsFormal/"
    ++ "Certificates.lean (the typed bridge, dossier 12 M3), each on its non-vacuity witness "
    ++ "plus the reference mirror's rejection tests"))
    ++ ", " ++ jField "kind" (jStr "certificates")
    ++ ", " ++ jField "certificates" certs ++ "}"

/-- Emit the fixtures as a JSON document. -/
def render : String :=
  let header := jField "_about" (jStr ("Multi-element + alternative-estimator CF-LIBS regression "
    ++ "fixtures for CF-LIBS-improved, generated by the Float mirror of the verified CflibsFormal "
    ++ "spec (oracle/Generate.lean). Each check instantiates a PROVEN theorem; see "
    ++ "oracle/README.md. Dimensionless inputs; tolerance ~1e-6."))
  let glob := "{" ++ jField "kB" (jNum kB) ++ ", " ++ jField "T" (jNum T) ++ ", "
    ++ jField "Fcal" (jNum Fcal) ++ "}"
  "{\n  " ++ header ++ ",\n  " ++ jField "global" glob ++ ",\n  "
    ++ jField "scenarios"
        (jArrayOf #[alloyScenario, twoStageScenario, errorBudgetScenario, energyOrdinateScenario,
          starkScenario, certificatesScenario])
    ++ "\n}"

def main : IO Unit := IO.println render

end Oracle

def main : IO Unit := Oracle.main
