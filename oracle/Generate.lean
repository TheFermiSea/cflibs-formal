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

/-- Mirror of `Alt.mean`: arithmetic mean over the lines. -/
def mean (f : Vec) : Float := f.foldl (· + ·) 0.0 / f.size.toFloat

/-- Mirror of `Alt.olsSlope`: covariance/variance of the Boltzmann-plot points. -/
def olsSlope (E y : Vec) : Float :=
  let eb := mean E
  let yb := mean y
  let num := (E.zip y).foldl (fun acc p => acc + (p.1 - eb) * (p.2 - yb)) 0.0
  let den := E.foldl (fun acc ek => acc + (ek - eb) * (ek - eb)) 0.0
  num / den

/-- Mirror of `Alt.olsIntercept`: `ȳ − slope · Ē`. -/
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
        (jArrayOf #[alloyScenario, twoStageScenario, errorBudgetScenario, energyOrdinateScenario])
    ++ "\n}"

def main : IO Unit := IO.println render

end Oracle

def main : IO Unit := Oracle.main
