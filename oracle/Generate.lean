/-
Copyright (c) 2026 Brian Squires. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Squires
-/

/-!
# CF-LIBS numerical regression-oracle generator

A computable **`Float` mirror** of the verified `CflibsFormal` forward map and classic
inversion, used to emit numerical regression fixtures for the companion numerical pipeline
(CF-LIBS-improved). It is NOT part of the verified spec: the verified definitions in
`CflibsFormal/` are `noncomputable` and ℝ-valued (so they cannot be `#eval`'d). Here we
re-implement the SAME formulas over `Float`; each def mirrors its ℝ counterpart verbatim.

The fixtures exercise the **multi-element** CF-LIBS problem that is the whole point of the
method: a sample of several **chemically distinct** elements, each with its OWN atomic data
`(g, E, A)` and hence its OWN partition function `U_s(T)`, tied together only by the closure
`Σ C_s = 1`. (A single shared atomic-data family would be trivial.) The verified
`Classic.classicComposition` takes per-species `g E A : κ → ι → ℝ`, so this is exactly the
generality the spec proves sound.

Each check instantiates a **proven theorem** (see `oracle/README.md` for the map):
* `forward`          — `lineIntensity` per element with its own `(g,E,A)`;
* `round_trip`       — `classicDensity(lineIntensity N) = N`  ⇐ `Classic.classic_sound`;
* `temperature`      — slope of a 2-line Boltzmann plot recovers `T`  ⇐ `classic_temperature_correct`;
* `closure`          — `Σ_s composition = 1` and equals the true mole fractions  ⇐ `composition_sum_one`;
* `calibration_free` — scaling `Fcal` leaves composition fixed  ⇐ `classic_calibration_free`.

`Float ≠ ℝ`, so the *formula structure* and the *invariants* are what is verified; numerical
eval is IEEE-754 and checks are tolerance-based (~1e-6). Dimensionless inputs (`E` in units of
`kB·T`, so `kB = T = 1`), kept O(1) so the 9-decimal formatter is lossless.

Regenerate with:  `lake exe oracle-fixtures > oracle/fixtures.json`
-/

namespace Oracle

abbrev Vec := Array Float

/-- Mirror of `CflibsFormal.boltzmannFactor`: `exp(-E / (kB · T))`. -/
def boltzmannFactor (kB T E : Float) : Float := Float.exp (-E / (kB * T))

/-- Mirror of `CflibsFormal.partitionFunction`: `Σ_k g_k · exp(-E_k / (kB · T))`. (Per element:
distinct `(g, E)` give distinct `U_s` — the crux of the multi-element problem.) -/
def partitionFunction (kB T : Float) (g E : Vec) : Float :=
  (g.zip E).foldl (fun acc ge => acc + ge.1 * boltzmannFactor kB T ge.2) 0.0

/-- Mirror of `CflibsFormal.population`: `N · g_k · bf_k / U(T)`. -/
def population (kB T N : Float) (g E : Vec) (k : Nat) : Float :=
  N * g[k]! * boltzmannFactor kB T E[k]! / partitionFunction kB T g E

/-- Mirror of `CflibsFormal.lineIntensity`: `Fcal · A_k · population`. -/
def lineIntensity (kB T N Fcal : Float) (g E A : Vec) (k : Nat) : Float :=
  Fcal * A[k]! * population kB T N g E k

/-- Mirror of `CflibsFormal.Classic.classicDensity`: `I · U / (Fcal · A_u · g_u · bf_u)`.
Uses the element's OWN `(g, E, A)` and `U`. -/
def classicDensity (kB T Fcal : Float) (g E A : Vec) (u : Nat) (I : Float) : Float :=
  I * partitionFunction kB T g E / (Fcal * A[u]! * g[u]! * boltzmannFactor kB T E[u]!)

/-- Mirror of `CflibsFormal.composition`: `n_s / Σ_t n_t`. -/
def composition (n : Vec) (s : Nat) : Float := n[s]! / n.foldl (· + ·) 0.0

/-- Two-line Boltzmann-plot temperature recovery (mirror of `Classic.classic_temperature_correct`):
from `y_k = log(I_k/(g_k A_k)) = log(Fcal·N/U) − E_k/(kB·T)`, the slope `(y_j−y_i)/(E_i−E_j) =
1/(kB·T)`, so `T = (E_i − E_j) / (kB · (y_j − y_i))`. Needs two distinct-energy lines `i ≠ j`. -/
def recoverT (kB : Float) (g E A : Vec) (i j : Nat) (Ii Ij : Float) : Float :=
  let yi := Float.log (Ii / (g[i]! * A[i]!))
  let yj := Float.log (Ij / (g[j]! * A[j]!))
  (E[i]! - E[j]!) / (kB * (yj - yi))

/-! ## Minimal JSON emission -/

/-- Fixed-point rendering with 9 decimal places via a scaled integer. Lean's `Float.toString`
is hard-wired to 6 decimals (and underflows small magnitudes to `0.000000`), so we roll our
own. Assumes `|x|` is O(1) (all oracle values are dimensionless and `≤ ~10`), keeping
`|x|·1e9` inside the exact-integer range of `Float`. ~9 significant figures — ample for a
formula-correctness regression oracle (tolerance ~1e-6). -/
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

/-! ## Multi-element scenario -/

/-- One chemical element: its OWN atomic-data family `(g, E, A)`, true number density `N`, and
designated emitting line `u`. Distinct elements have distinct `(g, E, A)` and hence distinct
partition functions. -/
structure Element where
  sym : String
  g : Vec
  E : Vec
  A : Vec
  N : Float
  u : Nat
  deriving Inhabited

-- DIMENSIONLESS constants (the spec is dimensionless — see CONTEXT.md). `E` is in units of
-- `kB·T`, so `kB = T = 1`; `Fcal = 1`. Feed the pipeline THESE exact inputs.
def kB : Float := 1.0
def T  : Float := 1.0
def Fcal : Float := 1.0

/-- A ternary "alloy": three chemically-distinct elements with DISTINCT atomic data (so
distinct `U_s`), four lines each. True densities 5/3/2 ⇒ true composition [0.5, 0.3, 0.2].
(Synthetic dimensionless atomic data — the oracle tests the FORMULAS and INVARIANTS, not the
atomic data; swap in NIST values + your unit convention.) -/
def alloy : Array Element :=
  #[{ sym := "El-A", g := #[2.0, 4.0, 6.0, 8.0], E := #[0.0, 1.2, 2.5, 3.8],
      A := #[1.0, 0.7, 0.5, 0.3], N := 5.0, u := 0 },
    { sym := "El-B", g := #[1.0, 3.0, 5.0, 7.0], E := #[0.0, 0.9, 2.1, 3.3],
      A := #[0.9, 0.6, 0.4, 0.2], N := 3.0, u := 1 },
    { sym := "El-C", g := #[3.0, 5.0, 7.0, 9.0], E := #[0.0, 1.5, 2.8, 4.0],
      A := #[0.8, 0.5, 0.35, 0.25], N := 2.0, u := 2 }]

/-- All line intensities of an element (its own atomic data). -/
def forwardLines (el : Element) : Vec :=
  (Array.range el.g.size).map (fun k => lineIntensity kB T el.N Fcal el.g el.E el.A k)

/-- Classic-recovered density for an element from its designated-line intensity at calibration `fc`. -/
def recoveredDensityOf (el : Element) (fc : Float) : Float :=
  classicDensity kB T fc el.g el.E el.A el.u (lineIntensity kB T el.N fc el.g el.E el.A el.u)

/-- Recovered composition over the alloy (each element inverted with its OWN atomic data, then closed). -/
def recoveredComposition (fc : Float) : Vec :=
  let dens : Vec := alloy.map (fun el => recoveredDensityOf el fc)
  (Array.range alloy.size).map (fun i => composition dens i)

def trueComposition : Vec :=
  let N : Vec := alloy.map (·.N)
  (Array.range N.size).map (fun i => composition N i)

/-- Temperature recovered from lines 0 and 1 (distinct energies) of an element. -/
def recoveredTOf (el : Element) : Float :=
  recoverT kB el.g el.E el.A 0 1
    (lineIntensity kB T el.N Fcal el.g el.E el.A 0)
    (lineIntensity kB T el.N Fcal el.g el.E el.A 1)

def jElement (el : Element) : String :=
  "{" ++ jField "sym" (jStr el.sym) ++ ", " ++ jField "g" (jVec el.g) ++ ", "
    ++ jField "E" (jVec el.E) ++ ", " ++ jField "A" (jVec el.A) ++ ", "
    ++ jField "N" (jNum el.N) ++ ", " ++ jField "u" (toString el.u) ++ ", "
    ++ jField "partitionFunction" (jNum (partitionFunction kB T el.g el.E)) ++ ", "
    ++ jField "intensities" (jVec (forwardLines el)) ++ "}"

/-- Emit the fixtures as a JSON document. -/
def render : String :=
  let header := jField "_about" (jStr ("Multi-element CF-LIBS regression fixtures for " ++
    "CF-LIBS-improved, generated by the Float mirror of the verified CflibsFormal spec " ++
    "(oracle/Generate.lean). Each check instantiates a PROVEN theorem; see oracle/README.md. " ++
    "Dimensionless inputs; tolerance ~1e-6."))
  let glob := "{" ++ jField "kB" (jNum kB) ++ ", " ++ jField "T" (jNum T) ++ ", "
    ++ jField "Fcal" (jNum Fcal) ++ "}"
  let elems := jArrayOf (alloy.map jElement)
  let trueDen := jVec (alloy.map (·.N))
  let recDen := jVec (alloy.map (fun el => recoveredDensityOf el Fcal))
  let trueT := jVec (alloy.map (fun _ => T))
  let recT := jVec (alloy.map recoveredTOf)
  let comp := jVec (recoveredComposition Fcal)
  let compScaled := jVec (recoveredComposition (1000.0 * Fcal))
  let fwd := "{" ++ jField "theorem" (jStr "ForwardMap.lineIntensity / boltzmann_plot_intensity")
    ++ ", " ++ jField "must" (jStr "recompute lineIntensity(element.g,E,A, element.N, k) == element.intensities[k] (per-element atomic data)") ++ "}"
  let rt := "{" ++ jField "theorem" (jStr "Classic.classicDensity_recovers / classic_sound")
    ++ ", " ++ jField "true_densities" trueDen ++ ", " ++ jField "recovered_densities" recDen
    ++ ", " ++ jField "must" (jStr "classicDensity(lineIntensity(N)) == N per element (each with its own U_s)") ++ "}"
  let tmp := "{" ++ jField "theorem" (jStr "Classic.classic_temperature_correct")
    ++ ", " ++ jField "true_T" trueT ++ ", " ++ jField "recovered_T" recT
    ++ ", " ++ jField "must" (jStr "2-line Boltzmann-plot slope recovers T per element == global T") ++ "}"
  let cl := "{" ++ jField "theorem" (jStr "Closure.composition_sum_one / classic_sound")
    ++ ", " ++ jField "true_composition" (jVec trueComposition) ++ ", " ++ jField "recovered_composition" comp
    ++ ", " ++ jField "must" (jStr "recovered == true mole fractions AND sum(recovered) == 1 (heterogeneous elements)") ++ "}"
  let cf := "{" ++ jField "theorem" (jStr "Classic.classic_calibration_free")
    ++ ", " ++ jField "Fcal_scale" (jNum 1000.0) ++ ", " ++ jField "composition_base" comp
    ++ ", " ++ jField "composition_scaled" compScaled
    ++ ", " ++ jField "must" (jStr "composition_scaled == composition_base (Fcal cancels)") ++ "}"
  let checks := "{" ++ jField "forward" fwd ++ ", " ++ jField "round_trip" rt ++ ", "
    ++ jField "temperature" tmp ++ ", " ++ jField "closure" cl ++ ", "
    ++ jField "calibration_free" cf ++ "}"
  let scenario := "{" ++ jField "name" (jStr ("ternary alloy — 3 chemically-distinct elements, " ++
    "distinct atomic data + partition functions, 4 lines each"))
    ++ ", " ++ jField "true_composition" (jVec trueComposition)
    ++ ", " ++ jField "elements" elems ++ ", " ++ jField "checks" checks ++ "}"
  "{\n  " ++ header ++ ",\n  " ++ jField "global" glob ++ ",\n  "
    ++ jField "scenarios" (jArrayOf #[scenario]) ++ "\n}"

def main : IO Unit := IO.println render

end Oracle

def main : IO Unit := Oracle.main
