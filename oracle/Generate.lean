/-
Copyright (c) 2026 Brian Squires. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Squires
-/

/-!
# CF-LIBS numerical regression-oracle generator

This is a **computable `Float` mirror** of the verified `CflibsFormal` forward map and
classic inversion, used to emit numerical regression fixtures for the companion numerical
pipeline (CF-LIBS-improved). It is NOT part of the verified spec: the verified definitions
in `CflibsFormal/` are `noncomputable` and ℝ-valued (so they cannot be `#eval`'d), and ℝ is
not computable. Here we re-implement the SAME formulas over `Float`. Each def below mirrors
its ℝ counterpart verbatim in formula; only the carrier changes (ℝ → `Float`).

What makes this an *oracle* (not just numbers): the fixtures it emits instantiate the
**proven theorems** as executable invariants —
* round-trip recovery `classicDensity (lineIntensity N) = N`  ⇐  `Classic.classicDensity_recovers`
  / `Classic.classic_sound`;
* closure `Σ_s composition = 1`                                ⇐  `Closure.composition_sum_one`;
* calibration-free invariance (scaling `Fcal` leaves composition fixed)
                                                               ⇐  `Classic.classic_calibration_free`.
The numbers are double-precision; the *formula structure* and the *invariants* are what the
ℝ spec proves. See `oracle/README.md` for the fixture ↔ theorem map.

Regenerate with:  `lake exe oracle-fixtures > oracle/fixtures.json`
-/

namespace Oracle

abbrev Vec := Array Float

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

/-- Mirror of `CflibsFormal.Classic.classicDensity`: `I · U / (Fcal · A_u · g_u · bf_u)`. -/
def classicDensity (kB T Fcal : Float) (g E A : Vec) (u : Nat) (I : Float) : Float :=
  I * partitionFunction kB T g E / (Fcal * A[u]! * g[u]! * boltzmannFactor kB T E[u]!)

/-- Mirror of `CflibsFormal.composition`: `n_s / Σ_t n_t`. -/
def composition (n : Vec) (s : Nat) : Float := n[s]! / n.foldl (· + ·) 0.0

/-! ## Minimal JSON emission -/

/-- Fixed-point rendering with 9 decimal places via a scaled integer. Lean's `Float.toString`
is hard-wired to 6 decimals (and underflows small magnitudes to `0.000000`), so we roll our
own. Assumes `|x|` is O(1) (all oracle values are dimensionless and `≤ ~10`), keeping
`|x|·1e9` well inside the exact-integer range of `Float`. Gives ~9 significant figures for
O(1) values — ample for a formula-correctness regression oracle (tolerance ~1e-6). -/
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

/-! ## Scenarios (physically-scaled but synthetic atomic data; swap in NIST values freely —
the oracle tests the FORMULAS and INVARIANTS, not the atomic data). -/

/-- A single-species emitter: shared atomic-data family `(g, E, A)` over its levels. -/
structure Species where
  g : Vec
  E : Vec       -- upper-level energies (eV)
  A : Vec       -- Einstein A (s⁻¹)
  N : Float     -- true number density (cm⁻³)
  u : Nat       -- chosen designated line index
  deriving Inhabited

-- DIMENSIONLESS constants (the spec is dimensionless — see CONTEXT.md). `E` is in units of
-- `kB·T`, so `kB = T = 1`; `Fcal = 1`. The pipeline must be fed THESE exact inputs; values are
-- kept O(1) so the 9-decimal formatter is lossless. (Atomic data is synthetic — the oracle
-- tests the FORMULAS and INVARIANTS, not the atomic data; swap in NIST values + your units.)
def kB : Float := 1.0
def T  : Float := 1.0
def Fcal : Float := 1.0

/-- Shared 4-level atomic-data family used across the scenario species (single-family case,
matching `MultiSpecies`). -/
def g0 : Vec := #[1.0, 2.0, 3.0, 4.0]
def E0 : Vec := #[0.0, 1.0, 2.0, 3.0]
def A0 : Vec := #[1.0, 0.8, 0.6, 0.4]

/-- Two species with true densities 1 and 3 ⇒ true composition [0.25, 0.75]. -/
def speciesList : Array Species :=
  #[{ g := g0, E := E0, A := A0, N := 1.0, u := 0 },
    { g := g0, E := E0, A := A0, N := 3.0, u := 1 }]

/-- Forward intensities of every line of a species. -/
def forwardLines (s : Species) : Vec :=
  (Array.range s.g.size).map (fun k => lineIntensity kB T s.N Fcal s.g s.E s.A k)

/-- Classic-recovered density for a species, from its designated-line forward intensity. -/
def recoveredDensity (s : Species) : Float :=
  let I := lineIntensity kB T s.N Fcal s.g s.E s.A s.u
  classicDensity kB T Fcal s.g s.E s.A s.u I

/-- classicComposition over the species: recover each density, then close. -/
def recoveredComposition (cFac : Float) : Vec :=
  let dens : Vec := speciesList.map (fun s =>
    let I := lineIntensity kB T s.N (cFac * Fcal) s.g s.E s.A s.u
    classicDensity kB T (cFac * Fcal) s.g s.E s.A s.u I)
  (Array.range speciesList.size).map (fun i => composition dens i)

def trueComposition : Vec :=
  let N : Vec := speciesList.map (·.N)
  (Array.range N.size).map (fun i => composition N i)

def jArrayOf (xs : Array String) : String := "[" ++ String.intercalate ", " xs.toList ++ "]"

/-- One species' forward record: true density, designated line, and all line intensities. -/
def jSpecies (s : Species) : String :=
  "{" ++ jField "N" (jNum s.N) ++ ", " ++ jField "u" (toString s.u)
    ++ ", " ++ jField "intensities" (jVec (forwardLines s)) ++ "}"

/-- Emit the fixtures as a JSON document. -/
def render : String :=
  let header := jField "_about" (jStr ("Numerical regression fixtures for CF-LIBS-improved, " ++
    "generated by the Float mirror of the verified CflibsFormal spec (oracle/Generate.lean). " ++
    "Each check instantiates a PROVEN theorem; see oracle/README.md. Dimensionless inputs; " ++
    "tolerance ~1e-6."))
  let consts := "{" ++ jField "kB" (jNum kB) ++ ", " ++ jField "T" (jNum T) ++ ", "
    ++ jField "Fcal" (jNum Fcal) ++ ", " ++ jField "g" (jVec g0) ++ ", "
    ++ jField "E" (jVec E0) ++ ", " ++ jField "A" (jVec A0) ++ "}"
  let species := jArrayOf (speciesList.map jSpecies)
  let recDen := jVec (speciesList.map recoveredDensity)
  let trueDen := jVec (speciesList.map (·.N))
  let comp := jVec (recoveredComposition 1.0)
  let compScaled := jVec (recoveredComposition 1000.0)  -- calibration-free: scale Fcal by 1000
  let fwd := "{" ++ jField "theorem" (jStr "CflibsFormal.lineIntensity (def) / boltzmann_plot_intensity")
    ++ ", " ++ jField "must" (jStr "recompute lineIntensity(constants, species.N, k) == species.intensities[k]") ++ "}"
  let rt := "{" ++ jField "theorem" (jStr "Classic.classicDensity_recovers / classic_sound")
    ++ ", " ++ jField "true_densities" trueDen ++ ", " ++ jField "recovered_densities" recDen
    ++ ", " ++ jField "must" (jStr "classicDensity(lineIntensity(N)) == N (exact in R; within tol in Float)") ++ "}"
  let cl := "{" ++ jField "theorem" (jStr "Closure.composition_sum_one / classic_sound")
    ++ ", " ++ jField "true_composition" (jVec trueComposition) ++ ", " ++ jField "recovered_composition" comp
    ++ ", " ++ jField "must" (jStr "recovered == true AND sum(recovered) == 1") ++ "}"
  let cf := "{" ++ jField "theorem" (jStr "Classic.classic_calibration_free")
    ++ ", " ++ jField "Fcal_scale" (jNum 1000.0) ++ ", " ++ jField "composition_base" comp
    ++ ", " ++ jField "composition_scaled" compScaled
    ++ ", " ++ jField "must" (jStr "composition_scaled == composition_base (Fcal cancels)") ++ "}"
  let checks := "{" ++ jField "forward" fwd ++ ", " ++ jField "round_trip" rt ++ ", "
    ++ jField "closure" cl ++ ", " ++ jField "calibration_free" cf ++ "}"
  "{\n  " ++ header ++ ",\n  " ++ jField "constants" consts ++ ",\n  "
    ++ jField "species" species ++ ",\n  " ++ jField "checks" checks ++ "\n}"

def main : IO Unit := IO.println render

end Oracle

def main : IO Unit := Oracle.main
