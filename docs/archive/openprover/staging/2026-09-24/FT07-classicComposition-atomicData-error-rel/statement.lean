import Mathlib
import CflibsFormal.AtomicDataPerturbation

/-!
# Queue target FT07-classicComposition-atomicData-error-rel (deep audit 2026-09-24, FT-07 item 5)

Abundance-scaled (relative) closure bound for the classic CF-LIBS reader under per-species
relative atomic-data (response-factor) error. Statement file for the proof queue: one target
theorem, one `sorry`.
-/

open Finset CflibsFormal

namespace Plan.FT07

variable {ι : Type*} [Fintype ι] {κ : Type*} [Fintype κ]

/-- **Relative closure bound for the classic reader under atomic-data error.** Each species `s`
is emitted with the TRUE atomic data `(g s, E s, A s)` at density `N s` (common calibration
`Fcal`, temperature `T` known to the reader) and read off its chosen line `u s` with the WRONG
data `(g' s, E' s, A' s)` (`recoveredDensity`). If every species' response factor
`ρ = g_u·A_u·exp(−E_u/(kB T))/U(T)` is off by at most a relative `δ`, `0 ≤ δ < 1` (`hpert`),
then every recovered number fraction obeys
  `|Ĉ_s − C_s| ≤ (2δ/(1 − δ)) · C_s`,
an error that scales with the true fraction `C_s`. The absolute twin
`classicComposition_atomicData_error` bounds the same error by `compositionErrorBound` with a
density cap `Nmax`, a bound whose leading term `Nmax·δ/((1 − δ)·Ŝ)` does not shrink with `C_s`,
so it is uninformative for minor elements. Example: `δ = 0.05` gives `2δ/(1 − δ) = 2/19 ≈ 0.105`,
so a species with `C_s = 0.005` is recovered within `≈ 5.26·10⁻⁴`.

Route: the EXACT aliasing identity `classicDensity_aliasing` gives `N̂_t = N_t·ρ_t/ρ'_t`, and
`hpert` gives `(1 − δ)·ρ_t ≤ ρ'_t ≤ (1 + δ)·ρ_t`, so `(1 − δ)·N̂_t ≤ N_t ≤ (1 + δ)·N̂_t` for every
species; closure then puts `Ĉ_s/C_s` in `[(1 − δ)/(1 + δ), (1 + δ)/(1 − δ)]`, whose larger
deviation from `1` is `2δ/(1 − δ)`. The constant is approached (numerical check, not
Lean-checked) when species `s` is read high by `1/(1 − δ)`, every other species low by
`1/(1 + δ)`, and the others' share tends to `1`. Routing instead through the additive envelope
`|N̂_t − N_t| ≤ N_t·δ/(1 − δ)` (`classicDensity_aliasing_error`) discards the multiplicative
structure and gives only `2δ/(1 − 2δ)` on `δ < 1/2`, which this statement dominates.

Hypotheses: `hg`, `hg'` (positive degeneracies: both partition functions are positive and
cancel); `hFcal` (the calibration cancels); `hA'` (positive analyst's chosen-line Einstein
coefficient; `A'` divides in the reader); `hA` (positive true chosen-line coefficient; implied by
`hg`, `hg'`, `hA'`, `hδ0` and `hpert`, Lean-checked in the statement-audit scratch, and kept as
the physical guard, as in the absolute twin); `hN` (positive true densities: the bound is
relative to them and the totals must be positive); `hδ0`; `hδ1 : δ < 1` (the absolute twin's
domain; necessary, by hand and not Lean-checked: at `δ ≥ 1` the analyst's response factor can
approach `0` and `Ĉ_s/C_s` is unbounded); `hpert` (the lumped per-species relative response
error: the per-symbol errors in `g`, `A`, `E`, `U` are collapsed into one scalar `δ`, an assumed
input).

Scope (two-axis): relation REDUCED (lumped uniform relative response error `δ`, classic reader at
known `T`; the algebra itself is exact); definitions used: `lineIntensity` REDUCED (optically thin
LTE forward map), `Classic.classicDensity` / `recoveredDensity` (estimator packaging),
`composition` PURE-MATH; published REDUCED. Citation: Tognoni 2010 (as for the absolute twin). -/
theorem classicComposition_atomicData_error_rel [Nonempty ι] [Nonempty κ]
    {kB T Fcal δ : ℝ} {N : κ → ℝ} {g E A g' E' A' : κ → ι → ℝ} {u : κ → ι}
    (hg : ∀ s k, 0 < g s k) (hg' : ∀ s k, 0 < g' s k) (hFcal : 0 < Fcal)
    (hA : ∀ s, 0 < A s (u s)) (hA' : ∀ s, 0 < A' s (u s))
    (hN : ∀ s, 0 < N s) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hpert : ∀ s, |responseFactor kB T (g' s) (E' s) (A' s) (u s)
                    - responseFactor kB T (g s) (E s) (A s) (u s)|
                  ≤ δ * responseFactor kB T (g s) (E s) (A s) (u s))
    (s : κ) :
    |composition (recoveredDensity kB T Fcal g E A g' E' A' u N) s - composition N s|
      ≤ (2 * δ / (1 - δ)) * composition N s := by
  sorry

end Plan.FT07
