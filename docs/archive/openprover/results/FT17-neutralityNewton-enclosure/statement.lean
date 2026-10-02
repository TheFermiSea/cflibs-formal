import Mathlib
import CflibsFormal.SahaEquilibrium

/-!
# FT-17 (enclosure): one Newton step brackets the charge-neutrality root

Staged queue target, 2026-09-24 audit, frontier FT-17 (reopens Frontier 03 M8, Newton).
The definition `neutralityNewton` is shared verbatim with the sibling target
`neutralityNewton_tendsto`.
-/

open Finset CflibsFormal

namespace Plan.FT17

variable {ι : Type*} [Fintype ι]

/-- **Newton map for multi-element charge neutrality.**
At fixed temperature, species `s` has Saha factor `S s = n_e · N_II / N_I > 0` and elemental
density `Ntot s ≥ 0` (one common density unit for `S`, `Ntot` and the electron density `x`). In the
two-stage model it contributes the ionized density `Ntot s * S s / (x + S s)`, and charge
neutrality is the fixed point `x = G x` of `G := multiElementIonized S Ntot`
(`SahaEquilibrium.lean`). This map is Newton's method on the residual `f x = x - G x`, whose
derivative is `f' x = 1 + ∑ s, Ntot s * S s / (x + S s) ^ 2`: `neutralityNewton S Ntot x =
x - f x / f' x`. It is meant for `x ≥ 0`, where every denominator is positive and `f' x ≥ 1`
(given `Ntot ≥ 0`); off that half-line the formula is not a Newton step. -/
noncomputable def neutralityNewton (S Ntot : ι → ℝ) (x : ℝ) : ℝ :=
  x - (x - multiElementIonized S Ntot x) / (1 + ∑ s, Ntot s * S s / (x + S s) ^ 2)

/-- **One Newton step brackets the charge-neutrality root from both sides.**
Let `G := multiElementIonized S Ntot` and let `r ≥ 0` be a charge-neutrality root, `r = G r`.
From ANY electron-density guess `x ≥ 0`, the Newton iterate `N x := neutralityNewton S Ntot x`
satisfies `N x ≤ r ≤ G (N x)`. Both ends of the bracket `[N x, G (N x)]` are computable from `x`
alone, so one step certifies an interval containing the root without knowing `r`.

Proof idea (not part of the statement): the exact error identity
`N x - r = -(x - r) ^ 2 * (∑ s, Ntot s * S s / ((x + S s) ^ 2 * (r + S s))) / f' x ≤ 0`
gives `N x ≤ r` with no convexity argument; `N x = (x * D + G x) / (1 + D) ≥ 0` with
`D = ∑ s, Ntot s * S s / (x + S s) ^ 2`; and `G` is antitone on `[0, ∞)` when `Ntot ≥ 0`, so
`G (N x) ≥ G r = r`.

Hypotheses. `hS` (`S s > 0`, the sign of a Saha factor) keeps every denominator `x + S s`,
`r + S s` positive. `hN` (`Ntot s ≥ 0`; absent species allowed) makes `G` antitone and `f' ≥ 1`.
`hx` restricts the guess to the physical half-line. `hr` selects the physical root: for one
species with `S = Ntot = 1`, `r = G r` also has the root `r = -(1 + √5) / 2`, and there
`N 0 = 1 / 2 > r`, so the bracket fails. `hfix` is charge neutrality at `r`. No `Nonempty ι` is
needed: with no species, or all `Ntot s = 0`, `G ≡ 0`, `r = 0` and `N x = 0`. Existence of a
root is a separate result (`multiElement_exists_pos_fixedPoint`, for `Ntot > 0`).

Scope, two-axis prediction (owner rule 2026-09-24): relation tag PURE-MATH (a numerical-analysis
fact about the Newton map of the given closure map); model tag of `multiElementIonized`: REDUCED
(fixed `T`, LTE, two stages per element; Z-stage cascades are not covered). Published tag: the
weaker of the two, REDUCED (the EXACT-semantics decision RF-27 is still pending). This is the
forward charge-neutrality closure, not the inverse (T, n_e) loop. Physics: Saha–Eggert (Griem);
the Saha–closure–neutrality coupling as in Yalcin 1999. -/
theorem neutralityNewton_enclosure {S Ntot : ι → ℝ} {x r : ℝ} (hS : ∀ s, 0 < S s)
    (hN : ∀ s, 0 ≤ Ntot s) (hx : 0 ≤ x) (hr : 0 ≤ r)
    (hfix : r = multiElementIonized S Ntot r) :
    neutralityNewton S Ntot x ≤ r ∧
      r ≤ multiElementIonized S Ntot (neutralityNewton S Ntot x) := by
  sorry

end Plan.FT17
