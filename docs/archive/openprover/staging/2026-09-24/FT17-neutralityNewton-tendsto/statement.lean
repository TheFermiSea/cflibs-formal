import Mathlib
import CflibsFormal.SahaEquilibrium

/-!
# FT-17 (convergence): Newton's method on charge neutrality converges from every `x0 ≥ 0`

Staged queue target, 2026-09-24 audit, frontier FT-17 (reopens Frontier 03 M8, Newton).
The definition `neutralityNewton` is shared verbatim with the sibling target
`neutralityNewton_enclosure`.
-/

open Finset CflibsFormal Filter Topology

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

/-- **Newton's method on multi-element charge neutrality converges from every start `x0 ≥ 0`.**
Let `G := multiElementIonized S Ntot` and let `r ≥ 0` be a charge-neutrality root, `r = G r`.
Then the Newton iterates `(neutralityNewton S Ntot)^[n] x0` converge to `r` for every
electron-density guess `x0 ≥ 0`. No damping and no closeness-to-the-root condition are needed.
Unlike the direct substitution `x ↦ G x` (antitone, so it oscillates) the Newton orbit is
one-sided: after the first step it rises monotonically to `r`.

Proof idea (not part of the statement): one step from any `x ≥ 0` lands in `[0, r]` (the exact
error identity `N x - r = -(x - r) ^ 2 * (∑ s, Ntot s * S s / ((x + S s) ^ 2 * (r + S s))) / f' x`
and `N x = (x * D + G x) / (1 + D)`); for `x ∈ [0, r]`, `N x - x = (G x - x) / f' x ≥ 0` because
`G x ≥ G r = r ≥ x`, and `N x ≤ r` again; the bounded monotone orbit has a limit `L ∈ [0, r]`;
continuity of `N` on `[0, ∞)` gives `N L = L`, so `G L = L`; then `L ≤ r ≤ G L = L` since `G` is
antitone. The statement asserts convergence only: it claims no rate (the quadratic bound
`|N x - r| ≤ (∑ s, Ntot s / S s ^ 2) * (x - r) ^ 2` is a separate result).

Hypotheses. `hS` (`S s > 0`) keeps every denominator positive on `[0, ∞)`. `hN` (`Ntot s ≥ 0`;
absent species allowed) makes `G` antitone and `f' ≥ 1`. `hr` selects the physical root (for one
species with `S = Ntot = 1`, `r = G r` also has the root `-(1 + √5) / 2`, which a nonnegative
orbit cannot approach). `hfix` is charge neutrality at `r`. `hx0` restricts the start to the
physical half-line. No `Nonempty ι` is needed (with no species `N ≡ 0` and `r = 0`). Existence
of a root is a separate result (`multiElement_exists_pos_fixedPoint`, for `Ntot > 0`).

Scope, two-axis prediction (owner rule 2026-09-24): relation tag PURE-MATH (convergence of a
numerical method for the given closure map); model tag of `multiElementIonized`: REDUCED (fixed
`T`, LTE, two stages per element; Z-stage cascades are not covered). Published tag: the weaker,
REDUCED (RF-27 pending). Forward closure only, not the inverse (T, n_e) loop. Physics:
Saha–Eggert (Griem); the Saha–closure–neutrality coupling as in Yalcin 1999. -/
theorem neutralityNewton_tendsto {S Ntot : ι → ℝ} {r x0 : ℝ} (hS : ∀ s, 0 < S s)
    (hN : ∀ s, 0 ≤ Ntot s) (hr : 0 ≤ r) (hfix : r = multiElementIonized S Ntot r)
    (hx0 : 0 ≤ x0) :
    Tendsto (fun n => (neutralityNewton S Ntot)^[n] x0) atTop (𝓝 r) := by
  sorry

end Plan.FT17
