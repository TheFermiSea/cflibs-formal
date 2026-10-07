import Mathlib
import CflibsFormal.EscapeFactor

/-!
# FT-13 (profile-generic): the log escape factor is antitone and 1/2-Lipschitz in the depth

Staged queue target, 2026-10-07, card `ft13.escape-factor-slab-bound`, open item "The
profile-generic escapeFactor Lipschitz lemma proposed for FT-13 is not landed." The repository
(83a6da0) has no `escapeFactor` definition: `EscapeFactor.lean` describes the
profile-integrated escape factor `W/(τ₀ ∫ψ)` only in prose. This file therefore defines it
(`Plan.FT13.escapeFactor`, the definition proposed by the 2026-09-24 audit, REPORT.md FT-13)
and states the bound for it.
-/

open CflibsFormal MeasureTheory

namespace Plan.FT13

/-- **Profile-integrated escape factor.** `escapeFactor ψ τ = W(ψ, τ) / (τ · ∫ψ)`: the
equivalent width (`equivWidth`, the self-absorbed integrated line strength) divided by its
optically thin value `τ ∫ψ`. For the rectangular profile on `[0, 1]` it is the flat-slab factor
`(1 − exp(−τ))/τ` (`equivWidth_rectangular`). Defined here because the repository has none. -/
noncomputable def escapeFactor (ψ : ℝ → ℝ) (τ : ℝ) : ℝ :=
  equivWidth ψ τ / (τ * ∫ x, ψ x)

/-- **The log escape factor of any peak-normalized profile is antitone and 1/2-Lipschitz in the
depth (PURE-MATH).** For a profile `ψ` with `0 ≤ ψ ≤ 1`, integrable, of positive area, and
depths `0 < τ ≤ τ'`,
`0 ≤ log (escapeFactor ψ τ) − log (escapeFactor ψ τ') ≤ (τ' − τ)/2`.
In particular `|log E(τ) − log E(τ')| ≤ |τ − τ'|/2` for all `τ, τ' > 0`.

Reading: a deeper line escapes a smaller fraction, and an error `Δ` in the line-centre depth
`τ` moves the log of the profile-integrated escape correction by at most `Δ/2`, for every
profile shape with `ψ ≤ 1`, not only the flat slab. The constant `1/2` cannot be lowered: for
the rectangular profile `E = SA` and `d/dτ log SA(τ) → −1/2` as `τ → 0⁺` (context; not part of
this statement).

Hypotheses.
* `hψ0 : 0 ≤ ψ` and `hint`: the standing hypotheses of `EquivalentWidth`; they make
  `equivWidth` the integral of a nonnegative integrable function and keep every pointwise depth
  `τ ψ x` in `[0, τ]`. `hψ0` is not claimed to be logically necessary.
* `hψ1 : ∀ x, ψ x ≤ 1`: load-bearing for the constant. Pointwise the depth is `τ ψ x ≤ τ`; for
  `ψ = 2` on `[0, 1]` one gets `E(τ) = SA(2τ)`, whose log has slope near `−1` at small `τ`
  (with `τ = 0.01, τ' = 0.02` the difference is `≈ 0.00995 > 0.005`).
* `hpos : 0 < ∫ ψ`: makes `escapeFactor` a genuine quotient. It is not logically necessary:
  for zero area Lean's `x / 0 = 0` gives `escapeFactor = 0` and the conclusion reads
  `0 ≤ 0 ∧ 0 ≤ (τ' − τ)/2`, true for a junk reason. (`hint` is implied by `hpos`; it is kept
  for parity with `escape_ge_slab`.)
* `hτ : 0 < τ` (hence `τ' > 0`): the physical domain, where `escapeFactor` is a genuine
  quotient. At `τ = 0` the definition is a `0 / 0` junk value.

Scope: PURE-MATH (a property of the defined functions). It does not say which profile a line
has, models no inhomogeneity along the line of sight, and assumes the depth error `Δ` rather
than measuring it. -/
theorem log_escapeFactor_antitone_lipschitz {ψ : ℝ → ℝ} {τ τ' : ℝ} (hψ0 : 0 ≤ ψ)
    (hψ1 : ∀ x, ψ x ≤ 1) (hint : Integrable ψ) (hpos : 0 < ∫ x, ψ x) (hτ : 0 < τ)
    (hττ' : τ ≤ τ') :
    0 ≤ Real.log (escapeFactor ψ τ) - Real.log (escapeFactor ψ τ') ∧
      Real.log (escapeFactor ψ τ) - Real.log (escapeFactor ψ τ') ≤ (τ' - τ) / 2 := by
  sorry

end Plan.FT13
