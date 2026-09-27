/-
Copyright (c) 2026 Brian Squires. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Squires
-/
import Mathlib

/-!
# Ratio-mode sensitivity to the assumed temperature

In ratio mode, density ratios `N̂_A / N̂_B` between elements are reported instead of a
closed composition (`Closure.ratio_mode_normalization_invariant`: no common-mode normalization
changes a ratio). The ratio still depends on the assumed temperature. This module gives the exact
derivative of the log-ratio in the inverse temperature `β = 1/(k_B T̂)`, for one line per element
and two ionization stages, with the electron density allowed to depend on `β`.

## Main results

* `ratioEstimate_hasDerivAt` — the chain rule for
  `Δ(b) = L0 + b (Ea − Eb) + (ln Ua − ln Ub)(b) + log (1 + exp (εa (ln Sa − ln n_e)(b)))
  − log (1 + exp (εb (ln Sb − ln n_e)(b)))`, with the derivatives of `ln U`, `ln S` and `ln n_e`
  as abstract inputs. The fixed-`n_e` form is the instance with `d ln n_e/dβ = 0`.

The statement is pure calculus on abstract functions; the physics (LTE, a single temperature,
two stages, a literal-sum partition function, one line per element) is only the reading of the
symbols. No bound on the size of the sensitivity is proved here.

## Literature

J. A. Aguilera and C. Aragón, "Multi-element Saha–Boltzmann and Boltzmann plots in
laser-induced plasmas", *Spectrochimica Acta Part B* **62** (2007) 378 — cross-stage
Saha–Boltzmann ratios between elements; H. R. Griem, *Principles of Plasma Spectroscopy*,
Cambridge University Press (1997) — the Saha equation behind the two-stage totals.
-/

namespace CflibsFormal

/-- **Exact `β`-derivative of the two-stage ratio-mode log-ratio.** Let
`Δ(b) = L0 + b (Ea - Eb) + (lnUa b - lnUb b) + log (1 + exp (εa (lnSa b - lnNe b)))
- log (1 + exp (εb (lnSb b - lnNe b)))`. If `lnUa, lnUb, lnSa, lnSb, lnNe` have derivatives
`dUa, dUb, dSa, dSb, dNe` at `β`, then `Δ` has derivative
`(Ea - Eb) + (dUa - dUb) + fa · εa (dSa - dNe) - fb · εb (dSb - dNe)` at `β`, where
`fX = exp xX / (1 + exp xX)`, `xX = εX (lnSX β - lnNe β)`.

Reading: `Δ` is the log of the estimated density ratio `N̂_A / N̂_B` as a function of the assumed
inverse temperature `b = 1/(k_B T̂)`, for one line per element with upper energy `EX`, stage
partition function `UX`, Saha factor `SX` and two-stage totals. For a neutral line `εX = 1`
(`N_tot = n_I (1 + S/n_e)`, `fX` is the ionized fraction); for an ion line `εX = -1`
(`N_tot = n_II (1 + n_e/S)`, `fX` is the neutral fraction) and `UX` is the ion's partition
function. `L0` is the `β`-independent term `log (I_a g_b A_b / (I_b g_a A_a))`. The electron
density enters as `exp (lnNe β)` with `HasDerivAt lnNe dNe β` an explicit input, because on the
Saha–Boltzmann offset route `n_e` is itself `T`-coupled; the fixed-`n_e` form is
`lnNe := fun _ => Real.log ne`, `dNe := 0`. The theorem is only the chain rule; with
`d ln U/dβ = -⟨E⟩` and `d ln S/dβ = -κ` it yields the audited coefficient
`(Ea - ⟨E⟩_IA) - (Eb - ⟨E⟩_IB) - fA κA + fB κB` (neutral lines, fixed `n_e`).

No hypothesis beyond differentiability is needed: `1 + exp x > 0`.

Scope: PURE-MATH (the chain rule on abstract functions; FT-08 audit). The REDUCED physics
reading above (LTE, single `T`, two ionization stages, literal-sum `U`, one line per element) is
not part of the statement. Literature: Aguilera & Aragón 2007 (multi-element Saha–Boltzmann
cross-stage ratios); Griem 1997 (Saha). -/
theorem ratioEstimate_hasDerivAt {lnUa lnUb lnSa lnSb lnNe : ℝ → ℝ}
    {L0 Ea Eb εa εb β dUa dUb dSa dSb dNe : ℝ}
    (hUa : HasDerivAt lnUa dUa β) (hUb : HasDerivAt lnUb dUb β)
    (hSa : HasDerivAt lnSa dSa β) (hSb : HasDerivAt lnSb dSb β)
    (hNe : HasDerivAt lnNe dNe β) :
    HasDerivAt
      (fun b => L0 + b * (Ea - Eb) + (lnUa b - lnUb b)
        + Real.log (1 + Real.exp (εa * (lnSa b - lnNe b)))
        - Real.log (1 + Real.exp (εb * (lnSb b - lnNe b))))
      ((Ea - Eb) + (dUa - dUb)
        + Real.exp (εa * (lnSa β - lnNe β)) / (1 + Real.exp (εa * (lnSa β - lnNe β)))
            * (εa * (dSa - dNe))
        - Real.exp (εb * (lnSb β - lnNe β)) / (1 + Real.exp (εb * (lnSb β - lnNe β)))
            * (εb * (dSb - dNe))) β := by
  have hA := (((hSa.fun_sub hNe).const_mul εa).exp.const_add 1).log (by positivity)
  have hB := (((hSb.fun_sub hNe).const_mul εb).exp.const_add 1).log (by positivity)
  have h0 := (((((hasDerivAt_id' β).mul_const (Ea - Eb)).const_add L0).fun_add
    (hUa.fun_sub hUb)).fun_add hA).fun_sub hB
  refine h0.congr_deriv ?_
  ring

end CflibsFormal
