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
* `log_ratioEstimate_lipschitz_box` — the two-point bound `|Δ β1 − Δ β2| ≤ L · |β1 − β2|` on a
  `β`-box where the whole derivative coefficient is bounded by `L` (mean-value theorem); bounding
  the coefficient as a whole keeps the cancellation between the two stage-fraction terms.

The statements are pure calculus on abstract functions; the physics (LTE, a single temperature,
two stages, a literal-sum partition function, one line per element) is only the reading of the
symbols. No value of `L` for physical partition functions and Saha factors is proved here.

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

/-- **Two-point `β`-box bound for the ratio-mode log-ratio (FT-08 (c)).** Let
`Δ(b) = L0 + b (Ea - Eb) + (lnUa b - lnUb b) + log (1 + exp (εa (lnSa b - lnNe b)))
- log (1 + exp (εb (lnSb b - lnNe b)))` (the function of `ratioEstimate_hasDerivAt`). If on the
box `[βmin, βmax]` the five inputs have derivatives `dUa b, …, dNe b` at every point, and the
derivative of `Δ` (the coefficient of `ratioEstimate_hasDerivAt`, written out in `hL`) is bounded
by `L` in absolute value on the box, then for any two `β1, β2` in the box
  `|Δ β1 - Δ β2| ≤ L · |β1 - β2|`.

Reading: `Δ` is the log of the estimated density ratio `N̂_A / N̂_B` at assumed inverse
temperature `b = 1/(k_B T̂)` (see `ratioEstimate_hasDerivAt` for the symbols: `EX` upper-level
energies, `UX` stage partition functions, `SX` Saha factors, `n_e = exp lnNe`, `εX = ±1` for a
neutral / ion line). `L` bounds the whole coefficient
`(Ea - Eb) + (dUa - dUb) + fa εa (dSa - dNe) - fb εb (dSb - dNe)`, where the stage fractions
`fX = exp xX / (1 + exp xX)` lie in `(0, 1)`. Bounding the coefficient as a whole keeps the
cancellation between the two stage-fraction terms that FT-08 (b) relies on (two elements that
ionize alike give a small coefficient even when each term is large); splitting it by the
triangle inequality, `|Ea - Eb| + MU + |εa| MSa + |εb| MSb` with `MU`, `MSa`, `MSb` box bounds
on the slope differences, gives a valid `L` (a corollary, not stated here) but loses that
cancellation (audit 2026-10-06). So a
temperature error `|β̂ - β|` moves the reported log-ratio by at most `L` times it.

Hypotheses and why each is present:
* `hβ1`, `hβ2`: both points lie in the box, where `hL` holds (the box is convex, so the segment
  between them does too).
* `hUa … hNe`: differentiability of the five inputs at every point of the box (needed for the
  mean-value theorem; `HasDerivAt` at the closed endpoints, as for smooth physical `U`, `S`).
* `hL`: the box bound on the derivative of `Δ`.
No positivity hypothesis is needed: `1 + exp x > 0`. `L ≥ 0` follows from `hL` when the box is
nonempty and is not assumed. Not vacuous: with constant `lnU`, `lnS`, `lnNe` (all slopes `0`)
the coefficient is `Ea - Eb`, `Δ` is affine with that slope, and the bound holds with equality
at `L = |Ea - Eb|`.

Scope: PURE-MATH (mean-value theorem on abstract functions; no repository physics definition is
used). The physics reading (LTE, single `T`, two ionization stages, literal-sum `U`, one line per
element) is REDUCED and is not part of the statement; a value of `L` for the physical `U` and
`S` is not supplied here. Literature: Aguilera & Aragón 2007 (multi-element Saha–Boltzmann
cross-stage ratios); Griem 1997 (Saha). -/
theorem log_ratioEstimate_lipschitz_box {lnUa lnUb lnSa lnSb lnNe dUa dUb dSa dSb dNe : ℝ → ℝ}
    {L0 Ea Eb εa εb βmin βmax β1 β2 L : ℝ}
    (hβ1 : β1 ∈ Set.Icc βmin βmax) (hβ2 : β2 ∈ Set.Icc βmin βmax)
    (hUa : ∀ b ∈ Set.Icc βmin βmax, HasDerivAt lnUa (dUa b) b)
    (hUb : ∀ b ∈ Set.Icc βmin βmax, HasDerivAt lnUb (dUb b) b)
    (hSa : ∀ b ∈ Set.Icc βmin βmax, HasDerivAt lnSa (dSa b) b)
    (hSb : ∀ b ∈ Set.Icc βmin βmax, HasDerivAt lnSb (dSb b) b)
    (hNe : ∀ b ∈ Set.Icc βmin βmax, HasDerivAt lnNe (dNe b) b)
    (hL : ∀ b ∈ Set.Icc βmin βmax,
      |(Ea - Eb) + (dUa b - dUb b)
        + Real.exp (εa * (lnSa b - lnNe b)) / (1 + Real.exp (εa * (lnSa b - lnNe b)))
            * (εa * (dSa b - dNe b))
        - Real.exp (εb * (lnSb b - lnNe b)) / (1 + Real.exp (εb * (lnSb b - lnNe b)))
            * (εb * (dSb b - dNe b))| ≤ L) :
    |(L0 + β1 * (Ea - Eb) + (lnUa β1 - lnUb β1)
        + Real.log (1 + Real.exp (εa * (lnSa β1 - lnNe β1)))
        - Real.log (1 + Real.exp (εb * (lnSb β1 - lnNe β1))))
      - (L0 + β2 * (Ea - Eb) + (lnUa β2 - lnUb β2)
        + Real.log (1 + Real.exp (εa * (lnSa β2 - lnNe β2)))
        - Real.log (1 + Real.exp (εb * (lnSb β2 - lnNe β2))))|
      ≤ L * |β1 - β2| := by
  set f : ℝ → ℝ := fun b => L0 + b * (Ea - Eb) + (lnUa b - lnUb b)
    + Real.log (1 + Real.exp (εa * (lnSa b - lnNe b)))
    - Real.log (1 + Real.exp (εb * (lnSb b - lnNe b)))
  set f' : ℝ → ℝ := fun b => (Ea - Eb) + (dUa b - dUb b)
    + Real.exp (εa * (lnSa b - lnNe b)) / (1 + Real.exp (εa * (lnSa b - lnNe b)))
        * (εa * (dSa b - dNe b))
    - Real.exp (εb * (lnSb b - lnNe b)) / (1 + Real.exp (εb * (lnSb b - lnNe b)))
        * (εb * (dSb b - dNe b))
  have hderiv : ∀ b ∈ Set.Icc βmin βmax, HasDerivWithinAt f (f' b) (Set.Icc βmin βmax) b := by
    intro b hb
    have h := ratioEstimate_hasDerivAt (L0 := L0) (Ea := Ea) (Eb := Eb) (εa := εa) (εb := εb)
      (hUa b hb) (hUb b hb) (hSa b hb) (hSb b hb) (hNe b hb)
    convert h.hasDerivWithinAt using 1
  have key := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := f)
    (f' := f')
    (C := L)
    hderiv
    (fun x hx => by rw [Real.norm_eq_abs]; exact hL x hx)
    (convex_Icc βmin βmax) hβ2 hβ1
  simpa only [Real.norm_eq_abs, abs_sub_comm] using key

/-- Non-vacuity of `log_ratioEstimate_lipschitz_box`, at the matched-ionization instance where
the stage-fraction terms cancel: `lnSa = lnSb = id`, `lnNe = 0`, `εa = εb = 1`, `Ea = Eb = 0`,
constant `lnU`. The coefficient is `fa - fb = 0` on the box, so `L = 0` and the log-ratio is
constant in `β`, which the triangle-split constant (here `2`) would not show. -/
example (β1 β2 : ℝ) (hβ1 : β1 ∈ Set.Icc (0 : ℝ) 1) (hβ2 : β2 ∈ Set.Icc (0 : ℝ) 1) :
    |(0 + β1 * (0 - 0) + ((fun _ => (0 : ℝ)) β1 - (fun _ => (0 : ℝ)) β1)
        + Real.log (1 + Real.exp (1 * ((fun b => b) β1 - (fun _ => (0 : ℝ)) β1)))
        - Real.log (1 + Real.exp (1 * ((fun b => b) β1 - (fun _ => (0 : ℝ)) β1))))
      - (0 + β2 * (0 - 0) + ((fun _ => (0 : ℝ)) β2 - (fun _ => (0 : ℝ)) β2)
        + Real.log (1 + Real.exp (1 * ((fun b => b) β2 - (fun _ => (0 : ℝ)) β2)))
        - Real.log (1 + Real.exp (1 * ((fun b => b) β2 - (fun _ => (0 : ℝ)) β2))))|
      ≤ 0 * |β1 - β2| :=
  log_ratioEstimate_lipschitz_box (lnUa := fun _ => 0) (lnUb := fun _ => 0)
    (lnSa := fun b => b) (lnSb := fun b => b) (lnNe := fun _ => 0) (dUa := fun _ => 0)
    (dUb := fun _ => 0) (dSa := fun _ => 1) (dSb := fun _ => 1) (dNe := fun _ => 0) (L0 := 0)
    (Ea := 0) (Eb := 0) (εa := 1) (εb := 1) (L := 0) hβ1 hβ2
    (fun b _ => hasDerivAt_const b 0) (fun b _ => hasDerivAt_const b 0)
    (fun b _ => hasDerivAt_id' b) (fun b _ => hasDerivAt_id' b)
    (fun b _ => hasDerivAt_const b 0) (fun b _ => by simp)

end CflibsFormal
