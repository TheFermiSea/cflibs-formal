# FT08-ratioEstimate-hasDerivAt: β-derivative of the two-stage ratio-mode log-ratio

Planning dossier (2026-09-24 audit, frontier FT-08 (b), decomposition step 3, chain rule), in
the total-derivative form the audit revision requires (`HasDerivAt lnNe` an explicit input).
Every name below was `#check`ed against lean-main (Mathlib v4.33.1). **Already proved in
scratch** (6 lines, axiom-clean): `_hand-land/FT08-ratioEstimate-hasDerivAt.proof.lean`.

## 1. Goal

```lean
import Mathlib
namespace Plan.FT08
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
  sorry
```

No repo definitions. Physics: `N_tot = n_I (1 + S/n_e)` (neutral line, `ε = 1`) or
`n_II (1 + n_e/S)` (ion line, `ε = -1`); `S/n_e = exp (lnS - lnNe)`. Fixed `n_e` is the instance
`lnNe := fun _ => Real.log ne`, `dNe := 0`. `L0 = log (I_a g_b A_b / (I_b g_a A_a))`.

## 2. Mathlib lemmas (checked)

`HasDerivAt.fun_sub`, `HasDerivAt.fun_add` (lambda forms), `HasDerivAt.const_mul`,
`HasDerivAt.mul_const`, `HasDerivAt.const_add`, `HasDerivAt.exp`
(`→ HasDerivAt (fun x => exp (f x)) (exp (f x) * f') x`), `HasDerivAt.log`
(`HasDerivAt f f' x → f x ≠ 0 → HasDerivAt (fun y => log (f y)) (f' / f x) x`),
`hasDerivAt_id'`, `HasDerivAt.congr_deriv`.

## 3. Proof route and pitfalls

Build `hA := (((hSa.fun_sub hNe).const_mul εa).exp.const_add 1).log (by positivity)`, same for
`hB`; combine with `((hasDerivAt_id' β).mul_const (Ea - Eb)).const_add L0`, `hUa.fun_sub hUb`
by `fun_add`/`fun_sub`; close with `refine h0.congr_deriv ?_; ring`.
Pitfall: `HasDerivAt.sub` produces the Pi form `(lnSa - lnNe)`; `convert ... using 1` then
generates instance goals (`Real.instAddCommGroup = ...`). Use the `fun_` variants and
`congr_deriv`.

## 4. Witness

All five functions constant `0` with all derivatives `0` (`hasDerivAt_const`): hypotheses hold.
Physical instance: `lnSX = log sahaFactor` in `β` (sibling target
FT08-log-sahaFactor-hasDerivAt-beta), `lnUX = log partitionFunction` in `β` (decomposition step
4; not staged or verified anywhere yet, checked FT-15 staging and results/).

## 5. Scope

REDUCED (LTE, single `T`, two ionization stages, literal-sum `U`, one line per element). The
theorem itself is the chain rule; the audited coefficient
`(Ea - ⟨E⟩_IA) - (Eb - ⟨E⟩_IB) - fA κA + fB κB` needs the step-4 and step-5 lemmas.
Literature: Aguilera & Aragón 2007 (cross-stage Saha-Boltzmann ratios), Griem 1997 (Saha).
