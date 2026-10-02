# FT08-log-sahaFactor-hasDerivAt-beta: d log S / dβ = -(χ + 3/(2β) + ⟨E⟩_II - ⟨E⟩_I)

Planning dossier (2026-09-24 audit, frontier FT-08 (b), decomposition step 5, grade B). Written
for a planner who cannot open the repository; every name below was `#check`ed against lean-main
(Mathlib v4.33.1). Decomposition step 4 (`d log U/dβ = -⟨E⟩`) is NOT staged or verified anywhere
(FT-15 staged only a Lipschitz bound and a monotonicity result), so it must be proved inline.

## 1. Goal

```lean
import Mathlib
import CflibsFormal.Saha
open CflibsFormal
namespace Plan.FT08
variable {ι κ : Type*} [Fintype ι] [Fintype κ]
noncomputable def meanExcitation (kB T : ℝ) (g E : ι → ℝ) : ℝ :=
  (∑ k, g k * E k * boltzmannFactor kB T (E k)) / partitionFunction kB T g E
theorem log_sahaFactor_hasDerivAt_beta [Nonempty ι] [Nonempty κ] {kB me h chi β : ℝ}
    {gZ EZ : ι → ℝ} {gZ1 EZ1 : κ → ℝ}
    (hkB : 0 < kB) (hβ : 0 < β) (hme : 0 < me) (hh : 0 < h)
    (hgZ : ∀ k, 0 < gZ k) (hgZ1 : ∀ k, 0 < gZ1 k) :
    HasDerivAt (fun b => Real.log (sahaFactor kB (1 / (kB * b)) me h chi gZ EZ gZ1 EZ1))
      (-(chi + 3 / (2 * β) + meanExcitation kB (1 / (kB * β)) gZ1 EZ1
          - meanExcitation kB (1 / (kB * β)) gZ EZ)) β := by
  sorry
```

`meanExcitation` is a local def (copied verbatim from the FT-15 targets); keep it verbatim.

## 2. Repo definitions and lemmas (namespace `CflibsFormal`)

```lean
noncomputable def boltzmannFactor (kB T E : ℝ) : ℝ := Real.exp (-E / (kB * T))
noncomputable def partitionFunction (kB T : ℝ) (g E : ι → ℝ) : ℝ :=
  ∑ k, g k * boltzmannFactor kB T (E k)
noncomputable def thermalBracket (kB T me h : ℝ) : ℝ :=
  (2 * Real.pi * me * kB * T) / h ^ 2
noncomputable def sahaFactor (kB T me h chi : ℝ) (gZ EZ : ι → ℝ) (gZ1 EZ1 : κ → ℝ) : ℝ :=
  2 * (partitionFunction kB T gZ1 EZ1 / partitionFunction kB T gZ EZ)
    * (thermalBracket kB T me h) ^ (3 / 2 : ℝ)
    * Real.exp (-chi / (kB * T))
lemma partitionFunction_pos [Nonempty ι] {kB T : ℝ} {g E : ι → ℝ}
    (hg : ∀ k, 0 < g k) : 0 < partitionFunction kB T g E
lemma thermalBracket_pos {kB T me h : ℝ}
    (hkB : 0 < kB) (hT : 0 < T) (hme : 0 < me) (hh : 0 < h) : 0 < thermalBracket kB T me h
theorem log_sahaFactor [Nonempty ι] [Nonempty κ] {kB T me h chi : ℝ}
    {gZ EZ : ι → ℝ} {gZ1 EZ1 : κ → ℝ}
    (hkB : 0 < kB) (hT : 0 < T) (hme : 0 < me) (hh : 0 < h)
    (hgZ : ∀ k, 0 < gZ k) (hgZ1 : ∀ k, 0 < gZ1 k) :
    Real.log (sahaFactor kB T me h chi gZ EZ gZ1 EZ1)
      = Real.log 2
        + (Real.log (partitionFunction kB T gZ1 EZ1)
            - Real.log (partitionFunction kB T gZ EZ))
        + (3 / 2 : ℝ) * Real.log (thermalBracket kB T me h)
        - chi / (kB * T)
```

Mathlib (checked): `HasDerivAt.congr_of_eventuallyEq` (`f₁ =ᶠ[nhds x] f`), `Ioi_mem_nhds`,
`Filter.eventually_of_mem`, `HasDerivAt.fun_sum` (lambda form of a finite sum), `HasDerivAt.log`,
`HasDerivAt.exp`, `HasDerivAt.const_mul`, `HasDerivAt.mul_const`, `HasDerivAt.const_add`,
`HasDerivAt.fun_add`, `HasDerivAt.fun_sub`, `hasDerivAt_id'`, `Real.hasDerivAt_log`
(`x ≠ 0 → HasDerivAt log x⁻¹ x`), `HasDerivAt.congr_deriv`, `Finset.sum_div`, `Finset.mul_sum`,
`Finset.sum_pos`; `HasDerivAt.rpow_const` exists but is not needed on this route.

## 3. Proof route

1. For `b > 0` put `T = 1/(kB b) > 0` and apply `log_sahaFactor`. Simplify with `kB ≠ 0`,
   `b ≠ 0`: `-E/(kB * (1/(kB b))) = -E * b`, `chi/(kB * T) = chi * b`,
   `thermalBracket kB T me h = c / b` with `c = 2π me / h² > 0`, so
   `log (thermalBracket ..) = log c - log b`.
2. Hence `log S =ᶠ[nhds β] F` with `F b = log 2 + (log (∑ k, gZ1 k * exp (-EZ1 k * b))
   - log (∑ k, gZ k * exp (-EZ k * b))) + 3/2 * (log c - log b) - chi * b`
   (use `Filter.eventually_of_mem (Ioi_mem_nhds hβ)`).
3. Differentiate `F`: each sum by `HasDerivAt.fun_sum` of
   `((hasDerivAt_id' β).const_mul (-E k)).exp.const_mul (g k)` (or `mul_const` form), then
   `.log` with the sum `> 0`; `log b` by `Real.hasDerivAt_log hβ.ne'`.
4. Identify: `meanExcitation kB (1/(kB β)) g E = (∑ g E exp(-E β)) / (∑ g exp(-E β))` by the
   same exponent rewrite under `Finset.sum_congr`; `d log U/dβ = -⟨E⟩`. Close with
   `congr_deriv` and `field_simp`/`ring` (`Finset.sum_div`, `Finset.sum_neg_distrib`).

Pitfalls: `log_sahaFactor` is only valid for `T > 0`, so use eventual equality, not a global
`funext`. `simp` turns `1 / x` into `x⁻¹`; keep one normal form. Do not differentiate the rpow
directly; the log identity has removed it. `HasDerivAt.sub` gives Pi forms; prefer `fun_`
variants.

## 4. Witness

`ι = κ = Unit`, `gZ = gZ1 = 1`, `EZ = EZ1 = 0`, `kB = β = me = h = chi = 1`: all hypotheses
hold and `sahaFactor > 0` (checked in scratch); the claimed derivative is `-5/2`. Necessity:
`me = 0` makes the bracket `0` and `log S ≡ 0`; `gZ = ![1, -1]`, `EZ = 0` makes `U_z ≡ 0`.

## 5. Scope

REDUCED: LTE, single `T`, two ionization stages, literal-sum `U` over the supplied levels, no
ionization-potential depression; energies in units where `β = 1/(k_B T)`. Physics check (audit
re-derivation): `S ∝ (U_II/U_I) β^(-3/2) e^(-βχ)` gives `-(χ + 3/(2β) + ⟨E⟩_II - ⟨E⟩_I)`; here
`(gZ1, EZ1)` is the upper stage (II). Literature: Griem 1997 (Saha).
