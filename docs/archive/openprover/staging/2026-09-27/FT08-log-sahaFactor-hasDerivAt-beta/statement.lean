import Mathlib
import CflibsFormal.Saha

/-!
# FT-08 (b2): `β`-derivative of `log sahaFactor`

Staged queue target, frontier FT-08 (b), decomposition step 5 (grade B: the `(3/2)` rpow of
`thermalBracket` re-expressed in `β`). Uses `Saha.sahaFactor` as it stands on main, at
`T = 1/(k_B β)`. One local definition, `meanExcitation`, copied verbatim from the FT-15 staged
targets (not on main). The `β`-derivative of `log partitionFunction` (decomposition step 4) is
not staged or verified anywhere, so it is part of this proof.
-/

open CflibsFormal

namespace Plan.FT08

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- **Boltzmann-weighted mean excitation energy**
`⟨E⟩_T = (∑ₖ gₖ·Eₖ·exp(−Eₖ/(k_B T))) / U(T)` over the supplied finite level list (same
`boltzmannFactor` and `partitionFunction` as `population`). Division is totalized (`0` if
`U = 0`). Copied verbatim from the FT-15 staged targets. -/
noncomputable def meanExcitation (kB T : ℝ) (g E : ι → ℝ) : ℝ :=
  (∑ k, g k * E k * boltzmannFactor kB T (E k)) / partitionFunction kB T g E

/-- **`d log S / dβ = -(χ + 3/(2β) + ⟨E⟩_II - ⟨E⟩_I)`.** Parametrize the Saha factor by the
inverse temperature `β = 1/(k_B T)`, i.e. evaluate `sahaFactor` at `T = 1/(k_B b)`. For
`β > 0`, `b ↦ log S(b)` has derivative `-(χ + 3/(2β) + ⟨E⟩_{z+1} - ⟨E⟩_z)` at `β`, where
`⟨E⟩_z = meanExcitation` of the lower stage `(gZ, EZ)` and `⟨E⟩_{z+1}` of the upper stage
`(gZ1, EZ1)`, both at `T = 1/(k_B β)`.

Reading: `S ∝ (U_{z+1}/U_z) · β^(-3/2) · exp(-β χ)`; `d log U/dβ = -⟨E⟩` gives the stage terms,
`(3/2) log (thermalBracket)` gives `-3/(2β)`, and the Saha exponent gives `-χ`. This is the
`κ_X` of the FT-08 coefficient. Energies are in the units of `k_B T`; `χ` is any real.

Hypotheses (all needed): `hkB`, `hβ` make `T = 1/(k_B β) > 0` and cancel `k_B`; `hme`, `hh` make
the thermal bracket positive (otherwise its `3/2` rpow is `0` and `log S = 0` identically);
`hgZ`, `hgZ1` make both partition functions positive (a signed `g` can give `U ≡ 0`).

Scope prediction: REDUCED (LTE, single `T`, two stages, literal-sum `U` over the supplied
levels, no ionization-potential depression). Literature: Griem 1997 (Saha). -/
theorem log_sahaFactor_hasDerivAt_beta [Nonempty ι] [Nonempty κ] {kB me h chi β : ℝ}
    {gZ EZ : ι → ℝ} {gZ1 EZ1 : κ → ℝ}
    (hkB : 0 < kB) (hβ : 0 < β) (hme : 0 < me) (hh : 0 < h)
    (hgZ : ∀ k, 0 < gZ k) (hgZ1 : ∀ k, 0 < gZ1 k) :
    HasDerivAt (fun b => Real.log (sahaFactor kB (1 / (kB * b)) me h chi gZ EZ gZ1 EZ1))
      (-(chi + 3 / (2 * β) + meanExcitation kB (1 / (kB * β)) gZ1 EZ1
          - meanExcitation kB (1 / (kB * β)) gZ EZ)) β := by
  sorry

end Plan.FT08
