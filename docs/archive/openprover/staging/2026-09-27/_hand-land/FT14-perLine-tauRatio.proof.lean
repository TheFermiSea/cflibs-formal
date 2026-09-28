import Mathlib
import CflibsFormal.OpticalDepth

/-!
# FT-14 (iv): two-line optical-depth ratio with per-line cross-sections and stimulated emission

Staged target, 2026-09-24 audit, frontier FT-14 (iv), restated per the verdict's revision: the
sketch was unguarded and false (`N = 0` gives `0 / 0 = 0` on the left), and it omitted the
stimulated-emission factor. No new definitions: `opticalDepth` (`OpticalDepth.lean`) is used
as it stands on main, with the per-line cross-section `σ0ᵢ := κ0ᵢ · (1 - exp (-xᵢ))`.
-/

open CflibsFormal

namespace Plan.FT14

/-- **Per-line optical-depth ratio.** Two lines of one species in one LTE slab (common `k_B`,
`T`, `N`, `ℓ`, level data `g`, `E`), with lower levels `l1`, `l2` and their own line-centre
cross-sections `σ0ᵢ = κ0ᵢ · (1 - exp (-xᵢ))`, `xᵢ = hνᵢ/(k_B T) = (E_uᵢ - E_lᵢ)/(k_B T)`.
Then `τ₁ / τ₂ = σ01 g_l1 e^(-E_l1/kT) / (σ02 g_l2 e^(-E_l2/kT))`: the density `N`, the path
`ℓ` and the partition function cancel, and the stimulated-emission ratio
`(1 - exp (-x1)) / (1 - exp (-x2))` survives. This generalizes the shared-`σ0` two-line
statements of `OpticalDepthBridge` to distinct `σ0ᵢ`.

The guards are the verdict's: `hN`, `hell`, `hg` are needed (without them the left side is a
`0 / 0`); `hσ2` and `[Nonempty ι]` are domain guards (the second also follows from `l1 : ι`,
and at `σ02 = 0` both sides are `0` in Lean).

Scope: REDUCED (homogeneous single-temperature slab, flat line-centre cross-section; the
dependence of `κ0ᵢ` on `A`, `g_u`, `λ` and `φ(0)` is NOT modelled, it is the abstract input).
Literature: Griem 1997 (LTE absorption with the negative-absorption factor). -/
theorem perLine_tauRatio {ι : Type*} [Fintype ι] [Nonempty ι] {kB T N ell κ01 κ02 x1 x2 : ℝ}
    {g E : ι → ℝ} {l1 l2 : ι} (hN : N ≠ 0) (hell : ell ≠ 0) (hg : ∀ k, 0 < g k)
    (hσ2 : κ02 * (1 - Real.exp (-x2)) ≠ 0) :
    opticalDepth kB T N (κ01 * (1 - Real.exp (-x1))) ell g E l1
        / opticalDepth kB T N (κ02 * (1 - Real.exp (-x2))) ell g E l2
      = κ01 * (1 - Real.exp (-x1)) * g l1 * boltzmannFactor kB T (E l1)
        / (κ02 * (1 - Real.exp (-x2)) * g l2 * boltzmannFactor kB T (E l2)) := by
  have hU : partitionFunction kB T g E ≠ 0 := (partitionFunction_pos hg).ne'
  have hg2 : g l2 ≠ 0 := (hg l2).ne'
  have hb2 : boltzmannFactor kB T (E l2) ≠ 0 := (boltzmannFactor_pos _ _ _).ne'
  obtain ⟨hk2, hs2⟩ := mul_ne_zero_iff.mp hσ2
  unfold opticalDepth population
  field_simp

end Plan.FT14
