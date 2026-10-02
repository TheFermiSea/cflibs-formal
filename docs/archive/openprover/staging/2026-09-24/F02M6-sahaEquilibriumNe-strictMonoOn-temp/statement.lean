import Mathlib
import CflibsFormal.SahaStability
import CflibsFormal.SahaEquilibrium

/-!
# Frontier 02, M6: the equilibrium electron density is strictly increasing in temperature

Staged queue target, 2026-09-24. Last open milestone of frontier dossier 02
(`docs/frontiers/02-saha-monotonicity.md`, M6). Composes the landed
`sahaFactor_strictMonoOn_temp` (`SahaStability.lean`) with `sahaEquilibriumNe_strictMono_S`
(`SahaEquilibrium.lean`). Neither imported module contains this theorem.
-/

open CflibsFormal

namespace Plan.F02M6

variable {ι : Type*} [Fintype ι] {κ : Type*} [Fintype κ]

/-- **Equilibrium electron density strictly increasing in temperature (Frontier 02, M6).**

For the reduced single-element, two-stage (neutral / singly ionized), fixed-total-density LTE
core, the self-consistent electron density `n_e(T) = sahaEquilibriumNe (S(T)) Ntot`, i.e. the
unique positive root of `n_e² = S(T)·(Ntot − n_e)` with `S(T) = sahaFactor kB T me h chi …`,
is strictly increasing in `T` on `(0, ∞)`: at fixed elemental density a hotter plasma is more
strongly ionized.

Hypotheses and why each is present:
* `hkB`, `hme`, `hh` (positive constants) and `hgZ`, `hgZ1` (positive statistical weights)
  give `0 < S(T)` for `T > 0` (`sahaFactor_pos`), which puts `S(T)` in the domain `(0, ∞)` of
  `sahaEquilibriumNe_strictMono_S`; they are also hypotheses of `sahaFactor_strictMonoOn_temp`.
* `hN : 0 < Ntot` is the hypothesis of `sahaEquilibriumNe_strictMono_S`.
* `hEZ1 : ∀ k, 0 ≤ EZ1 k` (upper-stage levels at or above that stage's ground state) and
  `hEχ : ∀ k, EZ k ≤ chi` are the load-bearing hypotheses of `sahaFactor_strictMonoOn_temp`.
  `hEχ` is a **cutoff obligation on the supplied lower-stage level list**: every listed level
  lies at or below `chi`. Here `chi` is one temperature-independent constant; an IPD-lowered
  `χ − Δχ(n_e, T)` that moves with `T` or `n_e` is outside this statement, and no IPD or cutoff
  policy is assumed. It is not a fact about atoms: raw level databases violate it for many
  species (2026-09-24 deep audit, PS-06: 202 of 324), so it holds only for a suitably truncated
  list. Which truncation policy produces such a list is a separate, pending decision; this
  theorem asserts none.
* `hchi`, `hEZ` are passed through to `sahaFactor_strictMonoOn_temp` for API parity; that
  lemma does not use them.

Scope (two-axis): own relation EXACT (a composition of proven facts about the stated model);
model tags of the definitions used: `sahaFactor` EXACT (Saha–Eggert (Griem)),
`sahaEquilibriumNe` REDUCED (one element, two stages, fixed `Ntot`, no multi-element
coupling); predicted published tag REDUCED. Citation: Saha–Eggert (Griem). -/
theorem sahaEquilibriumNe_strictMonoOn_temp [Nonempty ι] [Nonempty κ]
    {kB me h chi Ntot : ℝ} {gZ EZ : ι → ℝ} {gZ1 EZ1 : κ → ℝ}
    (hkB : 0 < kB) (hme : 0 < me) (hh : 0 < h) (hchi : 0 ≤ chi)
    (hgZ : ∀ k, 0 < gZ k) (hEZ : ∀ k, 0 ≤ EZ k)
    (hgZ1 : ∀ k, 0 < gZ1 k) (hEZ1 : ∀ k, 0 ≤ EZ1 k)
    (hEχ : ∀ k, EZ k ≤ chi) (hN : 0 < Ntot) :
    StrictMonoOn (fun T => sahaEquilibriumNe (sahaFactor kB T me h chi gZ EZ gZ1 EZ1) Ntot)
      (Set.Ioi 0) := by
  sorry

end Plan.F02M6
