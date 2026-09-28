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
  intro T1 hT1 T2 hT2 hlt
  have hS1 := sahaFactor_pos (chi := chi) (EZ := EZ) (EZ1 := EZ1) hkB hT1 hme hh hgZ hgZ1
  have hS2 := sahaFactor_pos (chi := chi) (EZ := EZ) (EZ1 := EZ1) hkB hT2 hme hh hgZ hgZ1
  exact sahaEquilibriumNe_strictMono_S hN hS1 hS2
    (sahaFactor_strictMonoOn_temp hkB hme hh hchi hgZ hEZ hgZ1 hEZ1 hEχ hT1 hT2 hlt)

/-- Non-vacuity witness: `Fin 1` levels, unit constants, `chi = 1`, ground-state-only lists,
`Ntot = 1`, temperatures `1 < 2`. -/
example :
    sahaEquilibriumNe (sahaFactor 1 1 1 1 1 (fun _ : Fin 1 => (1:ℝ)) (fun _ => 0)
        (fun _ : Fin 1 => (1:ℝ)) (fun _ => 0)) 1
      < sahaEquilibriumNe (sahaFactor 1 2 1 1 1 (fun _ : Fin 1 => (1:ℝ)) (fun _ => 0)
        (fun _ : Fin 1 => (1:ℝ)) (fun _ => 0)) 1 :=
  sahaEquilibriumNe_strictMonoOn_temp (ι := Fin 1) (κ := Fin 1) one_pos one_pos one_pos
    zero_le_one (fun _ => one_pos) (fun _ => le_refl 0) (fun _ => one_pos) (fun _ => le_refl 0)
    (fun _ => zero_le_one) one_pos (Set.mem_Ioi.mpr one_pos) (Set.mem_Ioi.mpr two_pos)
    one_lt_two

/-- Non-vacuity witness with `hEχ` satisfied non-trivially: `EZ = ![0, 9/10] ≤ chi = 1`,
`gZ1 ≡ 2`, `EZ1 = ![0, 1/2]`, `Ntot = 5`, temperatures `1 < 3`. -/
example :
    sahaEquilibriumNe (sahaFactor 1 1 1 1 1 (fun _ : Fin 2 => (1:ℝ)) ![0, 9/10]
        (fun _ : Fin 2 => (2:ℝ)) ![0, 1/2]) 5
      < sahaEquilibriumNe (sahaFactor 1 3 1 1 1 (fun _ : Fin 2 => (1:ℝ)) ![0, 9/10]
        (fun _ : Fin 2 => (2:ℝ)) ![0, 1/2]) 5 := by
  refine sahaEquilibriumNe_strictMonoOn_temp (ι := Fin 2) (κ := Fin 2) one_pos one_pos one_pos
    zero_le_one (fun _ => one_pos) ?_ (fun _ => two_pos) ?_ ?_ (by norm_num)
    (Set.mem_Ioi.mpr one_pos) (Set.mem_Ioi.mpr (by norm_num)) (by norm_num)
  · intro k; fin_cases k <;> norm_num
  · intro k; fin_cases k <;> norm_num
  · intro k; fin_cases k <;> norm_num

end Plan.F02M6
