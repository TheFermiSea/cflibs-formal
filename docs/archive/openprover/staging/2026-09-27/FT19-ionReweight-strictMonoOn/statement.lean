import Mathlib
import CflibsFormal.SahaStability

/-!
# FT-19 (a): the ion-stage zone reweight is strictly increasing in temperature

Staged queue target, 2026-09-24 audit, frontier FT-19, REVISE applied (verdict: the proposal's
`ρ = S/n_e` is wrong; the correct reweight has the partition functions cancelled). One new
definition, `ionReweight`, written here once; `thermalBracket` (`Saha.lean`) is used as it
stands on main.
-/

open CflibsFormal

namespace Plan.FT19

/-- **Ion-stage zone reweight** `ρ(T) = 2 · θ(T)^{3/2} · e^{−χ/(k_B T)} / n_e`, with
`θ(T) = thermalBracket kB T me h = 2π m_e k_B T / h²`.

Reading: at uniform electron density `n_e`, a zone with neutral column `N_I` has ion column
`N_II = N_I · S(T)/n_e` (Saha), and the ion zone weight `Fcal · N_II / U_II(T)` equals the
neutral zone weight `Fcal · N_I / U_I(T)` times `ρ(T)`: the partition-function ratio
`U_II/U_I` inside the Saha factor `S` cancels. So `ρ` is NOT `S/n_e`. -/
noncomputable def ionReweight (kB me h chi ne T : ℝ) : ℝ :=
  2 * thermalBracket kB T me h ^ (3/2 : ℝ) * Real.exp (-chi / (kB * T)) / ne

/-- **The ion reweight is strictly increasing in temperature on `(0, ∞)`.** For positive
`k_B, m_e, h, n_e` and a nonnegative ionization energy `χ`, `T ↦ ionReweight kB me h chi ne T`
is strictly increasing on `T > 0`. No cutoff hypothesis on the neutral levels (`E_k ≤ χ`) is
needed, unlike `sahaFactor_strictMonoOn_temp`: the partition functions are absent.

Proof idea: `θ` is strictly increasing and positive (`thermalBracket_strictMono`,
`thermalBracket_pos`), so `θ^{3/2}` is strictly increasing (`Real.rpow_lt_rpow`); for
`χ ≥ 0`, `−χ/(k_B T)` is nondecreasing in `T > 0`, so the exponential is nondecreasing; a
strictly increasing positive factor times a nondecreasing positive factor, divided by
`n_e > 0`, is strictly increasing.

Scope: PURE-MATH relation (monotonicity of an explicit real function); the physics reading of
`ionReweight` (uniform `n_e`, LTE Saha balance per zone) is REDUCED. Saha–Eggert law: Griem,
Plasma Spectroscopy (1964). -/
theorem ionReweight_strictMonoOn {kB me h chi ne : ℝ} (hkB : 0 < kB) (hme : 0 < me)
    (hh : 0 < h) (hchi : 0 ≤ chi) (hne : 0 < ne) :
    StrictMonoOn (ionReweight kB me h chi ne) (Set.Ioi 0) := by
  sorry

end Plan.FT19
