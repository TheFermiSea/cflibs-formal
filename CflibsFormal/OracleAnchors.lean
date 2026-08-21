/-
Copyright (c) 2026 Brian Squires. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Squires
-/
import Mathlib
import CflibsFormal.Certificates
import CflibsFormal.StarkBroadening
/-!
# CF-LIBS formalization — oracle fixture anchors (machine-checked spec ↔ fixtures link)

`oracle/Generate.lean` (a `Float` mirror) and `oracle/check_fixtures.py` (a Python mirror) are two
independent transcriptions checked against *each other*: a wrong-but-consistent formula copied into
both would pass every gate, because neither is ever compared to the verified `CflibsFormal` ℝ defs.
This module closes that gap. Each `example` below instantiates a **verified `CflibsFormal`
definition/predicate at the exact rational inputs of an `oracle/fixtures.json` entry** and
discharges it by `norm_num`/`simp`/`decide`. So the fixtures' verdicts and decisive values are
now pinned to the ℝ spec, not merely to their Float twin: change an anchored `CflibsFormal` def
and the matching anchor here stops compiling.

## Literature and scope
The anchored predicates inherit their physics citations from the wrapped theorems (see
`CflibsFormal/Certificates.lean` — Tognoni et al. 2010, Aguilera & Aragón 2007, McWhirter 1965 via
Cristoforetti et al. 2010, Griem 1997) and `CflibsFormal/StarkBroadening.lean` (Griem's linear Stark
width). **Scope.** This is a `PURE-MATH` regression harness: it adds no new mathematics and every
statement is `norm_num`/`decide`-closed at literal rationals. Anchored: the certificate scenario
(C1–C7, C10, C12–C14 predicates on their accept witnesses + the C1/C2/C10/C14 rejection witnesses)
and the Stark scenario (`starkDensity`, its forward/inverse round trip). Decisive-value anchors are
given for C1 (energy spread), C2 (joint Gram determinant), and C7 (McWhirter margin). **Not anchored
(and why):** every fixture whose value is transcendental — the forward intensities, partition
functions, log-slope temperature recoveries, the Saha factor `S(T)` and `SA(τ)` self-absorption
factor (all `exp`/`log`), and the `√`-heavy C9 Saha-iteration clauses and the `maxPerLineError`
threshold — resists a rational `norm_num` equality; those stay covered by the Float/Python
mirrors alone.
-/
namespace CflibsFormal

/-! ### Scenario 6 — runtime certificates: predicate verdicts at the fixtures' exact inputs. -/

-- C1 energy_spread / C3 conditioning · `E = (0,1)` · verdict true.
example : energySpreadCert (ι := Fin 2) ![0, 1] := by
  norm_num [energySpreadCert, mean, Fin.sum_univ_two]
example : conditioningCert (ι := Fin 2) ![0, 1] := by
  norm_num [conditioningCert, mean, Fin.sum_univ_two]
-- C1 decisive value: `SS_E = ∑ₖ (Eₖ − Ē)² = 1/2` (fixtures.json C1 `value`).
example : (∑ k : Fin 2, (![(0 : ℝ), 1] k - mean ![0, 1]) ^ 2) = 1 / 2 := by
  norm_num [mean, Fin.sum_univ_two]

-- C2 joint_rank · `E = (0,1,2)`, `s = (0,0,1)` · verdict true.
example : jointRankCert (ι := Fin 3) ![0, 1, 2] ![0, 0, 1] := by
  unfold jointRankCert mean; simp [Fin.sum_univ_three]; norm_num
-- C2 decisive value: joint Gram determinant `SS_E·SS_s − S_Es² = 1/3` (fixtures.json C2 `value`).
example :
    (∑ k : Fin 3, (![(0 : ℝ), 1, 2] k - mean ![0, 1, 2]) ^ 2)
      * (∑ k : Fin 3, (![(0 : ℝ), 0, 1] k - mean ![0, 0, 1]) ^ 2)
    - (∑ k : Fin 3, (![(0 : ℝ), 1, 2] k - mean ![0, 1, 2])
        * (![(0 : ℝ), 0, 1] k - mean ![0, 0, 1])) ^ 2 = 1 / 3 := by
  simp [mean, Fin.sum_univ_three]; norm_num

-- C4 slope_budget · `ε=1, τ_β=2, SS_E=1/2, n=2` · verdict true (budget tight, slack 0).
example : slopeBudgetCert 1 2 (1 / 2) 2 := by norm_num [slopeBudgetCert]
-- C5 temp_budget · `k_B=1, T̂=2, B=1/2, τ_T=1` · verdict true.
example : tempBudgetCert 1 2 (1 / 2) 1 := by norm_num [tempBudgetCert]
-- C6 comp_budget · `δ=1, τ_C=2, Ŝ=2, n=2` · verdict true (slack 1).
example : compBudgetCert 1 2 2 2 := by norm_num [compBudgetCert]
-- C7 mcwhirter · `C=1, T=1, ΔE=1, nₑ=2` · verdict true; decisive margin `nₑ − C√T·ΔE³ = 1`.
example : mcWhirterCert 1 1 1 2 := by norm_num [mcWhirterCert, Real.sqrt_one]
example : (2 : ℝ) - 1 * Real.sqrt 1 * (1 : ℝ) ^ 3 = 1 := by norm_num [Real.sqrt_one]
-- C10 damped_iter · `S = Ntot = (1,1)` · verdict true (positivity).
example : dampedIterCert (ι := Fin 2) ![1, 1] ![1, 1] :=
  ⟨fun s => by fin_cases s <;> norm_num, fun s => by fin_cases s <;> norm_num⟩
-- C12 known_tau · `τ=1` · verdict true.
example : knownTauCert 1 := by norm_num [knownTauCert]
-- C13 sa_distinct · `w₁=2, w₂=1` · verdict true.
example : saDistinctCert 2 1 := ⟨by norm_num, by norm_num⟩
-- C14 alias_budget · `δ=1/2` · verdict true.
example : aliasBudgetCert (1 / 2) := ⟨by norm_num, by norm_num⟩

/-! ### Scenario 6 — rejection witnesses: the four `verdict:false` fixtures. -/

-- C1 reject: flat energies `E=(1,1)` ⇒ `SS_E=0`, predicate fails.
example : ¬ energySpreadCert (ι := Fin 2) ![1, 1] := by
  norm_num [energySpreadCert, mean, Fin.sum_univ_two]
-- C2 reject: collinear `E=(0,1)`, `s=(0,2)` ⇒ det 0, predicate fails.
example : ¬ jointRankCert (ι := Fin 2) ![0, 1] ![0, 2] := by
  norm_num [jointRankCert, mean, Fin.sum_univ_two]
-- C10 reject: nonpositive Saha factor `S=(0,1)` fails `0 < Sₛ`.
example : ¬ dampedIterCert (ι := Fin 2) ![0, 1] ![1, 1] := by
  rintro ⟨h, -⟩; simpa using h 0
-- C14 reject: `δ=1` fails `δ < 1`.
example : ¬ aliasBudgetCert 1 := by norm_num [aliasBudgetCert]

/-! ### Scenario 5 — Stark broadening: the Griem linear `n_e` diagnostic at the fixture inputs. -/

-- `starkDensity(w=1/20, nRef=1, width=3/10) = nRef·width/(2w) = 3` (fixtures `stark_density.ne`).
example : starkDensity (1 / 20) 1 (3 / 10) = 3 := by norm_num [starkDensity]
-- Forward/inverse round trip: `starkFWHM(w, nRef, starkDensity(w, nRef, width)) = width = 3/10`.
example : starkFWHM (1 / 20) 1 (starkDensity (1 / 20) 1 (3 / 10)) = 3 / 10 := by
  norm_num [starkFWHM, starkDensity]

end CflibsFormal
