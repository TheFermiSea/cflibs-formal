import CflibsFormal

-- Ground-truth check for ft02.ipd-saha-inverse-gauge: confirms the four declarations resolve
-- with the exact pretty-printed types docs/catalog.jsonl records (up to pretty-printing
-- options), that all three theorems are axiom-clean, and non-vacuity witnesses for both
-- `ipdLogMap_root_subsingleton` (restated as named theorems so `#print axioms` applies) and the
-- headline `ipdLogMap_contracts`. Run from the repo root:
-- `lake env lean docs/theorems/evidence/ft02.ipd-saha-inverse-gauge/check.lean`.

open CflibsFormal

#check @CflibsFormal.ipdLogMap
#check @CflibsFormal.ipdLogMap_root_subsingleton
#check @CflibsFormal.ipdLogMap_contracts
#check @CflibsFormal.ipdInverse_twoPoint_sensitivity

#print axioms CflibsFormal.ipdLogMap_root_subsingleton
#print axioms CflibsFormal.ipdLogMap_contracts
#print axioms CflibsFormal.ipdInverse_twoPoint_sensitivity

/-- Restates `IpdSahaInverse.lean`'s first module example as a named theorem so
`#print axioms` applies to it: at `a = exp(-1/2)`, `b = 1/2`, `ℓ = 0` is a genuine member of the
regular-root set (non-vacuity for `ipdLogMap_root_subsingleton`). -/
theorem ipdLogMap_root_subsingleton_nonvacuous_root :
    (0 : ℝ) ∈ {ℓ | ipdLogMap (Real.exp (-1/2)) (1/2) ℓ = ℓ ∧ (1/2) * Real.exp (ℓ / 2) < 2} := by
  refine ⟨?_, ?_⟩
  · unfold ipdLogMap; rw [Real.log_exp]; simp; norm_num
  · simp; norm_num

/-- Restates `IpdSahaInverse.lean`'s second module example as a named theorem: the theorem then
pins every member of the regular-root set at that instance to `0`. -/
theorem ipdLogMap_root_subsingleton_nonvacuous_unique (ℓ : ℝ)
    (h : ℓ ∈ {ℓ | ipdLogMap (Real.exp (-1/2)) (1/2) ℓ = ℓ ∧ (1/2) * Real.exp (ℓ / 2) < 2}) :
    ℓ = 0 :=
  ipdLogMap_root_subsingleton (a := Real.exp (-1/2)) (b := 1/2) h
    ⟨by unfold ipdLogMap; rw [Real.log_exp]; simp; norm_num, by simp; norm_num⟩

#print axioms ipdLogMap_root_subsingleton_nonvacuous_root
#print axioms ipdLogMap_root_subsingleton_nonvacuous_unique

/-- Non-vacuity witness for the headline `ipdLogMap_contracts`: at `a = exp(-1/2)`, `b = 1/2`,
`ℓ1 = 0`, `q = 1/4`, the half-line `(-∞, 0]` is `hmaps`-invariant and the existence, uniqueness
and convergence conclusions all hold simultaneously (nothing here shows the theorem vacuous). -/
example : ∃ ℓs ∈ Set.Iic (0 : ℝ), ipdLogMap (Real.exp (-1/2)) (1/2) ℓs = ℓs ∧
    (∀ ℓ ∈ Set.Iic (0 : ℝ), ipdLogMap (Real.exp (-1/2)) (1/2) ℓ = ℓ → ℓ = ℓs) ∧
    ∀ ℓ0 ∈ Set.Iic (0 : ℝ),
      Filter.Tendsto (fun n => (ipdLogMap (Real.exp (-1/2)) (1/2))^[n] ℓ0)
        Filter.atTop (nhds ℓs) := by
  refine ipdLogMap_contracts (q := 1/4) (by norm_num) (by simp; norm_num) (by norm_num) ?_
  intro x hx
  simp only [Set.mem_Iic] at *
  unfold ipdLogMap
  rw [Real.log_exp]
  have : Real.exp (x / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  linarith
