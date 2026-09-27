import CflibsFormal

/-! Tractability probes: a few slate lemmas proved outright (frontier-proposer, 2026-09-23). -/

open Finset Real Filter Topology
open scoped BigOperators

namespace SlateProofs
open CflibsFormal

/-- FT-01 a-posteriori residual stop rule. -/
theorem residual_stop {Φ : ℝ → ℝ} {s : Set ℝ} {q u ustar : ℝ} (hq : q < 1)
    (hLip : ∀ x ∈ s, ∀ y ∈ s, |Φ x - Φ y| ≤ q * |x - y|) (hu : u ∈ s) (hs : ustar ∈ s)
    (hfix : Φ ustar = ustar) : |u - ustar| ≤ |Φ u - u| / (1 - q) := by
  have h1 : |u - ustar| ≤ |Φ u - u| + |Φ u - Φ ustar| := by
    rw [hfix]
    calc |u - ustar| = |(u - Φ u) + (Φ u - ustar)| := by ring_nf
      _ ≤ |u - Φ u| + |Φ u - ustar| := abs_add_le _ _
      _ = |Φ u - u| + |Φ u - ustar| := by rw [abs_sub_comm u]
  have h2 := hLip u hu ustar hs
  rw [le_div_iff₀ (by linarith)]
  nlinarith [abs_nonneg (u - ustar)]

def dampedMap (lam : ℝ) (g : ℝ → ℝ) (u : ℝ) : ℝ := (1 - lam) * u + lam * g u

/-- FT-01 exact affine error recursion. -/
theorem dampedAffine_iterate (lam g c u0 : ℝ) (hg : g ≠ 1) (n : ℕ) :
    (dampedMap lam (fun u => g * u + c))^[n] u0 - c / (1 - g)
      = (1 - lam + lam * g) ^ n * (u0 - c / (1 - g)) := by
  have h1 : (1 : ℝ) - g ≠ 0 := sub_ne_zero.mpr (Ne.symm hg)
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', pow_succ]
    set v := (dampedMap lam (fun u => g * u + c))^[n] u0
    unfold dampedMap
    have hv : v = c / (1 - g) + (1 - lam + lam * g) ^ n * (u0 - c / (1 - g)) := by
      linarith [ih]
    rw [hv]; field_simp; ring

/-- FT-06 C8 soundness on brackets. -/
theorem starkSaha_certificate_sound {lS uS lR uR C T dE ne : ℝ}
    (hS : lS ≤ ne ∧ ne ≤ uS) (hR : lR ≤ ne ∧ ne ≤ uR)
    (h : max lS lR ≤ min uS uR ∧ C * Real.sqrt T * dE ^ 3 ≤ max lS lR) :
    mcWhirterCert C T dE ne :=
  le_trans h.2 (max_le hS.1 hR.1)

/-- FT-06 disjoint-bracket refusal. -/
theorem starkSaha_refusal_sound {lS uS lR uR ne : ℝ} (hdis : min uS uR < max lS lR) :
    ¬ ((lS ≤ ne ∧ ne ≤ uS) ∧ (lR ≤ ne ∧ ne ≤ uR)) := by
  rintro ⟨⟨h1, h2⟩, h3, h4⟩
  exact absurd (lt_of_lt_of_le (lt_of_lt_of_le hdis (max_le h1 h3)) (le_min h2 h4))
    (lt_irrefl _)

/-- FT-03 gate value is nonnegative when refusal needs a certified lower bound above λ. -/
theorem pas_gate_value_nonneg {N : ℕ} (l L : Fin N → ℝ) (lam : ℝ) (hL : ∀ i, L i ≤ l i) :
    (∑ i, if lam < L i then lam else l i) ≤ ∑ i, l i := by
  refine Finset.sum_le_sum fun i _ => ?_
  split_ifs with h
  · exact le_of_lt (lt_of_lt_of_le h (hL i))
  · exact le_rfl

/-- FT-05 truncation tail bounds. -/
noncomputable def partitionFunctionCut {ι : Type*} [Fintype ι] (kB T cut : ℝ) (g E : ι → ℝ) : ℝ :=
  ∑ k ∈ univ.filter (fun k => E k < cut), g k * boltzmannFactor kB T (E k)

theorem partitionFunction_sub_cut_bounds {ι : Type*} [Fintype ι] {kB T cut : ℝ} {g E : ι → ℝ}
    (hg : ∀ k, 0 ≤ g k) (hkT : 0 < kB * T) :
    0 ≤ partitionFunction kB T g E - partitionFunctionCut kB T cut g E ∧
      partitionFunction kB T g E - partitionFunctionCut kB T cut g E
        ≤ (∑ k ∈ univ.filter (fun k => cut ≤ E k), g k) * Real.exp (-cut / (kB * T)) := by
  have hsplit : partitionFunction kB T g E - partitionFunctionCut kB T cut g E
      = ∑ k ∈ univ.filter (fun k => cut ≤ E k), g k * boltzmannFactor kB T (E k) := by
    unfold partitionFunction partitionFunctionCut
    rw [← Finset.sum_filter_add_sum_filter_not univ (fun k => E k < cut)]
    simp only [not_lt]; ring
  rw [hsplit]
  refine ⟨Finset.sum_nonneg fun k _ => mul_nonneg (hg k) (boltzmannFactor_pos _ _ _).le, ?_⟩
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun k hk => ?_
  have hk' : cut ≤ E k := (Finset.mem_filter.mp hk).2
  refine mul_le_mul_of_nonneg_left ?_ (hg k)
  unfold boltzmannFactor
  exact Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (by linarith) hkT.le)

/-- FT-09 energy-affine gauge, algebraic core. -/
theorem olsSlope_add_affine {ι : Type*} [Fintype ι] [Nonempty ι] (E y : ι → ℝ) (α b : ℝ)
    (hvar : 0 < ∑ k, (E k - mean E) ^ 2) :
    olsSlope E (fun k => y k + α + b * E k) = olsSlope E y + b := by
  rw [olsSlope_eq_centered, olsSlope_eq_centered]
  have h0 : ∑ k, (E k - mean E) = 0 := centered_sum_zero E
  have hEE : ∑ k, (E k - mean E) * E k = ∑ k, (E k - mean E) ^ 2 := by
    have : ∑ k, (E k - mean E) * E k
        = ∑ k, (E k - mean E) ^ 2 + mean E * ∑ k, (E k - mean E) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [this, h0, mul_zero, add_zero]
  have hsplit : ∑ k, (E k - mean E) * (y k + α + b * E k)
      = ∑ k, (E k - mean E) * y k + α * ∑ k, (E k - mean E)
        + b * ∑ k, (E k - mean E) * E k := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [hsplit, h0, hEE, mul_zero, add_zero, add_div, mul_div_assoc,
    div_self hvar.ne', mul_one]

end SlateProofs

#print axioms SlateProofs.residual_stop
#print axioms SlateProofs.dampedAffine_iterate
#print axioms SlateProofs.starkSaha_certificate_sound
#print axioms SlateProofs.starkSaha_refusal_sound
#print axioms SlateProofs.pas_gate_value_nonneg
#print axioms SlateProofs.partitionFunction_sub_cut_bounds
#print axioms SlateProofs.olsSlope_add_affine
