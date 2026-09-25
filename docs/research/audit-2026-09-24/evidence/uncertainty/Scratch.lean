import CflibsFormal.Certificates
open CflibsFormal

/-- C10 closed form: the certificate alone yields a positive fixed point and convergence to it. -/
theorem dampedIter_certificate_sound_closed {ι : Type*} [Fintype ι] [Nonempty ι]
    (S Ntot : ι → ℝ) {x0 : ℝ} (hcert : dampedIterCert S Ntot) (hx0 : 0 ≤ x0) :
    ∃ r, 0 < r ∧ r = multiElementIonized S Ntot r ∧
      Filter.Tendsto
        (fun n => (dampedMultiElementIter S Ntot (1 / (1 + ∑ s, Ntot s / S s)))^[n] x0)
        Filter.atTop (nhds r) := by
  obtain ⟨r, hr, hfix⟩ := multiElement_exists_pos_fixedPoint S Ntot hcert.1 hcert.2
  exact ⟨r, hr, hfix, dampedIter_certificate_sound S Ntot hcert rfl hr.le hfix hx0⟩

/-- PAS with a certified loss upper bound: answering iff the bound is ≤ λ never loses to
abstaining everywhere. -/
theorem pas_certified_le_lambda {N : ℕ} (l U : Fin N → ℝ) (lam : ℝ) (hU : ∀ i, l i ≤ U i) :
    ∑ i, (if U i ≤ lam then l i else lam) ≤ N * lam := by
  calc ∑ i, (if U i ≤ lam then l i else lam) ≤ ∑ _i : Fin N, lam := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        split_ifs with h
        · exact (hU i).trans h
        · exact le_rfl
    _ = N * lam := by simp

/-- PAS regret of an interval (L ≤ l ≤ U) policy against the oracle `answer iff l < lam`
is bounded by the certificate width on the ambiguous set. -/
theorem pas_interval_regret {N : ℕ} (l L U : Fin N → ℝ) (lam : ℝ)
    (hL : ∀ i, L i ≤ l i) (hU : ∀ i, l i ≤ U i) :
    ∑ i, (if U i ≤ lam then l i else lam) - ∑ i, min (l i) lam
      ≤ ∑ i, (if L i ≤ lam ∧ lam < U i then U i - L i else 0) := by
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum (fun i _ => ?_)
  have := hL i; have := hU i
  by_cases h1 : U i ≤ lam
  · simp only [h1, if_true]
    have : min (l i) lam = l i := min_eq_left (by linarith)
    rw [this]; split_ifs <;> linarith
  · simp only [h1, if_false]
    push_neg at h1
    by_cases h2 : L i ≤ lam
    · rw [if_pos ⟨h2, h1⟩]
      rcases le_total (l i) lam with h | h
      · rw [min_eq_left h]; linarith
      · rw [min_eq_right h]; linarith
    · rw [if_neg (fun h => h2 h.1)]
      push_neg at h2
      rw [min_eq_right (by linarith)]; simp
