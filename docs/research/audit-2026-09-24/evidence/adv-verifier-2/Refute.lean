import CflibsFormal

/-!
Adversarial-verifier probes for FT-11 .. FT-20 (scratch, not for the repo).
-/

open Finset Real CflibsFormal

namespace AdvV2

/-! ## FT-11 definitions copied verbatim from the slate -/

noncomputable def sahaStageProduct (S : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1
  | z + 1 => sahaStageProduct S z * S z

noncomputable def stageFraction (Z : ℕ) (S : ℕ → ℝ) (ne : ℝ) (z : ℕ) : ℝ :=
  (sahaStageProduct S z / ne ^ z) / ∑ k ∈ Finset.range (Z + 1), sahaStageProduct S k / ne ^ k

noncomputable def speciesCharge (Z : ℕ) (S : ℕ → ℝ) (Ntot ne : ℝ) : ℝ :=
  Ntot * ∑ z ∈ Finset.range (Z + 1), (z : ℝ) * stageFraction Z S ne z

noncomputable def totalIonizedCharge {κ : Type*} [Fintype κ] (Z : κ → ℕ) (S : κ → ℕ → ℝ)
    (Ntot : κ → ℝ) (ne : ℝ) : ℝ := ∑ s, speciesCharge (Z s) (S s) (Ntot s) ne

/-- `ne = 0` is a junk fixed point of the cascade map (totalized division). -/
theorem cascade_zero_junk_fixedPoint :
    totalIonizedCharge (κ := Unit) (fun _ => 1) (fun _ _ => 1) (fun _ => 1) 0 = 0 := by
  simp [totalIonizedCharge, speciesCharge, stageFraction, sahaStageProduct,
    Finset.sum_range_succ]

/-- The FT-11 S8 sketch, stated WITHOUT `0 < nestar` (as in the proposal), is FALSE. -/
theorem ft11_S8_sketch_false :
    ¬ (∀ x nestar : ℝ, 0 < x →
        nestar = totalIonizedCharge (κ := Unit) (fun _ => 1) (fun _ _ => 1) (fun _ => 1) nestar →
        |x - nestar|
          ≤ |x - totalIonizedCharge (κ := Unit) (fun _ => 1) (fun _ _ => 1) (fun _ => 1) x|) := by
  intro h
  have h1 := h 1 0 one_pos cascade_zero_junk_fixedPoint.symm
  have hQ : totalIonizedCharge (κ := Unit) (fun _ => 1) (fun _ _ => 1) (fun _ => 1) 1
      = 1 / 2 := by
    simp [totalIonizedCharge, speciesCharge, stageFraction, sahaStageProduct,
      Finset.sum_range_succ]
    norm_num
  rw [hQ] at h1
  norm_num [abs_of_pos] at h1

/-- S7 (Z = 1 reduction) with only `ne ≠ 0`. -/
theorem totalIonizedCharge_Z_one {κ : Type*} [Fintype κ] {S : κ → ℕ → ℝ} {Ntot : κ → ℝ}
    {Z : κ → ℕ} {ne : ℝ} (hne : ne ≠ 0) (hZ : ∀ s, Z s = 1) :
    totalIonizedCharge Z S Ntot ne = multiElementIonized (fun s => S s 0) Ntot ne := by
  unfold totalIonizedCharge multiElementIonized
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [hZ s]
  simp only [speciesCharge, stageFraction, sahaStageProduct, Finset.sum_range_succ,
    Finset.sum_range_zero]
  by_cases h : ne + S s 0 = 0
  · have : S s 0 = -ne := by linarith
    rw [h, this]
    field_simp
    simp
  · have h' : ne + S s 0 ≠ 0 := h
    have e : (ne + S s 0)⁻¹ * (ne + S s 0) = 1 := inv_mul_cancel₀ h'
    field_simp
    linear_combination (Ntot s * S s 0) * e

/-! ## FT-19: tiltMean antitone in the anchor is a free corollary of existing lemmas -/

theorem tiltMean_antitone_anchor {ζ : Type*} [Fintype ζ] [Nonempty ζ] {w b : ζ → ℝ}
    (hw : ∀ z, 0 < w z) : Antitone (tiltMean w b) := by
  intro a1 a2 h
  rcases h.eq_or_lt with h | h
  · rw [h]
  · exact (tiltMean_le_pairSlope hw h).trans (pairSlope_le_tiltMean hw h)

/-! ## FT-14 (i): the Kirchhoff identity is one `field_simp` -/

noncomputable def lineOpacity (κ0 nl x : ℝ) : ℝ := κ0 * nl * (1 - Real.exp (-x))
noncomputable def lineEmissivity (ε0 nu : ℝ) : ℝ := ε0 * nu

theorem source_eq_planck {κ0 ε0 B0 nl nu x gu gl : ℝ} (hx : 0 < x) (hκ : 0 < κ0)
    (hnl : 0 < nl) (hpop : nu / nl = gu / gl * Real.exp (-x))
    (hein : ε0 * gu / gl = κ0 * B0) :
    lineEmissivity ε0 nu / lineOpacity κ0 nl x = B0 / (Real.exp x - 1) := by
  unfold lineEmissivity lineOpacity
  have hnu : nu = gu / gl * Real.exp (-x) * nl := by
    rw [div_eq_iff hnl.ne'] at hpop; exact hpop
  have hex : 1 < Real.exp x := Real.one_lt_exp_iff.mpr hx
  have hen : Real.exp (-x) = 1 / Real.exp x := by rw [Real.exp_neg, one_div]
  have h1 : (1 : ℝ) - Real.exp (-x) ≠ 0 := by
    rw [hen]; have : 1 / Real.exp x < 1 := by rw [div_lt_one (by linarith)]; exact hex
    linarith
  have hB : ε0 * (gu / gl) = κ0 * B0 := by rw [← hein]; ring
  rw [hnu]
  have : ε0 * (gu / gl * Real.exp (-x) * nl) = κ0 * B0 * Real.exp (-x) * nl := by
    rw [← hB]; ring
  rw [this, hen]
  have hE : Real.exp x - 1 ≠ 0 := by linarith
  have hE0 : Real.exp x ≠ 0 := (Real.exp_pos x).ne'
  field_simp

/-! ## FT-16: the bias identity -/

theorem extractor_bias_identity {P L : Type*} [Fintype P] [Fintype L] [DecidableEq L]
    (K Kt : Matrix P L ℝ) (I : L → ℝ) (η : P → ℝ) (hdet : IsUnit (K.transpose * K).det) :
    ((K.transpose * K)⁻¹ * K.transpose).mulVec (Kt.mulVec I + η) - I
      = ((K.transpose * K)⁻¹ * K.transpose).mulVec ((Kt - K).mulVec I)
        + ((K.transpose * K)⁻¹ * K.transpose).mulVec η := by
  have hinv : (K.transpose * K)⁻¹ * (K.transpose * K) = 1 := Matrix.nonsing_inv_mul _ hdet
  have hKI : ((K.transpose * K)⁻¹ * K.transpose).mulVec (K.mulVec I) = I := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, hinv, Matrix.one_mulVec]
  rw [Matrix.mulVec_add, Matrix.sub_mulVec, Matrix.mulVec_sub, hKI]
  abel

/-! ## FT-13 (a) pointwise step via convexity of exp -/

theorem slab_chord_le {τ t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 - Real.exp (-τ)) * t ≤ 1 - Real.exp (-(τ * t)) := by
  have hc := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (-τ))
    (by linarith : (0 : ℝ) ≤ 1 - t) ht0 (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at hc
  have : t * -τ = -(τ * t) := by ring
  rw [this] at hc
  nlinarith [hc]

end AdvV2
#print axioms AdvV2.ft11_S8_sketch_false
#print axioms AdvV2.totalIonizedCharge_Z_one
#print axioms AdvV2.tiltMean_antitone_anchor
#print axioms AdvV2.source_eq_planck
#print axioms AdvV2.extractor_bias_identity
#print axioms AdvV2.slab_chord_le
