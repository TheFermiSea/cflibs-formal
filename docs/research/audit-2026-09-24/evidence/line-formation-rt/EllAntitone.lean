import CflibsFormal.OpticalDepthBridge

open CflibsFormal

/-- Falsification probe: at fixed (T, N, Fcal, σ₀) the state-bound thick line intensity is
STRICTLY DECREASING in the path length ℓ — a longer emitting slab gives a DIMMER line, because
ℓ enters τ but not the thin emission `lineIntensity`. Physically the emergent intensity
`B·(1 − e^{−κℓ})` is increasing in ℓ. -/
theorem thickLineIntensity_strictAntiOn_ell {ι : Type*} [Fintype ι] [Nonempty ι]
    {kB T N Fcal sigma0 : ℝ} {g E A : ι → ℝ} (hg : ∀ k, 0 < g k) (hN : 0 < N)
    (hFcal : 0 < Fcal) (hA : ∀ k, 0 < A k) (hsig : 0 < sigma0) (u l : ι) :
    StrictAntiOn (fun ell => thickLineIntensity kB T N Fcal sigma0 ell g E A u l)
      (Set.Ioi 0) := by
  intro a ha b hb hab
  have hI : 0 < lineIntensity kB T N Fcal g E A u := lineIntensity_pos hg hN hFcal hA u
  have hτa : 0 < opticalDepth kB T N sigma0 a g E l := opticalDepth_pos hg hN hsig ha l
  have hτb : 0 < opticalDepth kB T N sigma0 b g E l := opticalDepth_pos hg hN hsig hb l
  have hτlt : opticalDepth kB T N sigma0 a g E l < opticalDepth kB T N sigma0 b g E l := by
    simp only [opticalDepth_eq_linear]
    have hc := effectiveCrossSection_pos (kB := kB) (T := T) (E := E) hg hsig l
    nlinarith [mul_lt_mul_of_pos_left hab hc]
  have hSA := selfAbsorptionFactor_strictAntiOn hτa hτb hτlt
  simp only [thickLineIntensity, selfAbsorbedIntensity]
  exact mul_lt_mul_of_pos_left hSA hI

example : thickLineIntensity 1 1 1 1 1 2 ![1, 1] ![0, 1] ![1, 1] 1 0
    < thickLineIntensity 1 1 1 1 1 1 ![1, 1] ![0, 1] ![1, 1] 1 0 := by
  have hg : ∀ k : Fin 2, (0 : ℝ) < ![1, 1] k := by intro k; fin_cases k <;> norm_num
  exact thickLineIntensity_strictAntiOn_ell hg one_pos one_pos hg one_pos 1 0
    (Set.mem_Ioi.mpr one_pos) (Set.mem_Ioi.mpr (by norm_num)) (by norm_num)
