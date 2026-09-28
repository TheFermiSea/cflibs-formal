import Mathlib
import CflibsFormal.AtomicDataPerturbation

open Finset CflibsFormal

-- hA is implied by hg, hg', hA', hδ0, hδ1 and hpert (per species).
example {ι : Type*} [Fintype ι] [Nonempty ι] {kB T δ : ℝ} {g E A g' E' A' : ι → ℝ} {u : ι}
    (hg : ∀ k, 0 < g k) (hg' : ∀ k, 0 < g' k) (hA' : 0 < A' u) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hpert : |responseFactor kB T g' E' A' u - responseFactor kB T g E A u|
              ≤ δ * responseFactor kB T g E A u) : 0 < A u := by
  have hρ' : 0 < responseFactor kB T g' E' A' u := by
    unfold responseFactor
    exact div_pos (mul_pos (mul_pos (hg' u) hA') (boltzmannFactor_pos _ _ _))
      (partitionFunction_pos hg')
  have hρ : 0 < responseFactor kB T g E A u := by
    have := (abs_le.mp hpert).2
    nlinarith
  unfold responseFactor at hρ
  have hU := partitionFunction_pos (kB := kB) (T := T) (E := E) hg
  have hb := boltzmannFactor_pos kB T (E u)
  have h1 : 0 < g u * A u * boltzmannFactor kB T (E u) := by
    by_contra h
    push Not at h
    have : g u * A u * boltzmannFactor kB T (E u) / partitionFunction kB T g E ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg h hU.le
    linarith
  have h2 : 0 < g u * A u := pos_of_mul_pos_left h1 hb.le
  exact pos_of_mul_pos_right h2 (hg u).le
