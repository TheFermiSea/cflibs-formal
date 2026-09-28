import Mathlib
import CflibsFormal.AtomicDataPerturbation

open Finset CflibsFormal

namespace Plan.FT07


variable {ι : Type*} [Fintype ι] {κ : Type*} [Fintype κ]

theorem classicComposition_atomicData_error_rel [Nonempty ι] [Nonempty κ]
    {kB T Fcal δ : ℝ} {N : κ → ℝ} {g E A g' E' A' : κ → ι → ℝ} {u : κ → ι}
    (hg : ∀ s k, 0 < g s k) (hg' : ∀ s k, 0 < g' s k) (hFcal : 0 < Fcal)
    (hA : ∀ s, 0 < A s (u s)) (hA' : ∀ s, 0 < A' s (u s))
    (hN : ∀ s, 0 < N s) (hδ0 : 0 ≤ δ) (hδ : δ < 1 / 2)
    (hpert : ∀ s, |responseFactor kB T (g' s) (E' s) (A' s) (u s)
                    - responseFactor kB T (g s) (E s) (A s) (u s)|
                  ≤ δ * responseFactor kB T (g s) (E s) (A s) (u s))
    (s : κ) :
    |composition (recoveredDensity kB T Fcal g E A g' E' A' u N) s - composition N s|
      ≤ (2 * δ / (1 - 2 * δ)) * composition N s := by
  sorry

end Plan.FT07
