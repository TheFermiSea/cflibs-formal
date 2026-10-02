import Mathlib

open Filter Topology

namespace Plan.FT01


/-- Krasnoselskii–Mann damped map `u ↦ (1−λ)u + λ g(u)` (the pipeline uses `λ = 1/2`). -/
def dampedMap (lam : ℝ) (g : ℝ → ℝ) (u : ℝ) : ℝ := (1 - lam) * u + lam * g u

theorem tDamped_mobius_converges {g c lam : ℝ} (hg0 : 0 < g) (hg1 : g < 1) (hc : 0 < c)
    (hl0 : 0 < lam) (hl1 : lam ≤ 1) (T0 : ℝ) (hT0 : 0 < T0) :
    Tendsto (fun n => (dampedMap lam (fun T => T / (g + c * T)))^[n] T0) atTop
      (𝓝 ((1 - g) / c)) := by
  sorry

end Plan.FT01
