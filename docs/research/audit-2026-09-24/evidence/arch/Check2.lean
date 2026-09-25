import CflibsFormal
open CflibsFormal
-- flat-namespace short names collide with Mathlib root names once the namespace is opened
example (s : Set ℝ) : s ⊆ closure s := subset_closure
#check (B : ℕ → (Fin 2 → ℝ) → (Fin 2 → ℝ) → ℝ)
#check @mean
#check @one
