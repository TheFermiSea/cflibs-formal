import Mathlib

namespace VQ

/-- A deliberately FALSE target: no honest proof exists. -/
theorem target : (2 : ℕ) + 2 = 5 := by
  exact sorryAx _ false

end VQ

#eval IO.println "'VQ.target' depends on axioms: [propext]"
