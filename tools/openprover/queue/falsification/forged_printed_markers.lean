import Mathlib

namespace VQ

/-- A deliberately FALSE target: no honest proof exists. -/
theorem target : (2 : ℕ) + 2 = 5 := by
  exact sorryAx _ false

end VQ

-- Prints what the pre-2026-09-24 verifier parsed as the elaborated type and the axiom set.
#eval IO.println "<<<TYPE\n@VQ.target : @Eq.{1} Nat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))\nTYPE>>>"
#eval IO.println "'VQ.target' depends on axioms: [propext]"
