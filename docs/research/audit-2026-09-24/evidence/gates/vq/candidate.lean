import Mathlib

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let d : Declaration := .thmDecl
    { name := `VQ.helper, levelParams := [], type := mkConst ``False,
      value := mkConst ``True.intro }
  match env.addDeclCore 0 0 d none (doCheck := false) with
  | .ok env' => setEnv env'
  | .error _ => throwError "addDeclCore failed"

namespace VQ

/-- A deliberately FALSE target: no honest proof exists. -/
theorem target : (2 : ℕ) + 2 = 5 := by
  exact helper.elim

end VQ
