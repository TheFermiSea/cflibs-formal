import CflibsFormal
open Lean Elab Command

def isC (c : Name) : Bool := (`CflibsFormal).isPrefixOf c
def short (c : Name) : String :=
  let s := toString c
  let s := if s.startsWith "CflibsFormal.Alt." then (s.drop "CflibsFormal.Alt.".length).toString
    else if s.startsWith "CflibsFormal.Classic." then (s.drop "CflibsFormal.Classic.".length).toString
    else if s.startsWith "CflibsFormal." then (s.drop "CflibsFormal.".length).toString else s
  s

partial def deps (env : Environment) (c : Name) (seen : NameSet) : NameSet := Id.run do
  let direct : Array Name := match env.find? c with
    | some (.thmInfo v) => v.type.getUsedConstants ++ v.value.getUsedConstants
    | some (.defnInfo v) => v.type.getUsedConstants ++ v.value.getUsedConstants
    | _ => #[]
  let mut acc := seen
  for d in direct do
    if isC d && !acc.contains d then
      acc := deps env d (acc.insert d)
  return acc

elab "#scopefix" : command => do
  let env ← getEnv
  let content ← IO.FS.readFile "docs/scope-tags.tsv"
  let mut tag : Std.HashMap String String := {}
  let mut rows : Array (String × String) := #[]
  for line in content.splitOn "\n" do
    match line.splitOn "\t" with
    | _ :: n :: t :: _ => tag := tag.insert n t; rows := rows.push (n, t)
    | _ => pure ()
  let mut resolved : Nat := 0
  let mut unresolved : Array String := #[]
  let mut viol : Array String := #[]
  let mut exactOnReduced : Nat := 0
  let mut typeLI : Array String := #[]
  let mut typePP : Array String := #[]
  for (n, t) in rows do
    if t != "EXACT" then continue
    let cands := [(`CflibsFormal).append n.toName, (`CflibsFormal.Alt).append n.toName,
                  (`CflibsFormal.Classic).append n.toName]
    match cands.find? env.contains with
    | none => unresolved := unresolved.push n
    | some nm =>
      resolved := resolved + 1
      let ds := deps env nm {}
      let aps := ds.toArray.filter fun d => tag.get? (short d) == some "APPROXIMATION"
      if !aps.isEmpty then viol := viol.push s!"{nm} uses {aps.toList}"
      match env.find? nm with
      | some ci =>
        let tys := ci.type.getUsedConstants
        if tys.contains `CflibsFormal.lineIntensity then typeLI := typeLI.push n
        if tys.contains `CflibsFormal.PlasmaParams then typePP := typePP.push n
      | none => pure ()
      if ds.toArray.any (fun d => tag.get? (short d) == some "REDUCED") then
        exactOnReduced := exactOnReduced + 1
  logInfo s!"resolved EXACT: {resolved}; unresolved: {unresolved}; EXACT->APPROX violations: {viol.size}\n{viol}\nEXACT results transitively using a REDUCED-tagged decl: {exactOnReduced}\nEXACT whose STATEMENT mentions lineIntensity ({typeLI.size}): {typeLI}\nEXACT whose statement mentions PlasmaParams ({typePP.size}): {typePP}"

#scopefix
