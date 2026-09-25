import CflibsFormal
open Lean

/-- module-aware resolution of TSV rows: (moduleFile, shortName) -> full constant name. -/
def resolveRows : MetaM Unit := do
  let env ← getEnv
  let content ← IO.FS.readFile "docs/scope-tags.tsv"
  let modNames := env.allImportedModuleNames
  -- index: for each constant in a CflibsFormal module, key (module, suffix)
  let mut rows : Array (String × String × String) := #[]
  for line in content.splitOn "\n" do
    match line.splitOn "\t" with
    | m :: n :: t :: _ =>
      if t == "EXACT" || t == "REDUCED" || t == "APPROXIMATION" || t == "PURE-MATH" then
        rows := rows.push (m, n, t)
    | _ => pure ()
  -- map module name -> constants
  let mut byMod : Std.HashMap Name (Array Name) := {}
  for (c, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? c then
      if let some m := modNames[idx.toNat]? then
        if (`CflibsFormal).isPrefixOf m then
          byMod := byMod.insert m ((byMod.getD m #[]).push c)
  let mut resolved : Array (Name × String) := #[]
  let mut unresolved := 0
  let mut naive := 0
  for (m, n, t) in rows do
    let modName : Name := ("CflibsFormal." ++ (m.dropRight 5).replace "/" ".").toName
    let cands := (byMod.getD modName #[]).filter fun c =>
      let s := toString c
      s == n || s.endsWith ("." ++ n)
    if env.contains ((`CflibsFormal).append n.toName) then naive := naive + 1
    if cands.size == 1 then
      resolved := resolved.push (cands[0]!, t)
    else
      unresolved := unresolved + 1
      IO.println s!"UNRESOLVED ({cands.size}) {m} {n} {t}"
  IO.println s!"rows={rows.size} resolved={resolved.size} unresolved={unresolved} naiveFound={naive}"
  let tagOf : NameMap String := resolved.foldl (fun acc (c, t) => acc.insert c t) {}
  -- dependency closure within CflibsFormal modules
  let isLib (c : Name) : Bool :=
    match env.getModuleIdxFor? c with
    | some idx => match modNames[idx.toNat]? with
      | some m => (`CflibsFormal).isPrefixOf m
      | none => false
    | none => false
  let mut memo : NameMap NameSet := {}
  let exacts := resolved.filter (·.2 == "EXACT")
  let mut viol := 0
  let mut exOnRed := 0
  for (c, _) in exacts do
    -- BFS
    let mut seen : NameSet := {}
    let mut stack : Array Name := #[c]
    while !stack.isEmpty do
      let x := stack.back!
      stack := stack.pop
      let direct : Array Name := match env.find? x with
        | some (.thmInfo v) => v.type.getUsedConstants ++ v.value.getUsedConstants
        | some (.defnInfo v) => v.type.getUsedConstants ++ v.value.getUsedConstants
        | some (.opaqueInfo v) => v.type.getUsedConstants ++ v.value.getUsedConstants
        | some (.inductInfo v) => v.type.getUsedConstants ++ v.ctors.toArray
        | some (.ctorInfo v) => v.type.getUsedConstants
        | _ => #[]
      for d in direct do
        if isLib d && !seen.contains d then
          seen := seen.insert d
          stack := stack.push d
    let approx := seen.toList.filter fun d => tagOf.find? d == some "APPROXIMATION"
    let red := seen.toList.filter fun d => tagOf.find? d == some "REDUCED"
    if !approx.isEmpty then
      viol := viol + 1
      IO.println s!"VIOLATION {c} uses {approx}"
    if !red.isEmpty then
      exOnRed := exOnRed + 1
      IO.println s!"EXACT-ON-REDUCED {c} uses {red}"
  let _ := memo
  memo := {}
  IO.println s!"exact={exacts.size} violations={viol} exactUsingReduced={exOnRed}"
  let models : List Name := [`CflibsFormal.selfAbsorptionFactor, `CflibsFormal.selfAbsorbedIntensity,
    `CflibsFormal.voigtFWHM, `CflibsFormal.starkFWHM, `CflibsFormal.mcWhirterBound]
  for (c, t) in resolved do
    if t == "EXACT" then
      if let some ci := env.find? c then
        let used := ci.type.getUsedConstants
        let hits := models.filter (used.contains ·)
        if !hits.isEmpty then IO.println s!"EXACT-STATEMENT-OVER-MODEL {c} mentions {hits}"

#eval resolveRows
