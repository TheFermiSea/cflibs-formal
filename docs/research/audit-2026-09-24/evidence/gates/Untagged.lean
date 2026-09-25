import CflibsFormal
open Lean

def findUntagged : MetaM Unit := do
  let env ← getEnv
  let content ← IO.FS.readFile "docs/scope-tags.tsv"
  let modNames := env.allImportedModuleNames
  let mut tagged : Std.HashSet (Name × String) := {}
  for line in content.splitOn "\n" do
    match line.splitOn "\t" with
    | m :: n :: _ :: _ =>
      if m.endsWith ".lean" then
        let modName : Name := ("CflibsFormal." ++ ((m.dropEnd 5).toString).replace "/" ".").toName
        tagged := tagged.insert (modName, n)
    | _ => pure ()
  let mut count := 0
  let mut total := 0
  for (c, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? c | continue
    let some m := modNames[idx.toNat]? | continue
    unless (`CflibsFormal).isPrefixOf m do continue
    unless info matches .thmInfo _ do continue
    if c.isInternalDetail then continue
    if isPrivateName c then continue
    let s := toString c
    -- skip auto-generated equation / structure lemmas
    if s.endsWith ".eq_1" || s.endsWith ".eq_def" || (s.splitOn ".eq_").length > 1 then continue
    if (s.splitOn "._").length > 1 then continue
    total := total + 1
    -- tagged if some suffix of the name matches a row for this module
    let parts := c.componentsRev
    let mut found := false
    for k in [1:parts.length+1] do
      let suf := String.intercalate "." ((parts.take k).reverse.map toString)
      if tagged.contains (m, suf) then found := true
    unless found do
      count := count + 1
      IO.println s!"UNTAGGED public theorem: {m} :: {c}"
  IO.println s!"public theorems={total} untagged={count}"

#eval findUntagged
