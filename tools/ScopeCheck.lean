import AxiomAudit

/-!
# `scope-check`: a declaration-granularity epistemic-drift guard

Fails if any **EXACT**-tagged declaration in `docs/scope-tags.tsv` transitively *uses* (at the
constant level, via the kernel environment) a declaration tagged **APPROXIMATION** — i.e. an
"exact" physical claim that actually rests on a documented idealization.

This is the declaration-granular strengthening of `scripts/check-scope-consistency.sh`, whose
module-level *import* check is gameable: an APPROXIMATION result hidden inside a module that also
exports an EXACT one takes the script's advisory WARN branch and never FAILs, and a module-level
edge produces false positives (an EXACT result that only uses the module's EXACT parts). Working
on the actual per-declaration constant-use graph removes both.

Reuses `AxiomAudit`'s imported-environment builder (`withImportedEnv`) and heap-owned-string
helper (`freshStr`). Requires a built environment, so it is a CI step **after** `lake build`:
`lake exe scope-check` (run from the project root). Exits 0 if clean, 1 on a violation.
-/

open Lean AxiomAudit

/-- Is `c` a declaration of the `CflibsFormal` library? (mathlib / core are upstream.) -/
def isCflibs (c : Name) : Bool := (`CflibsFormal).isPrefixOf c

/-- The short (TSV) name of a `CflibsFormal` declaration: `CflibsFormal.foo ↦ "foo"`. -/
def shortName (c : Name) : String :=
  let s := toString c
  if s.startsWith "CflibsFormal." then
    (s.toRawSubstring.drop "CflibsFormal.".length).toString
  else s

/-- Reader/State pass: read-only `Environment`, memoizing each constant's transitive
`CflibsFormal`-dependency set so the library subgraph is walked once in total. -/
abbrev DepM := ReaderT Environment (StateM (NameMap NameSet))

/-- The set of `CflibsFormal` declarations transitively used by `c` (memoized). Short-circuits on
non-`CflibsFormal` constants: mathlib / core cannot reach back into `CflibsFormal`, so their
`CflibsFormal`-dependency set is empty — the walk stays inside the library subgraph. -/
partial def cflibsDeps (c : Name) : DepM NameSet := do
  if !isCflibs c then return {}
  if let some s := (← get).find? c then return s
  modify (·.insert c {})
  let env ← read
  let direct : Array Name :=
    match env.find? c with
    | some (.thmInfo v)    => v.type.getUsedConstants ++ v.value.getUsedConstants
    | some (.defnInfo v)   => v.type.getUsedConstants ++ v.value.getUsedConstants
    | some (.opaqueInfo v) => v.type.getUsedConstants ++ v.value.getUsedConstants
    | some (.axiomInfo v)  => v.type.getUsedConstants
    | some (.ctorInfo v)   => v.type.getUsedConstants
    | some (.recInfo v)    => v.type.getUsedConstants
    | some (.inductInfo v) => v.type.getUsedConstants ++ v.ctors.toArray
    | _                    => #[]
  let mut acc : NameSet := {}
  for d in direct do
    if isCflibs d then
      acc := acc.insert d
      let sub ← cflibsDeps d
      for n in sub.toArray do acc := acc.insert n
  modify (·.insert c acc)
  return acc

/-- Parse `docs/scope-tags.tsv` into a short-name → tag map (canonical tags only). -/
def parseTags : IO (Std.TreeMap String String) := do
  let content ← IO.FS.readFile "docs/scope-tags.tsv"
  let mut m : Std.TreeMap String String := .empty
  for line in content.splitOn "\n" do
    match line.splitOn "\t" with
    | _ :: name :: t :: _ =>
      if t == "EXACT" || t == "REDUCED" || t == "APPROXIMATION" || t == "PURE-MATH" then
        m := m.insert name t
    | _ => pure ()
  return m

def main : IO UInt32 := do
  let tag ← parseTags
  let exactNames : Array String :=
    (tag.toList.filterMap (fun (n, t) => if t == "EXACT" then some n else none)).toArray
  let (fails, checked) ← AxiomAudit.withImportedEnv #[`CflibsFormal] do
    let env ← getEnv
    let exactDecls : Array Name := exactNames.filterMap fun s =>
      let nm := (`CflibsFormal).append s.toName
      if env.contains nm then some nm else none
    let perDecl : Array NameSet := (exactDecls.mapM cflibsDeps |>.run env).run' {}
    let mut fails : Array (String × Array String) := #[]
    for i in [0:exactDecls.size] do
      let approx : Array String := perDecl[i]!.toArray.filterMap fun d =>
        if tag.get? (shortName d) == some "APPROXIMATION" then some (freshStr d) else none
      if !approx.isEmpty then
        fails := fails.push (freshStr exactDecls[i]!, approx)
    return (fails, exactDecls.size)
  if fails.isEmpty then
    IO.println
      s!"scope-check: OK — {checked} EXACT results checked (declaration-granular); none uses an APPROXIMATION-tagged declaration."
    return 0
  else
    IO.eprintln s!"scope-check: FAIL — {fails.size} EXACT result(s) transitively use an APPROXIMATION-tagged declaration:"
    for (d, aps) in fails do
      let apsStr := String.intercalate ", " aps.toList
      IO.eprintln s!"  {d}  uses  {apsStr}"
    return 1
