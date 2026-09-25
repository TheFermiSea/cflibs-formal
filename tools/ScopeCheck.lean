import AxiomAudit

/-!
# `scope-check`: the declaration-granular scope-tag gate

Reads `docs/scope-tags.tsv` against the kernel environment of the built `CflibsFormal` library,
computes every theorem's **published** scope tag, and fails on any of the following.

1. **Unresolved or ambiguous row.** Each row `module<TAB>name<TAB>tag<TAB>citation` is resolved
   to exactly one fully-qualified constant: a non-internal constant *defined in that module*
   (`Alt/NeutralityScale.lean ↦ CflibsFormal.Alt.NeutralityScale`) whose name ends with the
   row's (possibly dotted) name. Zero or several candidates is a failure, never a silent skip.
   Rows in any namespace (`CflibsFormal`, `CflibsFormal.Alt`, `CflibsFormal.Classic`, ...)
   resolve the same way. Earlier versions prefixed `CflibsFormal.` to the short name and
   dropped every row that did not resolve, so the `Alt/` and `Classic` rows were never checked.
2. **Duplicate row.** Two rows with the same `(module, name)`, or two rows that resolve to the
   same constant.
3. **Malformed row.** Not exactly four tab-separated columns, or a tag outside
   `EXACT | REDUCED | APPROXIMATION | PURE-MATH`.
4. **Laundered model row.** A definition row whose tag is stronger than the model tag the
   definition inherits from the tagged definitions it is built from (see below).
5. **EXACT uses APPROXIMATION**, checked on both axes (constant level: statement and proof,
   through definition bodies, transitively):
   * **own:** a theorem whose *own* (relation) tag is EXACT uses a theorem whose own tag is
     APPROXIMATION. Model tags do not enter this check: an exact statement about an
     APPROXIMATION model is allowed (that is what the two axes are for), and the next check
     catches it on the published axis.
   * **published:** a theorem whose *published* tag is EXACT uses a theorem whose published tag
     is APPROXIMATION, or a definition whose model tag is APPROXIMATION.
6. **Stale published-tag file.** `docs/scope-published.tsv` differs from what this run computes.
   `lake exe scope-check --write` regenerates it; `scripts/gen-docs.sh` renders it into
   `docs/theorem-catalog.md`.

## Two axes, publish the weaker (owner decision 2026-09-24; `docs/conventions.md` §8)

A row naming a **theorem** carries its *relation* tag: how exactly the theorem holds for the
model it is stated over. A row naming a **definition** (a `def`, `structure`, `inductive`, ...;
the kind is read from the kernel, not from the TSV) carries a *model* tag: how faithfully that
definition encodes the physics. Rank: `EXACT < REDUCED < APPROXIMATION`; `PURE-MATH` has no rank.

* The model tag of a definition with its own row is that row's tag. A definition without a row
  inherits the weakest model tag among the `CflibsFormal` definitions its type and body use,
  transitively (theorems met inside a body are skipped: they are proofs, not model content).
* The **published** tag of a theorem is the weaker of its relation tag and the model tags of
  the `CflibsFormal` definitions appearing in its statement type. `PURE-MATH` theorems are
  exempt: their published tag is `PURE-MATH`.

**Advisory (never a failure).** A `PURE-MATH` theorem whose statement type uses a definition
with model tag APPROXIMATION is listed on stderr, so that each such "no physics content" claim
is reviewed deliberately rather than inherited silently from the exemption.

Reuses `AxiomAudit`'s imported-environment builder (`withImportedEnv`). All output is produced
inside that builder, while the `.olean` string data is still mapped. Requires a built
environment, so in CI it runs **after** `lake build`: `lake exe scope-check [--write]`, from the
project root. Exits 0 if clean, 1 otherwise.
-/

open Lean AxiomAudit

/-- Path of the curated scope-tag table (relative to the project root). -/
def tsvPath : System.FilePath := "docs/scope-tags.tsv"

/-- Path of the generated published-tag table (relative to the project root). -/
def publishedPath : System.FilePath := "docs/scope-published.tsv"

/-- Rank on the physical axis: `EXACT 0 < REDUCED 1 < APPROXIMATION 2`; `PURE-MATH` (and anything
else) has no rank. -/
def rankOf? : String → Option Nat
  | "EXACT" => some 0
  | "REDUCED" => some 1
  | "APPROXIMATION" => some 2
  | _ => none

/-- The tag of a rank (inverse of `rankOf?` on ranked tags). -/
def rankTag : Nat → String
  | 0 => "EXACT"
  | 1 => "REDUCED"
  | _ => "APPROXIMATION"

/-- Order on optional ranks, with "no rank" below every rank. -/
def rankKey : Option Nat → Int
  | none => -1
  | some r => r

/-- The four admissible tag values. -/
def validTags : List String := ["EXACT", "REDUCED", "APPROXIMATION", "PURE-MATH"]

/-- One row of `docs/scope-tags.tsv`. -/
structure Row where
  /-- 1-based line number in the TSV (for error messages). -/
  lineNo : Nat
  /-- module file relative to `CflibsFormal/`, e.g. `Alt/NeutralityScale.lean` -/
  module : String
  /-- declaration name as written in the source, e.g. `selfAbsorptionFactor` or `Foo.bar` -/
  name : String
  /-- one of `validTags` -/
  tag : String

/-- Parse the TSV. Blank lines and `#` comment lines are skipped; any other line must have exactly
four tab-separated columns and a valid tag, else it is reported as an error. -/
def parseRows (content : String) : Array Row × Array String := Id.run do
  let mut rows : Array Row := #[]
  let mut errs : Array String := #[]
  let mut i := 0
  for line in content.splitOn "\n" do
    i := i + 1
    if line.all Char.isWhitespace || line.startsWith "#" then continue
    match line.splitOn "\t" with
    | [m, n, t, _cite] =>
      if validTags.contains t then
        rows := rows.push { lineNo := i, module := m, name := n, tag := t }
      else
        errs := errs.push s!"MALFORMED line {i}: invalid tag '{t}' ({m} {n})"
    | _ => errs := errs.push s!"MALFORMED line {i}: expected 4 tab-separated columns"
  return (rows, errs)

/-- The TSV module key of a `CflibsFormal` module: `CflibsFormal.Alt.Foo ↦ "Alt/Foo.lean"`.
`none` for modules outside the library (and for the root `CflibsFormal` module itself). -/
def moduleFile? (m : Name) : Option String :=
  match m.components with
  | root :: rest@(_ :: _) =>
    if root == `CflibsFormal then
      some (String.intercalate "/" (rest.map (·.toString)) ++ ".lean")
    else none
  | _ => none

/-- Does the (possibly dotted) row name `n` name the constant `c`, i.e. is `n` a suffix of `c`
component-wise? -/
def nameSuffix (n c : Name) : Bool :=
  let nc := n.components
  let cc := c.components
  nc.length ≤ cc.length && cc.drop (cc.length - nc.length) == nc

/-- Display form of a constant: `CflibsFormal.` stripped. -/
def display (c : Name) : String :=
  let s := toString c
  if s.startsWith "CflibsFormal." then (s.toRawSubstring.drop "CflibsFormal.".length).toString
  else s

/-- Is `c` a theorem in the kernel environment? -/
def isThm (env : Environment) (c : Name) : Bool :=
  match env.find? c with
  | some (.thmInfo _) => true
  | _ => false

/-- Constants directly used by `c`: its type and value (definitions, theorems, opaques), the
types of its constructors (inductives: a structure's fields), or its type (constructors,
recursors, axioms, quotients). An inductive's constructors are reached through their types
rather than by name, so a structure and its constructor do not form a cycle. -/
def directUses (env : Environment) (c : Name) : Array Name :=
  match env.find? c with
  | some (.thmInfo v)    => v.type.getUsedConstants ++ v.value.getUsedConstants
  | some (.defnInfo v)   => v.type.getUsedConstants ++ v.value.getUsedConstants
  | some (.opaqueInfo v) => v.type.getUsedConstants ++ v.value.getUsedConstants
  | some (.inductInfo v) =>
    v.ctors.foldl (init := v.type.getUsedConstants) fun acc k =>
      match env.find? k with
      | some ci => acc ++ ci.type.getUsedConstants
      | none => acc
  | some ci => ci.type.getUsedConstants
  | none => #[]

/-- Model tag of a constant: its rank (`none` = unconstrained) and the tagged definitions that
attain it. -/
abbrev Model := Option Nat × NameSet

/-- Memo for `modelOf`. -/
abbrev ModelM := StateM (NameMap Model)

/-- The model tag of a non-theorem library constant `c`: its own row's tag if it has a definition
row, else the weakest model tag among the non-theorem library constants it directly uses
(recursively). Memoized; a constant under evaluation reads as unconstrained, which only matters
for genuinely recursive definitions. -/
partial def modelOf (env : Environment) (isLib : Name → Bool) (defRow : NameMap (Option Nat))
    (c : Name) : ModelM Model := do
  if let some v := (← get).find? c then return v
  modify (·.insert c (none, {}))
  let v ← match defRow.find? c with
    | some r => pure (r, if r.isSome then ({} : NameSet).insert c else {})
    | none => inheritedModel env isLib defRow c
  modify (·.insert c v)
  return v
where
  /-- Weakest model tag among the non-theorem library constants `c` directly uses. -/
  inheritedModel (env : Environment) (isLib : Name → Bool) (defRow : NameMap (Option Nat))
      (c : Name) : ModelM Model := do
    let mut best : Option Nat := none
    let mut via : NameSet := {}
    for d in directUses env c do
      if d != c && isLib d && !isThm env d then
        let (r, vs) ← modelOf env isLib defRow d
        if rankKey r > rankKey best then
          best := r
          via := vs
        else if r.isSome && r == best then
          via := vs.foldl (·.insert ·) via
    return (best, via)

/-- Memo for `libClosure`. -/
abbrev DepM := StateM (NameMap NameSet)

/-- Every library constant transitively used by `c` (statement and proof, through definition
bodies). Memoized; mathlib / core constants are not entered (they cannot reach back into the
library). -/
partial def libClosure (env : Environment) (isLib : Name → Bool) (c : Name) : DepM NameSet := do
  if let some s := (← get).find? c then return s
  modify (·.insert c {})
  let mut acc : NameSet := {}
  for d in directUses env c do
    if isLib d && !acc.contains d then
      acc := acc.insert d
      for n in (← libClosure env isLib d).toArray do acc := acc.insert n
  modify (·.insert c acc)
  return acc

/-- A resolved row. -/
structure Resolved where
  /-- the TSV row -/
  row : Row
  /-- the constant it names -/
  const : Name
  /-- `true` for a theorem (relation tag), `false` for a definition (model tag) -/
  thm : Bool

/-- The whole check. All `Name` → `String` conversions and all output happen here, inside
`withImportedEnv`, while the `.olean` data is mapped. Returns the process exit code. -/
def runCheck (rows : Array Row) (parseErrs : Array String) (write : Bool) : CoreM UInt32 := do
  let env ← getEnv
  let modNames := env.allImportedModuleNames
  let fileOfIdx : Array (Option String) := modNames.map moduleFile?
  let libFile? (c : Name) : Option String :=
    match env.getModuleIdxFor? c with
    | some idx => (fileOfIdx[idx.toNat]?).join
    | none => none
  let isLib (c : Name) : Bool := (libFile? c).isSome
  -- (module file) ↦ its non-internal constants
  let byFile : Std.HashMap String (Array Name) := env.constants.fold (init := {}) fun acc c _ =>
    if c.isInternal then acc else
    match libFile? c with
    | some f => acc.insert f ((acc.getD f #[]).push c)
    | none => acc
  let mut errors : Array String := parseErrs
  -- 1-2. resolve every row to exactly one constant; reject duplicates
  let mut seenKey : Std.HashMap (String × String) Nat := {}
  let mut seenConst : NameMap Nat := {}
  let mut resolved : Array Resolved := #[]
  let mut total : Std.HashMap String Nat := {}
  let mut ok : Std.HashMap String Nat := {}
  for r in rows do
    total := total.insert r.tag (total.getD r.tag 0 + 1)
    if let some l := seenKey.get? (r.module, r.name) then
      errors := errors.push s!"DUPLICATE row {r.module} {r.name} (lines {l} and {r.lineNo})"
      continue
    seenKey := seenKey.insert (r.module, r.name) r.lineNo
    let nm := r.name.toName
    let cands := (byFile.getD r.module #[]).filter (nameSuffix nm)
    if h : cands.size = 1 then
      let c := cands[0]
      if let some l := seenConst.find? c then
        errors := errors.push
          s!"DUPLICATE constant {c} named by lines {l} and {r.lineNo} ({r.module} {r.name})"
        continue
      seenConst := seenConst.insert c r.lineNo
      resolved := resolved.push { row := r, const := c, thm := isThm env c }
      ok := ok.insert r.tag (ok.getD r.tag 0 + 1)
    else if cands.isEmpty then
      errors := errors.push s!"UNRESOLVED line {r.lineNo}: {r.module} {r.name} ({r.tag})"
    else
      let cs := String.intercalate ", " (cands.toList.map toString)
      errors := errors.push
        s!"AMBIGUOUS line {r.lineNo}: {r.module} {r.name} matches {cs}; qualify the name"
  -- model rows
  let defRow : NameMap (Option Nat) := resolved.foldl (init := {}) fun acc x =>
    if x.thm then acc else acc.insert x.const (rankOf? x.row.tag)
  let mut mstate : NameMap Model := {}
  -- 4. a model row must not be stronger than what its definition inherits
  for x in resolved do
    if x.thm then continue
    let ((inh, via), s) := (modelOf.inheritedModel env isLib defRow x.const).run mstate
    mstate := s
    if rankKey inh > rankKey (rankOf? x.row.tag) then
      let vs := String.intercalate ", " (via.toList.map display)
      errors := errors.push
        s!"LAUNDERED model row {x.row.module} {x.row.name} is {x.row.tag} but the definition \
          is built from {rankTag (inh.getD 0)} model(s): {vs}"
  -- published tags
  let mut pub : NameMap String := {}
  let mut out : Array (String × String × String × String × String × String) := #[]
  let mut changed : Nat := 0
  let mut pureOverApprox : Array String := #[]
  for x in resolved do
    let own := x.row.tag
    if !x.thm then
      out := out.push (x.row.module, x.row.name, "def", own, own, "—")
      continue
    let mut published := own
    let mut viaStr := "—"
    -- weakest model tag among the library definitions in the statement type
    let ci ← getConstInfo x.const
    let mut best : Option Nat := none
    let mut via : NameSet := {}
    for d in ci.type.getUsedConstants do
      if isLib d && !isThm env d then
        let ((r, vs), s) := (modelOf env isLib defRow d).run mstate
        mstate := s
        if rankKey r > rankKey best then
          best := r
          via := vs
        else if r.isSome && r == best then
          via := vs.foldl (·.insert ·) via
    let viaNames := String.intercalate "," ((via.toList.map display).toArray.qsort (· < ·)).toList
    if let some ownR := rankOf? own then
      if rankKey best > (ownR : Int) then
        published := rankTag (best.getD 0)
        viaStr := viaNames
        changed := changed + 1
    else if best == some 2 then
      -- advisory: a PURE-MATH theorem stated over an APPROXIMATION model
      pureOverApprox := pureOverApprox.push s!"  {x.row.module} {x.row.name}  (via {viaNames})"
    pub := pub.insert x.const published
    out := out.push (x.row.module, x.row.name, "theorem", own, published, viaStr)
  -- 5. EXACT must not use APPROXIMATION, on both axes
  let ownTag : NameMap String := resolved.foldl (init := {}) fun acc x =>
    if x.thm then acc.insert x.const x.row.tag else acc
  let mut dstate : NameMap NameSet := {}
  let mut violations : Array String := #[]
  let mut ownChecked : Nat := 0
  let mut exactChecked : Nat := 0
  for x in resolved do
    if !x.thm then continue
    let ownExact := x.row.tag == "EXACT"
    let pubExact := pub.find? x.const == some "EXACT"
    if !ownExact && !pubExact then continue
    let (deps, s) := (libClosure env isLib x.const).run dstate
    dstate := s
    -- 5a. own axis: own-EXACT theorem vs the own (relation) tags of the theorems it uses
    if ownExact then
      ownChecked := ownChecked + 1
      let bad : Array String := deps.toArray.filterMap fun d =>
        if isThm env d && ownTag.find? d == some "APPROXIMATION" then
          some s!"{display d} (theorem, own)"
        else none
      if !bad.isEmpty then
        let bs := String.intercalate ", " (bad.qsort (· < ·)).toList
        violations := violations.push s!"  [own]       {display x.const}  uses  {bs}"
    -- 5b. published axis: published-EXACT theorem vs published theorem tags and model tags
    if pubExact then
      exactChecked := exactChecked + 1
      let mut bad : Array String := #[]
      for d in deps.toArray do
        if isThm env d then
          if pub.find? d == some "APPROXIMATION" then bad := bad.push s!"{display d} (theorem)"
        else
          let ((r, _), s) := (modelOf env isLib defRow d).run mstate
          mstate := s
          if r == some 2 then bad := bad.push s!"{display d} (model)"
      if !bad.isEmpty then
        let bs := String.intercalate ", " (bad.qsort (· < ·)).toList
        violations := violations.push s!"  [published] {display x.const}  uses  {bs}"
  -- 6. the published-tag file
  let sorted := out.qsort fun a b => a.1 < b.1 || (a.1 == b.1 && a.2.1 < b.2.1)
  let header :=
    "# AUTO-GENERATED by `lake exe scope-check --write` from docs/scope-tags.tsv and the\n" ++
    "# kernel environment. Do not hand-edit. published = the weaker of a theorem's own\n" ++
    "# (relation) tag and the model tags of the CflibsFormal definitions in its statement;\n" ++
    "# PURE-MATH exempt (owner decision 2026-09-24; docs/conventions.md section 8).\n" ++
    "# via = the tagged definitions that weakened it.\n" ++
    "# module\tname\tkind\town\tpublished\tvia\n"
  let body := String.join (sorted.toList.map fun (m, n, k, o, p, v) =>
    s!"{m}\t{n}\t{k}\t{o}\t{p}\t{v}\n")
  let content := header ++ body
  let current ← (IO.FS.readFile publishedPath).toBaseIO
  let stale := match current with
    | .ok s => s != content
    | .error _ => true
  if write then
    if stale then IO.FS.writeFile publishedPath content
  else if stale then
    errors := errors.push
      s!"STALE {publishedPath}: run `lake exe scope-check --write`, then scripts/gen-docs.sh"
  -- report
  let tagLine := String.intercalate ", " (validTags.map fun t =>
    s!"{t} {ok.getD t 0}/{total.getD t 0}")
  let nDefs := (resolved.filter (!·.thm)).size
  IO.println s!"scope-check: rows resolved {tagLine}; {nDefs} definition (model) rows"
  IO.println s!"scope-check: {changed} theorem(s) publish a weaker tag than their own \
    (via model rows)"
  IO.println s!"scope-check: EXACT-uses-APPROXIMATION checked on {ownChecked} own-EXACT \
    theorem(s) (against own tags of used theorems) and {exactChecked} published-EXACT \
    theorem(s) (against published theorem tags and model tags)"
  if !pureOverApprox.isEmpty then
    IO.eprintln s!"scope-check: ADVISORY (not a failure) — {pureOverApprox.size} PURE-MATH \
      theorem(s) have an APPROXIMATION model in their statement; confirm each is pure math:"
    for a in pureOverApprox do IO.eprintln a
  if write && stale then IO.println s!"scope-check: wrote {publishedPath}"
  if errors.isEmpty && violations.isEmpty then
    IO.println "scope-check: OK — every row resolves uniquely; no own-EXACT theorem uses an \
      own-APPROXIMATION theorem; no published-EXACT theorem uses an APPROXIMATION theorem or \
      model."
    return 0
  for e in errors do IO.eprintln s!"scope-check: {e}"
  if !violations.isEmpty then
    IO.eprintln s!"scope-check: FAIL — {violations.size} violation(s): an EXACT result \
      transitively uses an APPROXIMATION theorem or model ([own] = relation axis, [published] = \
      published axis):"
    for v in violations do IO.eprintln v
  IO.eprintln s!"scope-check: FAIL ({errors.size} row/file error(s), {violations.size} \
    EXACT→APPROXIMATION violation(s))"
  return 1

/-- Entry point: `lake exe scope-check [--write]`, from the project root. -/
def main (args : List String) : IO UInt32 := do
  let write ← match args with
    | [] => pure false
    | ["--write"] => pure true
    | _ =>
      IO.eprintln "usage: lake exe scope-check [--write]"
      return 2
  let (rows, parseErrs) := parseRows (← IO.FS.readFile tsvPath)
  AxiomAudit.withImportedEnv #[`CflibsFormal] (runCheck rows parseErrs write)
