import Lean

/-!
# `export-catalog`: the machine-readable declaration catalog

Writes `docs/catalog.jsonl` from the kernel environment of the built `CflibsFormal` library: one
JSON object per line for every documented theorem and definition, so that the generated docs and
the theorem cards take statements, source lines, binders and axioms from Lean rather than from
hand-typed copies.

## Which declarations

Every constant that is (a) in the `CflibsFormal` namespace (including `CflibsFormal.Alt` and any
other sub-namespace), (b) not internal (`Name.isInternal`: private names, `_proof_n`, ...),
(c) a theorem or a definition in the kernel (`thmInfo` / `defnInfo`), (d) has a source range and
(e) has a docstring. Clauses (d) and (e) drop compiler-generated companions (equation lemmas,
`match_n`, `sizeOf_spec`, structure `recOn` / `casesOn` / `noConfusion` / `ext`), which have no
hand-written source or no docstring.

## Record (keys in exactly this order)

* `name`: fully qualified Lean name.
* `kind`: `"theorem"` or `"def"`.
* `module`: dotted module name, e.g. `CflibsFormal.InhomogeneityBias`.
* `file`: repo-relative source path, e.g. `CflibsFormal/InhomogeneityBias.lean`.
* `line`: start line of the declaration's name (`selectionRange`), or `null`.
* `docstring`: the docstring, or `null`.
* `type`: the declaration type, pretty-printed with fixed options (`pp.fullNames`,
  `pp.numericTypes`, `pp.unicode.fun`, width 100) so the output does not depend on the caller.
* `binders`: names of the outermost `∀` binders, in order (`forallTelescope`, no unfolding). An
  anonymous or hygienic (inaccessible, e.g. the `a✝` of an arrow `P → Q` or an unnamed instance
  binder) name is `"_"`: its macro-scope suffix changes with unrelated edits earlier in the file,
  so it would make the statement hash unstable.
* `usedConstants`: the `CflibsFormal`-namespace constants in the type (not the proof), sorted,
  the declaration itself excluded.
* `axioms`: for a theorem, the sorted axioms it transitively depends on (`Lean.collectAxioms`);
  `[]` for a definition.

Lines are sorted by `name` (code-point order, as Python's `sorted`), UTF-8, one trailing newline.
Two runs on the same build are byte-identical; CI regenerates the file and `diff -u`s it against
the committed `docs/catalog.jsonl`.

The tool fails (exit 1) rather than emit a partial record: a type that does not pretty-print, a
declaration whose module is unknown, or an empty catalog.

## Why not `AxiomAudit.withImportedEnv`

`axiom-audit` and `scope-check` build their environment with `Lean.withImportModules`, which never
loads environment-extension state. That is enough for walking constants, but not here: without
extension state no Mathlib (or core `notation`) delaborator or unexpander is registered, so `type`
would print `Real.instLT.lt (0 : Real) x` instead of `0 < x`, and `collectAxioms` loses the
per-module precomputed axiom table and re-walks every proof's full dependency closure (about 40
times slower). So this tool imports the way `runLinter` does: `enableInitializersExecution`, then
`importModules (loadExts := true)`. The environment is never freed (the process exits instead),
so no `.olean` string outlives its mapping.

Run from the project root after `lake build`: `lake exe export-catalog > docs/catalog.jsonl`. A
one-line summary goes to stderr.
-/

open Lean Meta

namespace ExportCatalog

/-- Page width for the pretty-printed `type`. -/
def ppWidth : Nat := 100

/-- The fixed pretty-printer options every `type` is printed with. -/
def ppOptions (o : Options) : Options :=
  let o := o.setBool `pp.fullNames true
  let o := o.setBool `pp.numericTypes true
  let o := o.setBool `pp.unicode.fun true
  o.set `format.width ppWidth

/-- Is `n` in the catalogued namespace (`CflibsFormal` or below)? -/
def inNamespace (n : Name) : Bool := (`CflibsFormal).isPrefixOf n

/-- Repo-relative source path of a module: `CflibsFormal.Alt.Foo ↦ CflibsFormal/Alt/Foo.lean`. -/
def moduleFile (m : Name) : String :=
  String.intercalate "/" (m.components.map (·.toString)) ++ ".lean"

/-- A JSON string literal (quoted and escaped). -/
def jstr (s : String) : String := (Json.str s).compress

/-- A JSON array of strings. -/
def jstrs (xs : Array String) : String := "[" ++ ",".intercalate (xs.map jstr).toList ++ "]"

/-- One JSON object with the keys in the given order (`Json.compress` would sort them). -/
def jobj (fields : List (String × String)) : String :=
  "{" ++ ",".intercalate (fields.map fun (k, v) => jstr k ++ ":" ++ v) ++ "}"

/-- Display name of a binder: `"_"` for an anonymous or hygienic (inaccessible) name. -/
def binderName (n : Name) : String :=
  if n.isAnonymous || n.hasMacroScopes then "_" else toString n

/-- Names of the outermost `∀` binders of `type`, in order (no definitional unfolding). -/
def binders (type : Expr) : MetaM (Array String) :=
  forallTelescope type fun xs _ =>
    xs.mapM fun x => return binderName (← x.fvarId!.getDecl).userName

/-- The catalogued `CflibsFormal` constants in `type`, sorted, `self` excluded. -/
def usedConstants (self : Name) (type : Expr) : Array String :=
  let names := type.getUsedConstants.filter fun c => inNamespace c && c != self
  let set : NameSet := names.foldl (·.insert ·) {}
  (set.toArray.map toString).qsort (· < ·)

/-- The JSON line for one declaration, or an error message. -/
def record (name : Name) (ci : ConstantInfo) (kind : String) (mod : Name) (line : Nat)
    (doc : String) : MetaM (Except String String) := withCurrHeartbeats do
  let type? ← try
      pure (some ((← ppExpr ci.type).pretty ppWidth))
    catch _ => pure none
  let some type := type? | return .error s!"{name}: its type does not pretty-print"
  let bs ← binders ci.type
  let axs ← if kind == "theorem" then collectAxioms name else pure #[]
  let axs := (axs.map toString).qsort (· < ·)
  return .ok <| jobj [
    ("name", jstr (toString name)),
    ("kind", jstr kind),
    ("module", jstr (toString mod)),
    ("file", jstr (moduleFile mod)),
    ("line", toString line),
    ("docstring", jstr doc),
    ("type", jstr type),
    ("binders", jstrs bs),
    ("usedConstants", jstrs (usedConstants name ci.type)),
    ("axioms", jstrs axs)]

/-- Build every record, sort by name, print the catalog to stdout and a summary to stderr.
Returns the process exit code. -/
def run (startMs : Nat) : CoreM UInt32 := withOptions ppOptions do
  let env ← getEnv
  let modNames := env.allImportedModuleNames
  let cands : Array (Name × ConstantInfo) := env.constants.fold (init := #[]) fun acc n ci =>
    if n.isInternal || !inNamespace n then acc
    else match ci with
      | .thmInfo _ | .defnInfo _ => acc.push (n, ci)
      | _ => acc
  let (lines, errs, thms) ← MetaM.run' do
    let mut lines : Array (String × String) := #[]
    let mut errs : Array String := #[]
    let mut thms := 0
    for (n, ci) in cands do
      let some range ← findDeclarationRanges? n | continue
      let some doc ← findDocString? env n | continue
      let kind := if ci matches .thmInfo _ then "theorem" else "def"
      let some mod := (env.getModuleIdxFor? n).bind (modNames[·.toNat]?)
        | errs := errs.push s!"{n}: no module"; continue
      match ← record n ci kind mod range.selectionRange.pos.line doc with
      | .ok l =>
        lines := lines.push (toString n, l)
        if kind == "theorem" then thms := thms + 1
      | .error e => errs := errs.push e
    return (lines, errs, thms)
  if !errs.isEmpty then
    for e in errs do IO.eprintln s!"export-catalog: {e}"
    IO.eprintln s!"export-catalog: FAIL ({errs.size} declaration(s) could not be exported)"
    return 1
  if lines.isEmpty then
    IO.eprintln "export-catalog: FAIL (no declarations exported; is the library built?)"
    return 1
  let sorted := lines.qsort (fun a b => a.1 < b.1)
  let out ← IO.getStdout
  for (_, l) in sorted do out.putStrLn l
  out.flush
  let ms := (← IO.monoMsNow) - startMs
  IO.eprintln s!"export-catalog: {sorted.size} declarations ({thms} theorem, \
    {sorted.size - thms} def) in {ms} ms"
  return 0

/-- Import `CflibsFormal` with environment extensions loaded (see the module docstring) and run
`act` in `CoreM`. `trustLevel := 1024`: imported constants are not re-checked; this tool reads a
library that `lake build` has already kernel-checked. -/
unsafe def withLoadedEnv {α} (act : CoreM α) : IO α := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules #[{ module := `CflibsFormal }] {} (trustLevel := 1024)
    (loadExts := true)
  Prod.fst <$> Core.CoreM.toIO act
    (ctx := { fileName := "<export-catalog>", fileMap := default }) (s := { env := env })

end ExportCatalog

/-- Entry point: `lake exe export-catalog > docs/catalog.jsonl`, from the project root. -/
def main (args : List String) : IO UInt32 := do
  unless args.isEmpty do
    IO.eprintln "usage: lake exe export-catalog > docs/catalog.jsonl"
    return 2
  let start ← IO.monoMsNow
  unsafe ExportCatalog.withLoadedEnv (ExportCatalog.run start)
