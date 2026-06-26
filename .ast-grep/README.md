# ast-grep structural tooling for cflibs-formal

Structural (tree-sitter) search/lint over the Lean sources — a fast, **comment/string-aware**
complement to ripgrep and to the authoritative gates (`lake exe axiom-audit`, `runLinter`).

## Why

ast-grep matches by syntax-tree **node kind**, so `axiom`/`sorry` checks fire only on real
declarations/terms, never on the words appearing in a docstring or comment (which `rg` false-positives
on). It also opens up relational structural queries that regex can't express.

## Setup (once per machine)

```bash
./.ast-grep/build-parser.sh        # builds .ast-grep/parser/lean.so (gitignored, ~8 MB)
```

This needs `npm`, a C compiler, and `git`. It clones `wvhulle/tree-sitter-lean` (pinned), regenerates
its parser at **ABI 14**, and compiles `parser.c` + `scanner.c` into the shared library that
`sgconfig.yml` registers as the custom `lean` language.

### Grammar / ABI notes (non-obvious)

- ast-grep 0.41 cannot load the grammar's default **ABI-15** build → we regenerate at **ABI 14**.
- We use the **v0.3.0** grammar (`16f43e0`), *not* the `tree-sitter-lean4` **0.0.6** crate: 0.0.6 does
  not model `import`, `/- -/` block comments, or layout, so it whole-file-ERRORs on mathlib-style
  Lean and is unusable here. v0.3.0 recovers the declaration structure (some proof-body ERRORs
  remain — fine for declaration-level rules).
- **Pattern matching (`-p '…'`) is unreliable** with this grammar (meta-vars parse to ERROR nodes).
  Use **`kind:`-based rules** instead — that is what the rules here do.

## Use

```bash
./.ast-grep/audit.sh               # run the rule-set (exit non-zero on any violation)
ast-grep scan CflibsFormal         # same, directly
ast-grep run --lang lean -p '…'    # ad-hoc (pattern matching is flaky; prefer kind rules)
```

## Rules (`.ast-grep/rules/`)

| rule | matches | invariant |
|---|---|---|
| `no-axiom` | `kind: axiom` | no home-rolled axioms (axiom-clean) |
| `no-sorry` | `kind: sorry` | no `sorry` placeholders |
| `no-unsound-tactics` | `identifier` = `admit`/`native_decide`/`sorryAx` | no axiom-introducing tactics |

These are a *local pre-check*; `lake exe axiom-audit` remains the authoritative CI gate (it also
follows imports and catches `sorryAx`/`ofReduceBool`).
