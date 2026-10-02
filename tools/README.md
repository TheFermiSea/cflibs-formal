# axiom-audit (vendored)

Kernel-level axiom-allowlist auditor for the cflibs-formal Lean library. Fails if any
declaration transitively depends on an axiom outside `{propext, Classical.choice, Quot.sound}`
— catching `sorry`/`admit` (`sorryAx`), `native_decide` (`Lean.ofReduceBool`), and any
home-rolled `axiom`, including ones reaching in through imports (which `grep` cannot).

## Attribution

`AxiomAudit.lean` and `Main.lean` are vendored **verbatim** from
[leanprover-community/axiom-audit](https://github.com/leanprover-community/axiom-audit)
@ commit `46024e005996495c65ef609368e11ab39c4222e3`, licensed Apache-2.0 (see
`AXIOM_AUDIT_LICENSE`). Vendored (rather than `require`d) because the upstream pins its own
toolchain (v4.32.0-rc1 at vendoring time) and a `require` would let `lake update` drag this
project off its mathlib-matched toolchain (v4.33.1 since 2026-09-02). The tool is deliberately
dependency-free, so it builds verbatim under our toolchain.

## Usage

    lake build                 # build the library first (audit reads its oleans)
    lake exe axiom-audit --root CflibsFormal

# export-catalog

`ExportCatalog.lean` (this repo's own tool, not vendored) writes `docs/catalog.jsonl`: one JSON
line per documented theorem or definition in the `CflibsFormal` namespace (including
`CflibsFormal.Alt`), sorted by name. A declaration is included when it is non-internal, a kernel
`theorem` or `def`, and has both a source line and a docstring; that drops compiler-generated
companions (equation lemmas, `match_n`, structure `recOn`/`casesOn`/`ext`).

Keys, in this order: `name`, `kind` (`theorem`/`def`), `module`, `file` (repo-relative), `line`
(the declaration name's line), `docstring`, `type` (printed with `pp.fullNames`,
`pp.numericTypes`, `pp.unicode.fun`, width 100), `binders` (outermost `∀` binder names; `"_"` for
an anonymous or hygienic one such as an unnamed instance binder), `usedConstants` (the
`CflibsFormal` constants in the type, sorted, self excluded) and `axioms` (sorted, theorems only;
`[]` for definitions). The docs generators and the theorem cards read it; a card's reviewed
statement hash is computed from `name`, `type` and `binders`.

Unlike `axiom-audit` and `scope-check`, it loads environment-extension state (the `runLinter`
import pattern), so the printed statements use Mathlib notation and `collectAxioms` uses the
per-module precomputed axiom table. See the module docstring.

## Usage

    lake build
    lake exe export-catalog > docs/catalog.jsonl    # summary line on stderr

CI regenerates it into `/tmp` and `diff -u`s against the committed file (the catalog-staleness
gate), so regenerate and commit it whenever a declaration, docstring or line moves. The output
is byte-identical across runs on the same build; it takes about 10 s, mostly environment loading.
