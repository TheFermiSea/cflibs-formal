# axiom-audit (vendored)

Kernel-level axiom-allowlist auditor for the cflibs-formal Lean library. Fails if any
declaration transitively depends on an axiom outside `{propext, Classical.choice, Quot.sound}`
— catching `sorry`/`admit` (`sorryAx`), `native_decide` (`Lean.ofReduceBool`), and any
home-rolled `axiom`, including ones reaching in through imports (which `grep` cannot).

## Attribution

`AxiomAudit.lean` and `Main.lean` are vendored **verbatim** from
[leanprover-community/axiom-audit](https://github.com/leanprover-community/axiom-audit)
@ commit `46024e005996495c65ef609368e11ab39c4222e3`, licensed Apache-2.0 (see
`AXIOM_AUDIT_LICENSE`). Vendored (rather than `require`d) because the upstream pins a newer
toolchain (v4.32.0-rc1) and `lake update` would otherwise bump this project off its
mathlib-matched v4.31.0 toolchain. The tool is deliberately dependency-free, so it builds
verbatim under our toolchain.

## Usage

    lake build                 # build the library first (audit reads its oleans)
    lake exe axiom-audit --root CflibsFormal
