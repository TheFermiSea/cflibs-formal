#!/usr/bin/env python3
"""Source-hygiene gate for the Lean sources (run by scripts/stats.sh; pure stdlib, no Lean).

Checks, over the git-tracked sources with comments and docstrings removed:

1. Import hygiene. Every import in the header of `CflibsFormal.lean` and of each module under
   `CflibsFormal/` names `Mathlib` or a `CflibsFormal` module; `upstream/*.lean` may import only
   `Mathlib`. The header is read token by token, the way Lean reads it, so several imports on
   one line, indented imports and `public`/`private`/`meta` imports under a `module` header are
   all seen. (A line-anchored `^import` grep misses each of those.)
2. No orphan module. Every module under `CflibsFormal/` is imported by the root
   `CflibsFormal.lean`, so the build, the axiom audit and the scope gate see it.
3. No proof escape hatch in source. The tokens `sorry`, `admit`, `native_decide` and the kernel
   or compiler bypasses (`skipKernelTC`, `run_cmd`, `run_elab`, `addDecl`, `implemented_by`,
   `extern`, `unsafe`, `ofReduceBool`, `trustCompiler`) and the `axiom` command do not occur.
   The axiom audit sees only declarations that enter the environment; an `example` does not, so
   a `sorry` or `native_decide` inside one is invisible to it. This scan covers those.

Exit 0 if clean, 1 otherwise. `--root DIR` checks another tree (used to test the gate itself).
"""
from __future__ import annotations

import argparse
import pathlib
import re
import subprocess
import sys

HEADER_WORDS = {"module", "prelude", "public", "private", "meta", "import", "all", "runtime"}
IMPORT_MODIFIERS = {"all", "runtime", "meta", "public", "private"}
FORBIDDEN = ["sorry", "admit", "native_decide", "skipKernelTC", "run_cmd", "run_elab", "addDecl",
             "implemented_by", "extern", "unsafe", "ofReduceBool", "trustCompiler", "axiom"]
# An identifier character on either side means the word is part of a longer name.
IDENT = r"[A-Za-z0-9_'!?À-￿]"
FORBIDDEN_RE = re.compile(r"(?<!" + IDENT + r")(" + "|".join(FORBIDDEN) + r")(?!" + IDENT + ")")


def strip_comments(text: str) -> str:
    """Remove `--` line comments and nested `/- ... -/` block comments (docstrings included),
    keeping newlines so line numbers survive. String literals are left alone except that comment
    markers inside them are not interpreted."""
    out = []
    i, n, depth = 0, len(text), 0
    in_str = False
    while i < n:
        two = text[i:i + 2]
        c = text[i]
        if depth == 0 and in_str:
            out.append(c)
            if c == "\\" and i + 1 < n:
                out.append(text[i + 1]); i += 2; continue
            if c == '"':
                in_str = False
            i += 1
        elif two == "/-":
            depth += 1; i += 2
        elif depth > 0 and two == "-/":
            depth -= 1; i += 2
        elif depth > 0:
            if c == "\n":
                out.append("\n")
            i += 1
        elif two == "--":
            while i < n and text[i] != "\n":
                i += 1
        elif c == '"':
            in_str = True; out.append(c); i += 1
        else:
            out.append(c); i += 1
    return "".join(out)


def header_imports(code: str) -> list[str]:
    """Module names imported by the file header (comments already stripped)."""
    names = []
    toks = code.split()
    i = 0
    while i < len(toks) and toks[i] in HEADER_WORDS:
        if toks[i] == "import":
            i += 1
            while i < len(toks) and toks[i] in IMPORT_MODIFIERS:
                i += 1
            if i < len(toks):
                names.append(toks[i])
        i += 1
    return names


def allowed(name: str, prefixes: tuple[str, ...]) -> bool:
    return any(name == p or name.startswith(p + ".") for p in prefixes)


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--root", default=str(pathlib.Path(__file__).resolve().parent.parent))
    args = ap.parse_args()
    root = pathlib.Path(args.root)
    listed = subprocess.run(
        ["git", "ls-files", "CflibsFormal.lean", "CflibsFormal/*.lean", "upstream/*.lean"],
        cwd=root, capture_output=True, text=True, check=True).stdout.split("\n")
    files = sorted(f for f in listed if f)
    if "CflibsFormal.lean" not in files:
        print("FAIL: CflibsFormal.lean is not tracked"); return 1
    bad = 0
    root_imports: list[str] = []
    for f in files:
        code = strip_comments((root / f).read_text(encoding="utf-8"))
        imports = header_imports(code)
        prefixes = ("Mathlib",) if f.startswith("upstream/") else ("Mathlib", "CflibsFormal")
        for name in imports:
            if not allowed(name, prefixes):
                print(f"FAIL: {f} imports `{name}` (allowed: {', '.join(prefixes)})"); bad += 1
        if f == "CflibsFormal.lean":
            root_imports = imports
        for ln, line in enumerate(code.split("\n"), 1):
            for m in FORBIDDEN_RE.finditer(line):
                print(f"FAIL: {f}:{ln}: forbidden token `{m.group(1)}`"); bad += 1
    for f in files:
        if f.startswith("CflibsFormal/"):
            mod = f[:-len(".lean")].replace("/", ".")
            if mod not in root_imports:
                print(f"FAIL: {f} is not imported by CflibsFormal.lean (orphan module)"); bad += 1
    if bad:
        print(f"source-hygiene: {bad} violation(s)")
        return 1
    print(f"OK: {len(files)} files; every import is Mathlib / CflibsFormal, every module is "
          "imported by the root, no sorry / admit / native_decide / axiom / kernel-bypass token.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
