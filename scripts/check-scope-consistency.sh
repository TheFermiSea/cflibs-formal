#!/usr/bin/env bash
# Epistemic-drift CI guard for cflibs-formal.
#
# An EXACT result claims to faithfully encode the cited physics. If such a result rests on a
# dependency whose ONLY physical content is an APPROXIMATION (a documented idealization / limiting
# case), the EXACT claim is over-reaching: it is exact only relative to an approximation. This
# script surfaces that drift from the two artifacts that already encode the epistemic status of the
# spec — docs/scope-tags.tsv (curated scope tags) and the intra-repo `import CflibsFormal.X` graph.
#
# Scope ordering (least -> most approximate):  EXACT < REDUCED < APPROXIMATION.
# (PURE-MATH carries no physical claim and is ignored by the ordering.)
#
# Rule:
#   FAIL (exit 1)  — a module with an EXACT result transitively imports a PURE-approximation module
#                    (a module whose physics claims are APPROXIMATION with NO EXACT result of its
#                    own). The importer can only be resting on approximate physics => genuine
#                    over-reach. The offending import path is named.
#   WARN (exit 0)  — a module with an EXACT result transitively imports a MIXED module that also
#                    carries an APPROXIMATION result (it exposes EXACT results too, so the importer
#                    may legitimately rest on the exact part; module granularity cannot decide).
#   WARN (exit 0)  — a module with an EXACT result transitively imports a module whose most
#                    approximate physical claim is REDUCED (EXACT-on-REDUCED).
#
# Dependency-light: bash + python3 stdlib only. No Lean invocation. Read-only.
set -euo pipefail
cd "$(dirname "$0")/.."

python3 - "$PWD" <<'PY'
import pathlib, re, sys
from collections import deque

ROOT = pathlib.Path(sys.argv[1])
SRC = ROOT / "CflibsFormal"
TSV = ROOT / "docs" / "scope-tags.tsv"

# --- scope ordering; PURE-MATH is intentionally absent (no physical claim) -------------------
RANK = {"EXACT": 0, "REDUCED": 1, "APPROXIMATION": 2}
VALID_TAGS = set(RANK) | {"PURE-MATH"}

# --- 1. parse docs/scope-tags.tsv -> per-module set of tags ----------------------------------
# tab-separated: module<TAB>name<TAB>TAG<TAB>citation ; header/comment/malformed rows skipped.
tags: dict[str, set[str]] = {}
unknown_tags: set[str] = set()
if not TSV.exists():
    print(f"check-scope-consistency: MISSING {TSV}", file=sys.stderr)
    sys.exit(2)
for line in TSV.read_text(encoding="utf-8").splitlines():
    if not line.strip() or line.startswith("#"):
        continue
    parts = line.split("\t")
    if len(parts) != 4:
        continue
    module, _name, tag, _cite = (p.strip() for p in parts)
    if tag not in VALID_TAGS:
        unknown_tags.add(tag)
        continue
    tags.setdefault(module, set()).add(tag)

# --- 2. parse import edges -> intra-repo dependency graph ------------------------------------
# `import CflibsFormal.Alt.CSigma`  ->  module key "Alt/CSigma.lean" (matches the tsv column).
IMPORT_RE = re.compile(r"^import\s+CflibsFormal\.(\S+)")
graph: dict[str, list[str]] = {}
all_modules: set[str] = set()
for f in sorted(SRC.rglob("*.lean")):
    rel = str(f.relative_to(SRC))
    all_modules.add(rel)
    deps: list[str] = []
    for l in f.read_text(encoding="utf-8").splitlines():
        m = IMPORT_RE.match(l)
        if m:
            deps.append(m.group(1).replace(".", "/") + ".lean")
    graph[rel] = deps
for m in tags:
    all_modules.add(m)

# --- classify approximation-bearing modules -------------------------------------------------
def has(mod: str, tag: str) -> bool:
    return tag in tags.get(mod, ())

def worst_rank(mod: str) -> int:
    """Most-approximate PHYSICAL claim rank of a module (-1 if none / pure-math only)."""
    rs = [RANK[t] for t in tags.get(mod, ()) if t in RANK]
    return max(rs) if rs else -1

# --- shortest import path (for a readable, name-the-edge report) -----------------------------
def import_path(src: str, dst: str) -> list[str]:
    if src == dst:
        return [src]
    prev = {src: None}
    q = deque([src])
    while q:
        u = q.popleft()
        for v in graph.get(u, ()):
            if v not in prev:
                prev[v] = u
                if v == dst:
                    path = [v]
                    while prev[path[-1]] is not None:
                        path.append(prev[path[-1]])
                    return list(reversed(path))
                q.append(v)
    return []

def fmt_path(p: list[str]) -> str:
    return " -> ".join(p) if p else "(no path)"

# --- 3. walk: for each EXACT module, inspect transitive physical dependencies ----------------
fails = []   # (exact_module, approx_module, path)   genuine over-reach
warns_approx = []  # (exact_module, mixed_module, path)  EXACT-on-mixed-approximation
warns_reduced = []  # (exact_module, reduced_module, path)

exact_modules = sorted(m for m in all_modules if has(m, "EXACT"))
for m in exact_modules:
    # transitive closure of imports
    seen: set[str] = set()
    stack = list(graph.get(m, ()))
    while stack:
        d = stack.pop()
        if d in seen:
            continue
        seen.add(d)
        stack.extend(graph.get(d, ()))
    for d in sorted(seen):
        if d == m:
            continue
        if has(d, "APPROXIMATION"):
            if has(d, "EXACT"):
                warns_approx.append((m, d, import_path(m, d)))
            else:
                # pure-approximation dependency under an EXACT claim = genuine over-reach
                fails.append((m, d, import_path(m, d)))
        elif worst_rank(d) == RANK["REDUCED"]:
            warns_reduced.append((m, d, import_path(m, d)))

# --- 4. report ------------------------------------------------------------------------------
print("== scope-consistency (epistemic-drift guard) ==")
print(f"   modules: {len(all_modules)}   with EXACT result: {len(exact_modules)}")
approx_pure = sorted(m for m in tags if has(m, "APPROXIMATION") and not has(m, "EXACT"))
approx_mixed = sorted(m for m in tags if has(m, "APPROXIMATION") and has(m, "EXACT"))
print(f"   APPROXIMATION-only modules (fail if an EXACT result depends on them): "
      f"{approx_pure or '(none)'}")
print(f"   mixed EXACT+APPROXIMATION modules (warn only): {approx_mixed or '(none)'}")
if unknown_tags:
    print(f"   note: ignored unrecognized scope tag(s): {sorted(unknown_tags)}")
print("")

if warns_reduced:
    # Compact: one line per EXACT module listing its REDUCED dependencies (paths omitted — this
    # tier is advisory and high-volume; ForwardMap-style REDUCED bases are imported widely).
    by_src: dict[str, list[str]] = {}
    for m, d, _p in warns_reduced:
        by_src.setdefault(m, []).append(d)
    print(f"-- WARNING: {len(warns_reduced)} EXACT-transitively-on-REDUCED dependency(ies) "
          f"across {len(by_src)} module(s) (non-fatal, advisory) --")
    for m in sorted(by_src):
        print(f"   WARN  {m}  ->  REDUCED: {', '.join(sorted(by_src[m]))}")
    print("")

if warns_approx:
    print(f"-- WARNING: {len(warns_approx)} EXACT result(s) transitively on a MIXED "
          f"EXACT+APPROXIMATION module (non-fatal; module granularity cannot prove over-reach) --")
    for m, d, p in warns_approx:
        print(f"   WARN  {m}  depends on mixed-approximation  {d}")
        print(f"         path: {fmt_path(p)}")
    print("")

if fails:
    print(f"-- FAIL: {len(fails)} EXACT result(s) resting on an APPROXIMATION-only dependency "
          f"(over-reach) --")
    for m, d, p in fails:
        print(f"   FAIL  {m}  (EXACT) transitively imports APPROXIMATION-only  {d}")
        print(f"         offending path: {fmt_path(p)}")
    print("")
    print("check-scope-consistency: FAILED — an EXACT claim rests on approximate-only physics.")
    print("  Resolve by (a) demoting the offending EXACT result(s) to REDUCED/APPROXIMATION in")
    print("  docs/scope-tags.tsv if they truly inherit the approximation, or (b) refactoring so the")
    print("  EXACT result no longer imports the approximation-only module.")
    sys.exit(1)

print("OK: no EXACT result rests on an approximation-only dependency.")
if warns_approx or warns_reduced:
    print(f"    ({len(warns_approx)} mixed-approximation + {len(warns_reduced)} reduced "
          f"dependency warning(s) above — advisory, not blocking.)")
sys.exit(0)
PY