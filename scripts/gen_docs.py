#!/usr/bin/env python3
"""Generate the auto documentation for cflibs-formal.

Walks the Lean source under CflibsFormal/ and emits two always-in-sync references:
  - docs/module-reference.md   : a table (module, namespace, #results, #defs, base?, lit?, role)
  - docs/theorem-catalog.md    : every named result + def, grouped by module, with a one-line
                                 summary lifted from its docstring.

Pure stdlib, deterministic (sorted), no Lean invocation. Run via scripts/gen-docs.sh; the
docs-sync CI gate regenerates and diffs against the committed copies (mirroring the oracle gate),
so these files cannot drift from the source.
"""
from __future__ import annotations

import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
SRC = ROOT / "CflibsFormal"

# Mirror scripts/stats.sh's counting EXACTLY: declarations at column 0; results = theorem/lemma
# with an optional `@[attr]` prefix; defs = `def` with an optional `noncomputable`. `private`,
# `protected`, `abbrev`, and `example` are NOT counted (they start with a different token).
RESULT_RE = re.compile(r"^(?:@\[[^\]]*\]\s*)?(theorem|lemma) ([A-Za-z_][A-Za-z0-9_'.]*)")
DEF_RE = re.compile(r"^(?:noncomputable )?def ([A-Za-z_][A-Za-z0-9_'.]*)")
NS_RE = re.compile(r"^namespace\s+(\S+)")
IMPORT_RE = re.compile(r"^import\s+(CflibsFormal\S*)")
HEADING_RE = re.compile(r"^#\s+(.*\S)\s*$")


def first_summary(doc_lines: list[str]) -> str:
    """One-line summary from a `/-- ... -/` docstring block (list of inner lines)."""
    text = " ".join(l.strip() for l in doc_lines).strip()
    text = re.sub(r"\*\*(.*?)\*\*", r"\1", text)        # drop bold markers, keep content
    # first sentence (up to a period that ends a clause), else first ~140 chars
    m = re.match(r"(.*?[.!])(\s|$)", text)
    summary = m.group(1) if m else text
    summary = summary.strip()
    if len(summary) > 160:
        summary = summary[:157].rstrip() + "…"
    return summary or "—"


def parse_module(path: pathlib.Path):
    rel = path.relative_to(SRC).with_suffix("")
    dotted = "CflibsFormal." + ".".join(rel.parts)
    lines = path.read_text(encoding="utf-8").splitlines()

    namespace = None
    imports: list[str] = []
    title = None
    has_lit = False
    decls: list[tuple[str, str, str]] = []   # (kind, name, summary)

    pending_doc: list[str] | None = None     # inner lines of the most recent `/-- ... -/`
    in_doc = False
    doc_buf: list[str] = []
    in_module_doc = False

    for line in lines:
        stripped = line.strip()

        # module/section docstring `/-! ... -/` — harvest the first `# ` heading as the title
        if not in_doc and stripped.startswith("/-!"):
            in_module_doc = True
        if in_module_doc:
            if title is None:
                h = HEADING_RE.match(stripped)
                if h:
                    title = h.group(1)
            if "## Literature" in line:
                has_lit = True
            if "-/" in stripped and not stripped.startswith("/-!"):
                in_module_doc = False
            elif stripped.endswith("-/") and stripped.startswith("/-!"):
                in_module_doc = False
            continue

        # declaration docstring `/-- ... -/`
        if not in_doc and stripped.startswith("/--"):
            in_doc = True
            doc_buf = []
            inner = stripped[3:]
            if inner.endswith("-/"):
                doc_buf.append(inner[:-2])
                in_doc = False
                pending_doc = doc_buf[:]
            else:
                doc_buf.append(inner)
            continue
        if in_doc:
            if stripped.endswith("-/"):
                doc_buf.append(stripped[:-2])
                in_doc = False
                pending_doc = doc_buf[:]
            else:
                doc_buf.append(stripped)
            continue

        if namespace is None:
            ns = NS_RE.match(line)
            if ns:
                namespace = ns.group(1)
        imp = IMPORT_RE.match(line)
        if imp:
            imports.append(imp.group(1))

        m_res = RESULT_RE.match(line)
        m_def = DEF_RE.match(line)
        if m_res or m_def:
            kind = m_res.group(1) if m_res else "def"
            name = m_res.group(2) if m_res else m_def.group(1)
            summary = first_summary(pending_doc) if pending_doc else "—"
            decls.append((kind, name, summary))
            pending_doc = None
            continue

        # any other non-blank, non-attribute, non-`omit/variable` line clears a dangling docstring
        if stripped and not (stripped.startswith("@[") or stripped.startswith("omit ")
                             or stripped.startswith("variable") or stripped.startswith("open ")):
            pending_doc = None

    results = [d for d in decls if d[0] in ("theorem", "lemma")]
    defs = [d for d in decls if d[0] == "def"]
    is_base = not imports
    role = title or "—"
    # trim a common prefix for readability
    role = re.sub(r"^(Saha[–-]Boltzmann formalization|CF-LIBS formalization)\s*[—-]\s*", "", role)
    return {
        "dotted": dotted, "rel": str(rel) + ".lean", "namespace": namespace or "—",
        "imports": sorted(imports), "is_base": is_base, "has_lit": has_lit,
        "role": role, "results": results, "defs": defs, "decls": decls,
    }


def main() -> int:
    paths = sorted(p for p in SRC.rglob("*.lean"))
    mods = [parse_module(p) for p in paths]
    mods.sort(key=lambda m: m["rel"])

    # ---- module-reference.md ----
    mr = ["# Module reference", "",
          "> **AUTO-GENERATED** by `scripts/gen-docs.sh` — do not hand-edit; regenerate after",
          "> adding/removing modules or results. The docs-sync CI gate diffs this against source.",
          "", "One row per module under `CflibsFormal/`. *Base* = imports no `CflibsFormal` module.",
          "*Lit* = carries a `## Literature` citation paragraph.", "",
          "| Module | Namespace | Results | Defs | Base | Lit | Role |",
          "|---|---|--:|--:|:--:|:--:|---|"]
    tot_r = tot_d = 0
    for m in mods:
        tot_r += len(m["results"]); tot_d += len(m["defs"])
        mr.append(f"| `{m['rel']}` | `{m['namespace']}` | {len(m['results'])} | {len(m['defs'])}"
                  f" | {'✓' if m['is_base'] else '–'} | {'✓' if m['has_lit'] else '–'}"
                  f" | {m['role']} |")
    mr.append(f"| **{len(mods)} modules** | | **{tot_r}** | **{tot_d}** | | | |")
    mr.append("")
    (ROOT / "docs" / "module-reference.md").write_text("\n".join(mr) + "\n", encoding="utf-8")

    # ---- theorem-catalog.md ----
    tc = ["# Theorem catalog", "",
          "> **AUTO-GENERATED** by `scripts/gen-docs.sh`. Every named result and definition, grouped",
          "> by module, with a one-line summary lifted from its docstring. Scope tags",
          "> (EXACT / REDUCED / APPROXIMATION / PURE-MATH) and per-result citations are being layered",
          "> in on top of this index — see `reviews/literature-validity-audit.md` for the current",
          "> faithful/reduced/idealized/pure-math classification of the established corpus.", ""]
    for m in mods:
        if not m["decls"]:
            continue
        tc.append(f"## `{m['rel']}`  ({m['namespace']})")
        if m["role"] and m["role"] != "—":
            tc.append(f"*{m['role']}*")
        tc.append("")
        defs = [d for d in m["decls"] if d[0] == "def"]
        results = [d for d in m["decls"] if d[0] in ("theorem", "lemma")]
        if defs:
            tc.append("**Definitions**")
            for _k, name, summ in defs:
                tc.append(f"- `{name}` — {summ}")
            tc.append("")
        if results:
            tc.append("**Results**")
            for _k, name, summ in results:
                tc.append(f"- `{name}` — {summ}")
            tc.append("")
    (ROOT / "docs" / "theorem-catalog.md").write_text("\n".join(tc) + "\n", encoding="utf-8")

    print(f"gen-docs: {len(mods)} modules, {tot_r} results, {tot_d} defs "
          f"-> docs/module-reference.md, docs/theorem-catalog.md")
    return 0


if __name__ == "__main__":
    sys.exit(main())
