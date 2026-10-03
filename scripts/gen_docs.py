#!/usr/bin/env python3
"""Generate the auto documentation for cflibs-formal.

Walks the Lean source under CflibsFormal/ and emits two always-in-sync references:
  - docs/module-reference.md   : a table (module, namespace, #results, #defs, base?, lit?, role)
  - docs/theorem-catalog.md    : every named result + def, grouped by module, with a one-line
                                 summary lifted from its docstring.

It also rewrites the size line between `<!-- stats:begin -->` and `<!-- stats:end -->` in
README.md, AGENTS.md and CONTEXT.md, so the counts quoted there cannot go stale.

Pure stdlib, deterministic (sorted), no Lean invocation. Run via scripts/gen-docs.sh; the
docs-sync CI gate regenerates and diffs against the committed copies (mirroring the oracle gate),
so these files cannot drift from the source. `--check` writes nothing and exits 1 if any
generated file would change.

Completeness is checked twice. The source regexes below find the results a reader sees; the
kernel-derived docs/catalog.jsonl (`lake exe export-catalog`, itself gated against staleness in
CI) lists every documented theorem that actually entered the environment. Every catalog theorem
must have a scope-tag row and every result found by regex must be in the catalog, so a theorem
the regex cannot see (an unusual declaration form) or one with no docstring fails the gate.
A module with a physics-tagged result must carry a `## Literature` section.

Scope tags (owner decision 2026-09-24, docs/conventions.md section 8): a row of
docs/scope-tags.tsv naming a theorem carries its RELATION tag; a row naming a definition carries
its MODEL tag. The PUBLISHED tag of a theorem (the weaker of its relation tag and the model tags of
the definitions in its statement) needs the kernel environment, so it is computed by
`lake exe scope-check --write` into docs/scope-published.tsv and only rendered here. This script
fails if that file is missing or out of step with docs/scope-tags.tsv.
"""
from __future__ import annotations

import argparse
import json
import pathlib
import re
import subprocess
import sys
from collections import Counter

ROOT = pathlib.Path(__file__).resolve().parent.parent
SRC = ROOT / "CflibsFormal"

# Same counting rule as scripts/stats.sh: declarations at column 0; results = theorem/lemma with
# an optional `@[attr]` prefix; defs = `def` with an optional `noncomputable`. `private`,
# `protected`, `abbrev`, and `example` are NOT counted (they start with a different token).
# A name runs to the first whitespace or binder/colon character, so Unicode names (`foo₂`) are
# read whole. These regexes are a reader's view of the source; the fail-closed completeness
# check is the cross-check against docs/catalog.jsonl in `main`.
NAME = r"([^\s:({\[⦃]+)"
RESULT_RE = re.compile(r"^(?:@\[[^\]]*\]\s*)?(theorem|lemma)\s+" + NAME)
DEF_RE = re.compile(r"^(?:noncomputable\s+)?def\s+" + NAME)
NS_RE = re.compile(r"^namespace\s+(\S+)")
IMPORT_RE = re.compile(r"^import\s+(CflibsFormal\S*)")
HEADING_RE = re.compile(r"^#\s+(.*\S)\s*$")
# Declarations a MODEL row may name (definition-like; never counted as results or defs above).
MODEL_RE = re.compile(r"^(?:(?:noncomputable|protected)\s+)*(def|abbrev|structure|inductive|class)"
                      r"\s+" + NAME)
STATS_BEGIN, STATS_END = "<!-- stats:begin -->", "<!-- stats:end -->"
STATS_FILES = ("README.md", "AGENTS.md", "CONTEXT.md")


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
    models: dict[str, tuple[str, str]] = {}  # definition-like decl name -> (kind, summary)

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
            if "-/" in inner:           # closes on this line (anything after it is not scanned)
                doc_buf.append(inner[:inner.index("-/")])
                in_doc = False
                pending_doc = doc_buf[:]
            else:
                doc_buf.append(inner)
            continue
        if in_doc:
            if "-/" in stripped:
                doc_buf.append(stripped[:stripped.index("-/")])
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
        m_model = MODEL_RE.match(line)
        if m_model:
            models[m_model.group(2)] = (m_model.group(1),
                                        first_summary(pending_doc) if pending_doc else "—")
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
        "role": role, "results": results, "defs": defs, "models": models,
    }


SCOPE_TAGS = ("EXACT", "REDUCED", "APPROXIMATION", "PURE-MATH")


RANK = {"EXACT": 0, "REDUCED": 1, "APPROXIMATION": 2}


def load_scope_tags() -> tuple[dict, list[str]]:
    """Curated authoritative scope classification: (module_rel, name) -> (tag, citation).

    Returns the map and a list of errors (malformed or duplicate rows): a duplicate key would
    otherwise silently overwrite the earlier row."""
    path = ROOT / "docs" / "scope-tags.tsv"
    out: dict = {}
    errors: list[str] = []
    for i, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        if not line.strip() or line.startswith("#"):
            continue
        parts = line.split("\t")
        if len(parts) != 4:
            errors.append(f"MALFORMED scope-tags row (line {i}): expected 4 tab-separated columns")
            continue
        module, name, tag, cite = parts
        if (module, name) in out:
            errors.append(f"DUPLICATE scope-tags row (line {i}): {module} :: {name}")
            continue
        out[(module, name)] = (tag, cite)
    return out, errors


def load_published() -> dict | None:
    """docs/scope-published.tsv (written by `lake exe scope-check --write`):
    (module_rel, name) -> (kind, own, published, via). None if the file is missing."""
    path = ROOT / "docs" / "scope-published.tsv"
    if not path.exists():
        return None
    out = {}
    for line in path.read_text(encoding="utf-8").splitlines():
        if not line.strip() or line.startswith("#"):
            continue
        parts = line.split("\t")
        if len(parts) == 6:
            module, name, kind, own, published, via = parts
            out[(module, name)] = (kind, own, published, via)
    return out


def load_catalog_theorems() -> dict | None:
    """docs/catalog.jsonl theorems: module_rel -> list of fully-qualified names. None if the
    catalog is missing."""
    path = ROOT / "docs" / "catalog.jsonl"
    if not path.exists():
        return None
    out: dict = {}
    for line in path.read_text(encoding="utf-8").splitlines():
        if not line.strip():
            continue
        d = json.loads(line)
        if d["kind"] == "theorem":
            out.setdefault(d["file"].removeprefix("CflibsFormal/"), []).append(d["name"])
    return out


def is_suffix(short: str, full: str) -> bool:
    """`short` (possibly dotted) is a name-component suffix of the fully-qualified `full`."""
    return full == short or full.endswith("." + short)


def stats_line(n_mods: int, n_results: int, n_defs: int) -> str:
    return f"{n_mods} modules · {n_results} named results (theorem/lemma) · {n_defs} defs"


def with_stats(text: str, line: str, name: str) -> str:
    """`text` with the line(s) between the stats markers replaced by `line`, keeping the
    markers' indentation."""
    if text.count(STATS_BEGIN) != 1 or text.count(STATS_END) != 1:
        raise SystemExit(f"gen-docs: {name} must contain exactly one {STATS_BEGIN} ... "
                         f"{STATS_END} block")
    head, rest = text.split(STATS_BEGIN)
    _old, tail = rest.split(STATS_END)
    indent = head[head.rfind("\n") + 1:]
    return f"{head}{STATS_BEGIN}\n{indent}{line}\n{indent}{STATS_END}{tail}"


def main() -> int:
    ap = argparse.ArgumentParser(description="Regenerate the auto docs (see the module docstring).")
    ap.add_argument("--check", action="store_true",
                    help="write nothing; exit 1 if a generated file would change")
    args = ap.parse_args()
    outputs: dict[pathlib.Path, str] = {}

    tracked = subprocess.run(["git", "ls-files", "CflibsFormal/*.lean"], cwd=ROOT,
                             capture_output=True, text=True, check=True).stdout.split("\n")
    mods = [parse_module(ROOT / f) for f in tracked if f]
    mods.sort(key=lambda m: m["rel"])

    scope, row_errors = load_scope_tags()
    result_keys = {(m["rel"], name) for m in mods for (_k, name, _s) in m["results"]}
    # MODEL rows name a definition-like declaration (def/abbrev/structure/inductive/class)
    model_keys = {(m["rel"], name) for m in mods for name in m["models"]} - result_keys
    untagged = sorted(k for k in result_keys if k not in scope)
    stale = sorted(k for k in scope if k not in result_keys and k not in model_keys)
    bad_tag = sorted(k for k, (t, _c) in scope.items() if t not in SCOPE_TAGS)
    model_rows = {k: v for k, v in scope.items() if k in model_keys}

    # published tags (computed from the kernel environment by `lake exe scope-check --write`)
    published = load_published()
    pub_errors: list[str] = []
    if published is None:
        pub_errors.append("MISSING docs/scope-published.tsv — run `lake exe scope-check --write`")
        published = {}
    else:
        expect = {k: ("theorem" if k in result_keys else "def", t)
                  for k, (t, _c) in scope.items() if k in result_keys or k in model_keys}
        got = {k: (kind, own) for k, (kind, own, _p, _v) in published.items()}
        for k in sorted(set(expect) | set(got)):
            if expect.get(k) != got.get(k):
                pub_errors.append(f"STALE published tag for {k[0]} :: {k[1]} "
                                  f"(scope-tags {expect.get(k)}, scope-published {got.get(k)})")
        for k, (kind, own, pub, _v) in published.items():
            if pub not in SCOPE_TAGS or (own in RANK and RANK.get(pub, -1) < RANK[own]) \
                    or (own == "PURE-MATH" and pub != own):
                pub_errors.append(f"BAD published tag for {k[0]} :: {k[1]}: {own} -> {pub}")
        if pub_errors:
            pub_errors.append("docs/scope-published.tsv is out of step with docs/scope-tags.tsv "
                              "— run `lake exe scope-check --write`, then scripts/gen-docs.sh")

    def pub_of(key: tuple[str, str]) -> tuple[str, str]:
        """(published tag, via) of a result; falls back to its own tag if unknown."""
        own = scope.get(key, ("UNTAGGED", ""))[0]
        _kind, _own, pub, via = published.get(key, ("theorem", own, own, "—"))
        return pub, via

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
    outputs[ROOT / "docs" / "module-reference.md"] = "\n".join(mr) + "\n"
    for name in STATS_FILES:
        path = ROOT / name
        outputs[path] = with_stats(path.read_text(encoding="utf-8"),
                                   stats_line(len(mods), tot_r, tot_d), name)

    # ---- kernel cross-check and Literature gate ----
    extra_errors: list[str] = []
    catalog = load_catalog_theorems()
    if catalog is None:
        extra_errors.append("MISSING docs/catalog.jsonl — run "
                            "`lake exe export-catalog > docs/catalog.jsonl`")
    else:
        by_rel = {m["rel"]: m for m in mods}
        for rel, fulls in sorted(catalog.items()):
            m = by_rel.get(rel)
            rows = [name for (mod, name) in scope if mod == rel]
            # a Prop-valued field of a structure declared in this module is not a named result
            structs = {n for n, (kind, _s) in (m["models"] if m else {}).items()
                       if kind in ("structure", "class")}
            for full in sorted(fulls):
                parts = full.split(".")
                if len(parts) >= 2 and parts[-2] in structs:
                    continue
                if not any(is_suffix(r, full) for r in rows):
                    extra_errors.append(f"UNTAGGED theorem in the kernel catalog (the source scan "
                                        f"does not see it): {rel} :: {full}")
        for m in mods:
            fulls = catalog.get(m["rel"], [])
            for (_k, name, _s) in m["results"]:
                if not any(is_suffix(name, full) for full in fulls):
                    extra_errors.append(
                        f"NOT IN CATALOG: {m['rel']} :: {name} — it has no docstring, or "
                        f"docs/catalog.jsonl is stale (`lake exe export-catalog`)")
    for m in mods:
        physics = [name for (_k, name, _s) in m["results"]
                   if scope.get((m["rel"], name), ("", ""))[0] in RANK]
        if physics and not m["has_lit"]:
            extra_errors.append(f"NO `## Literature` section in {m['rel']}, which has "
                                f"{len(physics)} physics-tagged result(s) (AGENTS.md rule 4)")

    # ---- theorem-catalog.md ----
    mix = Counter(scope.get((m["rel"], name), ("?", ""))[0]
                  for m in mods for (_k, name, _s) in m["results"])
    pub_mix = Counter(pub_of((m["rel"], name))[0]
                      for m in mods for (_k, name, _s) in m["results"])
    n_changed = sum(1 for m in mods for (_k, name, _s) in m["results"]
                    if pub_of((m["rel"], name))[0] != scope.get((m["rel"], name), ("?", ""))[0])
    tc = ["# Theorem catalog", "",
          "> **AUTO-GENERATED** by `scripts/gen-docs.sh`. Every named result and definition, grouped by",
          "> module, with a one-line docstring summary. Each **result** carries a curated **scope tag**",
          "> (the integrity spine) + citation from `docs/scope-tags.tsv`; the docs-sync CI gate fails if",
          "> any result is untagged, so a new theorem cannot land without declaring its epistemic status.",
          "",
          "**Two axes, publish the weaker** (owner decision 2026-09-24; "
          "`docs/conventions.md` §8). A result's own tag is its **relation** tag: how exactly it "
          "holds for the model it is stated over. A tagged definition carries a **model** tag: "
          "how faithfully it encodes the physics. The **published** tag of a result is the weaker "
          "(`EXACT < REDUCED < APPROXIMATION`) of its own tag and the model tags of the "
          "`CflibsFormal` definitions in its statement (a definition without a row inherits the "
          "weakest model tag of the tagged definitions it is built from); `PURE-MATH` results "
          "are exempt. Computed from the kernel environment by `lake exe scope-check --write` "
          "(`docs/scope-published.tsv`).",
          "",
          "A result shows `own → published` when the two differ (with the definitions that "
          "weakened it), and a single tag when they agree. A definition with its own row shows "
          "`model TAG`.",
          "",
          "**Own-tag mix** (" + str(sum(mix.values())) + " results): "
          + " · ".join(f"**{t}** {mix.get(t, 0)}" for t in SCOPE_TAGS),
          "",
          "**Published-tag mix** (" + str(sum(pub_mix.values())) + " results; "
          + str(n_changed) + " weakened by a model tag): "
          + " · ".join(f"**{t}** {pub_mix.get(t, 0)}" for t in SCOPE_TAGS),
          "",
          "`EXACT` = an exact theorem about the model it is stated over · `REDUCED` = exact only "
          "after a stated reduction (a dimensionless/lumped-factor form) · `APPROXIMATION` = the "
          "statement itself is approximate (documented idealization / limiting case) · "
          "`PURE-MATH` = infrastructure lemma, no physical claim. The tags are the authors' "
          "classification, reviewed result by result as each landed. Only the first 186-entry "
          "corpus was cross-checked in one pass against the literature "
          "(`reviews/literature-validity-audit.md`), and the then 412 results again on "
          "2026-07-09 (`docs/literature-validation.md`); later results have no whole-corpus "
          "literature audit.", ""]
    for m in mods:
        defs, results = m["defs"], m["results"]
        if not defs and not results:
            continue
        tc.append(f"## `{m['rel']}`  ({m['namespace']})")
        if m["role"] and m["role"] != "—":
            tc.append(f"*{m['role']}*")
        tc.append("")
        def_names = {name for _k, name, _s in defs}
        # tagged definition-like decls that are not plain `def`s (e.g. a `structure`)
        extra_models = sorted(name for (mod, name) in model_rows
                              if mod == m["rel"] and name not in def_names)
        if defs or extra_models:
            tc.append("**Definitions**")
            for _k, name, summ in defs:
                mt = model_rows.get((m["rel"], name))
                if mt:
                    citestr = f"  _[{mt[1]}]_" if mt[1] and mt[1] != "—" else ""
                    tc.append(f"- `model {mt[0]}` · `{name}` — {summ}{citestr}")
                else:
                    tc.append(f"- `{name}` — {summ}")
            for name in extra_models:
                kind, summ = m["models"][name]
                tag, cite = model_rows[(m["rel"], name)]
                citestr = f"  _[{cite}]_" if cite and cite != "—" else ""
                tc.append(f"- `model {tag}` · `{name}` ({kind}) — {summ}{citestr}")
            tc.append("")
        if results:
            tc.append("**Results**")
            for _k, name, summ in results:
                tag, cite = scope.get((m["rel"], name), ("UNTAGGED", "—"))
                citestr = f"  _[{cite}]_" if cite and cite != "—" else ""
                pub, via = pub_of((m["rel"], name))
                if pub != tag and tag != "UNTAGGED":
                    vias = ", ".join(f"`{v}`" for v in via.split(",")) if via != "—" else "—"
                    tc.append(f"- `{tag} → {pub}` · `{name}` — {summ}{citestr}  (via {vias})")
                else:
                    tc.append(f"- `{tag}` · `{name}` — {summ}{citestr}")
            tc.append("")
    outputs[ROOT / "docs" / "theorem-catalog.md"] = "\n".join(tc) + "\n"

    drift = [p for p, text in outputs.items()
             if not p.exists() or p.read_text(encoding="utf-8") != text]
    if args.check:
        for p in drift:
            print(f"gen-docs: OUT OF DATE {p.relative_to(ROOT)} — run scripts/gen-docs.sh")
    else:
        for p in drift:
            p.write_text(outputs[p], encoding="utf-8")

    if untagged or stale or bad_tag or row_errors or pub_errors or extra_errors:
        for e in row_errors + pub_errors + extra_errors:
            print(f"gen-docs: {e}")
        for k in untagged:
            print(f"gen-docs: UNTAGGED result — add to docs/scope-tags.tsv: {k[0]} :: {k[1]}")
        for k in stale:
            print(f"gen-docs: STALE scope-tag (no such result): {k[0]} :: {k[1]}")
        for k in bad_tag:
            print(f"gen-docs: BAD scope-tag value (not in {SCOPE_TAGS}): {k[0]} :: {k[1]}")
        print(f"gen-docs: scope-tag completeness FAILED "
              f"({len(untagged)} untagged, {len(stale)} stale, {len(bad_tag)} bad, "
              f"{len(row_errors)} malformed/duplicate, {len(pub_errors)} published-tag errors, "
              f"{len(extra_errors)} catalog/literature errors)")
        return 1
    if args.check and drift:
        return 1

    print(f"gen-docs: {len(mods)} modules, {tot_r} results, {tot_d} defs "
          f"-> docs/module-reference.md, docs/theorem-catalog.md; "
          f"all {len(result_keys)} results scope-tagged "
          f"({' '.join(f'{t}={mix.get(t,0)}' for t in SCOPE_TAGS)}); {len(model_rows)} model rows; "
          f"published ({' '.join(f'{t}={pub_mix.get(t,0)}' for t in SCOPE_TAGS)}), "
          f"{n_changed} weakened by a model tag")
    return 0


if __name__ == "__main__":
    sys.exit(main())
