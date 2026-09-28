#!/usr/bin/env python3
"""Validate the cflibs-formal theorem-card tree against the schema in IA-proposal §2 and the
check list in §4.1. Build-free (reads `docs/catalog.jsonl` + the TSVs; never invokes `lake`).

    scripts/check_cards.py [--catalog PATH] [--cards-dir PATH] [--root PATH] [--docs-dir PATH]
                            [--require-coverage]
    scripts/check_cards.py --selftest [--fixtures-dir PATH] ...

`--selftest` runs first, always: every fixture under `scripts/cards_selftest/fixtures/` must
produce EXACTLY its expected error (a substring listed in the sibling `.expect` file, or the
literal sentinel `OK` for a fixture that must pass cleanly) — the positive control the anchor
validator and check_cards.py itself both rely on (IA-proposal §1.4, §4.1). If any fixture's
outcome does not match its expectation, `--selftest` FAILS LOUDLY and the real cards are never
checked (a broken checker must not report a false "clean").

Exit code: 0 if every check (and, under `--selftest`, every fixture) passes; 1 otherwise.
Coverage against `docs/theorems/registry/cards.yaml` is ADVISORY unless `--require-coverage` is
given (Phase 1 is incremental; IA-proposal §5, §4.1's "Coverage" row).
"""
from __future__ import annotations

import argparse
import os
import hashlib
import pathlib
import re
import sys

import gen_cards as gc  # same directory; the two scripts share one catalog/card-loading layer

try:
    import yaml
except ImportError:  # pragma: no cover
    yaml = None

ID_RE = re.compile(r"^[a-z0-9]+(?:\.[a-z0-9-]+)+$")

KIND_VALUES = {"result", "family", "counterexample", "model"}
DEPTH_VALUES = {"full", "brief"}
STATUS_LEAN_VALUES = {"proved", "partial", "stated", "parked"}
STATUS_PIPELINE_VALUES = {"none", "referenced", "wired", "tested"}
STATUS_PIPELINE_RELIANCE_VALUES = {"none", "implicit", "explicit"}
STATUS_CERTIFICATE_VALUES = {"n/a", "not-implemented", "stated", "wired"}
CITATION_ROLE_VALUES = {"model-source", "estimator-context", "consistent-with-measurement",
                         "prior-art", "corroborating", "convention"}
PIPELINE_RELATION_VALUES = {"implements", "mirrors", "assumes", "tension", "narrows", "proposed",
                             "none"}
CERT_RELATION_VALUES = {"implements", "building-block", "premise", "narrows",
                         "proposes-replacement"}
OPEN_ITEM_KIND_VALUES = {"lean", "docstring", "citation", "pipeline", "model-row",
                          "owner-decision"}
WHITELIST_STATUS_VALUES = {"VERIFIED", "CORRECTED", "AUDIT-VETTED", "UNVERIFIED", "SUSPECT",
                            "CONVENTION"}
REQUIRED_KEYS = ["schema", "id", "title", "kind", "depth", "summary", "lean", "status",
                  "open_items", "provenance", "updated"]
REQUIRED_STATUS_KEYS = ["lean", "pipeline", "pipeline_reliance"]

FULL_SECTIONS = ["1. Statement", "2. Physical meaning", "3. Scope and validity", "4. Proof idea",
                  "5. Role in the composition-extraction pipeline", "6. Status and remaining work",
                  "7. Literature", "8. Provenance"]
BRIEF_SECTIONS = ["1. Statement", "3. Scope and validity", "6. Status and remaining work"]

ABS_PATH_PATTERNS = [
    (re.compile(r"/home/"), "/home/ path"),
    (re.compile(r"/root/"), "/root/ path"),
    (re.compile(r"/Users/"), "/Users/ path"),
    (re.compile(r"[A-Za-z]:\\"), "drive-letter path"),
    (re.compile(r"\b(?:10(?:\.\d{1,3}){3}|192\.168(?:\.\d{1,3}){2}|100\.(?:6[4-9]|[7-9]\d|1[01]\d"
                r"|12[0-7])(?:\.\d{1,3}){2})\b"), "private IP address"),
    # CF-LIBS-improved (private) backlog id conventions — D23 / SCHEMA.md "Disclosure rules"
    (re.compile(r"\bBL-\d+\b"), "CF-LIBS-improved backlog id"),
    (re.compile(r"\bR\d{1,2}-\d+\b"), "CF-LIBS-improved backlog id"),
    (re.compile(r"\bTS-\d+\b"), "CF-LIBS-improved backlog id"),
    (re.compile(r"\bSC-\d+\b"), "CF-LIBS-improved backlog id"),
    (re.compile(r"\bW3-[A-Z\d]+\b"), "CF-LIBS-improved backlog id"),
    (re.compile(r"\bG[12]\b"), "CF-LIBS-improved backlog id"),
]

# Machine names are deliberately NOT listed here: this checker is public, and a list of the
# owner's hosts would itself be the disclosure D23 forbids. A maintainer may keep one regex per
# line in a git-ignored `.disclosure-denylist` at the repo root (or point CARDS_DENYLIST at a
# file); each line is then checked as "machine name". CI has no such file and skips this check.
def load_local_denylist(root: pathlib.Path) -> list[tuple[re.Pattern, str]]:
    """Optional, local-only extra ABS-PATH patterns (see the comment above)."""
    path = pathlib.Path(os.environ.get("CARDS_DENYLIST") or root / ".disclosure-denylist")
    if not path.is_file():
        return []
    return [(re.compile(line.strip()), "machine name")
            for line in path.read_text(encoding="utf-8").splitlines()
            if line.strip() and not line.startswith("#")]
ANCHOR_RE = re.compile(r"\b((?:[A-Za-z][\w./-]*/)?[A-Za-z][\w'-]*\.lean)#([A-Za-z_][\w'.]*)")
# A GitHub line-number fragment (`File.lean#L42`, as the generated Facts block itself links) is
# not a `File.lean#decl` cross-reference — never resolved as a declaration name.
GITHUB_LINE_FRAGMENT_RE = re.compile(r"^L\d+$")
FRONTIER_AMBIGUOUS_RE = re.compile(r"\bfrontier\s+\d+\b", re.I)


class Findings(list):
    """A list of "CODE: message" strings for one card (or the repo-wide pass)."""

    def add(self, code: str, message: str) -> None:
        self.append(f"{code}: {message}")


# ---------------------------------------------------------------------------------------------
# Per-card checks (schema, resolution, hash, sections, citations, registry ids, evidence).
# ---------------------------------------------------------------------------------------------

def check_schema(fm: dict) -> Findings:
    f = Findings()
    for key in REQUIRED_KEYS:
        if key not in fm or fm[key] in (None, ""):
            f.add("SCHEMA", f"missing required key '{key}'")
    if fm.get("schema") not in (None, "card/v1"):
        f.add("SCHEMA", f"unknown schema version {fm.get('schema')!r} (expected 'card/v1')")
    cid = fm.get("id")
    if cid is not None and not ID_RE.match(str(cid)):
        f.add("SCHEMA", f"id {cid!r} does not match ^[a-z0-9]+(\\.[a-z0-9-]+)+$")
    if "kind" in fm and fm["kind"] not in KIND_VALUES:
        f.add("VOCAB", f"kind {fm['kind']!r} not in {sorted(KIND_VALUES)}")
    if "depth" in fm and fm["depth"] not in DEPTH_VALUES:
        f.add("VOCAB", f"depth {fm['depth']!r} not in {sorted(DEPTH_VALUES)}")
    lean = fm.get("lean")
    if not isinstance(lean, dict) or not lean.get("decl"):
        f.add("SCHEMA", "missing required key 'lean.decl'")
    if not isinstance(lean, dict) or not isinstance(lean.get("reviewed"), dict):
        f.add("SCHEMA", "missing required key 'lean.reviewed' ({commit, statement_hash, by, "
                        "method})")
    else:
        for k in ("commit", "statement_hash", "by", "method"):
            if not lean["reviewed"].get(k):
                f.add("SCHEMA", f"lean.reviewed.{k} is missing or empty")
    status = fm.get("status")
    if not isinstance(status, dict):
        f.add("SCHEMA", "missing required key 'status'")
    else:
        for k in REQUIRED_STATUS_KEYS:
            if k not in status:
                f.add("SCHEMA", f"missing required key 'status.{k}'")
        if status.get("lean") is not None and status["lean"] not in STATUS_LEAN_VALUES:
            f.add("VOCAB", f"status.lean {status['lean']!r} not in {sorted(STATUS_LEAN_VALUES)}")
        if status.get("pipeline") is not None and status["pipeline"] not in STATUS_PIPELINE_VALUES:
            f.add("VOCAB", f"status.pipeline {status['pipeline']!r} not in "
                            f"{sorted(STATUS_PIPELINE_VALUES)}")
        pr = status.get("pipeline_reliance")
        if pr is not None and pr not in STATUS_PIPELINE_RELIANCE_VALUES:
            f.add("VOCAB", f"status.pipeline_reliance {pr!r} not in "
                            f"{sorted(STATUS_PIPELINE_RELIANCE_VALUES)}")
        cert = status.get("certificate")
        if cert is not None and cert not in STATUS_CERTIFICATE_VALUES:
            f.add("VOCAB", f"status.certificate {cert!r} not in "
                            f"{sorted(STATUS_CERTIFICATE_VALUES)}")
        if fm.get("certificates") and cert is None:
            f.add("SCHEMA", "status.certificate is required when 'certificates[]' is non-empty "
                             "(SCHEMA.md front-matter table)")
    if fm.get("open_items") is None:
        f.add("SCHEMA", "'open_items' must be present (a list; may be empty)")
    for item in fm.get("open_items") or []:
        if isinstance(item, dict):
            if item.get("kind") not in OPEN_ITEM_KIND_VALUES:
                f.add("VOCAB", f"open_items[].kind {item.get('kind')!r} not in "
                                f"{sorted(OPEN_ITEM_KIND_VALUES)}")
            if not item.get("text"):
                f.add("SCHEMA", "open_items[] entry has no 'text'")
        else:
            f.add("SCHEMA", f"open_items[] entry {item!r} is not a mapping ({{kind, text, ref?}})")
    for c in fm.get("citations") or []:
        if not isinstance(c, dict) or not c.get("key"):
            f.add("SCHEMA", f"citations[] entry {c!r} has no 'key'")
        elif c.get("role") is not None and c["role"] not in CITATION_ROLE_VALUES:
            f.add("VOCAB", f"citations[].role {c['role']!r} not in {sorted(CITATION_ROLE_VALUES)}")
    for p in fm.get("pipeline") or []:
        if isinstance(p, dict) and p.get("relation") is not None \
                and p["relation"] not in PIPELINE_RELATION_VALUES:
            f.add("VOCAB", f"pipeline[].relation {p['relation']!r} not in "
                            f"{sorted(PIPELINE_RELATION_VALUES)}")
    for c in fm.get("certificates") or []:
        if isinstance(c, dict) and c.get("relation") is not None \
                and c["relation"] not in CERT_RELATION_VALUES:
            f.add("VOCAB", f"certificates[].relation {c['relation']!r} not in "
                            f"{sorted(CERT_RELATION_VALUES)}")
    return f


def check_filename(path: pathlib.Path, fm: dict) -> Findings:
    f = Findings()
    cid = fm.get("id")
    if cid is not None and path.stem != cid:
        f.add("FILENAME", f"filename stem {path.stem!r} != id {cid!r}")
    return f


def check_resolution(fm: dict, catalog: dict) -> tuple[Findings, list[tuple[str, str]]]:
    """Returns (findings, resolved [(label, fq_name)] in card order — headline first)."""
    f = Findings()
    order: list[tuple[str, str]] = []
    for label, name in gc.ordered_decls(fm):
        resolved, candidates = gc.resolve_name(name, catalog)
        if resolved:
            order.append((label, resolved))
        elif candidates:
            f.add("AMBIGUOUS", f"{label} '{name}' matches {len(candidates)} catalog names: "
                                f"{', '.join(candidates)}")
        else:
            f.add("RESOLVE", f"{label} '{name}' does not resolve in the catalog")
    return f, order


def check_statement_hash(fm: dict, order: list[tuple[str, str]], catalog: dict) -> Findings:
    f = Findings()
    if not order:
        return f
    current = gc.compute_statement_hash([catalog[n] for _l, n in order])
    reviewed = ((fm.get("lean") or {}).get("reviewed")) or {}
    reviewed_hash = reviewed.get("statement_hash")
    if not reviewed_hash:
        f.add("HASH-MISSING", "lean.reviewed.statement_hash is not set — run "
                               "`gen_cards.py --stamp <id>` after review")
    elif reviewed_hash != current:
        f.add("HASH-STALE", f"lean.reviewed.statement_hash ({reviewed_hash}) != current "
                             f"({current}) — LaTeX must be re-reviewed and the card re-stamped")
    return f


def check_binder_coverage(fm: dict, body: str, order: list[tuple[str, str]],
                           catalog: dict) -> Findings:
    """Every named (non "_") outermost binder of the headline + members must appear in backticks
    somewhere in the '## 1. Statement' H2 section (IA-proposal §2.3's binder-coverage rule)."""
    f = Findings()
    if not order:
        return f
    section = extract_h2_section(body, "1. Statement")
    for label, name in order:
        rec = catalog.get(name)
        if not rec:
            continue
        for b in rec.get("binders") or []:
            if b == "_":
                continue
            if section is None or f"`{b}`" not in section:
                f.add("BINDER", f"{label} '{name}' binder `{b}` is not named in backticks in "
                                 "'## 1. Statement'")
    return f


def extract_h2_section(body: str, heading: str) -> str | None:
    """Text of a `## <heading>` section (up to the next `## `), or None if absent. Matches the
    heading text after stripping a leading '#'*N + space, ignoring extra whitespace."""
    lines = body.splitlines()
    start = None
    for i, line in enumerate(lines):
        m = re.match(r"^##\s+(.*\S)\s*$", line)
        if m and m.group(1).strip() == heading:
            start = i + 1
            break
    if start is None:
        return None
    end = len(lines)
    for j in range(start, len(lines)):
        if re.match(r"^##\s+\S", lines[j]) and not lines[j].startswith("###"):
            end = j
            break
    return "\n".join(lines[start:end])


def check_sections(fm: dict, body: str) -> Findings:
    f = Findings()
    depth = fm.get("depth")
    required = FULL_SECTIONS if depth == "full" else BRIEF_SECTIONS if depth == "brief" else []
    for heading in required:
        if extract_h2_section(body, heading) is None:
            f.add("SECTION", f"required section '## {heading}' is missing")
    scope_section = extract_h2_section(body, "3. Scope and validity")
    if scope_section is not None:
        m = re.search(r"does not claim", scope_section, re.I)
        if not m:
            f.add("DOES-NOT-CLAIM", "'## 3. Scope and validity' has no 'does NOT claim' "
                                     "subsection")
        else:
            tail = scope_section[m.end():]
            # content before the next bold/heading marker or end of section
            stop = re.search(r"\n\s*\n\s*\*\*|\n##|\Z", tail)
            content = tail[: stop.start() if stop else None]
            # "empty" means no actual word content remains — not merely that a stray character
            # (the bold marker's closing '.', '*', punctuation) survives naive stripping.
            if not re.search(r"\w", content):
                f.add("DOES-NOT-CLAIM", "'does NOT claim' subsection is empty")
    return f


def check_citations(fm: dict, whitelist: dict) -> Findings:
    f = Findings()
    for c in fm.get("citations") or []:
        if not isinstance(c, dict):
            continue
        key = c.get("key")
        if not key:
            continue
        status = whitelist.get(key)
        if status is None:
            f.add("CITATION-KEY", f"citation key '{key}' is not in docs/citation-whitelist.tsv")
        elif status == "SUSPECT":
            f.add("CITATION-SUSPECT", f"citation key '{key}' is whitelisted SUSPECT — must not "
                                       "support any claim")
        if c.get("locator") and status not in ("VERIFIED", "CORRECTED"):
            f.add("CITATION-ROLE", f"citation '{key}' has a locator but whitelist status is "
                                    f"{status!r} (locator allowed only for VERIFIED/CORRECTED)")
    return f


def check_registry_ids(fm: dict, decisions: set[str], frontier_ids: set[str] | None,
                        cert_ids: set[str] | None) -> Findings:
    f = Findings()
    for d in fm.get("decisions") or []:
        if d not in decisions:
            f.add("REGISTRY-DECISION", f"decision {d!r} has no row in docs/decisions.md")
    frontier = fm.get("frontier")
    if isinstance(frontier, dict):
        for fid in frontier.get("ids") or []:
            if frontier_ids is not None and fid not in frontier_ids:
                f.add("REGISTRY-FRONTIER", f"frontier id {fid!r} not in "
                                            "docs/theorems/registry/frontier.yaml")
    for c in fm.get("certificates") or []:
        cid = c.get("id") if isinstance(c, dict) else c
        if cert_ids is not None and cid not in cert_ids:
            f.add("REGISTRY-CERT", f"certificate id {cid!r} not in "
                                    "docs/theorems/registry/certificates.yaml")
    return f


def check_evidence(fm: dict, root: pathlib.Path) -> Findings:
    f = Findings()
    for e in fm.get("evidence") or []:
        if not isinstance(e, dict) or not e.get("file"):
            f.add("EVIDENCE-MISSING", f"evidence[] entry {e!r} has no 'file'")
            continue
        p = root / e["file"]
        if not p.exists():
            f.add("EVIDENCE-MISSING", f"evidence file not found: {e['file']}")
            continue
        want = e.get("sha256")
        if want:
            got = hashlib.sha256(p.read_bytes()).hexdigest()
            if got != want:
                f.add("EVIDENCE-SHA", f"{e['file']}: sha256 {got} != recorded {want}")
    return f


def check_frontier_ambiguous(text: str, where: str) -> Findings:
    """SCHEMA.md 'Frontier numbering': a bare 'frontier 01'/'Frontier 2' string is ambiguous
    between the FT-NN audit slate and the legacy Fnn dossiers — new prose must write one of the
    two explicitly."""
    f = Findings()
    m = FRONTIER_AMBIGUOUS_RE.search(text)
    if m:
        f.add("FRONTIER-AMBIGUOUS", f"{where}: ambiguous {m.group(0)!r} — write 'FT-NN' or "
                                     "'Fnn' (docs/frontiers/NN-...) explicitly")
    return f


def check_no_absolute_paths(text: str, where: str, extra=()) -> Findings:
    f = Findings()
    for pat, label in [*ABS_PATH_PATTERNS, *extra]:
        m = pat.search(text)
        if m:
            f.add("ABS-PATH", f"{where}: {label} ({m.group(0)!r})")
    return f


_SCOPE_CACHE: dict = {}


def check_scope_prose(fm: dict, body: str, order, catalog: dict, root: pathlib.Path) -> Findings:
    """Every bolded scope tag in '## 3. Scope and validity' (e.g. **REDUCED**) must be one of the
    own, published or model tags of the card's declarations in docs/scope-tags.tsv /
    docs/scope-published.tsv. The Facts block is authoritative; this keeps the prose from going
    stale when a tag changes. Skipped when no scope row is found (e.g. the self-test fixtures)."""
    f = Findings()
    section = extract_h2_section(body, "3. Scope and validity")
    if section is None:
        return f
    key = str(root)
    if key not in _SCOPE_CACHE:
        tags_p, pub_p = root / "docs" / "scope-tags.tsv", root / "docs" / "scope-published.tsv"
        _SCOPE_CACHE[key] = (gc.load_scope_tags(tags_p) if tags_p.exists() else {},
                             gc.load_scope_published(pub_p))
    scope_tags, published = _SCOPE_CACHE[key]
    # The card's own declarations, plus any declaration §3 names in backticks (prose may state the
    # tag of a related result, e.g. "the **REDUCED** closure of `multiElement_exists_pos_fixedPoint`").
    names = [name for _label, name in order or []]
    by_leaf: dict[str, list[str]] = {}
    for full in catalog:
        by_leaf.setdefault(full.rsplit(".", 1)[-1], []).append(full)
    for tok in re.findall(r"`([A-Za-z_][\w.']*)`", section):
        names += [c for c in (tok, "CflibsFormal." + tok) if c in catalog] or by_leaf.get(tok, [])
    allowed: set[str] = set()
    for name in names:
        rec = catalog.get(name)
        if not rec:
            continue
        row = gc.scope_row(rec, scope_tags)
        if row:
            allowed.add(row[0])
        module_rel, qualified, leaf = gc.scope_lookup_keys(rec)
        pub = published.get((module_rel, qualified)) or published.get((module_rel, leaf))
        if pub:
            allowed.update({pub[1], pub[2]})
    if not allowed:
        return f
    for m in re.finditer(r"\*\*(EXACT|REDUCED|APPROXIMATION|PURE-MATH)\*\*", section):
        if m.group(1) not in allowed:
            f.add("SCOPE-PROSE", f"§3 states **{m.group(1)}** but the card's declarations and those "
                                 f"§3 names carry only {sorted(allowed)} (docs/scope-tags.tsv, "
                                 f"scope-published.tsv)")
    return f


def check_card(path: pathlib.Path, catalog: dict, whitelist: dict, decisions: set[str],
               frontier_ids, cert_ids, root: pathlib.Path) -> Findings:
    findings = Findings()
    try:
        fm, body, _fm_text = gc.load_card(path)
    except gc.CardError as e:
        findings.add("SCHEMA", f"{path.name}: {e}")
        return findings
    findings += check_schema(fm)
    findings += check_filename(path, fm)
    res, order = check_resolution(fm, catalog)
    findings += res
    findings += check_statement_hash(fm, order, catalog)
    findings += check_binder_coverage(fm, body, order, catalog)
    findings += check_sections(fm, body)
    findings += check_scope_prose(fm, body, order, catalog, root)
    findings += check_citations(fm, whitelist)
    findings += check_registry_ids(fm, decisions, frontier_ids, cert_ids)
    findings += check_evidence(fm, root)
    raw = path.read_text(encoding="utf-8")
    deny = load_local_denylist(root)
    findings += check_no_absolute_paths(raw, path.name, deny)
    # Evidence files are published next to the card, so the same disclosure rules apply to them.
    ev_dir = path.parent / "evidence" / path.stem
    for ev in sorted(ev_dir.rglob("*")) if ev_dir.is_dir() else []:
        if ev.is_file() and ev.stat().st_size < 2_000_000:
            text = ev.read_text(encoding="utf-8", errors="replace")
            findings += check_no_absolute_paths(text, str(ev.relative_to(path.parent)), deny)
    findings += check_frontier_ambiguous(raw, path.name)
    return findings


# ---------------------------------------------------------------------------------------------
# Repo-wide checks: one-card-per-declaration, docs/**/*.md anchors, coverage.
# ---------------------------------------------------------------------------------------------

def check_one_card_per_decl(cards: list[tuple[pathlib.Path, dict]], catalog: dict) -> Findings:
    f = Findings()
    owner: dict[str, str] = {}
    for path, fm in cards:
        try:
            for _label, name in gc.ordered_decls(fm):
                resolved, _c = gc.resolve_name(name, catalog)
                key = resolved or name
                if key in owner and owner[key] != path.stem:
                    f.add("DUP-DECL", f"'{key}' is claimed by both '{owner[key]}' and "
                                       f"'{path.stem}'")
                else:
                    owner[key] = path.stem
        except Exception:
            continue
    return f


def check_docs_anchors(docs_dir: pathlib.Path, catalog: dict) -> Findings:
    f = Findings()
    if not docs_dir.exists():
        return f
    for path in sorted(docs_dir.rglob("*.md")):
        text = path.read_text(encoding="utf-8")
        for m in ANCHOR_RE.finditer(text):
            file_part, decl = m.group(1), m.group(2)
            if GITHUB_LINE_FRAGMENT_RE.match(decl):
                continue
            resolved, candidates = gc.resolve_name(decl, catalog)
            if not resolved:
                what = "no match" if not candidates else f"ambiguous: {', '.join(candidates)}"
                f.add("ANCHOR-UNRESOLVED",
                      f"{path.relative_to(docs_dir.parent)}: '{file_part}#{decl}' ({what})")
    return f


def load_yaml_ids(path: pathlib.Path) -> set[str] | None:
    """A registry file's top-level keys as ids; None if the file does not exist (checks against
    it are then skipped, not failed — the registries are a later, separate deliverable)."""
    if not path.exists():
        return None
    if yaml is None:
        return None
    with open(path, encoding="utf-8") as fh:
        data = yaml.safe_load(fh) or {}
    if isinstance(data, dict):
        return set(data.keys())
    if isinstance(data, list):
        return {d.get("id") if isinstance(d, dict) else d for d in data}
    return set()


def load_decision_ids(path: pathlib.Path) -> set[str]:
    if not path.exists():
        return set()
    return set(re.findall(r"\|\s*(D\d+)\s*\|", path.read_text(encoding="utf-8")))


def check_coverage(cards_dir: pathlib.Path, cards: list[tuple[pathlib.Path, dict]], catalog: dict,
                    require: bool) -> tuple[Findings, str]:
    registry = gc.load_registry_cards(cards_dir)
    if registry is None:
        return Findings(), "docs/theorems/registry/cards.yaml not found — coverage not tracked"
    covered: set[str] = set()
    for _path, fm in cards:
        for _label, name in gc.ordered_decls(fm):
            resolved, _c = gc.resolve_name(name, catalog)
            covered.add(resolved or name)
    planned = gc.planned_decls_from_registry(registry)
    missing = sorted(planned - covered)
    f = Findings()
    if missing and require:
        for d in missing:
            f.add("COVERAGE", f"planned declaration '{d}' has no card")
    summary = f"{len(planned) - len(missing)}/{len(planned)} planned declarations covered" \
        + (f" ({len(missing)} advisory gap(s))" if missing and not require else "")
    return f, summary


# ---------------------------------------------------------------------------------------------
# Driver.
# ---------------------------------------------------------------------------------------------

def run_all(root: pathlib.Path, catalog_path: pathlib.Path, cards_dir: pathlib.Path,
            docs_dir: pathlib.Path, require_coverage: bool) -> tuple[bool, list[str]]:
    report: list[str] = []
    if not catalog_path.exists():
        return False, [f"catalog not found: {catalog_path}"]
    try:
        catalog = gc.load_catalog(catalog_path)
    except gc.CardError as e:
        return False, [f"catalog: {e}"]

    whitelist_path = root / "docs" / "citation-whitelist.tsv"
    whitelist = gc.load_whitelist(whitelist_path) if whitelist_path.exists() else {}
    decisions = load_decision_ids(root / "docs" / "decisions.md")
    frontier_ids = load_yaml_ids(cards_dir / "registry" / "frontier.yaml")
    cert_ids = load_yaml_ids(cards_dir / "registry" / "certificates.yaml")

    paths = gc.iter_card_paths(cards_dir)
    ok = True
    all_cards: list[tuple[pathlib.Path, dict]] = []
    for path in paths:
        findings = check_card(path, catalog, whitelist, decisions, frontier_ids, cert_ids, root)
        try:
            fm, _b, _f = gc.load_card(path)
            all_cards.append((path, fm))
        except gc.CardError:
            pass
        if findings:
            ok = False
            report.append(f"{path.name}:")
            for msg in findings:
                report.append(f"  {msg}")
        else:
            report.append(f"{path.name}: OK")

    repo_findings = check_one_card_per_decl(all_cards, catalog)
    repo_findings += check_docs_anchors(docs_dir, catalog)
    if repo_findings:
        ok = False
        report.append("(repo-wide):")
        for msg in repo_findings:
            report.append(f"  {msg}")

    cov_findings, cov_summary = check_coverage(cards_dir, all_cards, catalog, require_coverage)
    report.append(f"coverage: {cov_summary}")
    if cov_findings:
        ok = False
        report.append("  " + "; ".join(cov_findings))

    report.append(f"{len(paths)} card(s) checked: {'OK' if ok else 'FAIL'}")
    return ok, report


def run_selftest(fixtures_dir: pathlib.Path) -> tuple[bool, list[str]]:
    report: list[str] = []
    if not fixtures_dir.exists():
        return False, [f"selftest: fixtures dir not found: {fixtures_dir}"]
    support = fixtures_dir.parent / "support"
    catalog_path = support / "catalog.jsonl"
    if not catalog_path.exists():
        return False, [f"selftest: support catalog not found: {catalog_path}"]
    catalog = gc.load_catalog(catalog_path)
    whitelist = gc.load_whitelist(support / "citation-whitelist.tsv")
    decisions = load_decision_ids(support / "decisions.md")
    frontier_ids = load_yaml_ids(support / "registry" / "frontier.yaml")
    cert_ids = load_yaml_ids(support / "registry" / "certificates.yaml")

    cases = sorted(p for p in fixtures_dir.glob("*.md"))
    if not cases:
        return False, [f"selftest: no fixtures under {fixtures_dir}"]
    all_ok = True
    for card_path in cases:
        expect_path = card_path.with_suffix(".expect")
        if not expect_path.exists():
            report.append(f"selftest FAIL {card_path.name}: no sibling .expect file")
            all_ok = False
            continue
        expected = expect_path.read_text(encoding="utf-8").strip()
        findings = check_card(card_path, catalog, whitelist, decisions, frontier_ids, cert_ids,
                               support)
        if expected == "OK":
            if not findings:
                report.append(f"selftest ok   {card_path.name}: clean, as expected")
            else:
                report.append(f"selftest FAIL {card_path.name}: expected OK, got: "
                               f"{'; '.join(findings)}")
                all_ok = False
        else:
            if any(expected in msg for msg in findings):
                report.append(f"selftest ok   {card_path.name}: found expected {expected!r}")
            else:
                got = "; ".join(findings) if findings else "(no findings)"
                report.append(f"selftest FAIL {card_path.name}: expected {expected!r}, got: {got}")
                all_ok = False
    # Repo-wide checks (DUP-DECL, ANCHOR-UNRESOLVED, COVERAGE) act on a whole card tree / docs
    # tree at once, so they cannot be exercised by check_card() on one fixture in isolation —
    # each gets its own small multi-file scenario under repo_fixtures/<name>/expect.
    repo_dir = fixtures_dir.parent / "repo_fixtures"
    repo_cases = sorted(p for p in repo_dir.iterdir() if p.is_dir()) if repo_dir.exists() else []
    for case_dir in repo_cases:
        expect_path = case_dir / "expect"
        if not expect_path.exists():
            report.append(f"selftest FAIL repo_fixtures/{case_dir.name}: no 'expect' file")
            all_ok = False
            continue
        expected = expect_path.read_text(encoding="utf-8").strip()
        if case_dir.name == "dup-decl":
            cards = []
            for p in gc.iter_card_paths(case_dir):
                fm, _b, _f = gc.load_card(p)
                cards.append((p, fm))
            findings = check_one_card_per_decl(cards, catalog)
        elif case_dir.name == "anchor-unresolved":
            findings = check_docs_anchors(case_dir, catalog)
        elif case_dir.name == "coverage":
            findings, _summary = check_coverage(case_dir, [], catalog, require=True)
        else:
            report.append(f"selftest FAIL repo_fixtures/{case_dir.name}: unknown scenario name")
            all_ok = False
            continue
        # Exact match, not mere containment: each repo_fixtures/ scenario is built to trip
        # exactly one finding, so an extra unexpected finding (e.g. a false-positive regression
        # like flagging the Facts block's own `#L<n>` links) must fail the selftest too.
        matches = [msg for msg in findings if expected in msg]
        if len(matches) == 1 and len(findings) == 1:
            report.append(f"selftest ok   repo_fixtures/{case_dir.name}: found expected "
                           f"{expected!r}, nothing else")
        else:
            got = "; ".join(findings) if findings else "(no findings)"
            report.append(f"selftest FAIL repo_fixtures/{case_dir.name}: expected exactly one "
                           f"finding containing {expected!r}, got: {got}")
            all_ok = False

    report.append(f"selftest: {len(cases)} per-card fixture(s) + {len(repo_cases)} repo-wide "
                   f"scenario(s), {'ALL OK' if all_ok else 'FAILED'}")
    return all_ok, report


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                  formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--root", type=pathlib.Path,
                     default=pathlib.Path(__file__).resolve().parent.parent)
    ap.add_argument("--catalog", type=pathlib.Path, default=None)
    ap.add_argument("--cards-dir", type=pathlib.Path, default=None)
    ap.add_argument("--docs-dir", type=pathlib.Path, default=None,
                     help="root to scan for File.lean#decl cross-reference anchors "
                          "(default: <root>/docs); the no-absolute-path and frontier-numbering "
                          "checks are card-scoped, not run over this whole tree")
    ap.add_argument("--selftest", action="store_true")
    ap.add_argument("--fixtures-dir", type=pathlib.Path, default=None)
    ap.add_argument("--require-coverage", action="store_true")
    args = ap.parse_args(argv)

    if yaml is None:
        gc.require_yaml()  # exits with the standard message

    root = args.root.resolve()
    cards_dir = args.cards_dir or (root / "docs" / "theorems")
    catalog_path = args.catalog or (root / "docs" / "catalog.jsonl")
    docs_dir = args.docs_dir or (root / "docs")

    if args.selftest:
        fixtures_dir = args.fixtures_dir or (pathlib.Path(__file__).resolve().parent
                                              / "cards_selftest" / "fixtures")
        ok, report = run_selftest(fixtures_dir)
        print("\n".join(report))
        if not ok:
            print("check_cards: --selftest FAILED — refusing to check the real cards until the "
                  "checker's own positive control passes", file=sys.stderr)
            return 1
        print()

    ok, report = run_all(root, catalog_path, cards_dir, docs_dir, args.require_coverage)
    print("\n".join(report))
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
