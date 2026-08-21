#!/usr/bin/env bash
# Citation-string hygiene ADVISORY for cflibs-formal. Always exits 0.
#
# ============================================================================================
# WHAT THIS SCRIPT CAN PROVE
#   * Exactly which citation strings occur in docs/scope-tags.tsv column 4, and how often.
#   * Which of those strings occur in only one place across the whole repo (TSV rows + the
#     `## Literature` docstring blocks) — a string with a single occurrence is the shape a typo
#     or an accidental variant takes, so it is worth a human glance.
#   * Which pairs of citation strings are textually SIMILAR after normalization (accents, dashes,
#     `&`/`and`, punctuation, case) — candidate variants of one source.
#   * Which citation strings are absent from docs/citation-whitelist.tsv.
#   * Which whitelisted sources in use are NOT statused VERIFIED/CORRECTED — i.e. no primary
#     source is on record as having been opened for them.
#   * Which four-digit years appear in `## Literature` prose but belong to no whitelist row —
#     candidate sources named in a docstring that the whitelist has never acknowledged.
#
# WHAT THIS SCRIPT CANNOT PROVE — and never will
#   * That any cited paper EXISTS. It is offline and reads only this repo.
#   * That a DOI resolves, or resolves to the right record.
#   * That an author wrote what is attributed to them. The failure that cost this repo most was
#     a real author credited with an invented result ("the Noda Wronskian"); every string
#     involved was well-formed and this script would have reported nothing.
#   * That a constant, sign, or inequality direction matches the source.
#   * That a well-formed citation is not wholly fabricated. "Corsi et al. (2000), Appl.
#     Spectrosc. 54(4) 623-633" had a title, journal, volume, pages and a resolving DOI, and did
#     not exist.
#
# A SIMILARITY FLAG IS NOT A DEFECT REPORT. "Griem 1974" and "Griem 1997" trip it and are two
# different books by the same author. Every flag below means "look at this", never "this is a
# typo". Likewise a clean run means "no string-level anomaly found", never "citations verified".
#
# ONLY .claude/skills/citation-integrity/SKILL.md verifies anything: open the primary source,
# locate the claimed sentence/equation, and record one of VERIFIED / CORRECTED / UNVERIFIED /
# SUSPECT-OR-FABRICATED.
#
# Exit code is ALWAYS 0 by design: an offline string check must not be able to certify or block.
# Dependency-light: bash + python3 stdlib only. Read-only. No Lean invocation.
# ============================================================================================
set -uo pipefail
cd "$(dirname "$0")/.."

python3 - "$PWD" <<'PY'
import pathlib, re, sys, unicodedata, difflib
from collections import Counter, defaultdict

ROOT = pathlib.Path(sys.argv[1])
SRC = ROOT / "CflibsFormal"
TSV = ROOT / "docs" / "scope-tags.tsv"
WL = ROOT / "docs" / "citation-whitelist.tsv"

EMPTY = {"", "—", "-", "–"}          # em-dash is the repo's "no citation" marker
SIM_THRESHOLD = 0.75
# statuses that mean a primary source is on record as OPENED (see the skill)
EVIDENCED = {"VERIFIED", "CORRECTED"}
# statuses that carry nothing to open
NOTHING_TO_OPEN = {"CONVENTION"}


def norm(s: str) -> str:
    """Fold accents, dashes, ampersands, punctuation and case for variant detection."""
    s = unicodedata.normalize("NFKD", s)
    s = "".join(c for c in s if not unicodedata.combining(c))
    s = s.replace("–", "-").replace("—", "-").replace("&", " and ")
    return re.sub(r"[^a-z0-9]+", " ", s.lower()).strip()


def surnames(cit: str) -> list[str]:
    """Capitalized name-shaped tokens of a citation string (for prose corroboration)."""
    base = unicodedata.normalize("NFKD", cit)
    base = "".join(c for c in base if not unicodedata.combining(c))
    toks = re.split(r"[^A-Za-z]+", base)
    # Deliberately unfiltered: any capitalized 3+ token counts. A compound like "Saha-Eggert"
    # or a parenthetical source pointer like "(Griem)" yields several tokens and ANY of them
    # matching prose is enough — this check is for corroboration, where a false match is
    # cheap and a false miss sends a reader looking for a gap that is not there.
    return [t for t in toks if len(t) > 2 and t[0].isupper()]


def years_of(s: str) -> set[str]:
    return set(re.findall(r"\b(1[6-9]\d\d|20\d\d)\b", s))


print("== citation-integrity ADVISORY (string hygiene only; ALWAYS exit 0) ==")
print("   Proves: string-level anomalies in this repo.  Proves NOT: that any paper exists,")
print("   that a DOI resolves, or that an author wrote what is attributed to them.")
print("   Verification lives in .claude/skills/citation-integrity/SKILL.md — open the source.")
print("")

# --- 1. citation strings from docs/scope-tags.tsv column 4 ----------------------------------
if not TSV.exists():
    print(f"check-citations: MISSING {TSV} — nothing to check.")
    sys.exit(0)

tsv_counts: Counter = Counter()
tsv_modules: dict[str, set[str]] = defaultdict(set)
malformed = 0
for line in TSV.read_text(encoding="utf-8").splitlines():
    if not line.strip() or line.lstrip().startswith("#"):
        continue
    parts = line.split("\t")
    if len(parts) != 4:
        malformed += 1
        continue
    module, _name, _tag, cit = (p.strip() for p in parts)
    if cit in EMPTY:
        continue
    tsv_counts[cit] += 1
    tsv_modules[cit].add(module)

print(f"-- scope-tags.tsv column 4 --")
print(f"   distinct citation strings: {len(tsv_counts)}   "
      f"(tagged rows carrying a citation: {sum(tsv_counts.values())})")
if malformed:
    print(f"   note: {malformed} row(s) not 4 tab-separated fields — skipped")
for c, n in sorted(tsv_counts.items(), key=lambda kv: (-kv[1], kv[0])):
    print(f"   {n:>3}  {c}    [{len(tsv_modules[c])} module(s)]")
print("")

# --- 2. `## Literature` prose blocks ---------------------------------------------------------
# Heading variants seen in the corpus: "## Literature" and "## Literature and scope".
# A block runs to the docstring terminator `-/` or the next `## ` heading.
blocks: list[tuple[str, str]] = []
if SRC.exists():
    for f in sorted(SRC.rglob("*.lean")):      # rglob: the corpus has an Alt/ subdirectory
        lines = f.read_text(encoding="utf-8").splitlines()
        for i, l in enumerate(lines):
            if l.strip().startswith("## Literature"):
                body = []
                for j in range(i + 1, len(lines)):
                    s = lines[j].strip()
                    if s == "-/" or s.startswith("## "):
                        break
                    body.append(lines[j])
                blocks.append((str(f.relative_to(ROOT)), re.sub(r"\s+", " ", " ".join(body))))
prose_all = " ".join(b for _f, b in blocks)
print(f"-- `## Literature` docstring blocks --")
print(f"   blocks found: {len(blocks)} across {len({f for f, _ in blocks})} module(s)")
print("")

# --- 3. prose corroboration: is each TSV citation actually named in some Literature block? ----
# Heuristic and deliberately loose: a citation is "corroborated" when some block contains one of
# its name-shaped tokens AND (if the citation carries a year) that year. Matching is on
# (surname, year), not raw strings, because prose spells references out in full
# ("Bulajic, Corsi, Cristoforetti, ... (2002)" vs the TSV's "Bulajic 2002").
prose_hits: dict[str, set[str]] = {}
for c in tsv_counts:
    ys = years_of(c)
    names = [n for n in surnames(c) if not n.isdigit()]
    hit = set()
    for f, b in blocks:
        if any(n in b for n in names) and (not ys or (ys & years_of(b))):
            hit.add(f)
    prose_hits[c] = hit

uncorroborated = sorted(c for c in tsv_counts if not prose_hits[c])
if uncorroborated:
    print(f"-- ADVISORY: {len(uncorroborated)} scope-tags citation(s) not name-matched in any "
          f"`## Literature` block --")
    print("   (heuristic surname+year match; a miss can mean a spelling variant, a prose gap,")
    print("    or a citation whose module carries no Literature docstring)")
    for c in uncorroborated:
        print(f"   NO-PROSE  {c}    [tags: {', '.join(sorted(tsv_modules[c]))}]")
    print("")

# --- 4. singletons: one occurrence across TSV rows + Literature blocks combined ---------------
singletons = []
for c, n in tsv_counts.items():
    total = n + len(prose_hits[c])
    if total <= 1:
        singletons.append((c, n, len(prose_hits[c])))
print(f"-- singleton citations (total occurrences <= 1 across TSV rows + Literature blocks) --")
if singletons:
    print("   A single occurrence is the shape a typo or an accidental variant takes. It is ALSO")
    print("   the shape of a legitimately once-used source. Look; do not assume.")
    for c, n, p in sorted(singletons):
        print(f"   SINGLETON  {c}    (tsv rows: {n}, prose blocks: {p})")
else:
    print("   (none)")
print("")

# --- 5. similarity: candidate variants of one source -----------------------------------------
keys = sorted(tsv_counts)
pairs = []
for i in range(len(keys)):
    for j in range(i + 1, len(keys)):
        r = difflib.SequenceMatcher(None, norm(keys[i]), norm(keys[j])).ratio()
        if r >= SIM_THRESHOLD:
            pairs.append((r, keys[i], keys[j]))
print(f"-- similar citation-string pairs (normalized ratio >= {SIM_THRESHOLD}) --")
if pairs:
    print("   NOT a defect report. Distinct works by one author are expected to trip this")
    print("   (e.g. Griem 1974 = Spectral Line Broadening by Plasmas; Griem 1997 = Principles of")
    print("   Plasma Spectroscopy — two different books, not a typo pair).")
    for r, a, b in sorted(pairs, reverse=True):
        print(f"   SIMILAR {r:.2f}  {a!r}  ~  {b!r}")
else:
    print("   (none)")
print("")

# --- 6. whitelist ----------------------------------------------------------------------------
if not WL.exists():
    print(f"-- whitelist --")
    print(f"   MISSING {WL} — off-whitelist and status checks SKIPPED.")
    print("   Create it (see .claude/skills/citation-integrity/SKILL.md) to enable them.")
    print("")
    print("check-citations: advisory complete (whitelist checks skipped). exit 0")
    sys.exit(0)

wl_status: dict[str, str] = {}
wl_year: dict[str, str] = {}
wl_note: dict[str, str] = {}
for line in WL.read_text(encoding="utf-8").splitlines():
    if not line.strip() or line.lstrip().startswith("#"):
        continue
    parts = line.split("\t")
    if len(parts) < 2:
        continue
    cit = parts[0].strip()
    wl_status[cit] = parts[1].strip()
    wl_year[cit] = parts[2].strip() if len(parts) > 2 else ""
    wl_note[cit] = parts[3].strip() if len(parts) > 3 else ""

by_status = Counter(wl_status.values())
print(f"-- whitelist (docs/citation-whitelist.tsv) --")
print(f"   rows: {len(wl_status)}   " +
      "  ".join(f"{s}:{n}" for s, n in sorted(by_status.items())))
print("   Reminder: a whitelist row records what was DONE, not that a paper exists. Only")
print("   VERIFIED/CORRECTED rows carry first-hand evidence.")
print("")

off = sorted(c for c in tsv_counts if c not in wl_status)
print(f"-- off-whitelist citations in docs/scope-tags.tsv --")
if off:
    print(f"   {len(off)} citation string(s) used in column 4 with NO whitelist row. Each one is")
    print("   an unrecorded attribution: run the citation-integrity skill, then add a row with")
    print("   the outcome you actually reached (UNVERIFIED is a legitimate outcome; silence is not).")
    for c in off:
        print(f"   OFF-WHITELIST  {c}    [tags: {', '.join(sorted(tsv_modules[c]))}]")
else:
    print("   (none — every scope-tags citation has a whitelist row)")
    print("   NOTE: the whitelist was seeded FROM this column, so a clean result here is expected")
    print("   today and proves nothing about the sources. This check bites on FUTURE additions,")
    print("   which is its purpose as a gate.")
print("")

# --- 7. in-use citations whose whitelist row carries no opened source -------------------------
unevidenced = sorted(
    c for c in tsv_counts
    if c in wl_status and wl_status[c] not in EVIDENCED and wl_status[c] not in NOTHING_TO_OPEN
)
print(f"-- in-use citations with NO primary source on record --")
if unevidenced:
    print(f"   {len(unevidenced)} of {len(tsv_counts)} scope-tags citations are whitelisted at a")
    print("   status short of VERIFIED/CORRECTED. Sanctioned for continued use; NOT first-hand")
    print("   evidence for a NEW constant, sign, inequality, or attributed result.")
    for c in unevidenced:
        print(f"   {wl_status[c]:<13} {c}")
else:
    print("   (none)")
print("")

# --- 8. prose years the whitelist has never acknowledged --------------------------------------
# Mechanical and low-false-negative: every 4-digit year in a Literature block whose value matches
# no whitelist row's year. Catches sources named ONLY in prose. Cannot catch an undated citation.
wl_years = {y for y in wl_year.values() if re.fullmatch(r"(1[6-9]\d\d|20\d\d)", y)}
for c in wl_status:
    wl_years |= years_of(c)
unknown: dict[str, list[tuple[str, str]]] = defaultdict(list)
for f, b in blocks:
    for m in re.finditer(r"\b(1[6-9]\d\d|20\d\d)\b", b):
        y = m.group(1)
        if y not in wl_years:
            unknown[y].append((f, b[max(0, m.start() - 100):m.end() + 20].strip()))
print(f"-- `## Literature` prose years with no whitelist row --")
if unknown:
    print(f"   {len(unknown)} year value(s). Each is a source named in a docstring that the")
    print("   whitelist has never acknowledged. Expect some false positives (edition years,")
    print("   publisher dates, ranges). A citation given WITHOUT a year cannot be caught here.")
    for y in sorted(unknown):
        f0, ctx = unknown[y][0]
        print(f"   UNACKNOWLEDGED {y}  ({len(unknown[y])} mention(s), e.g. {f0})")
        print(f"       ...{ctx}...")
else:
    print("   (none)")
print("")

print("check-citations: advisory complete. No verdict rendered — this script cannot open a paper.")
print("  Next step for anything flagged: .claude/skills/citation-integrity/SKILL.md")
sys.exit(0)
PY
