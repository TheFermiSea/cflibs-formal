#!/usr/bin/env bash
# mutate-check.sh — spec-mutation checker (mechanizes discipline Gate 5)
#
# WHY THIS EXISTS
# ---------------
# AGENTS.md: "Gate 5 of the *discipline* — a faithfulness/statement audit — is human/agent
# judgment, not automated."  Gates 1–4 (build / axiom-audit / linter / stats) all pass happily
# on a green proof of a VACUOUS, tautological, or accidentally-weakened statement.  That is the
# one failure mode this repo says is worthless-if-missed.
#
# Mutation testing gives it an executable edge: perturb a theorem's STATEMENT (flip an
# inequality, negate an exponent sign, swap strict for non-strict, delete a load-bearing
# hypothesis) and the file MUST stop typechecking.  A mutation that still compiles is a
# NON-KILLED MUTANT: the original statement did not pin down what its docstring claims.
#
# BUILD SAFETY (non-negotiable)
# -----------------------------
#   * Never runs `lake build` — a shared `.lake` may be in use by concurrent agents.
#   * Never edits anything under CflibsFormal/.  Every mutation is applied to a COPY in a
#     mktemp'd directory and typechecked with `lake env lean <copy>`, which reads the prebuilt
#     oleans and writes none.
#   * The script refuses to run if a target path is not a file under CflibsFormal/.
#
# WHAT A KILL DOES AND DOES NOT PROVE
# -----------------------------------
#   class=content  — the mutation changes what the statement ASSERTS (sign, direction,
#                    strictness, a hypothesis turned into its negation).  A kill is evidence
#                    the proof genuinely pins that content down; a survivor means the claimed
#                    content is not actually being asserted.
#   class=hyp-drop — the mutation deletes a hypothesis the docstring calls load-bearing.  A kill
#                    proves only that THIS PROOF uses the hypothesis (it does not prove the
#                    statement is false without it).  A survivor is still a real finding: the
#                    hypothesis is decoration and the docstring overclaims.
#
# USAGE   (must be run from its checkout — the repo root is derived from the script's own path)
#   scripts/mutate-check.sh              # run every mutant (sequential; ~40 s per Lean run, ~8 min)
#   scripts/mutate-check.sh --list       # print the mutation table, run nothing
#   scripts/mutate-check.sh --only M3    # run one mutant by id (repeatable)
#   scripts/mutate-check.sh --selftest   # positive control: a meaning-preserving mutant MUST survive
#   scripts/mutate-check.sh --keep       # keep the temp dir for inspection
#
# EXIT CODES
#   0  every mutant killed (statements pin down their content)
#   1  at least one mutant SURVIVED  <- the finding
#   2  infrastructure failure: baseline copy did not compile, anchor not found, bad target,
#      no mutants selected, or the --selftest control was killed

set -uo pipefail

SCRIPT_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd -- "${SCRIPT_DIR}/.." && pwd)"

# ---------------------------------------------------------------------------
# The mutation table.
#
# One record per line, fields separated by '|':
#   id | relative-file | theorem-name | class | anchor (exact substring of the STATEMENT) |
#   replacement | description
#
# The anchor is matched ONLY inside the statement slice of `theorem-name` — from its
# declaration line up to (not including) the `:=` that opens its proof — and must occur there
# exactly once, so a table entry can never silently rewrite a docstring or a proof term.
# An empty replacement deletes the anchor.
# ---------------------------------------------------------------------------
read -r -d '' MUTATIONS <<'EOF'
M1|CflibsFormal/Saha.lean|log_sahaFactor|content|- chi / (kB * T)|+ chi / (kB * T)|Saha exponent sign: the Boltzmann/Saha term -chi/(kB T) flipped to +chi/(kB T)
M2|CflibsFormal/Saha.lean|electronDensity_antitone|content|StrictAntiOn|StrictMonoOn|Density-diagnostic monotonicity direction: n_e = S/R is antitone in R, mutated to monotone
M3|CflibsFormal/SelfAbsorption.lean|selfAbsorbedIntensity_lt_lineIntensity|content|k tau < lineIntensity|k tau > lineIntensity|Self-absorption bias direction: I_meas < I_thin flipped to I_meas > I_thin
M4|CflibsFormal/PartialLTE.lean|mcwhirter_iff_thermalizationLimit|content|dE ^ 3 ≤ ne|dE ^ 3 ≥ ne|McWhirter bound direction: C*sqrt(T)*dE^3 <= n_e flipped to >=
M5|CflibsFormal/PartialLTE.lean|mcwhirter_iff_thermalizationLimit|hyp-drop| (hne : 0 ≤ ne)||Drop the hypothesis the docstring calls load-bearing (0 <= ne, needed for the real cube root)
M6|CflibsFormal/Closure.lean|composition_sum_one|hyp-drop|(hN : 0 < totalDensity n) ||Closure sum-to-one: drop the positive-total hypothesis (without it n = 0 gives sum 0, not 1)
M7|CflibsFormal/Identifiability.lean|temperature_identifiability|content|hE : E i ≠ E j|hE : E i = E j|Identifiability: negate the distinct-energy premise, which temperature_degeneracy says makes T unidentifiable
EOF

# ---------------------------------------------------------------------------
# POSITIVE CONTROL (`--selftest`).
#
# "Every mutant was killed" is exactly what a broken harness that never really runs the
# mutation would also print.  This control is an ALPHA-EQUIVALENT rewrite — it renames the
# bound variable of a `∀` inside a hypothesis and changes nothing about the meaning — so the
# mutant MUST still typecheck.  If `--selftest` reports a kill, the harness is not measuring
# what it claims and every "killed" verdict above is untrustworthy.
# ---------------------------------------------------------------------------
read -r -d '' CONTROL <<'EOF'
C1|CflibsFormal/Closure.lean|composition_le_one|control|(hn : ∀ s, 0 ≤ n s)|(hn : ∀ t, 0 ≤ n t)|alpha-equivalent binder rename — semantically a no-op, so this mutant MUST survive
EOF

# ---------------------------------------------------------------------------
# Slice-scoped mutator.  Reads the pristine source, locates the statement slice of the named
# declaration, requires exactly one occurrence of the anchor there, rewrites it, writes the
# mutated copy, and prints "<start-line> <end-line>" so the caller can tell an error AT the
# theorem from a downstream one.  Any failure exits nonzero with a diagnostic.
# ---------------------------------------------------------------------------
mutate() { # src dst decl anchor replacement
  python3 - "$@" <<'PY'
import re, sys
src, dst, decl, anchor, repl = sys.argv[1:6]
lines = open(src, encoding="utf-8").read().split("\n")

decl_re = re.compile(r'^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|nonrec\s+)*'
                     r'(?:theorem|lemma)\s+' + re.escape(decl) + r'(?![\w\'!?₀-₉])')
start = next((i for i, l in enumerate(lines) if decl_re.match(l)), None)
if start is None:
    sys.exit(f"ERROR: declaration '{decl}' not found in {src}")

# The statement runs to the ':=' that opens the proof (Lean style in this repo puts it at the
# end of the final statement line).  Cut the slice there so proofs are never mutated.
end, cut = None, None
for i in range(start, min(start + 60, len(lines))):
    m = re.search(r':=', lines[i])
    if m:
        end, cut = i, m.start()
        break
if end is None:
    sys.exit(f"ERROR: could not find the ':=' ending the statement of '{decl}' in {src}")

slice_lines = lines[start:end] + [lines[end][:cut]]
tail = lines[end][cut:]
blob = "\n".join(slice_lines)

n = blob.count(anchor)
if n != 1:
    sys.exit(f"ERROR: anchor {anchor!r} occurs {n} times in the statement of '{decl}' "
             f"({src} lines {start+1}-{end+1}); need exactly 1")

blob = blob.replace(anchor, repl)
new_slice = blob.split("\n")
new_slice[-1] += tail
open(dst, "w", encoding="utf-8").write("\n".join(lines[:start] + new_slice + lines[end+1:]))
print(start + 1, end + 1)
PY
}

# ---------------------------------------------------------------------------
# Argument parsing
# ---------------------------------------------------------------------------
LIST_ONLY=0
KEEP=0
ONLY=""
EXPECT=kill
while [ $# -gt 0 ]; do
  case "$1" in
    --list) LIST_ONLY=1 ;;
    --keep) KEEP=1 ;;
    --selftest) MUTATIONS="$CONTROL"; EXPECT=survive ;;
    --only) shift; ONLY="${ONLY} ${1:-}" ;;
    --only=*) ONLY="${ONLY} ${1#--only=}" ;;
    # print the whole leading comment header, however long it grows
    -h|--help) awk 'NR>1 && /^#/ {print; next} NR>1 {exit}' "$0"; exit 0 ;;
    *) echo "unknown argument: $1" >&2; exit 2 ;;
  esac
  shift
done

selected() { # id
  [ -z "${ONLY// /}" ] && return 0
  case " ${ONLY} " in *" $1 "*) return 0 ;; *) return 1 ;; esac
}

if [ "$LIST_ONLY" = 1 ]; then
  printf '%-4s %-34s %-9s %s\n' ID THEOREM CLASS MUTATION
  while IFS='|' read -r id file decl cls anchor repl desc; do
    [ -z "${id:-}" ] && continue
    printf '%-4s %-34s %-9s %s\n' "$id" "$decl" "$cls" "$desc"
  done <<< "$MUTATIONS"
  exit 0
fi

# ---------------------------------------------------------------------------
# Workspace
# ---------------------------------------------------------------------------
TMP="$(mktemp -d "${TMPDIR:-/tmp}/mutate-check.XXXXXX")"
cleanup() { [ "$KEEP" = 1 ] && echo "kept: $TMP" || rm -rf "$TMP"; }
trap cleanup EXIT

echo "=== mutate-check — spec-mutation audit (discipline Gate 5) ==="
echo "repo:    $ROOT"
echo "workdir: $TMP   (all mutations are applied to COPIES; CflibsFormal/ is never touched)"
echo "method:  lake env lean <copy>   (no lake build — shared .lake stays untouched)"
echo

cd "$ROOT" || exit 2

# --- Phase 1: baselines -----------------------------------------------------
# An unmutated copy of every targeted file must typecheck.  Without this control, a mutant
# "kill" could be an artifact of the copy/temp-path setup rather than of the mutation.
BASE_FAIL=0
FILES="$(while IFS='|' read -r id file decl cls a r d; do
           [ -n "${file:-}" ] && selected "$id" && echo "$file"
         done <<< "$MUTATIONS" | sort -u)"

for f in $FILES; do
  case "$f" in CflibsFormal/*) ;; *) echo "REFUSING: target outside CflibsFormal/: $f" >&2; exit 2 ;; esac
  [ -f "$ROOT/$f" ] || { echo "REFUSING: no such file: $f" >&2; exit 2; }
  base="$TMP/base_$(basename "$f")"
  cp "$ROOT/$f" "$base"
  printf 'baseline  %-40s ' "$f"
  if lake env lean "$base" > "$base.log" 2>&1; then
    echo "OK (unmutated copy typechecks)"
  else
    echo "FAILED — cannot trust any result from this file"
    sed -n '1,10p' "$base.log"
    BASE_FAIL=1
  fi
done
[ "$BASE_FAIL" = 1 ] && { echo; echo "INFRASTRUCTURE FAILURE: a baseline copy did not compile."; exit 2; }
echo

# --- Phase 2: mutants -------------------------------------------------------
KILLED=0; SURVIVED=0; ERRORS=0
SUMMARY="$TMP/summary.txt"
: > "$SUMMARY"

while IFS='|' read -r id file decl cls anchor repl desc; do
  [ -z "${id:-}" ] && continue
  selected "$id" || continue

  mfile="$TMP/${id}_$(basename "$file")"
  span="$(mutate "$ROOT/$file" "$mfile" "$decl" "$anchor" "$repl" 2>&1)"
  rc=$?
  if [ $rc -ne 0 ] || [ -z "$span" ]; then
    echo "[$id] MUTATION-ERROR  $decl — $span"
    printf '%-4s %-9s %-34s %s\n' "$id" "$cls" "$decl" "MUTATION-ERROR (anchor not applied)" >> "$SUMMARY"
    ERRORS=$((ERRORS + 1))
    continue
  fi
  set -- $span; sline=$1; eline=$2

  echo "[$id] $file :: $decl   (class=$cls)"
  echo "      mutation: $desc"
  echo "      applied:  '${anchor}'  ->  '${repl}'   (statement lines ${sline}-${eline})"

  if lake env lean "$mfile" > "$mfile.log" 2>&1; then
    echo "      RESULT:   *** SURVIVED *** — the mutated statement still typechecks."
    echo "                The original statement does not pin down this content."
    printf '%-4s %-9s %-34s %s\n' "$id" "$cls" "$decl" "SURVIVED  <-- FINDING" >> "$SUMMARY"
    SURVIVED=$((SURVIVED + 1))
  else
    errline="$(grep -m1 -E '^.*\.lean:[0-9]+:[0-9]+: error' "$mfile.log" | head -1)"
    lno="$(sed -n 's/^.*\.lean:\([0-9]\+\):[0-9]\+: error.*/\1/p' <<< "$errline" | head -1)"
    where="downstream"
    if [ -n "$lno" ] && [ "$lno" -ge "$sline" ] 2>/dev/null; then
      # errors reported at or after the statement, but before the next declaration, count as
      # "at the theorem"; anything much later is a downstream user of the mutated result.
      [ "$lno" -le "$((eline + 60))" ] && where="at the mutated theorem"
    fi
    echo "      RESULT:   killed ($where)"
    [ -n "$errline" ] && echo "                first error: ${errline##*/}"
    printf '%-4s %-9s %-34s %s\n' "$id" "$cls" "$decl" "killed ($where)" >> "$SUMMARY"
    KILLED=$((KILLED + 1))
  fi
  echo
done <<< "$MUTATIONS"

# --- Report -----------------------------------------------------------------
echo "=== summary ==="
cat "$SUMMARY"
echo
echo "killed=$KILLED  survived=$SURVIVED  mutation-errors=$ERRORS"

# A gate that runs zero mutants and reports green is the exact failure mode this script exists
# to catch, so it must never happen here (e.g. a typo'd `--only` id selecting nothing).
if [ "$((KILLED + SURVIVED + ERRORS))" = 0 ]; then
  echo
  echo "INFRASTRUCTURE FAILURE: no mutants were selected — nothing was audited."
  echo "Check the --only ids against 'scripts/mutate-check.sh --list'."
  exit 2
fi

if [ "$EXPECT" = survive ]; then
  echo
  if [ "$ERRORS" = 0 ] && [ "$KILLED" = 0 ] && [ "$SURVIVED" -gt 0 ]; then
    echo "SELFTEST PASSED: the harness reports SURVIVED when a mutant really does still compile,"
    echo "so a 'killed' verdict from the real table is a genuine typecheck failure, not a stub."
    exit 0
  fi
  echo "SELFTEST FAILED: an alpha-equivalent, meaning-preserving mutation did NOT survive."
  echo "The harness is not measuring what it claims — do not trust its 'killed' verdicts."
  exit 2
fi

if [ "$ERRORS" -gt 0 ]; then
  echo
  echo "INFRASTRUCTURE FAILURE: a mutation could not be applied (anchor drifted after an edit)."
  echo "Fix the table above; an unapplied mutation would masquerade as a killed mutant."
  exit 2
fi
if [ "$SURVIVED" -gt 0 ]; then
  echo
  echo "NON-KILLED MUTANT(S) FOUND — a statement compiled after its meaning was changed."
  echo "Audit the statement, not the proof: it is weaker or more vacuous than its docstring claims."
  exit 1
fi
echo "All mutants killed: every audited statement changed meaning when perturbed."
exit 0
