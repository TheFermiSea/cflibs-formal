#!/bin/sh
# prereg.sh — mechanical freeze & audit for pre-registrations.
#
# ---------------------------------------------------------------------------
# WHY THIS GATE EXISTS IN cflibs-formal
#
# Every other gate here judges the PRESENT state of the repo: `lake build` says
# the proof compiles, `axiom-audit` says it is axiom-clean, `scope-check` says
# the scope tag matches the declaration as it stands today. None of them can
# see BACKWARDS. Nothing in the repo can distinguish "I proved what I set out
# to prove" from "I weakened the statement until something went green and then
# wrote a docstring saying that was the plan all along".
#
# That second failure mode is not hypothetical here: it is exactly the 2DCOS
# "Model B" defect (docs/2dcos/ERRATA.md) — a standardless method derived,
# quietly weakened when the derivation would not close (an eliminated n_e
# reappearing inside a lumped parameter), and then rationalized after the fact.
# A green Lean proof of a retreated statement looks identical to a green Lean
# proof of the intended one.
#
# So: before attempting a proof, freeze the PREDICTED theorem statement and its
# EXPECTED scope tag (EXACT / REDUCED / APPROXIMATION / PURE-MATH) in
# docs/preregistrations/. `freeze` makes that a git commit — the timestamp is
# then unforgeable ancestry, not a self-reported date. `audit` afterwards proves
# the prediction pre-dates the Lean file and was never edited. A statement that
# had to be weakened to close then shows up as a visible, dated DEVIATION
# between the frozen prediction and the shipped theorem, instead of silently
# becoming "what I meant all along".
#
# The prediction is the unit under audit, not the proof. Failing to prove the
# predicted statement is fine and expected — hiding that you retreated is not.
#
# See "cflibs-formal usage notes" at the bottom of this header for the
# --results scoping this repo requires.
# ---------------------------------------------------------------------------
#
# Turns the pre-registration Iron Law into something checkable from git
# history alone: `freeze` makes the timestamp real, `audit` proves (or
# disproves) that the registration preceded the outputs and was never
# edited afterward. Zero dependencies beyond git and a POSIX shell.
#
# Usage:
#   prereg.sh freeze <prereg-file> [raw-data-file ...]
#   prereg.sh audit [--results <path>] [prereg-file ...]
#   prereg.sh help
#
# freeze:
#   1. Records a git blob checksum for each raw data file (optional args)
#      in a "## Frozen data checksums" section of the document.
#   2. Commits the pre-registration alone: "prereg-freeze: <path>".
#      That commit IS the timestamp: it proves the prediction preceded
#      the result. The file must not have any earlier git history.
#   3. Stamps the freeze commit hash into the "**Frozen at commit:**"
#      line and commits the stamp ("prereg-stamp: ...").
#
# audit (read-only; run before reporting any confirmatory claim):
#   FROZEN      the registration has a freeze commit in history
#   STAMP       the stamped hash matches the real freeze commit
#   INTEGRITY   content is byte-identical to the frozen version (the
#               stamp line is the only permitted difference), at HEAD
#               and in the working tree
#   CHRONOLOGY  no commit touching a results path is at-or-before the
#               freeze commit (commit ancestry, not forgeable dates)
#   DATA        frozen raw-data checksums still match the files
#
#   Results paths default to: results outputs figures reports derived
#   (those that exist). In a repo holding several studies, scope with
#   --results so an earlier study's outputs don't trip the check.
#   Paths containing whitespace are not supported.
#
# Exit codes: 0 = all checks passed, 1 = at least one FAIL, 2 = usage error.
#
# ---------------------------------------------------------------------------
# cflibs-formal usage notes (READ BEFORE RUNNING `audit` BARE)
#
# DEFAULT_RESULTS here is "CflibsFormal docs/scope-tags.tsv oracle" — the three
# evidence surfaces a theorem claim lands on. But ALL THREE ALREADY HAVE YEARS
# OF HISTORY: 73 / 33 / 10 commits at the time of vendoring. CHRONOLOGY asks
# "is any results commit an ancestor of the freeze?", and every one of those
# commits is. So a bare `audit` in this repo FAILS CHRONOLOGY by construction,
# and that failure is meaningless — it is repo age, not misconduct.
#
# The default is therefore only meaningful for an evidence path with NO
# pre-freeze history — i.e. a brand-new module. Scope every audit to the
# specific artifact the prediction is about:
#
#   ./scripts/prereg.sh audit --results CflibsFormal/DOptimality.lean \
#       docs/preregistrations/2026-08-21-d-optimality-boltzmann-design.md
#
# Each pre-registration should name its own `--results` scope in an
# "Audit command" section, so the check is reproducible by anyone.
# `--results` accepts files as well as directories.
# ---------------------------------------------------------------------------
#
# ---------------------------------------------------------------------------
# PROVENANCE / LICENSE
#
# Vendored from https://github.com/K-Dense-AI/science-superpowers
#   (skills/preregistering-analysis/prereg.sh), MIT licensed.
#
# MIT License
#
# Copyright (c) 2026 K-Dense, Inc.
#
# Permission is hereby granted, free of charge, to any person obtaining a copy
# of this software and associated documentation files (the "Software"), to deal
# in the Software without restriction, including without limitation the rights
# to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
# copies of the Software, and to permit persons to whom the Software is
# furnished to do so, subject to the following conditions:
#
# The above copyright notice and this permission notice shall be included in
# all copies or substantial portions of the Software.
#
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
# FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
# AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
# LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
# OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
# THE SOFTWARE.
#
# Modifications for cflibs-formal (2026-08-21):
#   1. Added the "WHY THIS GATE EXISTS" and "usage notes" header blocks above.
#   2. PREREG_DIR      -> docs/preregistrations
#   3. DEFAULT_RESULTS -> "CflibsFormal docs/scope-tags.tsv oracle"
#   4. Cosmetic: CHRONOLOGY messages no longer append a hard-coded "/" to the
#      results path, since results paths here may be files (scope-tags.tsv),
#      not just directories. No logic change.
#   5. BUG FIX (upstream defect, found by running it): the stamping step in
#      `freeze` inserted a blank line in addition to the "**Frozen at commit:**"
#      line. `strip_stamp` removes only the stamp line, so the stray blank made
#      the stamped file differ from the frozen file and INTEGRITY FAILed on
#      every freshly frozen document — the PASS path was unreachable. The stamp
#      line is now the only line that step adds. (Documents that already carry
#      a "**Frozen at commit:**" placeholder took the in-place-replace branch
#      and were never affected; the recommended template carries one.)
#   6. BUG FIX (upstream defect, found by running it): the DATA check ended with
#      `[ "$nbad" -eq 0 ] && pass ...` as the last command of `audit_one`, so a
#      DATA failure made the function return 1 and `set -e` aborted the script —
#      suppressing the RESULT summary and skipping every remaining
#      pre-registration. Rewritten as a plain `if`, with an explicit `return 0`.
# No other logic was altered.
# ---------------------------------------------------------------------------

set -eu

# Retargeted for cflibs-formal. NOTE: no trailing slash — the freeze location
# check globs "$PREREG_DIR"/*, which never matches if PREREG_DIR ends in "/".
PREREG_DIR="docs/preregistrations"
# The evidence surfaces a theorem claim lands on: the Lean sources, the scope-tag
# spine, and the numerical oracle. See the usage notes above — these all predate
# any new freeze, so scope real audits with --results.
DEFAULT_RESULTS="CflibsFormal docs/scope-tags.tsv oracle"
STAMP_PREFIX='**Frozen at commit:**'

usage() {
    awk 'NR > 1 && /^#/ { sub(/^# ?/, ""); print; next } NR > 1 { exit }' "$0"
}

die() {
    echo "prereg.sh: error: $*" >&2
    exit 2
}

repo_root() {
    git rev-parse --show-toplevel 2>/dev/null || die "not inside a git repository"
}

# rel_path <file> -> path relative to the repo root
rel_path() {
    _abs=$(cd "$(dirname "$1")" 2>/dev/null && pwd) || die "no such file: $1"
    _abs="$_abs/$(basename "$1")"
    printf '%s\n' "${_abs#"$ROOT"/}"
}

# strip_stamp — filter out the stamp line so it never breaks INTEGRITY
strip_stamp() {
    grep -v "^\*\*Frozen at commit:\*\*" || true
}

# ---------------------------------------------------------------- freeze

cmd_freeze() {
    [ $# -ge 1 ] || die "freeze needs a pre-registration file"
    ROOT=$(repo_root)
    git rev-parse -q --verify HEAD >/dev/null 2>&1 \
        || die "repository has no commits yet; commit a clean baseline first"

    file=$1; shift
    [ -f "$file" ] || die "no such file: $file"
    rel=$(rel_path "$file")

    case "$rel" in
        "$PREREG_DIR"/*) ;;
        *) echo "prereg.sh: warning: $rel is outside $PREREG_DIR/ (the conventional location)" >&2 ;;
    esac

    if git -C "$ROOT" log --format=%H -- "$rel" 2>/dev/null | grep -q .; then
        die "$rel already has git history — a freeze must be the file's FIRST commit.
Pre-register a NEW file for a fresh confirmatory test; never re-freeze."
    fi

    # Record raw-data checksums (git blob hashes) before freezing.
    if [ $# -gt 0 ]; then
        printf '\n## Frozen data checksums\n\n' >> "$file"
        for data in "$@"; do
            [ -f "$data" ] || die "no such data file: $data"
            datarel=$(rel_path "$data")
            blob=$(git hash-object -- "$data")
            printf -- '- %s %s\n' "$datarel" "$blob" >> "$file"
        done
    fi

    git -C "$ROOT" add -- "$rel"
    git -C "$ROOT" commit -q -m "prereg-freeze: $rel" -- "$rel"
    freeze=$(git -C "$ROOT" rev-parse HEAD)

    # Stamp the freeze commit into the document (the one permitted edit).
    tmp=$(mktemp)
    if grep -q "^\*\*Frozen at commit:\*\*" "$file"; then
        awk -v c="$freeze" -v p="$STAMP_PREFIX" \
            'index($0, p) == 1 { print p " " c; next } { print }' "$file" > "$tmp"
    else
        # NOTE (cflibs-formal fix): upstream also emitted `print ""` here, adding a
        # blank line on top of the stamp line. `strip_stamp` removes only the stamp
        # line, so that stray blank made the stamped file differ from the frozen
        # file and INTEGRITY FAILed on every freshly frozen document that had no
        # pre-existing stamp line — i.e. the PASS path was unreachable. The stamp
        # line must be the ONLY line this step adds.
        awk -v c="$freeze" -v p="$STAMP_PREFIX" \
            'NR == 1 { print; print p " " c; next } { print }' "$file" > "$tmp"
    fi
    mv "$tmp" "$file"
    git -C "$ROOT" add -- "$rel"
    git -C "$ROOT" commit -q -m "prereg-stamp: $rel $freeze" -- "$rel"

    echo "FROZEN: $rel"
    echo "  freeze commit: $freeze"
    echo "  This commit is the timestamp proving the prediction preceded the result."
    echo "  From here on: any edit to this file, and any output committed at-or-before"
    echo "  the freeze, will fail 'prereg.sh audit'."
}

# ----------------------------------------------------------------- audit

FAILS=0
WARNS=0

pass() { echo "PASS  $*"; }
fail() { echo "FAIL  $*"; FAILS=$((FAILS + 1)); }
warn() { echo "WARN  $*"; WARNS=$((WARNS + 1)); }
note() { echo "      $*"; }

audit_one() {
    rel=$1
    echo ""
    echo "== prereg audit: $rel =="

    # FROZEN — the first commit that touched the file is the freeze claim.
    freeze=$(git -C "$ROOT" log --format=%H -- "$rel" | tail -n 1)
    if [ -z "$freeze" ]; then
        fail "FROZEN: $rel has never been committed — there is no freeze timestamp."
        note "Any analysis it describes is exploratory until a real freeze exists."
        return 0
    fi
    short=$(git -C "$ROOT" rev-parse --short "$freeze")
    fdate=$(git -C "$ROOT" show -s --format=%ci "$freeze" | cut -d' ' -f1)
    pass "FROZEN: first committed at $short ($fdate)"

    # STAMP — if the document names its freeze commit, it must be the real one.
    if [ -f "$ROOT/$rel" ]; then
        stamp=$(sed -n "s/^\*\*Frozen at commit:\*\* *//p" "$ROOT/$rel" | head -n 1)
    else
        stamp=""
    fi
    case "$stamp" in
        *[!0-9a-f]*|"")
            note "INFO  STAMP: no commit hash stamped in the document (freeze derived from git history)"
            ;;
        *)
            case "$freeze" in
                "$stamp"*) pass "STAMP: stamped hash matches the freeze commit" ;;
                *) fail "STAMP: document claims freeze commit $stamp but the file's first commit is $short"
                   note "A stamp pointing elsewhere is a forged timestamp." ;;
            esac
            ;;
    esac

    # INTEGRITY — byte-identical to the frozen version, stamp line aside.
    frozen_tmp=$(mktemp); head_tmp=$(mktemp); work_tmp=$(mktemp)
    integrity_bad=0
    git -C "$ROOT" show "$freeze:$rel" 2>/dev/null | strip_stamp > "$frozen_tmp"
    if ! git -C "$ROOT" cat-file -e "HEAD:$rel" 2>/dev/null; then
        fail "INTEGRITY: $rel is not present at HEAD"
        integrity_bad=1
    else
        git -C "$ROOT" show "HEAD:$rel" | strip_stamp > "$head_tmp"
    fi
    if [ ! -f "$ROOT/$rel" ]; then
        fail "INTEGRITY: $rel is missing from the working tree"
        integrity_bad=1
    else
        strip_stamp < "$ROOT/$rel" > "$work_tmp"
    fi
    if [ "$integrity_bad" -eq 0 ]; then
        if ! diff "$frozen_tmp" "$head_tmp" > /dev/null 2>&1; then
            fail "INTEGRITY: content at HEAD differs from the frozen version ($short):"
            diff "$frozen_tmp" "$head_tmp" | sed 's/^/      /' || true
            note "Edited after freeze -> the registration no longer pre-dates the analysis it describes."
            note "Every claim under it is exploratory. Pre-register a fresh test on unused data."
        elif ! diff "$frozen_tmp" "$work_tmp" > /dev/null 2>&1; then
            fail "INTEGRITY: uncommitted edits to $rel in the working tree:"
            diff "$frozen_tmp" "$work_tmp" | sed 's/^/      /' || true
        else
            pass "INTEGRITY: content unchanged since the freeze"
        fi
    fi
    rm -f "$frozen_tmp" "$head_tmp" "$work_tmp"

    # CHRONOLOGY — no results commit at-or-before the freeze (commit ancestry).
    chrono_fails_before=$FAILS
    checked=0
    for rpath in $RESULTS_PATHS; do
        violations=""
        for c in $(git -C "$ROOT" log --format=%H -- "$rpath"); do
            checked=$((checked + 1))
            if git -C "$ROOT" merge-base --is-ancestor "$c" "$freeze" 2>/dev/null; then
                violations="$violations $c"
            elif ! git -C "$ROOT" merge-base --is-ancestor "$freeze" "$c" 2>/dev/null; then
                warn "CHRONOLOGY: commit $(git -C "$ROOT" rev-parse --short "$c") touching $rpath is on a parallel branch — order vs the freeze is unprovable"
            fi
        done
        if [ -n "$violations" ]; then
            fail "CHRONOLOGY: $rpath has commits at-or-before the freeze commit:"
            for c in $violations; do
                note "$(git -C "$ROOT" log -1 --format='%h %ci %s' "$c")"
            done
            note "Outputs existed before the prediction was locked -> the analysis is exploratory."
        fi
        if [ -n "$(git -C "$ROOT" status --porcelain -- "$rpath" 2>/dev/null)" ]; then
            warn "CHRONOLOGY: uncommitted files under $rpath — commit outputs to make their timing provable"
        fi
    done
    if [ "$checked" -eq 0 ]; then
        note "INFO  CHRONOLOGY: no committed outputs found under: $RESULTS_PATHS"
    elif [ "$FAILS" -eq "$chrono_fails_before" ]; then
        pass "CHRONOLOGY: every committed output post-dates the freeze"
    fi

    # DATA — frozen raw-data checksums still match.
    if [ -f "$ROOT/$rel" ] && grep -q '^## Frozen data checksums' "$ROOT/$rel"; then
        nchecked=0; nbad=0
        for pair in $(awk '/^## Frozen data checksums/ { f = 1; next }
                           /^## / { f = 0 }
                           f && /^- / { print $2 ":" $3 }' "$ROOT/$rel"); do
            dpath=${pair%%:*}; dhash=${pair#*:}
            nchecked=$((nchecked + 1))
            if [ ! -f "$ROOT/$dpath" ]; then
                fail "DATA: frozen raw data file is missing: $dpath"
                nbad=$((nbad + 1))
            elif [ "$(git -C "$ROOT" hash-object -- "$dpath")" != "$dhash" ]; then
                fail "DATA: $dpath no longer matches its frozen checksum — raw data changed after the freeze"
                nbad=$((nbad + 1))
            fi
        done
        # NOTE (cflibs-formal fix): upstream wrote this as
        #   [ "$nbad" -eq 0 ] && pass ...
        # which is the LAST command of audit_one, so on a DATA failure the
        # function returned 1 and `set -e` aborted the whole script — skipping
        # the RESULT summary and any remaining pre-registrations. Exit status
        # was still 1, but the report was truncated. Made it a plain `if`.
        if [ "$nbad" -eq 0 ]; then
            pass "DATA: $nchecked frozen data checksum(s) verified"
        fi
    fi
    return 0
}

cmd_audit() {
    ROOT=$(repo_root)
    RESULTS_PATHS=""
    files=""

    while [ $# -gt 0 ]; do
        case "$1" in
            --results)
                [ $# -ge 2 ] || die "--results needs a path"
                RESULTS_PATHS="$RESULTS_PATHS ${2%/}"; shift 2 ;;
            -*) die "unknown audit option: $1" ;;
            *)  files="$files $(rel_path "$1")"; shift ;;
        esac
    done

    if [ -z "$RESULTS_PATHS" ]; then
        for p in $DEFAULT_RESULTS; do
            if [ -d "$ROOT/$p" ] || git -C "$ROOT" log -1 --format=%H -- "$p" 2>/dev/null | grep -q .; then
                RESULTS_PATHS="$RESULTS_PATHS $p"
            fi
        done
    fi

    if [ -z "$files" ]; then
        for f in "$ROOT/$PREREG_DIR"/*.md; do
            [ -f "$f" ] && files="$files ${f#"$ROOT"/}"
        done
        [ -n "$files" ] || die "no pre-registrations found under $PREREG_DIR/ (pass files explicitly)"
    fi

    for f in $files; do
        audit_one "$f"
    done

    echo ""
    if [ "$FAILS" -eq 0 ]; then
        echo "RESULT: PASS ($WARNS warning(s)) — freeze verified: predictions pre-date outputs and were never edited."
        exit 0
    else
        echo "RESULT: FAIL ($FAILS failed check(s), $WARNS warning(s))"
        echo "A failed audit means the confirmatory label cannot be defended."
        echo "Report the affected analyses as exploratory, or pre-register a fresh test on unused data."
        exit 1
    fi
}

case "${1:-help}" in
    freeze) shift; cmd_freeze "$@" ;;
    audit)  shift; cmd_audit "$@" ;;
    help|-h|--help) usage ;;
    *) die "unknown command: $1 (try: prereg.sh help)" ;;
esac
