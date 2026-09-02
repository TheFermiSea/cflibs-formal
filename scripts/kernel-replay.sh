#!/usr/bin/env bash
# kernel-replay.sh — independent kernel re-check of compiled modules with the toolchain's
# built-in `leanchecker` (Lean ≥ 4.28; leanprover/lean4checker merged upstream).
#
# WHY A SEPARATE GATE. `lake build` type-checks each file as it elaborates it, and `axiom-audit` /
# `#print axioms` then WALK the stored environment — but both trust the .olean files as written.
# `leanchecker <Module>` replays every declaration of that module through the kernel afresh,
# starting from the environment of its imports, so a corrupted / hand-forged / stale .olean
# cannot pass. It is the "Validating a Lean proof" rung above `#print axioms`.
#
# COST (measured 2026-09-02 on this corpus, LEAN_NUM_THREADS=1): ~42 s and ~2.6 GB peak RSS PER
# MODULE, dominated by loading the Mathlib environment. Two invocations that are NOT safe:
#   * `leanchecker` with no module   → checks EVERY .olean on the search path (Lean + Mathlib).
#   * `leanchecker CflibsFormal` with the DEFAULT thread count → OOM-killed (exit 137) after ~7 min
#     on a 64 GB machine. OBSERVED, not inferred: the same root aggregator module replays fine at
#     ~1.3 GB when pinned to LEAN_NUM_THREADS=1 (it is just the heaviest module — it imports all
#     72 others), so the hazard is the multi-threaded environment load, not the module itself.
# So this script always runs PER MODULE with a bounded worker pool and ONE thread each.
#
# USAGE
#   scripts/kernel-replay.sh --changed <git-base>   modules whose .lean changed since <git-base>
#   scripts/kernel-replay.sh --all                  every module under CflibsFormal/ (+ root)
#   scripts/kernel-replay.sh <Module> [<Module>...] explicit module names
# ENV
#   KERNEL_REPLAY_JOBS   parallel workers (default 2 — sized for a 7 GB hosted runner; use 8 on
#                        a 64 GB workstation). Each worker is pinned to LEAN_NUM_THREADS=1.
# EXIT  0 all replayed modules accepted by the kernel; 1 a module was rejected; 2 usage error.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"
JOBS="${KERNEL_REPLAY_JOBS:-2}"

path_to_module() {  # CflibsFormal/Alt/CSigma.lean -> CflibsFormal.Alt.CSigma ; CflibsFormal.lean -> CflibsFormal
  local p="${1%.lean}"; echo "${p//\//.}"
}

mods=()
case "${1:-}" in
  --all)
    mods+=("CflibsFormal")
    while IFS= read -r f; do mods+=("$(path_to_module "$f")"); done \
      < <(find CflibsFormal -name '*.lean' | sort)
    ;;
  --changed)
    base="${2:-}"
    [ -n "$base" ] || { echo "kernel-replay: --changed needs a git base (e.g. origin/main, HEAD~1)" >&2; exit 2; }
    git rev-parse --verify --quiet "$base^{commit}" >/dev/null \
      || { echo "kernel-replay: base '$base' is not a reachable commit (shallow checkout? set fetch-depth ≥ 2)" >&2; exit 2; }
    while IFS= read -r f; do
      [ -f "$f" ] || continue                       # deleted files have no module to replay
      case "$f" in CflibsFormal.lean|CflibsFormal/*.lean) mods+=("$(path_to_module "$f")");; esac
    done < <(git diff --name-only "$base" HEAD -- 'CflibsFormal.lean' 'CflibsFormal/**/*.lean' 'CflibsFormal/*.lean')
    ;;
  "")
    echo "usage: $0 --changed <git-base> | --all | <Module>..." >&2; exit 2 ;;
  *)
    mods=("$@") ;;
esac

if [ "${#mods[@]}" -eq 0 ]; then
  echo "kernel-replay: no CflibsFormal modules to replay (nothing changed under CflibsFormal/)"; exit 0
fi

echo "kernel-replay: ${#mods[@]} module(s), $JOBS worker(s), LEAN_NUM_THREADS=1"
log="$(mktemp -d)"
export log
# One worker = one module = one kernel replay. Output captured per module; failures tallied.
printf '%s\n' "${mods[@]}" | xargs -P "$JOBS" -I{} bash -c '
  m="$1"; out="$log/${m}.log"
  if LEAN_NUM_THREADS=1 lake env leanchecker "$m" >"$out" 2>&1; then
    echo "  ok    $m"
  else
    echo "  FAIL  $m"; sed "s/^/        /" "$out" | head -20; touch "$log/FAILED"
  fi' _ {}

if [ -e "$log/FAILED" ]; then
  echo "kernel-replay: FAIL — a module was rejected by the kernel (see above)"; rm -rf "$log"; exit 1
fi
echo "kernel-replay: OK — all ${#mods[@]} module(s) accepted by an independent kernel replay"
rm -rf "$log"
