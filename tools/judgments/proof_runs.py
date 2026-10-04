#!/usr/bin/env python3
"""Post-mortem of the proof queue's runs: exact counts first, then typed judgments.

Reads the run records of the continuous proof queue (``tools/openprover/queue``) under
``$OPENPROVER_HOME`` (default ``~/.local/share/openprover``). Nothing is executed, verified or
changed; a run's verdict stays whatever ``verify.py`` said.

Two layers, kept apart on purpose:

* **Exact** (:func:`run_facts`): read from the records, no model involved. Whether the run was
  verified; how many workers returned an empty result; how many model calls ended at the
  per-call token cap with no answer text; how many output tokens those workers used. These
  are the labels.
* **Judged** (:data:`RUN_TRAITS`): what the planner's final whiteboard SAYS happened, read by
  a System One model (:mod:`judgments`). A whiteboard is the planner's own account, so a
  trait is a claim to test against the exact layer, not a fact.

::

    python3 tools/judgments/proof_runs.py --out report.json
    python3 tools/judgments/proof_runs.py --out report.json \\
        --key-file <key file, mode 600> --cache traits.jsonl [--dry-run]

Limits. The queue has run a few dozen attempts over about fifteen targets, and attempts at one
target are not independent, so every interval here is wide and optimistic. A whiteboard that
was never rewritten (a run that died before its first planner step) is skipped. Runs aborted
for an outage (node down, planner down) are not post-mortem material and are skipped too.
"""

from __future__ import annotations

import argparse
import collections
import json
import os
import re
import sys
import tomllib
from pathlib import Path
from typing import Any, Dict, List, Mapping, NamedTuple, Optional, Sequence, Tuple

sys.path.insert(0, str(Path(__file__).resolve().parent))

import judgments as jd  # noqa: E402

RUN_TRAITS = jd.TraitSet(
    name="proof-run-whiteboard",
    version="1",
    state_field="whiteboard",
    traits=(
        jd.Trait(
            "worker_output_lost",
            "Does `whiteboard` report that a worker returned an empty, truncated or missing"
            " answer?",
            "At least one note says a worker's output was empty, cut off, truncated, lost, or"
            " ended in a tool call with no final answer.",
            "No note mentions empty, truncated or lost worker output.",
            (("output_lost", True), ("verified", False)),
            "report lost worker output",
        ),
        jd.Trait(
            "tool_misbehaved",
            "Does `whiteboard` report that a tool or the harness did not behave as expected?",
            "A note says stored items did not persist, a tool call was rejected, a tool was"
            " unavailable, or a request failed with an HTTP error.",
            "No note mentions a tool or harness problem.",
            (("verified", False),),
            "report a tool or harness problem",
        ),
        jd.Trait(
            "informal_proof_done",
            "Does `whiteboard` say that the informal (prose) proof is complete?",
            "The informal proof is marked done, verified, accepted or submitted.",
            "The informal proof is not mentioned, or is still open.",
            (("informal_written", True),),
        ),
        jd.Trait(
            "lean_lemma_compiled",
            "Does `whiteboard` record at least one Lean lemma that compiled?",
            "A Lean lemma or file is marked as compiled, verified, passed or saved after a"
            " successful check.",
            "No Lean code is recorded as compiling.",
            (("lean_items_saved", True), ("verified", True)),
            "record a compiled Lean lemma",
        ),
        jd.Trait(
            "stuck_on_lean_detail",
            "Does `whiteboard` describe a Lean error that was still unresolved when it was"
            " written?",
            "A tactic failure, a type mismatch, an unknown lemma name or a goal that would not"
            " close is listed without a fix that worked.",
            "Every Lean error mentioned has a fix recorded, or no Lean error is mentioned.",
            (("verified", False),),
            "end with an unresolved Lean error",
        ),
        jd.Trait(
            "statement_doubted",
            "Does `whiteboard` say that the theorem to prove may be false, ill-posed or missing"
            " a hypothesis?",
            "A note questions the statement itself: a counterexample, a missing assumption,"
            " or a claim that it cannot hold as written.",
            "The statement is taken as correct throughout.",
            (("verified", False),),
            "doubt the statement",
        ),
    ),
)

LABEL_TEXT = {
    "verified": "were verified",
    "output_lost": "had a worker return nothing",
    "lean_items_saved": "saved Lean items",
}

_VERIFIED = re.compile(r"\S+ (\S+): VERIFIED \(attempt (\d+)")
_FAILED = re.compile(
    r"\S+ (\S+): not verified \(run (\d+), .*openprover said '([^']*)', abort=(\w+)"
)
#: The whiteboard OpenProver starts every run with (the dossier): the planner never wrote one.
_UNWRITTEN = "**Prove and Formalize**\nProduce both"


def home() -> Path:
    return Path(os.environ.get("OPENPROVER_HOME", Path.home() / ".local/share/openprover"))


def outcomes(log_text: str) -> Dict[Tuple[str, int], Tuple[bool, Optional[str], Optional[str]]]:
    """``(target, attempt) -> (verified, what OpenProver reported, abort reason)`` from the
    supervisor log (the supervisor never reuses an attempt number)."""
    out: Dict[Tuple[str, int], Tuple[bool, Optional[str], Optional[str]]] = {}
    for line in log_text.splitlines():
        m = _VERIFIED.match(line)
        if m:
            out[(m.group(1), int(m.group(2)))] = (True, "proved", None)
            continue
        m = _FAILED.match(line)
        if m:
            abort = None if m.group(4) == "None" else m.group(4)
            out[(m.group(1), int(m.group(2)))] = (False, m.group(3), abort)
    return out


def run_facts(run_dir: Path) -> Dict[str, Any]:
    """Exact counts from one run's records (no model)."""
    workers = empty = tokens = tokens_empty = calls = calls_cap_empty = 0
    for meta in sorted(run_dir.glob("steps/step_*/meta.toml")):
        try:
            doc = tomllib.loads(meta.read_text())
        except (OSError, tomllib.TOMLDecodeError):
            continue
        for w in doc.get("workers", []):
            workers += 1
            out_tokens = int(w.get("output_tokens", 0) or 0)
            tokens += out_tokens
            result = meta.parent / "workers" / f"result_{w.get('index')}.md"
            if result.exists() and result.stat().st_size == 0:
                empty += 1
                tokens_empty += out_tokens
    for raw in run_dir.glob("steps/step_*/workers/worker_*.raw.json"):
        try:
            choice = (json.loads(raw.read_text()).get("choices") or [{}])[0]
        except (OSError, json.JSONDecodeError, AttributeError):
            continue
        calls += 1
        content = (choice.get("message") or {}).get("content") or ""
        if choice.get("finish_reason") == "length" and not content.strip():
            calls_cap_empty += 1
    repo = run_dir / "repo"
    return {
        "workers": workers,
        "workers_empty_result": empty,
        "worker_output_tokens": tokens,
        "worker_output_tokens_in_empty_results": tokens_empty,
        "worker_calls": calls,
        "worker_calls_at_cap_without_answer": calls_cap_empty,
        "informal_written": (run_dir / "PROOF.md").exists(),
        "lean_items_saved": repo.exists() and any(repo.rglob("*.lean")),
    }


class Run(NamedTuple):
    target: str
    attempt: int
    facts: Dict[str, Any]
    labels: Dict[str, Optional[bool]]
    whiteboard: Optional[str]


def load_runs(root: Path) -> Tuple[List[Run], Dict[str, int]]:
    """Runs with a logged verdict that were not aborted for an outage."""
    skipped: Dict[str, int] = collections.Counter()
    log = root / "supervisor.log"
    runs: List[Run] = []
    for (target, attempt), (verified, _, abort) in sorted(outcomes(log.read_text()).items()):
        run_dir = root / "runs" / f"{target}-{attempt}"
        if abort in ("infra", "planner_down"):
            skipped[f"aborted_{abort}"] += 1
            continue
        if not run_dir.is_dir():
            skipped["no_run_directory"] += 1
            continue
        facts = run_facts(run_dir)
        labels: Dict[str, Optional[bool]] = {
            "verified": verified,
            "output_lost": facts["workers_empty_result"] > 0 if facts["workers"] else None,
            "informal_written": facts["informal_written"],
            "lean_items_saved": facts["lean_items_saved"],
        }
        board = run_dir / "WHITEBOARD.md"
        text = board.read_text() if board.exists() else None
        if text is not None and _UNWRITTEN in text[:300]:
            text = None
        runs.append(Run(target, attempt, facts, labels, text))
    return runs, dict(skipped)


def totals(runs: Sequence[Run]) -> Dict[str, Dict[str, int]]:
    """The exact counts summed over verified and unverified runs."""
    out: Dict[str, Dict[str, int]] = {}
    for name, keep in (("verified", True), ("not_verified", False)):
        group = [r for r in runs if r.labels["verified"] is keep]
        summed: Dict[str, int] = collections.Counter()
        for r in group:
            for k, v in r.facts.items():
                summed[k] += int(v)
        summed["runs"] = len(group)
        summed["runs_with_an_empty_result"] = sum(
            r.facts["workers_empty_result"] > 0 for r in group
        )
        out[name] = dict(summed)
    return out


def _print_totals(t: Mapping[str, Mapping[str, int]]) -> None:
    for name, s in t.items():
        w, e = s["workers"], s["workers_empty_result"]
        tok, lost = s["worker_output_tokens"], s["worker_output_tokens_in_empty_results"]
        c, cap = s["worker_calls"], s["worker_calls_at_cap_without_answer"]
        print(
            f"EXACT {name}: {s['runs']} runs; {e} of {w} workers returned nothing"
            f" ({s['runs_with_an_empty_result']} runs affected); they used {lost} of {tok}"
            f" worker output tokens; {cap} of {c} model calls ended at the token cap with no"
            " answer text",
            flush=True,
        )


def main(argv: Optional[Sequence[str]] = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--home", default=None, help="queue state directory (default: OPENPROVER_HOME)")
    ap.add_argument("--out", required=True)
    ap.add_argument("--key-file", default="", help="TypeSafe API key file (mode 600)")
    ap.add_argument("--cache", default="", help="JSONL cache of model answers")
    ap.add_argument("--model", default=jd.PINNED_MODEL)
    ap.add_argument("--dry-run", action="store_true", help="count the requests, send none")
    args = ap.parse_args(argv)

    runs, skipped = load_runs(Path(args.home) if args.home else home())
    print(f"LOADED {len(runs)} runs with a verdict; skipped {skipped}", flush=True)
    report: Dict[str, Any] = {"n_runs": len(runs), "skipped": skipped, "exact": totals(runs)}
    report["runs"] = [
        {"target": r.target, "attempt": r.attempt, **r.facts, "verified": r.labels["verified"]}
        for r in runs
    ]
    _print_totals(report["exact"])

    if args.key_file or args.cache:
        client = None
        if args.key_file and not args.dry_run:
            client = jd.JevClient(jd.read_key(args.key_file), model=args.model)
        reader = jd.TraitReader(RUN_TRAITS, client, args.cache or None)
        boards = [r for r in runs if r.whiteboard is not None]
        todo = sum(reader.cached(r.whiteboard) is None for r in boards)
        print(f"MODEL {todo} of {len(boards)} whiteboards to ask", flush=True)
        rows: List[jd.Row] = []
        read: List[Dict[str, Any]] = []
        for r in boards:
            nouls = reader.read(r.whiteboard)
            if nouls is None:
                continue
            rows.append((nouls, r.labels))
            read.append({"target": r.target, "attempt": r.attempt, "nouls": nouls})
        tested = jd.hypotheses(RUN_TRAITS, rows)
        report["judged"] = {
            "trait_set": [RUN_TRAITS.name, RUN_TRAITS.version],
            "model": reader.model,
            "requests": client.requests if client else 0,
            "input_tokens": client.input_tokens if client else 0,
            "n_failures": len(reader.failures),
            "failures": reader.failures[:20],
            "n_read": len(rows),
            "hypotheses": tested,
            "lessons": jd.lessons(RUN_TRAITS, tested, LABEL_TEXT, "Runs"),
            "runs": read,
        }
        for h in tested:
            (a, b), (c, d) = h["label_true_when_yes"], h["label_true_when_no"]
            if h["testable"]:
                lo, hi = h["auc_interval95"] or (float("nan"), float("nan"))
                verdict = f"AUC {h['auc_declared']:.3f} [{lo:.3f}, {hi:.3f}]"
            else:
                verdict = "not testable"
            print(
                f"  jev {h['trait']:22s} -> {h['label']:18s} ({h['declared']}): {verdict};"
                f" label true in {a}/{b} when yes, {c}/{d} when no (n={h['n']})"
            )

    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(report, indent=2, default=str))
    print(f"WROTE {out}", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
