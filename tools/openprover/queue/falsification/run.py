#!/usr/bin/env python3
"""Falsification set for verify.py. Every forged candidate must FAIL, both through the full
verifier and through the kernel/probe layers alone (text deny-list bypassed), and every genuine
proof given on the command line as `candidate:statement:theorem` must PASS.
usage: run.py <lean-project-dir> [candidate.lean:statement.lean:Fully.Qualified.thm ...]"""
import importlib.util
import sys
from pathlib import Path

here = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("verify", here.parent / "verify.py")
vf = importlib.util.module_from_spec(spec)
spec.loader.exec_module(vf)
project = Path(sys.argv[1])
ok = True
forged = ["forged_nocheck.lean", "forged_sorryax_printed_axioms.lean", "forged_printed_markers.lean"]
for f in forged:
    full = vf.verify(here / f, here / "statement.lean", "VQ.target", project)
    saved = vf.FORBIDDEN, vf.bad_options
    vf.FORBIDDEN, vf.bad_options = [], (lambda s: [])  # bypass the text layer
    deep = vf.verify(here / f, here / "statement.lean", "VQ.target", project)
    vf.FORBIDDEN, vf.bad_options = saved
    dc = deep["checks"]
    caught = ("kernel" if dc.get("kernel_replay_rc") not in (None, 0) else
              "sorry/compile" if dc.get("sorry_warning") or dc.get("errors") else
              "axioms" if dc.get("axioms") is None or not set(dc["axioms"]) <= vf.STANDARD_AXIOMS else
              "type" if dc.get("elaborated_type_identical") is False else "NOT CAUGHT")
    good = not full["passed"] and not deep["passed"]
    ok &= good
    print(f"{'ok  ' if good else 'FAIL'} forged {f}: full={full['passed']} "
          f"text={full['checks'].get('forbidden')} deep={deep['passed']} caught_by={caught}")
for arg in sys.argv[2:]:
    cand, stmt, thm = arg.split(":")
    r = vf.verify(Path(cand), Path(stmt), thm, project)
    ok &= r["passed"]
    print(f"{'ok  ' if r['passed'] else 'FAIL'} genuine {Path(cand).parent.name}/{Path(cand).name}: "
          f"{ {k: r['checks'].get(k) for k in ('kernel_replay_rc', 'axioms', 'elaborated_type_identical')} }")
sys.exit(0 if ok else 1)
