"""The supervisor's pure parts (``pytest tools/openprover/queue``): the per-call cap a run is
started with, and the exact count of workers that returned nothing."""

from __future__ import annotations

import importlib
import json
import sys
from pathlib import Path

import pytest


@pytest.fixture
def supervisor(tmp_path, monkeypatch):
    monkeypatch.setenv("OPENPROVER_HOME", str(tmp_path))
    monkeypatch.syspath_prepend(str(Path(__file__).resolve().parent))
    sys.modules.pop("supervisor", None)
    module = importlib.import_module("supervisor")
    for k in ("pending", "running", "done", "parked"):
        (module.Q / k).mkdir(parents=True)
    module.RUNS.mkdir()
    return module


def _target(supervisor, **extra):
    d = supervisor.Q / "running" / "T1"
    d.mkdir()
    (d / "target.json").write_text(json.dumps({"theorem": "A.b", **extra}))
    (d / "statement.lean").write_text("theorem b : True := by sorry\n")
    (d / "dossier.md").write_text("goal\n")
    return d


def _start(supervisor, monkeypatch):
    seen = {}

    class Proc:
        pid = 1

    def popen(cmd, **kw):
        seen["cmd"] = cmd
        return Proc()

    monkeypatch.setattr(supervisor.subprocess, "Popen", popen)
    monkeypatch.setattr(supervisor, "planner_usd_24h", lambda: 0.0)
    job = supervisor.start("T1", {"name": "n1", "host": "h", "port": 1})
    cmd = seen["cmd"]
    return job, cmd[cmd.index("--answer-reserve") + 1]


def test_the_per_call_cap_exceeds_the_fleet_reasoning_budget_by_default(supervisor, monkeypatch):
    _target(supervisor)
    job, reserve = _start(supervisor, monkeypatch)
    assert reserve == "24576" and int(reserve) > 16384
    assert job["plan"]["answer_reserve"] == 24576
    recorded = json.loads(Path(f"{job['run_dir']}.planner.json").read_text())
    assert recorded["answer_reserve"] == 24576


def test_a_target_can_set_its_own_cap(supervisor, monkeypatch):
    _target(supervisor, answer_reserve=16384)
    job, reserve = _start(supervisor, monkeypatch)
    assert reserve == "16384" and job["plan"]["answer_reserve"] == 16384


def test_workers_that_returned_nothing_are_counted_from_the_records(supervisor, tmp_path):
    run = tmp_path / "runs" / "T1-1"
    workers = run / "steps" / "step_001" / "workers"
    workers.mkdir(parents=True)
    (run / "steps" / "step_001" / "meta.toml").write_text(
        "[[workers]]\nindex = 0\n[[workers]]\nindex = 1\n[[workers]]\nindex = 2\n"
    )
    (workers / "result_0.md").write_text("")
    (workers / "result_1.md").write_text("theorem t : True := trivial")
    # worker 2 has no result file (still running, or killed): not counted as empty
    (run / "steps" / "step_002").mkdir()
    (run / "steps" / "step_002" / "meta.toml").write_text("not toml [")
    assert supervisor.worker_losses(run) == (1, 3)
    assert supervisor.worker_losses(tmp_path / "runs" / "absent") == (0, 0)


def _earlier_run(supervisor, n, files, board="## Status\nL1 done; L2 next.\n"):
    run = supervisor.RUNS / f"T1-{n}"
    (run / "repo" / "lean").mkdir(parents=True)
    for name, body in files.items():
        (run / "repo" / "lean" / name).write_text(body)
    (run / "WHITEBOARD.md").write_text(board)
    return run


def test_a_first_attempt_is_given_the_audited_dossier_and_nothing_else(supervisor, monkeypatch):
    d = _target(supervisor)
    job, _ = _start(supervisor, monkeypatch)
    assert job["plan"]["carried"] is None
    assert not Path(f"{job['run_dir']}.dossier.md").exists()
    assert supervisor.carried("T1", 1) == ("", {})
    assert (d / "dossier.md").read_text() == "goal\n"


def test_a_later_attempt_gets_the_compiling_items_of_the_run_that_got_furthest(
    supervisor, monkeypatch
):
    d = _target(supervisor)
    two = "theorem good : True := trivial\n\nlemma also : True := trivial\n"
    _earlier_run(supervisor, 1, {"old.lean": "theorem old : True := trivial\n"})
    _earlier_run(
        supervisor,
        2,
        {"good.lean": two, "bad.lean": "theorem bad : False := x\n"},
        board="## Status\nL1 done; L2 next.\n",
    )
    # the latest run saved less than run 2, and its only item does not compile
    _earlier_run(supervisor, 3, {"late.lean": "theorem late : True := trivial\n"}, board="late")
    checked = []

    def check(f):
        checked.append(f.name)
        return ": True" in f.read_text()

    monkeypatch.setattr(supervisor, "compiles", check)
    text, record = supervisor.carried("T1", 4)
    assert record == {"from_attempt": 2, "lean_items": ["lean/good.lean"]}
    assert "theorem good" in text and "theorem bad" not in text
    assert "theorem old" not in text and "theorem late" not in text
    assert "not part of the audited dossier" in text and "L1 done; L2 next." in text
    assert checked == ["bad.lean", "good.lean"]  # only the richest run is compiled
    seen = {}
    proc = type("P", (), {"pid": 1})()
    monkeypatch.setattr(
        supervisor.subprocess, "Popen", lambda cmd, **kw: seen.update(cmd=cmd) or proc
    )
    monkeypatch.setattr(supervisor, "planner_usd_24h", lambda: 0.0)
    job = supervisor.start("T1", {"name": "n1", "host": "h", "port": 1})
    cmd = seen["cmd"]
    given = Path(cmd[cmd.index("--theorem") + 1])
    assert given.name == "T1-4.dossier.md" and given.read_text().startswith("goal\n")
    assert "theorem good" in given.read_text()
    assert job["plan"]["carried"] == record
    assert (d / "dossier.md").read_text() == "goal\n"  # the audited dossier is never edited


def test_ties_go_to_the_later_run_and_a_run_with_nothing_compiling_is_passed_over(supervisor):
    _target(supervisor)
    one = "theorem a : True := trivial\n"
    _earlier_run(supervisor, 1, {"a.lean": one})
    _earlier_run(supervisor, 2, {"a.lean": one})
    assert supervisor.carried("T1", 3, lambda f: True)[1]["from_attempt"] == 2
    _earlier_run(supervisor, 3, {"b.lean": "theorem x : False := y\n\ntheorem z : False := y\n"})
    record = supervisor.carried("T1", 4, lambda f: ": True" in f.read_text())[1]
    assert record["from_attempt"] == 2  # run 3 has more declarations, none of them compiling


def test_pilot_targets_and_opted_out_targets_carry_nothing(supervisor, monkeypatch):
    for extra in ({"pilot": True}, {"carry_forward": False}):
        _target(supervisor, **extra)
        _earlier_run(supervisor, 1, {"good.lean": "theorem good : True := trivial\n"})
        monkeypatch.setattr(supervisor, "compiles", lambda f: True)
        job, _ = _start(supervisor, monkeypatch)
        assert job["plan"]["carried"] is None
        import shutil

        shutil.rmtree(supervisor.Q / "running" / "T1")
        shutil.rmtree(supervisor.RUNS)
        supervisor.RUNS.mkdir()


def test_an_item_with_a_sorry_or_a_failed_check_is_not_carried(supervisor, tmp_path, monkeypatch):
    f = tmp_path / "x.lean"
    f.write_text("theorem t : True := by sorry\n")
    calls = []
    monkeypatch.setattr(
        supervisor.subprocess,
        "run",
        lambda *a, **k: calls.append(a) or type("R", (), {"returncode": 0, "stdout": ""})(),
    )
    assert supervisor.compiles(f) is False and calls == []  # a sorry is refused before Lean runs
    f.write_text("theorem t : True := trivial\n")
    assert supervisor.compiles(f) is True and len(calls) == 1
    monkeypatch.setattr(
        supervisor.subprocess,
        "run",
        lambda *a, **k: type("R", (), {"returncode": 1, "stdout": "error"})(),
    )
    assert supervisor.compiles(f) is False


def test_an_unwritten_whiteboard_and_an_oversized_item_are_left_out(supervisor):
    big = "theorem big : True := trivial\n" + "-- pad\n" * 20000
    _earlier_run(
        supervisor,
        1,
        {"a_small.lean": "theorem small : True := trivial\n", "b_big.lean": big},
        board="## Goal\n\n**Prove and Formalize**\nProduce both an informal proof\n",
    )
    text, record = supervisor.carried("T1", 2, lambda f: True)
    assert record["lean_items"] == ["lean/a_small.lean"]
    assert "final whiteboard" not in text and len(text) < supervisor.CARRY_MAX_CHARS
