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
