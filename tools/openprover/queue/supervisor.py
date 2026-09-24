#!/usr/bin/env python3
"""Continuous proof queue for the infer-0x fleet (spec 04 §10.4, decision D14).

Layout under $OPENPROVER_HOME (default ~/.local/share/openprover):
  venv/                  openprover==1.0.1 + tools/openprover/patch_local_alias.py
  lean-main/             git worktree of origin/main (the Lean project every run and check uses)
  leanproj/              symlinks into lean-main (OpenProver writes OpenProver-<id>/ here)
  fleet.json             [{"name": "infer-01", "host": "10.0.0.26", "port": 8081}, ...]
  queue/pending/<id>/    target.json + statement.lean + dossier.md   (drop new targets here)
  queue/running/<id>/    claimed by a node
  queue/done/<id>/       a candidate passed verify.py; proof + verdict copied to results/<id>/
  queue/parked/<id>/     max_attempts exhausted without a verified proof
  runs/<id>-<n>/         OpenProver run directories
  status.json, supervisor.log

target.json: {"theorem": "Fully.Qualified.name", "max_tokens": 150000, "max_attempts": 2,
              "planner": "sonnet", "worker": "qwen38-local", "note": "..."}

One run per healthy node. A node whose /health fails is restarted once over ssh; if it is still
down it is skipped for 30 minutes. Every candidate (PROOF.lean and every stored Lean item of the
run) goes through verify.py; OpenProver's own `proved` is never trusted on its own. Nothing is
committed, pushed or opened as a PR: landing a verified proof is a human step.
"""
import json
import os
import shutil
import subprocess
import time
import urllib.request
from datetime import datetime, timezone
from pathlib import Path

HOME = Path(os.environ.get("OPENPROVER_HOME", Path.home() / ".local/share/openprover"))
Q = HOME / "queue"
RUNS, RESULTS = HOME / "runs", HOME / "results"
VERIFY = Path(__file__).with_name("verify.py")
POLL_S, WALL_S, NODE_BACKOFF_S = 30, 9 * 3600, 1800
DEFAULTS = {"max_tokens": 150000, "max_attempts": 2, "planner": "sonnet", "worker": "qwen38-local"}


def now() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def log(msg: str) -> None:
    with open(HOME / "supervisor.log", "a") as f:
        f.write(f"{now()} {msg}\n")


def healthy(node: dict) -> bool:
    try:
        with urllib.request.urlopen(f"http://{node['host']}:{node['port']}/health", timeout=5) as r:
            return json.load(r).get("status") == "ok"
    except Exception:
        return False


def restart(node: dict) -> bool:
    log(f"{node['name']}: unhealthy, restarting llm-server@qwen38")
    subprocess.run(["ssh", "-o", "BatchMode=yes", "-o", "ConnectTimeout=10", node["name"],
                    "systemctl restart llm-server@qwen38"], capture_output=True, timeout=120)
    for _ in range(40):
        time.sleep(15)
        if healthy(node):
            log(f"{node['name']}: back after restart")
            return True
    return False


def target_cfg(d: Path) -> dict:
    return {**DEFAULTS, **json.loads((d / "target.json").read_text())}


def candidates(run_dir: Path) -> list[Path]:
    c = [run_dir / "PROOF.lean"] if (run_dir / "PROOF.lean").exists() else []
    return c + sorted((run_dir / "repo").rglob("*.lean")) if (run_dir / "repo").exists() else c


def start(tid: str, node: dict) -> dict:
    d = Q / "running" / tid
    cfg = target_cfg(d)
    attempt = len(list(RUNS.glob(f"{tid}-*"))) + 1
    run_dir = RUNS / f"{tid}-{attempt}"
    cmd = [str(HOME / "venv/bin/openprover"), str(run_dir), "--headless", "--autonomous",
           "--planner-model", cfg["planner"], "--worker-model", cfg["worker"],
           "--provider-url", f"http://{node['host']}:{node['port']}",
           "--answer-reserve", "16384", "--max-tokens", str(cfg["max_tokens"]),
           "--on-rate-limited", "backoff",
           "--lean-project", str(HOME / "leanproj"),
           "--lean-theorem", str(d / "statement.lean"), "--theorem", str(d / "dossier.md")]
    out = open(f"{run_dir}.log", "w")
    proc = subprocess.Popen(cmd, cwd=HOME / "leanproj", stdout=out, stderr=subprocess.STDOUT,
                            start_new_session=True)
    log(f"{tid}: attempt {attempt} started on {node['name']} (pid {proc.pid})")
    return {"tid": tid, "node": node["name"], "proc": proc, "run_dir": run_dir, "attempt": attempt,
            "started": time.time(), "cfg": cfg}


def finish(job: dict) -> None:
    tid, run_dir, cfg = job["tid"], job["run_dir"], job["cfg"]
    d = Q / "running" / tid
    reported = "?"
    logf = Path(f"{run_dir}.log")
    if logf.exists():
        for line in logf.read_text(errors="replace").splitlines():
            if line.startswith("[result]"):
                reported = line.split(maxsplit=1)[1].strip()
    verdicts = []
    for cand in candidates(run_dir):
        p = subprocess.run(["python3", str(VERIFY), str(cand), str(d / "statement.lean"),
                            cfg["theorem"], str(HOME / "lean-main")], capture_output=True, text=True)
        try:
            v = json.loads(p.stdout)
        except json.JSONDecodeError:
            v = {"candidate": str(cand), "passed": False, "error": p.stderr[-500:]}
        verdicts.append(v)
        if v.get("passed"):
            break
    (run_dir / "verdicts.json").write_text(json.dumps(verdicts, indent=2)) if run_dir.exists() else None
    ok = next((v for v in verdicts if v.get("passed")), None)
    hours = (time.time() - job["started"]) / 3600
    if ok:
        res = RESULTS / tid
        res.mkdir(parents=True, exist_ok=True)
        shutil.copy(ok["candidate"], res / "PROOF.lean")
        shutil.copy(d / "statement.lean", res / "statement.lean")
        (res / "verdict.json").write_text(json.dumps({**ok, "node": job["node"], "attempt": job["attempt"],
                                                      "run_dir": str(run_dir), "hours": round(hours, 2),
                                                      "openprover_result": reported,
                                                      "verified_at": now()}, indent=2))
        shutil.move(str(d), Q / "done" / tid)
        log(f"{tid}: VERIFIED (attempt {job['attempt']}, {hours:.1f} h, openprover said {reported!r})")
    else:
        if reported == "proved":
            log(f"{tid}: FINDING - openprover reported proved but no candidate passed verify.py")
        dest = "pending" if job["attempt"] < cfg["max_attempts"] else "parked"
        shutil.move(str(d), Q / dest / tid)
        log(f"{tid}: not verified (attempt {job['attempt']}, {hours:.1f} h, openprover said "
            f"{reported!r}) -> {dest}")


def write_status(jobs: dict, down: dict) -> None:
    st = {"at": now(),
          "running": {n: {"target": j["tid"], "attempt": j["attempt"],
                          "hours": round((time.time() - j["started"]) / 3600, 2)} for n, j in jobs.items()},
          "nodes_down_until": {n: datetime.fromtimestamp(t, timezone.utc).isoformat(timespec="seconds")
                               for n, t in down.items()},
          **{k: sorted(p.name for p in (Q / k).iterdir()) for k in ("pending", "done", "parked")}}
    (HOME / "status.json").write_text(json.dumps(st, indent=2))


def main() -> None:
    for k in ("pending", "running", "done", "parked"):
        (Q / k).mkdir(parents=True, exist_ok=True)
    RUNS.mkdir(exist_ok=True)
    RESULTS.mkdir(exist_ok=True)
    for d in (Q / "running").iterdir():  # interrupted by a supervisor restart: requeue
        shutil.move(str(d), Q / "pending" / d.name)
        log(f"{d.name}: requeued after supervisor restart")
    fleet = json.loads((HOME / "fleet.json").read_text())
    jobs: dict[str, dict] = {}
    down: dict[str, float] = {}
    log(f"supervisor up; fleet {[n['name'] for n in fleet]}")
    while True:
        for name, job in list(jobs.items()):
            if job["proc"].poll() is not None:
                finish(job)
                del jobs[name]
            elif time.time() - job["started"] > WALL_S:
                log(f"{job['tid']}: wall-clock guard ({WALL_S // 3600} h) on {name}, terminating")
                os.killpg(job["proc"].pid, 15)
        for node in fleet:
            n = node["name"]
            if n in jobs or down.get(n, 0) > time.time():
                continue
            pending = sorted((Q / "pending").iterdir(), key=lambda p: p.stat().st_mtime)
            if not pending:
                break
            if not healthy(node) and not restart(node):
                down[n] = time.time() + NODE_BACKOFF_S
                log(f"{n}: still down, skipping for {NODE_BACKOFF_S // 60} min")
                continue
            down.pop(n, None)
            tid = pending[0].name
            shutil.move(str(pending[0]), Q / "running" / tid)
            jobs[n] = start(tid, node)
        write_status(jobs, down)
        time.sleep(POLL_S)


if __name__ == "__main__":
    main()
