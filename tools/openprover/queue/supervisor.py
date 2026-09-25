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
              "max_planner_usd": 30, "planner": "opus", "worker": "qwen38-local", "note": "..."}
  optional: "effort" (Claude planner, default "high"), "advisor" (e.g. "opus"; attached only on
  planner steps 1, 1+advisor_every, ... up to advisor_max per run), "history_budget" (chars of
  planner history, default 120000 for every planner so arms see the same history), "pilot" (true:
  exempt from the daily-cap fallback below, so a planner comparison keeps its arms).

Daily planner cap (owner, 2026-09-25): when the Claude planner spend of the last 24 h (every
step's meta.toml, advisor included) reaches OPENPROVER_DAILY_PLANNER_USD (default 60, list-price
equivalent), new non-pilot attempts are planned by the local model (qwen38-local) with no
advisor. Running attempts keep their per-attempt cap.

One run per healthy node. A node whose /health fails is restarted once over ssh; if it is still
down it is skipped for 30 minutes. Running jobs are watched too: a node that fails two consecutive
health checks mid-run is restarted, and if that fails the run is terminated and requeued without
charging an attempt; five consecutive failed planner calls (the Claude CLI refusing, e.g. at the
subscription limit) terminate the run uncharged and pause all dispatch for 30 minutes (2026-09-24: a SLURM prolog killed a node's server and the planner kept
spawning workers into a dead endpoint, ~$50 nominal). Each attempt is also capped by planner spend
(`max_planner_usd`, default 30) and a 9 h wall clock. Every candidate (PROOF.lean and every stored Lean item of the
run) goes through verify.py; OpenProver's own `proved` is never trusted on its own. Nothing is
committed, pushed or opened as a PR: landing a verified proof is a human step.
"""
import json
import os
import re
import tomllib
import shutil
import signal
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
DEFAULTS = {"max_tokens": 150000, "max_attempts": 2, "planner": "opus", "worker": "qwen38-local",
            "max_planner_usd": 30.0, "effort": "high", "advisor": None, "advisor_every": 5,
            "advisor_max": 3, "history_budget": 120000, "pilot": False}
CLAUDE_PLANNERS = {"sonnet", "opus"}
LOCAL_PLANNER = "qwen38-local"
DAILY_PLANNER_USD = float(os.environ.get("OPENPROVER_DAILY_PLANNER_USD", "60"))
UNHEALTHY_POLLS = 2  # consecutive failed /health checks on a running job's node before acting
PLANNER_DOWN_STREAK = [0]  # consecutive planner-outage aborts; the pause doubles each time (cap 8x)
PLANNER_ERR_STEPS = 5  # consecutive planner llm_error steps (e.g. subscription limit) before pausing


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


def planner_usd(run_dir: Path) -> float:
    total = 0.0
    for f in run_dir.glob("steps/step_*/meta.toml"):
        try:
            total += tomllib.loads(f.read_text()).get("planner", {}).get("cost_usd", 0.0)
        except (OSError, tomllib.TOMLDecodeError):
            pass
    return total


def planner_usd_24h() -> float:
    """Planner spend (list-price $, advisor included) of every step finished in the last 24 h."""
    cutoff = time.time() - 86400
    total = 0.0
    for steps in RUNS.glob("*/steps"):
        if steps.stat().st_mtime < cutoff - WALL_S:  # no step started in the window
            continue
        for f in steps.glob("step_*/meta.toml"):
            try:
                if f.stat().st_mtime >= cutoff:
                    total += tomllib.loads(f.read_text()).get("planner", {}).get("cost_usd", 0.0)
            except (OSError, tomllib.TOMLDecodeError):
                pass
    return total


def choose_planner(tid: str, cfg: dict) -> tuple[str, str | None]:
    """(planner, advisor) for a new attempt: the target's own, or the local planner over the cap."""
    if cfg["planner"] in CLAUDE_PLANNERS and not cfg["pilot"]:
        spent = planner_usd_24h()
        if spent >= DAILY_PLANNER_USD:
            log(f"{tid}: Claude planner spend ${spent:.2f} in the last 24 h >= "
                f"${DAILY_PLANNER_USD:.0f} cap, planning with {LOCAL_PLANNER}")
            return LOCAL_PLANNER, None
    return cfg["planner"], cfg["advisor"]


def trailing_llm_errors(run_dir: Path) -> int:
    """Consecutive most-recent steps whose planner call failed (status = "llm_error")."""
    n = 0
    for f in sorted(run_dir.glob("steps/step_*/meta.toml"), reverse=True):
        try:
            if tomllib.loads(f.read_text()).get("status") != "llm_error":
                break
        except (OSError, tomllib.TOMLDecodeError):
            break
        n += 1
    return n


def charged(d: Path) -> int:
    f = d / "attempts_charged"
    return int(f.read_text()) if f.exists() else 0


def candidates(run_dir: Path) -> list[Path]:
    c = [run_dir / "PROOF.lean"] if (run_dir / "PROOF.lean").exists() else []
    return c + sorted((run_dir / "repo").rglob("*.lean")) if (run_dir / "repo").exists() else c


def start(tid: str, node: dict) -> dict:
    d = Q / "running" / tid
    cfg = target_cfg(d)
    used = [int(m.group(1)) for p in RUNS.glob(f"{tid}-*")
            if (m := re.fullmatch(rf"{re.escape(tid)}-(\d+)(?:\.log)?", p.name))]
    attempt = max(used, default=0) + 1  # never reuse a run dir: OpenProver would resume it
    run_dir = RUNS / f"{tid}-{attempt}"
    planner, advisor = choose_planner(tid, cfg)
    cmd = [str(HOME / "venv/bin/openprover"), str(run_dir), "--headless", "--autonomous",
           "--planner-model", planner, "--worker-model", cfg["worker"],
           "--provider-url", f"http://{node['host']}:{node['port']}",
           "--answer-reserve", "16384", "--max-tokens", str(cfg["max_tokens"]),
           "--history-budget", str(cfg["history_budget"]),
           "--on-rate-limited", "backoff",
           "--lean-project", str(HOME / "leanproj"),
           "--lean-theorem", str(d / "statement.lean"), "--theorem", str(d / "dossier.md")]
    if planner in CLAUDE_PLANNERS:
        cmd += ["--effort", cfg["effort"]]
    env = {k: v for k, v in os.environ.items() if not k.startswith("OPENPROVER_ADVISOR_")}
    if advisor and planner in CLAUDE_PLANNERS:  # read by the patched llm/claude.py
        env.update(OPENPROVER_ADVISOR_MODEL=advisor, OPENPROVER_ADVISOR_EVERY=str(cfg["advisor_every"]),
                   OPENPROVER_ADVISOR_MAX=str(cfg["advisor_max"]))
    else:
        advisor = None
    plan = {"planner": planner, "advisor": advisor,
            "effort": cfg["effort"] if planner in CLAUDE_PLANNERS else None,
            "advisor_every": cfg["advisor_every"] if advisor else None,
            "advisor_max": cfg["advisor_max"] if advisor else None,
            "history_budget": cfg["history_budget"], "pilot": cfg["pilot"],
            "fallback": planner != cfg["planner"]}
    Path(f"{run_dir}.planner.json").write_text(json.dumps(plan, indent=2))
    out = open(f"{run_dir}.log", "w")
    proc = subprocess.Popen(cmd, cwd=HOME / "leanproj", stdout=out, stderr=subprocess.STDOUT,
                            start_new_session=True, env=env)
    log(f"{tid}: attempt {attempt} started on {node['name']} (pid {proc.pid}; planner {planner}"
        f"{f' + advisor {advisor}' if advisor else ''})")
    return {"tid": tid, "node": node["name"], "proc": proc, "run_dir": run_dir, "attempt": attempt,
            "started": time.time(), "cfg": cfg, "plan": plan, "unhealthy": 0, "abort": None}


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
    if job["abort"] is None:
        PLANNER_DOWN_STREAK[0] = 0  # a run finished normally: the planner is back
    hours = (time.time() - job["started"]) / 3600
    if ok:
        res = RESULTS / tid
        res.mkdir(parents=True, exist_ok=True)
        shutil.copy(ok["candidate"], res / "PROOF.lean")
        shutil.copy(d / "statement.lean", res / "statement.lean")
        (res / "verdict.json").write_text(json.dumps({**ok, "node": job["node"], "attempt": job["attempt"],
                                                      "run_dir": str(run_dir), "hours": round(hours, 2),
                                                      "openprover_result": reported,
                                                      "plan": job["plan"],
                                                      "planner_usd": round(planner_usd(run_dir), 2),
                                                      "verified_at": now()}, indent=2))
        shutil.move(str(d), Q / "done" / tid)
        log(f"{tid}: VERIFIED (attempt {job['attempt']}, {hours:.1f} h, openprover said {reported!r})")
    else:
        if reported == "proved" and (run_dir / "PROOF.lean").exists():
            log(f"{tid}: FINDING - openprover accepted a PROOF.lean that verify.py rejected")
        elif reported == "proved":  # cli.py prints `proved` whenever PROOF.md exists
            log(f"{tid}: openprover's 'proved' is informal only (PROOF.md, no PROOF.lean)")
        n = charged(d)
        if job["abort"] not in ("infra", "planner_down"):  # outages are not the target's fault
            n += 1
            (d / "attempts_charged").write_text(str(n))
        dest = "pending" if n < cfg["max_attempts"] else "parked"
        shutil.move(str(d), Q / dest / tid)
        log(f"{tid}: not verified (run {job['attempt']}, {n}/{cfg['max_attempts']} attempts charged, "
            f"{hours:.1f} h, openprover said {reported!r}, abort={job['abort']}, "
            f"planner {job['plan']['planner']}) -> {dest}")


def write_status(jobs: dict, down: dict) -> None:
    st = {"at": now(),
          "planner_usd_24h": round(planner_usd_24h(), 2), "daily_planner_cap_usd": DAILY_PLANNER_USD,
          "running": {n: {"target": j["tid"], "attempt": j["attempt"], "planner": j["plan"]["planner"],
                          "advisor": j["plan"]["advisor"],
                          "hours": round((time.time() - j["started"]) / 3600, 2)} for n, j in jobs.items()},
          "nodes_down_until": {n: datetime.fromtimestamp(t, timezone.utc).isoformat(timespec="seconds")
                               for n, t in down.items()},
          **{k: sorted(p.name for p in (Q / k).iterdir()) for k in ("pending", "done", "parked")}}
    (HOME / "status.json").write_text(json.dumps(st, indent=2))


def tick(fleet: list, jobs: dict, down: dict) -> None:
    """One supervisor poll: reap, watch and dispatch."""
    for name, job in list(jobs.items()):
        if job["proc"].poll() is not None:
            finish(job)
            del jobs[name]
            continue
        if job["abort"]:
            continue  # already signalled; wait for the process to exit
        node = next(n for n in fleet if n["name"] == name)
        job["unhealthy"] = 0 if healthy(node) else job["unhealthy"] + 1
        usd = planner_usd(job["run_dir"])
        if time.time() - job["started"] > WALL_S:
            job["abort"] = "wall"
            log(f"{job['tid']}: wall-clock guard ({WALL_S // 3600} h) on {name}, terminating")
        elif usd > job["cfg"]["max_planner_usd"]:
            job["abort"] = "planner_budget"
            log(f"{job['tid']}: planner spend ${usd:.2f} > ${job['cfg']['max_planner_usd']:.2f} "
                f"on {name}, terminating")
        elif trailing_llm_errors(job["run_dir"]) >= PLANNER_ERR_STEPS:
            job["abort"] = "planner_down"
            PLANNER_DOWN_STREAK[0] += 1
            pause = NODE_BACKOFF_S * 2 ** min(PLANNER_DOWN_STREAK[0] - 1, 3)
            down["*"] = max(down.get("*", 0), time.time() + pause)
            log(f"{job['tid']}: {PLANNER_ERR_STEPS}+ consecutive planner errors (Claude CLI; quota?), "
                f"terminating (not charged) and pausing dispatch {pause // 60} min "
                f"(outage #{PLANNER_DOWN_STREAK[0]} in a row)")
        elif job["unhealthy"] >= UNHEALTHY_POLLS and not restart(node):
            job["abort"] = "infra"
            down[name] = time.time() + NODE_BACKOFF_S
            log(f"{job['tid']}: {name} down mid-run and restart failed, terminating (not charged)")
        if job["abort"]:
            os.killpg(job["proc"].pid, 15)
    if down.get("*", 0) > time.time():
        return  # global pause (planner outage)
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


def main() -> None:
    # `systemctl stop/restart` signals the whole cgroup: without this, the loop can reap a job the
    # stop just killed and charge it as a failed attempt (seen 2026-09-24 05:53). Exit at once;
    # the next start requeues every running/ target uncharged.
    signal.signal(signal.SIGTERM, lambda *_: os._exit(0))
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
        tick(fleet, jobs, down)
        write_status(jobs, down)
        time.sleep(POLL_S)


if __name__ == "__main__":
    main()
