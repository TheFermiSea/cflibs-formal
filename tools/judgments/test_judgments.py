"""Tests for the shared judgment layer and the proof-run post-mortem (``pytest tools/judgments``).

No request leaves the process: the client is driven through its ``opener`` seam, and the run
records are built in a temporary directory in the queue's own layout.
"""

from __future__ import annotations

import io
import json
import sys
import urllib.error
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent))

import judgments as jd  # noqa: E402
import proof_runs  # noqa: E402

KEY = "ts-test-key-0123456789abcdef0123456789"
TRAITS = jd.TraitSet(
    name="toy",
    version="1",
    state_field="text",
    traits=(
        jd.Trait(
            "loud", "Is `text` loud?", "It shouts.", "It does not.", (("heard", True),), "shout"
        ),
        jd.Trait("long", "Is `text` long?", "Many words.", "Few words.", (("heard", False),)),
    ),
)


class FakeResponse:
    def __init__(self, doc):
        self._body = json.dumps(doc).encode("utf-8")

    def read(self):
        return self._body

    def __enter__(self):
        return self

    def __exit__(self, *exc):
        return False


def _answers(value=0.9, model=jd.PINNED_MODEL):
    return {
        "model": model,
        "answers": {tid: {"type": "noul", "noul": value} for tid in TRAITS.ids},
        "usage": {"input_tokens": 321, "output_tokens": 20},
    }


def _http_error(code, headers=None):
    return urllib.error.HTTPError(jd.API_URL, code, "x", headers or {}, io.BytesIO(b"{}"))


class Transport:
    """Replays a list of responses or exceptions; records every request."""

    def __init__(self, *replies):
        self.replies = list(replies)
        self.requests = []
        self.sleeps = []

    def __call__(self, request, timeout):
        self.requests.append(request)
        reply = self.replies.pop(0)
        if isinstance(reply, Exception):
            raise reply
        return FakeResponse(reply)

    def client(self, **kw):
        return jd.JevClient(KEY, opener=self, sleep=self.sleeps.append, **kw)


# --------------------------------------------------------------------------- the client
def test_the_request_is_one_noul_per_trait_against_a_pinned_model():
    transport = Transport(_answers())
    nouls = transport.client().ask({"text": "HEY"}, TRAITS.questions())
    request = transport.requests[0]
    body = json.loads(request.data.decode("utf-8"))
    assert request.full_url == jd.API_URL and request.get_method() == "POST"
    assert request.get_header("Authorization") == f"Bearer {KEY}"
    assert body["model"] == jd.PINNED_MODEL and not body["model"].endswith("latest")
    assert body["state"] == {"text": "HEY"} and set(body["questions"]) == {"loud", "long"}
    for q in body["questions"].values():
        assert q["type"] == "noul" and set(q["criteria"]) == {"true", "false"}
    assert nouls == {"loud": 0.9, "long": 0.9}


def test_rate_limits_are_retried_and_the_server_delay_is_honoured():
    transport = Transport(_http_error(429, {"retry-after": "7"}), _http_error(529), _answers())
    client = transport.client()
    assert client.ask({}, TRAITS.questions())["loud"] == 0.9
    assert transport.sleeps == [7.0, 2.0] and client.requests == 1 and client.input_tokens == 321


def test_a_rejected_key_is_not_retried_and_the_error_does_not_carry_it():
    transport = Transport(_http_error(401), _answers())
    with pytest.raises(jd.JevError) as err:
        transport.client().ask({}, TRAITS.questions())
    assert len(transport.requests) == 1 and KEY not in str(err.value)


def test_retries_are_bounded():
    transport = Transport(*[_http_error(529)] * 3)
    with pytest.raises(jd.JevError, match="3 attempts"):
        transport.client(max_attempts=3).ask({}, TRAITS.questions())
    assert len(transport.sleeps) == 2


@pytest.mark.parametrize(
    "mutate",
    [
        lambda d: d["answers"].pop("loud"),
        lambda d: d["answers"].__setitem__("loud", {"type": "noul", "noul": 1.5}),
        lambda d: d["answers"].__setitem__("loud", {"type": "noul", "noul": True}),
        lambda d: d["answers"].__setitem__("loud", {"type": "choice", "choice": "a"}),
        lambda d: d.__setitem__("model", "jev-2.0.0"),
        lambda d: d.pop("answers"),
    ],
)
def test_an_incomplete_or_foreign_answer_is_an_error_not_a_value(mutate):
    doc = _answers()
    mutate(doc)
    with pytest.raises(jd.JevError):
        Transport(doc).client().ask({}, TRAITS.questions())


def test_a_key_file_others_can_read_is_refused(tmp_path):
    path = tmp_path / "key"
    path.write_text(KEY + "\n")
    path.chmod(0o644)
    with pytest.raises(PermissionError):
        jd.read_key(str(path))
    path.chmod(0o600)
    assert jd.read_key(str(path)) == KEY


# --------------------------------------------------------------------------- the cache
def test_a_text_is_asked_once_and_the_cache_holds_no_key(tmp_path):
    cache = tmp_path / "traits.jsonl"
    transport = Transport(_answers(0.8))
    reader = jd.TraitReader(TRAITS, transport.client(), str(cache))
    assert reader.cached("HEY") is None
    first = reader.read("HEY")
    assert reader.read("HEY") == first and len(transport.requests) == 1
    assert KEY not in cache.read_text()
    assert jd.TraitReader(TRAITS, None, str(cache)).read("HEY") == first


def test_the_cache_is_per_model_set_and_version(tmp_path):
    cache = tmp_path / "traits.jsonl"
    jd.TraitReader(TRAITS, Transport(_answers(0.8)).client(), str(cache)).read("HEY")
    other = Transport(_answers(0.2, model="jev-9.9.9"))
    reader = jd.TraitReader(TRAITS, other.client(model="jev-9.9.9"), str(cache))
    assert reader.read("HEY")["loud"] == 0.2
    assert jd.TraitReader(TRAITS._replace(version="2"), None, str(cache)).cached("HEY") is None
    assert jd.TraitReader(TRAITS._replace(name="other"), None, str(cache)).cached("HEY") is None


def test_a_failed_request_is_recorded_and_yields_nothing(tmp_path):
    reader = jd.TraitReader(TRAITS, Transport(_http_error(401)).client(), str(tmp_path / "c"))
    assert reader.read("HEY") is None
    assert len(reader.failures) == 1 and not (tmp_path / "c").exists()


# --------------------------------------------------------------------------- the evidence
def test_auc_orientation_and_ties():
    assert jd.auc([0.9, 0.8, 0.2, 0.1], [True, True, False, False]) == 1.0
    assert jd.auc([0.1, 0.2, 0.8, 0.9], [True, True, False, False]) == 0.0
    assert jd.auc([0.5, 0.5, 0.5, 0.5], [True, False, True, False]) == 0.5
    assert jd.auc([1.0, 0.0, 1.0, 0.0], [True, True, False, False]) == 0.5
    assert jd.auc([0.3, 0.4], [True, True]) is None


def test_marks_and_signature():
    assert [jd.mark(v) for v in (None, 0.5, 0.36, 0.35, 0.65, 1.0)] == list("???nyy")
    assert jd.signature(TRAITS, {"loud": 0.9}) == "y?"


def _rows(n=24):
    """``loud`` predicts ``heard`` perfectly; ``long`` is unrelated; one row is unmeasured."""
    rows = [({"loud": 0.9 if i < n // 2 else 0.1, "long": 0.9 if i % 2 else 0.1},
             {"heard": i < n // 2}) for i in range(n)]  # fmt: skip
    return rows + [({"loud": 0.9, "long": None}, {"heard": None})]


def test_hypotheses_follow_the_declared_direction():
    by = {h["trait"]: h for h in jd.hypotheses(TRAITS, _rows())}
    assert by["loud"]["testable"] and by["loud"]["auc_declared"] == 1.0 and by["loud"]["n"] == 24
    assert by["loud"]["label_true_when_yes"] == [12, 12]
    assert by["loud"]["label_true_when_no"] == [0, 12]
    assert by["long"]["declared"] == "yes lowers it" and by["long"]["auc_declared"] == 0.5
    few = jd.hypotheses(TRAITS, _rows(12))
    assert not any(h["testable"] for h in few)  # six of each class: below MIN_CLASS


def test_lessons_state_counts_for_decided_hypotheses_only():
    tested = jd.hypotheses(TRAITS, _rows())
    assert jd.lessons(TRAITS, tested, {"heard": "were heard"}, "Texts") == [
        "Texts that shout were heard in 12 of 12 cases; texts that do not, in 0 of 12."
    ]  # ``long`` is undecided (interval around 0.5) and has no lesson phrase
    assert jd.lessons(TRAITS, tested, {}, "Texts") == []


# --------------------------------------------------------------------------- proof runs
LOG = """\
2026-09-28T01:36:45+00:00 A-target: not verified (run 1, 1/2 attempts charged, 3.4 h, openprover said 'proved', abort=None, planner opus) -> pending
2026-09-28T02:36:45+00:00 A-target: VERIFIED (attempt 2, 2.4 h, openprover said 'proved')
2026-09-28T03:00:00+00:00 B-target: not verified (run 1, 0/2 attempts charged, 0.1 h, openprover said 'not_proved', abort=planner_down, planner opus) -> pending
2026-09-28T03:10:00+00:00 supervisor up; slots []
"""


def _run(root, name, *, empty, board, proof_md=True, lean=True):
    run = root / "runs" / name
    workers = run / "steps" / "step_001" / "workers"
    workers.mkdir(parents=True)
    (run / "steps" / "step_001" / "meta.toml").write_text(
        'status = "ok"\n[[workers]]\nindex = 0\noutput_tokens = 32768\n'
        "[[workers]]\nindex = 1\noutput_tokens = 1000\n"
    )
    (workers / "result_0.md").write_text("" if empty else "theorem t : True := trivial")
    (workers / "result_1.md").write_text("done")
    capped = {"choices": [{"finish_reason": "length", "message": {"content": ""}}]}
    fine = {"choices": [{"finish_reason": "stop", "message": {"content": "ok"}}]}
    (workers / "worker_0_call_0.raw.json").write_text(json.dumps(capped if empty else fine))
    (workers / "worker_1_call_0.raw.json").write_text(json.dumps(fine))
    (run / "WHITEBOARD.md").write_text(board)
    if proof_md:
        (run / "PROOF.md").write_text("informal")
    if lean:
        (run / "repo").mkdir()
        (run / "repo" / "l1.lean").write_text("theorem t : True := trivial")
    return run


def _home(tmp_path):
    (tmp_path / "supervisor.log").write_text(LOG)
    _run(tmp_path, "A-target-1", empty=True, board="## Failed\n- step 3: EMPTY output\n")
    _run(tmp_path, "A-target-2", empty=False, board="## Status\nAll done.\n")
    _run(tmp_path, "B-target-1", empty=False, board="x", proof_md=False, lean=False)
    return tmp_path


def test_outcomes_are_read_from_the_supervisor_log():
    assert proof_runs.outcomes(LOG) == {
        ("A-target", 1): (False, "proved", None),
        ("A-target", 2): (True, "proved", None),
        ("B-target", 1): (False, "not_proved", "planner_down"),
    }


def test_exact_counts_come_from_the_records(tmp_path):
    facts = proof_runs.run_facts(_home(tmp_path) / "runs" / "A-target-1")
    assert facts["workers"] == 2 and facts["workers_empty_result"] == 1
    assert facts["worker_output_tokens"] == 33768
    assert facts["worker_output_tokens_in_empty_results"] == 32768
    assert facts["worker_calls"] == 2 and facts["worker_calls_at_cap_without_answer"] == 1
    assert facts["informal_written"] and facts["lean_items_saved"]


def test_outage_runs_and_unwritten_whiteboards_are_not_post_mortem_material(tmp_path):
    home = _home(tmp_path)
    board = home / "runs" / "A-target-2" / "WHITEBOARD.md"
    board.write_text("## Goal\n\n**Prove and Formalize**\nProduce both an informal proof\n")
    runs, skipped = proof_runs.load_runs(home)
    assert skipped == {"aborted_planner_down": 1}
    assert [(r.target, r.attempt, r.labels["verified"]) for r in runs] == [
        ("A-target", 1, False),
        ("A-target", 2, True),
    ]
    assert runs[0].labels["output_lost"] is True and runs[1].labels["output_lost"] is False
    assert runs[0].whiteboard is not None and runs[1].whiteboard is None


def test_the_report_keeps_exact_and_judged_apart_and_a_dry_run_sends_nothing(
    tmp_path, monkeypatch, capsys
):
    home = _home(tmp_path)
    key = tmp_path / "key"
    key.write_text(KEY)
    key.chmod(0o600)
    sent = []

    class Client:
        model = jd.PINNED_MODEL
        requests = 0
        input_tokens = 0

        def __init__(self, api_key, **kw):
            assert api_key == KEY

        def ask(self, state, qs):
            sent.append(state)
            self.requests += 1
            lost = "EMPTY" in state["whiteboard"]
            return {tid: (0.95 if lost else 0.05) for tid in qs}

    monkeypatch.setattr(jd, "JevClient", Client)
    out = tmp_path / "report.json"
    argv = ["--home", str(home), "--out", str(out)]
    assert proof_runs.main(argv) == 0
    report = json.loads(out.read_text())
    assert "judged" not in report and report["n_runs"] == 2
    assert report["exact"]["not_verified"]["workers_empty_result"] == 1
    assert report["exact"]["verified"]["worker_calls_at_cap_without_answer"] == 0
    assert "1 of 2 workers returned nothing" in capsys.readouterr().out
    judged = argv + ["--key-file", str(key), "--cache", str(tmp_path / "t.jsonl")]
    assert proof_runs.main(judged + ["--dry-run"]) == 0 and sent == []
    assert proof_runs.main(judged) == 0 and len(sent) == 2
    report = json.loads(out.read_text())
    assert report["judged"]["n_read"] == 2 and KEY not in out.read_text()
    assert proof_runs.main(judged) == 0 and len(sent) == 2  # cached
