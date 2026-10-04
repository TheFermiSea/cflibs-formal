"""Typed judgments about an artifact, tested against what an exact verifier measured.

Two loops in this project have the same shape: a language model proposes an artifact (a
proof attempt; in the companion pipeline, a numerical kernel), an exact verifier rules on it
(the Lean kernel; the Lean-twinned fixtures and the scorer), and the ruling says little about
WHY. This module reads artifacts into typed traits and measures whether a trait predicts the
ruling. It is shared by both loops, and the companion vendors this file verbatim.

* :class:`TraitSet` -- yes/no questions about one kind of artifact, each with the measured
  labels it is expected to predict, declared before any answer is seen.
* :class:`JevClient` -- one request per artifact to a System One model (TypeSafe Jev,
  ``POST /v1/systemone``): one "noul" per trait, answered as the probability of yes.
* :class:`TraitReader` -- answers cached by (trait set, version, model, text), so a report
  regenerates without asking again.
* :func:`hypotheses` -- per declared (trait, label): the AUC with a bootstrap interval.
* :func:`lessons` -- the hypotheses the data supports, as sentences with their counts.

Rules that hold for every use:

* A judgment never replaces the verifier. It describes, predicts and routes; the Lean kernel
  and the scorer stay the only things that accept a proof or score a kernel.
* A trait is trusted only as far as it has been tested against exact outcomes on the
  artifacts at hand. An untested trait is a guess with a probability attached.
* The API key is read from a file only its owner can read, never from the environment (a
  jail that runs model-written code inherits its launcher's environment), and is never
  written to a cache, a report or an error message.
* The model id is pinned. An alias moves when a release ships, and answers compared across
  runs must come from one model.

Only the standard library is used.
"""

from __future__ import annotations

import collections
import hashlib
import json
import os
import random
import stat
import time
import urllib.error
import urllib.request
from pathlib import Path
from typing import Any, Callable, Dict, List, Mapping, NamedTuple, Optional, Sequence, Tuple

PINNED_MODEL = "jev-1.13.0"
API_URL = "https://api.typesafe.ai/v1/systemone"
#: A noul inside this band is reported as uncertain, not as a yes or a no.
UNCERTAIN = (0.35, 0.65)
#: Fewer positives or negatives than this and a hypothesis is listed as not testable.
MIN_CLASS = 10


class Trait(NamedTuple):
    """One yes/no question and the measured labels it is expected to predict.

    ``predicts`` is declared with the question: ``(label, True)`` says a yes should make the
    label more likely, ``(label, False)`` less likely. ``lesson`` completes the sentence
    "Artifacts that ..." (used by :func:`lessons`; empty: the trait yields no lesson).
    """

    id: str
    question: str
    yes: str
    no: str
    predicts: Tuple[Tuple[str, bool], ...] = ()
    lesson: str = ""


class TraitSet(NamedTuple):
    """Questions about one kind of artifact. ``version`` is part of every cache key: change
    it whenever a question or its criteria change."""

    name: str
    version: str
    state_field: str
    traits: Tuple[Trait, ...]

    @property
    def ids(self) -> Tuple[str, ...]:
        return tuple(t.id for t in self.traits)

    def questions(self) -> Dict[str, Dict[str, Any]]:
        """The request's ``questions`` map: one noul per trait."""
        return {
            t.id: {
                "type": "noul",
                "instructions": t.question,
                "criteria": {"true": t.yes, "false": t.no},
            }
            for t in self.traits
        }

    def cache_key(self, model: str, text: str) -> str:
        """Identity of one reading: the questions, the model and the text that was read."""
        blob = json.dumps([self.name, self.version, model, text]).encode("utf-8")
        return hashlib.sha256(blob).hexdigest()


# --------------------------------------------------------------------------- the model
def read_key(path: str) -> str:
    """The API key from a file only its owner can read (refused otherwise)."""
    p = Path(path).expanduser()
    mode = p.stat().st_mode
    if mode & (stat.S_IRWXG | stat.S_IRWXO):
        raise PermissionError(f"{p} is readable by group or others; chmod 600 it")
    key = p.read_text().strip()
    if not key:
        raise ValueError(f"{p} is empty")
    return key


class JevError(RuntimeError):
    """A request that did not yield one valid answer per question."""


#: Rate limited (429), overloaded (529) and transient server errors are retried.
_RETRY_STATUS = frozenset({429, 500, 502, 503, 504, 529})


class JevClient:
    """``POST /v1/systemone`` with bounded retries (``opener`` and ``sleep`` are test seams)."""

    def __init__(
        self,
        api_key: str,
        *,
        model: str = PINNED_MODEL,
        url: str = API_URL,
        timeout_s: float = 60.0,
        max_attempts: int = 5,
        opener: Callable[..., Any] = urllib.request.urlopen,
        sleep: Callable[[float], None] = time.sleep,
    ) -> None:
        self._key = api_key
        self.model = model
        self.url = url
        self.timeout_s = timeout_s
        self.max_attempts = max_attempts
        self._opener = opener
        self._sleep = sleep
        self.input_tokens = 0
        self.requests = 0

    def ask(self, state: Any, qs: Mapping[str, Mapping[str, Any]]) -> Dict[str, float]:
        """The noul (probability of yes) for every question id."""
        body = json.dumps({"state": state, "model": self.model, "questions": dict(qs)})
        request = urllib.request.Request(
            self.url,
            data=body.encode("utf-8"),
            method="POST",
            headers={
                "Authorization": f"Bearer {self._key}",
                "Content-Type": "application/json",
            },
        )
        last = ""
        for attempt in range(self.max_attempts):
            try:
                with self._opener(request, timeout=self.timeout_s) as response:
                    doc = json.loads(response.read().decode("utf-8"))
                self.requests += 1
                return self._nouls(doc, qs)
            except urllib.error.HTTPError as exc:
                if exc.code not in _RETRY_STATUS:
                    raise JevError(f"HTTP {exc.code} from {self.url}") from None
                last = f"HTTP {exc.code}"
                delay = _retry_after(exc) or min(2.0**attempt, 30.0)
            except (urllib.error.URLError, TimeoutError, ConnectionError) as exc:
                last = type(exc).__name__
                delay = min(2.0**attempt, 30.0)
            if attempt + 1 < self.max_attempts:
                self._sleep(delay)
        raise JevError(f"no answer after {self.max_attempts} attempts ({last})")

    def _nouls(self, doc: Any, qs: Mapping[str, Any]) -> Dict[str, float]:
        answers = doc.get("answers") if isinstance(doc, dict) else None
        if not isinstance(answers, dict):
            raise JevError("response has no answers map")
        if not str(doc.get("model", "")).startswith(self.model):
            # the cache is keyed by the model asked for; an answer from another model (an
            # alias that moved) must not be stored under it
            raise JevError(f"answered by {doc.get('model')!r}, asked {self.model!r}")
        out: Dict[str, float] = {}
        for qid in qs:
            answer = answers.get(qid)
            value = answer.get("noul") if isinstance(answer, dict) else None
            if isinstance(value, bool) or not isinstance(value, (int, float)):
                raise JevError(f"question {qid!r}: no noul in the answer")
            if not 0.0 <= float(value) <= 1.0:
                raise JevError(f"question {qid!r}: noul {value!r} outside [0, 1]")
            out[qid] = float(value)
        usage = doc.get("usage") if isinstance(doc.get("usage"), dict) else {}
        self.input_tokens += int(usage.get("input_tokens") or 0)
        return out


def _retry_after(exc: urllib.error.HTTPError) -> Optional[float]:
    try:
        value = float(exc.headers.get("retry-after", ""))
    except (AttributeError, TypeError, ValueError):
        return None
    return min(max(value, 0.0), 120.0)


class TraitReader:
    """Model answers for an artifact's text, read once: an append-only JSONL cache keyed by
    :meth:`TraitSet.cache_key`."""

    def __init__(
        self, traits: TraitSet, client: Optional[JevClient], cache_path: Optional[str] = None
    ) -> None:
        self.traits = traits
        self.client = client
        self.cache_path = Path(cache_path) if cache_path else None
        self._cache: Dict[str, Dict[str, float]] = {}
        self.failures: List[str] = []
        if self.cache_path and self.cache_path.exists():
            for line in self.cache_path.read_text().splitlines():
                row = json.loads(line)
                self._cache[row["key"]] = {k: float(v) for k, v in row["nouls"].items()}

    @property
    def model(self) -> str:
        return self.client.model if self.client else PINNED_MODEL

    def cached(self, text: str) -> Optional[Dict[str, float]]:
        return self._cache.get(self.traits.cache_key(self.model, text))

    def read(self, text: str) -> Optional[Dict[str, float]]:
        """The nouls for ``text``; None when there is no client or the request failed (the
        failure is recorded, never raised: a missing judgment must not stop its caller)."""
        key = self.traits.cache_key(self.model, text)
        if key in self._cache:
            return self._cache[key]
        if self.client is None:
            return None
        try:
            nouls = self.client.ask({self.traits.state_field: text}, self.traits.questions())
        except JevError as exc:
            self.failures.append(str(exc))
            return None
        self._cache[key] = nouls
        if self.cache_path:
            self.cache_path.parent.mkdir(parents=True, exist_ok=True)
            row = {
                "key": key,
                "set": self.traits.name,
                "version": self.traits.version,
                "model": self.model,
                "nouls": nouls,
            }
            with self.cache_path.open("a") as fh:
                fh.write(json.dumps(row) + "\n")
                fh.flush()
                os.fsync(fh.fileno())
        return nouls


# --------------------------------------------------------------------------- the evidence
#: One artifact: its trait values (a noul, or 0/1 from a rule; None: unread) and its measured
#: labels (None: not measured).
Row = Tuple[Mapping[str, Optional[float]], Mapping[str, Optional[bool]]]


def auc(scores: Sequence[float], positive: Sequence[bool]) -> Optional[float]:
    """P(score of a positive > score of a negative), ties counted half (None: one class)."""
    pos = collections.Counter(s for s, y in zip(scores, positive) if y)
    neg = collections.Counter(s for s, y in zip(scores, positive) if not y)
    if not pos or not neg:
        return None
    below = 0
    wins = 0.0
    for value in sorted(set(pos) | set(neg)):
        wins += pos[value] * (below + 0.5 * neg[value])
        below += neg[value]
    return wins / (sum(pos.values()) * sum(neg.values()))


def auc_interval(
    scores: Sequence[float], positive: Sequence[bool], n_boot: int = 1000, seed: int = 0
) -> Optional[Tuple[float, float]]:
    """Percentile bootstrap (95%) over artifacts."""
    rng = random.Random(seed)
    n = len(scores)
    draws = []
    for _ in range(n_boot):
        ix = [rng.randrange(n) for _ in range(n)]
        value = auc([scores[i] for i in ix], [positive[i] for i in ix])
        if value is not None:
            draws.append(value)
    if len(draws) < n_boot // 2:
        return None
    draws.sort()
    return draws[int(0.025 * len(draws))], draws[int(0.975 * len(draws)) - 1]


def mark(value: Optional[float]) -> str:
    """``y`` / ``n`` for a decided trait, ``?`` for an uncertain or unread one."""
    if value is None or UNCERTAIN[0] < value < UNCERTAIN[1]:
        return "?"
    return "y" if value >= UNCERTAIN[1] else "n"


def signature(traits: TraitSet, values: Mapping[str, Optional[float]]) -> str:
    """The marks of every trait, in the set's order."""
    return "".join(mark(values.get(tid)) for tid in traits.ids)


def hypotheses(traits: TraitSet, rows: Sequence[Row]) -> List[Dict[str, Any]]:
    """One entry per declared (trait, label): does a yes move the label the declared way?

    ``auc_declared`` is oriented so that above 0.5 supports the declared direction. The
    counts are the label's rate among decided yes and decided no artifacts.
    """
    out: List[Dict[str, Any]] = []
    for trait in traits.traits:
        for label, direction in trait.predicts:
            pairs = [
                (float(v), bool(labels[label]))
                for values, labels in rows
                for v in [values.get(trait.id)]
                if v is not None and labels.get(label) is not None
            ]
            scores = [s for s, _ in pairs]
            agree = [y == direction for _, y in pairs]
            yes = [y for s, y in pairs if mark(s) == "y"]
            no = [y for s, y in pairs if mark(s) == "n"]
            entry: Dict[str, Any] = {
                "trait": trait.id,
                "label": label,
                "declared": "yes raises it" if direction else "yes lowers it",
                "n": len(pairs),
                "label_true_when_yes": [sum(yes), len(yes)],
                "label_true_when_no": [sum(no), len(no)],
                "testable": min(sum(agree), len(agree) - sum(agree)) >= MIN_CLASS,
            }
            if entry["testable"]:
                entry["auc_declared"] = auc(scores, agree)
                entry["auc_interval95"] = auc_interval(scores, agree)
            out.append(entry)
    return out


def lessons(
    traits: TraitSet,
    tested: Sequence[Mapping[str, Any]],
    label_text: Mapping[str, str],
    subject: str,
) -> List[str]:
    """Sentences for the hypotheses whose interval excludes 0.5, in either direction.

    ``tested`` is :func:`hypotheses` output; ``label_text[label]`` completes "... <verb
    phrase> in a of b"; ``subject`` is the plural noun ("Kernels"). A lesson states counts
    and nothing else: it is an association in the artifacts read, not a cause.
    """
    by_id = {t.id: t for t in traits.traits}
    out: List[str] = []
    for h in tested:
        trait = by_id[h["trait"]]
        interval = h.get("auc_interval95")
        if not h.get("testable") or not interval or not trait.lesson:
            continue
        if interval[0] <= 0.5 <= interval[1] or h["label"] not in label_text:
            continue
        (a, b), (c, d) = h["label_true_when_yes"], h["label_true_when_no"]
        if min(b, d) < MIN_CLASS:
            continue
        out.append(
            f"{subject} that {trait.lesson} {label_text[h['label']]} in {a} of {b} cases;"
            f" {subject.lower()} that do not, in {c} of {d}."
        )
    return out
