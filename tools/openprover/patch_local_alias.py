#!/usr/bin/env python3
"""Add a `leanstral-local` worker alias to an installed openprover==1.0.1, and make its Claude
planner client work with Claude Code CLI >= 2.1 (whose `--output-format json` returns a list of
messages ending in a `type: result` element, not a single result object) without loading the
user's global MCP servers.

OpenProver hard-codes its model aliases (cli.py) and the context-length table (llm/hf.py); the
`leanstral` alias it ships routes to Mistral's hosted API. This patch adds `leanstral-local`,
an OpenAI-compatible HFClient target served by llama.cpp on the infer-0x fleet
(docs/spec/04 §10.4). Idempotent: re-running on a patched install is a no-op.

Usage:  <venv>/bin/python tools/openprover/patch_local_alias.py
"""
import importlib, pathlib, sys

ALIAS, SERVED_NAME, CTX = "leanstral-local", "leanstral", 65536

def patch(path: pathlib.Path, pairs):
    s = path.read_text()
    if pairs[0][1] in s:
        print(f"already patched: {path}"); return
    for old, new in pairs:
        assert s.count(old) == 1, f"{path}: pattern not found or not unique: {old[:60]!r}"
        s = s.replace(old, new)
    path.write_text(s); print(f"patched: {path}")

cli = pathlib.Path(importlib.import_module("openprover.cli").__file__)
hf = pathlib.Path(importlib.import_module("openprover.llm.hf").__file__)
cl = pathlib.Path(importlib.import_module("openprover.llm.claude").__file__)
hl = pathlib.Path(importlib.import_module("openprover.tui.headless").__file__)

patch(cli, [
    ('    model_choices = ["sonnet", "opus", "minimax-m2.5", "leanstral"]',
     f'    model_choices = ["sonnet", "opus", "minimax-m2.5", "leanstral", "{ALIAS}"]'),
    ('    HF_MODEL_MAP = {\n        "minimax-m2.5": "MiniMaxAI/MiniMax-M2.5",\n    }',
     f'    HF_MODEL_MAP = {{\n        "minimax-m2.5": "MiniMaxAI/MiniMax-M2.5",\n        "{ALIAS}": "{SERVED_NAME}",  # llama-server --alias {SERVED_NAME} on the infer-0x fleet\n    }}'),
    ('    VLLM_MODELS = {"minimax-m2.5"}  # served via vLLM (standard OpenAI API)',
     f'    VLLM_MODELS = {{"minimax-m2.5", "{ALIAS}"}}  # standard OpenAI API with tool calls (vLLM or llama-server --jinja)'),
    ('    non_claude_models = {"minimax-m2.5", "leanstral"}',
     f'    non_claude_models = {{"minimax-m2.5", "leanstral", "{ALIAS}"}}'),
    ('    MODEL_DISPLAY = {"sonnet": "sonnet 4.6", "opus": "opus 4.6", "leanstral": "leanstral"}',
     f'    MODEL_DISPLAY = {{"sonnet": "sonnet 4.6", "opus": "opus 4.6", "leanstral": "leanstral", "{ALIAS}": "Leanstral 1.5 (local llama.cpp)"}}'),
])
patch(hf, [
    ('MODEL_CONTEXT_LENGTHS = {\n    "MiniMaxAI/MiniMax-M2.5": 196608,\n}',
     f'MODEL_CONTEXT_LENGTHS = {{\n    "MiniMaxAI/MiniMax-M2.5": 196608,\n    "{SERVED_NAME}": {CTX},  # Leanstral 1.5 Q6_K via llama-server -c {CTX} (run-leanstral)\n}}'),
])
patch(cl, [
    ('        try:\n            raw = json.loads(stdout)\n        except json.JSONDecodeError:',
     '        try:\n            raw = json.loads(stdout)\n            if isinstance(raw, list):  # Claude Code CLI >= 2.1: list of messages, last is the result\n                raw = next(x for x in reversed(raw) if isinstance(x, dict) and x.get("type") == "result")\n        except json.JSONDecodeError:'),
    ('        else:\n            cmd.extend(["--tools", ""])\n        if json_schema:',
     '        else:\n            cmd.extend(["--tools", "", "--strict-mcp-config", "--mcp-config", \'{"mcpServers":{}}\'])  # do not start the user\'s global MCP servers\n        if json_schema:'),
])
patch(hl, [
    ('    def cleanup(self):\n        pass\n',
     '    def cleanup(self):\n        pass\n\n    def _sync_step_log_line(self, step_idx: int):\n        pass  # prover.py calls this on spawn; 1.0.1 only implements it on the curses TUI\n'),
])
