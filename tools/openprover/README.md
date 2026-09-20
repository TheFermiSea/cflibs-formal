# OpenProver as the cflibs-formal proof Worker harness

Decision D7 (`docs/spec/README.md`); design in `docs/spec/04-autoformalization-framework.md` §10.

- Upstream: `openprover` 1.0.1 (MIT, Kripner & Straka, arXiv 2607.09217). Not vendored as source;
  installed into a scratch venv and patched by `patch_local_alias.py`.
- The patch adds one worker alias, `leanstral-local`, bound to the OpenAI-compatible llama.cpp
  endpoint on the infer-0x fleet (`/usr/local/bin/run-leanstral`, `--alias leanstral`, port 8082).
  The planner stays on the Claude CLI (the owner's subscription).

```sh
python3 -m venv /tmp/opvenv && /tmp/opvenv/bin/pip install openprover==1.0.1
/tmp/opvenv/bin/python tools/openprover/patch_local_alias.py
cd /home/brian/code/cflibs-formal
/tmp/opvenv/bin/openprover --headless --autonomous \
  --planner-model sonnet --worker-model leanstral-local \
  --provider-url http://10.0.0.27:8082/v1 \
  --lean-project . --lean-theorem <statement-only .lean file> --theorem <dossier .md> \
  --max-time 2h
```

Never point the endpoint at a global proxy or shell rc: the base URL lives only in this command /
the saved `run_config.toml` of a run (global rule: per-tool base URLs only).
Worker output is accepted only after `lake exe axiom-audit` and kernel replay (`docs/spec/05` §4).
