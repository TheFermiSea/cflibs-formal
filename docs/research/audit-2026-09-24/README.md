# Deep audit, 2026-09-24

A 15-agent audit of cflibs-formal `main` at `fb1681d`, run from the development-spec session. It
compares the repo with CF-LIBS-improved (including that project's own 104-finding overhaul review,
branch `overhaul/2026-09`) and with the literature, then proposes refactors and frontier theorems.
Every proposal was checked by an adversarial verifier.

- `REPORT.md`: the synthesis. Executive summary, health by area, the defect and refactor table
  (RF-01…30, P0 first), the spec-pipeline contract per overhaul workstream, the frontier slate
  (FT-01…20) with Lean sketches and decompositions, sequencing, and an appendix of refuted
  sub-claims.
- `audits.json`: the nine auditors' findings (PS, LF, INV, U, ARCH, G, SPC, LIT, FM prefixes) and
  frontier ideas.
- `frontier.json` and `refactor.json`: the two proposal slates with the verifiers' verdicts
  (keep / revise, with revisions). Nothing was killed outright.
- `evidence/`: the scripts, scratch Lean files and outputs the agents ran. Paths in the JSON and
  the report point here. Scratch Lean files are evidence, not library code, and are not built.

Status of the two findings about the audit session's own tooling: RF-07 (the proof-queue verifier
accepted forged proofs) is fixed in `tools/openprover/queue/verify.py` with a falsification suite.
RF-10 (the M4 acceptance document) is re-issued as v2 in `docs/integration/m4-population-context.md`.
The other items are proposals for the owner.
