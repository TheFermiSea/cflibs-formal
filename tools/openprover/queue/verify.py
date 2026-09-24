#!/usr/bin/env python3
"""Independent re-verification of a Worker proof against its audited statement file.

A Worker's `proved` is a self-report (AGENTS.md: trust nothing self-reported). A candidate
passes only if ALL hold:
  1. no escape hatch or metaprogramming in the candidate text (comments stripped first):
     `sorry`/`admit`/`sorryAx`/`native_decide`/`axiom`/`implemented_by`/`extern`/`unsafe`,
     kernel-skip options, any `#` command (`#eval`, `#print`, `#check`, ...), `run_cmd`/`run_elab`/
     `run_meta`, `elab`/`macro`/`syntax` definitions, `initialize`, `addDecl`/`doCheck`/
     `Environment`, and any `set_option` other than heartbeat/recursion limits;
  2. its imports are a subset of the audited file's (a new import could bring the answer in);
  3. every definition in the audited file appears verbatim (whitespace-normalised) in the
     candidate, and the target theorem's signature is textually identical;
  4. the candidate compiles as its own module (`lean -o`), and `leanchecker` replays every one of
     its declarations through the kernel (this is what rejects declarations added with
     `doCheck := false`, which would otherwise report no axioms at all);
  5. a probe file written HERE, importing the compiled candidate, reports the theorem's axioms as a
     subset of {propext, Classical.choice, Quot.sound} and a fully elaborated type (`pp.all`)
     identical to the one a second probe reads from the compiled audited statement. Probe output
     is read only between per-run random markers, so nothing the candidate prints can stand in
     for it (the candidate's own commands do not run when it is imported).

Falsified 2026-09-24 against three forged proofs of `(2:ℕ)+2=5` from the deep audit (RF-07):
`addDeclCore (doCheck := false)`, `sorryAx` plus a printed fake axioms line, and printed fake
type markers; all three fail, and the three C3 proofs and F02 still pass.

usage: verify.py <candidate.lean> <audited.lean> <fully.qualified.theorem> <lean-project-dir>
prints a JSON verdict; exit 0 iff it passed.
"""
import json
import os
import re
import secrets
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
ALLOWED_OPTIONS = {"maxHeartbeats", "maxRecDepth", "synthInstance.maxHeartbeats"}
FORBIDDEN = [r"\bsorry\b", r"\badmit\b", r"\bsorryAx\b", r"\bnative_decide\b",
             r"^\s*(private\s+|protected\s+)?axiom\b", r"implemented_by", r"@\[\s*extern",
             r"\bunsafe\b", r"skipKernelTC", r"debug\.skip", r"\bdecide\s*:=\s*true",
             # `#` commands (not Mathlib's `#s` cardinality notation, which a proof may use)
             r"#(eval|print|check|reduce|exit|guard_msgs|guard|synth|help|lint|time|where|simp"
             r"|norm_num|conv|find|with_exporting|html|widget|explode)\b",
             r"\brun_cmd\b", r"\brun_elab\b", r"\brun_meta\b", r"\belab\b", r"\belab_rules\b",
             r"\bmacro\b", r"\bmacro_rules\b", r"\bsyntax\b", r"\binitialize\b",
             r"\bbuiltin_initialize\b", r"\baddDecl\w*\b", r"\bdoCheck\b", r"\bEnvironment\b",
             r"\bofReduceBool\b", r"\btrustCompiler\b", r"@\[\s*csimp"]


def strip_comments(s: str) -> str:
    s = re.sub(r"/-.*?-/", "", s, flags=re.S)
    return re.sub(r"--[^\n]*", "", s)


def norm(t: str) -> str:
    return " ".join(t.split())


def imports(s: str) -> list[str]:
    return re.findall(r"^import\s+(\S+)", s, re.M)


def defs(s: str) -> list[str]:
    pat = r"((?:noncomputable\s+)?(?:def|abbrev|structure|inductive|class)\s.*?)(?=\n\s*\n|\ntheorem|\nlemma|\n/--|\Z)"
    return [norm(d) for d in re.findall(pat, s, re.S)]


def signature(s: str, short: str) -> str | None:
    m = re.search(rf"(theorem\s+{re.escape(short)}\b.*?):=", s, re.S)
    return norm(m.group(1)) if m else None


def bad_options(s: str) -> list[str]:
    return [o for o in re.findall(r"set_option\s+([\w.]+)", s) if o not in ALLOWED_OPTIONS]


class Toolchain:
    """`lean`/`leanchecker` from the project's toolchain, with the project's LEAN_PATH."""

    def __init__(self, project: Path):
        def lake_env(*cmd: str) -> str:
            return subprocess.run(["lake", "env", *cmd], cwd=project, capture_output=True,
                                  text=True, check=True).stdout.strip()
        self.project = project
        self.lean_path = lake_env("printenv", "LEAN_PATH")
        self.lean = lake_env("which", "lean")
        self.leanchecker = lake_env("which", "leanchecker")

    def run(self, cmd: list[str], extra: Path, timeout: int = 1200) -> tuple[int, str]:
        env = {**os.environ, "LEAN_PATH": f"{self.lean_path}:{extra}", "LEAN_NUM_THREADS": "1"}
        try:
            p = subprocess.run(cmd, cwd=self.project, env=env, capture_output=True, text=True,
                               timeout=timeout)
            return p.returncode, (p.stdout + p.stderr).replace(str(extra), "<tmp>")
        except subprocess.TimeoutExpired:
            return 124, "timeout"

    def compile(self, src: str, mod: str, root: Path) -> tuple[int, str]:
        f = root / f"{mod}.lean"
        f.write_text(src)
        return self.run([self.lean, "-R", str(root), "-o", str(root / f"{mod}.olean"), str(f)], root)

    def probe(self, mod: str, thm: str, root: Path) -> dict:
        """Axioms and pp.all type of `thm` read from a trusted file that imports `mod`."""
        tag = secrets.token_hex(12)
        src = (f"import {mod}\n#eval IO.println \"{tag}:TYPE\"\nset_option pp.all true in\n"
               f"#check @{thm}\n#eval IO.println \"{tag}:AXIOMS\"\n#print axioms {thm}\n"
               f"#eval IO.println \"{tag}:END\"\n")
        rc, out = self.compile(src, f"Probe{tag}", root)
        m = re.search(rf"{tag}:TYPE\n(.*?){tag}:AXIOMS\n(.*?){tag}:END", out, re.S)
        if rc != 0 or not m:
            return {"rc": rc, "type": None, "axioms": None, "out": out[-800:]}
        ty = norm(re.sub(r"^<tmp>/\S+:\d+:\d+: info:\s*", "", m.group(1), flags=re.M))
        ax_txt = m.group(2)
        am = re.search(rf"'{re.escape(thm)}' depends on axioms: \[(.*?)\]", ax_txt, re.S)
        if am:
            ax = sorted(a.strip() for a in am.group(1).split(",") if a.strip())
        elif f"'{thm}' does not depend on any axioms" in ax_txt:
            ax = []
        else:
            ax = None
        return {"rc": rc, "type": ty, "axioms": ax}


def verify(cand_path: Path, audited_path: Path, thm: str, project: Path) -> dict:
    short = thm.split(".")[-1]
    cand_raw, aud_raw = cand_path.read_text(), audited_path.read_text()
    cand, aud = strip_comments(cand_raw), strip_comments(aud_raw)
    v = {"candidate": str(cand_path), "theorem": thm, "passed": False, "checks": {}}
    c = v["checks"]
    c["forbidden"] = [p for p in FORBIDDEN if re.search(p, cand, re.M)] + \
        [f"set_option {o}" for o in bad_options(cand)]
    c["extra_imports"] = sorted(set(imports(cand)) - set(imports(aud)))
    c["missing_defs"] = [d[:120] for d in defs(aud) if d not in set(defs(cand))]
    sa, sc = signature(aud, short), signature(cand, short)
    c["signature_identical"] = sa is not None and sa == sc
    if c["forbidden"] or c["extra_imports"] or c["missing_defs"] or not c["signature_identical"]:
        return v
    tc = Toolchain(project)
    root = Path(tempfile.mkdtemp(prefix="verify-"))
    try:
        nonce = secrets.token_hex(6)
        cmod, smod = f"Cand{nonce}", f"Stmt{nonce}"
        rc, out = tc.compile(cand_raw, cmod, root)
        c["compile_rc"] = rc
        c["errors"] = [l for l in out.splitlines() if ": error" in l][:5]
        c["sorry_warning"] = "declaration uses 'sorry'" in out
        if rc != 0 or c["errors"] or c["sorry_warning"]:
            return v
        rc, out = tc.run([tc.leanchecker, cmod], root)
        c["kernel_replay_rc"] = rc
        if rc != 0:
            c["kernel_replay_out"] = out[-600:]
            return v
        pc = tc.probe(cmod, thm, root)
        c["axioms"] = pc["axioms"]
        if pc["axioms"] is None or not set(pc["axioms"]) <= STANDARD_AXIOMS:
            c["probe_out"] = pc.get("out", "")
            return v
        rc, out = tc.compile(aud_raw, smod, root)  # the audited file: one sorry, by design
        ps = tc.probe(smod, thm, root)
        c["elaborated_type_identical"] = bool(ps["type"]) and ps["type"] == pc["type"]
        v["passed"] = c["elaborated_type_identical"]
        return v
    finally:
        shutil.rmtree(root, ignore_errors=True)


if __name__ == "__main__":
    if len(sys.argv) != 5:
        sys.exit(__doc__)
    verdict = verify(Path(sys.argv[1]), Path(sys.argv[2]), sys.argv[3], Path(sys.argv[4]))
    print(json.dumps(verdict, indent=2))
    sys.exit(0 if verdict["passed"] else 1)
