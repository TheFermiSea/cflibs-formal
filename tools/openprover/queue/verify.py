#!/usr/bin/env python3
"""Independent re-verification of a Worker proof against its audited statement file.

A Worker's `proved` is a self-report (AGENTS.md: trust nothing self-reported). A candidate
passes only if ALL hold:
  1. no `sorry`/`admit`/`native_decide`/`axiom`/`implemented_by`/`extern`/`unsafe`/kernel-skip
     options in the candidate (comments stripped first);
  2. its imports are a subset of the audited file's (a new import could bring the answer in);
  3. every definition in the audited file appears verbatim (whitespace-normalised) in the
     candidate, and the target theorem's signature is textually identical;
  4. the target theorem's fully elaborated type (`#check @thm` under `pp.all`) is identical in
     the candidate and in the audited file, which also catches shadowed or redefined names;
  5. the candidate compiles with `lake env lean` without errors or `sorry` warnings, and
     `#print axioms` reports a subset of {propext, Classical.choice, Quot.sound}.

usage: verify.py <candidate.lean> <audited.lean> <fully.qualified.theorem> <lean-project-dir>
prints a JSON verdict; exit 0 iff it passed.
"""
import json
import re
import subprocess
import sys
import tempfile
from pathlib import Path

STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
FORBIDDEN = [r"\bsorry\b", r"\badmit\b", r"\bnative_decide\b", r"^\s*(private\s+)?axiom\b",
             r"implemented_by", r"@\[\s*extern", r"\bunsafe\b", r"skipKernelTC",
             r"debug\.skip", r"\bdecide\s*:=\s*true"]


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


def run_lean(src: str, project: Path, timeout: int = 900) -> tuple[int, str]:
    with tempfile.NamedTemporaryFile("w", suffix=".lean", dir=project, delete=False) as f:
        f.write(src)
        path = Path(f.name)
    try:
        p = subprocess.run(["lake", "env", "lean", str(path)], cwd=project, capture_output=True,
                           text=True, timeout=timeout)
        return p.returncode, (p.stdout + p.stderr).replace(str(path), "<file>")
    except subprocess.TimeoutExpired:
        return 124, "timeout"
    finally:
        path.unlink(missing_ok=True)


def elaborated_type(src: str, thm: str, project: Path) -> tuple[int, str]:
    probe = src + f'\n\n#eval IO.println "<<<TYPE"\nset_option pp.all true in\n#check @{thm}\n#eval IO.println "TYPE>>>"\n'
    rc, out = run_lean(probe, project)
    m = re.search(r"<<<TYPE\n(.*?)TYPE>>>", out, re.S)
    return rc, (norm(re.sub(r"^<file>:\d+:\d+: info:\s*", "", m.group(1), flags=re.M)) if m else "")


def verify(cand_path: Path, audited_path: Path, thm: str, project: Path) -> dict:
    short = thm.split(".")[-1]
    cand_raw, aud_raw = cand_path.read_text(), audited_path.read_text()
    cand, aud = strip_comments(cand_raw), strip_comments(aud_raw)
    v = {"candidate": str(cand_path), "theorem": thm, "passed": False, "checks": {}}
    c = v["checks"]
    c["forbidden"] = [p for p in FORBIDDEN if re.search(p, cand, re.M)]
    c["extra_imports"] = sorted(set(imports(cand)) - set(imports(aud)))
    c["missing_defs"] = [d[:120] for d in defs(aud) if d not in set(defs(cand))]
    sa, sc = signature(aud, short), signature(cand, short)
    c["signature_identical"] = sa is not None and sa == sc
    if c["forbidden"] or c["extra_imports"] or c["missing_defs"] or not c["signature_identical"]:
        return v
    rc, out = run_lean(cand_raw + f"\n\n#print axioms {thm}\n", project)
    c["compile_rc"] = rc
    c["errors"] = [l for l in out.splitlines() if ": error" in l][:5]
    c["sorry_warning"] = "declaration uses 'sorry'" in out
    m = re.search(rf"'{re.escape(thm)}' depends on axioms: \[(.*?)\]", out, re.S)
    ax = {a.strip() for a in m.group(1).split(",")} if m else None
    if m is None and f"'{thm}' does not depend on any axioms" in out:
        ax = set()
    c["axioms"] = sorted(ax) if ax is not None else None
    if rc != 0 or c["errors"] or c["sorry_warning"] or ax is None or not ax <= STANDARD_AXIOMS:
        return v
    _, ta = elaborated_type(aud_raw, thm, project)
    _, tc = elaborated_type(cand_raw, thm, project)
    c["elaborated_type_identical"] = bool(ta) and ta == tc
    v["passed"] = c["elaborated_type_identical"]
    return v


if __name__ == "__main__":
    if len(sys.argv) != 5:
        sys.exit(__doc__)
    verdict = verify(Path(sys.argv[1]), Path(sys.argv[2]), sys.argv[3], Path(sys.argv[4]))
    print(json.dumps(verdict, indent=2))
    sys.exit(0 if verdict["passed"] else 1)
