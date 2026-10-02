"""Run the line-extraction metamorphic fixtures against a kernel (default: the trapezoid seed).

    python3 check_fixtures.py [fixtures.json] [--kernel package.module:function]

Exit 0 iff every case holds. A candidate kernel is any callable with the contract
extract_line(wavelength, intensity, peak_idx, half_width_px, wl_step) -> (area, sigma) | None.
"""

import argparse
import importlib
import json
import math
import sys
from pathlib import Path

import numpy as np

from reference import extract_line as seed


def load_kernel(spec):
    if spec is None:
        return seed
    mod, _, fn = spec.partition(":")
    return getattr(importlib.import_module(mod), fn)


def check(doc, kernel):
    wl = np.array(doc["wavelength"])
    spectra = {k: np.array(v) for k, v in doc["spectra"].items()}

    def run(side):
        out = kernel(wl, spectra[side["spectrum"]], side["peak_idx"], side["half_width_px"],
                     side["wl_step"])
        return None if out is None else (float(out[0]), float(out[1]))

    results = []
    for c in doc["cases"]:
        a0, a1 = run(c["base"]), run(c["transformed"])
        rel = c["relation"]
        ok, why = True, ""
        if c.get("sigma_only"):
            if a1 is None:
                ok, why = bool(c.get("may_refuse")), "kernel refused"
            else:
                ok = math.isfinite(a1[1]) and a1[1] > 0.0 and math.isfinite(a1[0])
                why = f"sigma={a1[1]}"
        elif a0 is None or a1 is None:
            ok, why = False, f"kernel refused (base={a0}, transformed={a1})"
        elif rel.startswith("sigma_t >="):
            ok = a1[1] >= a0[1] * (1.0 - c["rtol"])
            why = f"sigma {a0[1]} -> {a1[1]}"
        elif rel.startswith("area_t == k"):
            ok = math.isclose(a1[0], c["k"] * a0[0], rel_tol=c["rtol"])
            why = f"{a1[0]} vs {c['k'] * a0[0]}"
        elif rel.startswith("area(f+g)"):
            g = run({**c["base"], "spectrum": c["addend"]["spectrum"]})
            ok = g is not None and math.isclose(a1[0], a0[0] + g[0], rel_tol=c["rtol"])
            why = f"{a1[0]} vs {a0[0]} + {None if g is None else g[0]}"
        elif rel.startswith("area_t - area_0 =="):
            want, diff = c["c"] * c["window_width_nm"], a1[0] - a0[0]
            tol = c["atol"] + c["rtol"] * abs(a0[0])
            mode = "raw" if abs(diff - want) <= tol else "invariant" if abs(diff) <= tol else None
            ok = mode is not None
            why = f"shift {diff} (raw would be {want}, invariant 0) -> {mode}"
        elif rel.startswith("|area_t"):
            ok = abs(a1[0] - a0[0]) <= c["bound"] + c["atol"]
            why = f"|diff|={abs(a1[0] - a0[0]):.6g} <= {c['bound']:.6g}"
        elif rel == "area_t == area_0":
            ok = abs(a1[0] - a0[0]) <= c["atol"] + c["rtol"] * abs(a0[0])
            why = f"{a0[0]} vs {a1[0]}"
        else:
            ok, why = False, f"unknown relation {rel!r}"
        results.append((c["id"], bool(ok), why))
    return results


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("fixtures", nargs="?", default=str(Path(__file__).with_name("fixtures.json")))
    ap.add_argument("--kernel")
    args = ap.parse_args(argv)
    doc = json.loads(Path(args.fixtures).read_text())
    results = check(doc, load_kernel(args.kernel))
    for cid, ok, why in results:
        print(("PASS " if ok else "FAIL ") + cid + "  " + why)
    bad = [r for r in results if not r[1]]
    print(f"{len(results) - len(bad)}/{len(results)} relations hold")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
