"""Check the Tier-2 fixtures against the reference predicates (or a candidate module).

    python3 check_fixtures.py [fixtures.json] [--module package.module]

A candidate module must expose the same function names as predicates.py. Exit 0 iff all agree.
"""

import argparse
import importlib
import json
import math
import sys
from pathlib import Path

import numpy as np

import predicates as ref


def close(a, b, rtol):
    if a is None or b is None:
        return a is b
    return math.isclose(a, b, rel_tol=rtol, abs_tol=0.0)


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("fixtures", nargs="?", default=str(Path(__file__).with_name("fixtures.json")))
    ap.add_argument("--module")
    args = ap.parse_args(argv)
    P = importlib.import_module(args.module) if args.module else ref
    doc = json.loads(Path(args.fixtures).read_text())
    bad = 0
    for c in doc["cases"]:
        i, e, kind = c["inputs"], c["expected"], c["predicate"]
        if kind == "t_identifiable":
            got = {
                "energy_spread": P.energy_spread(i["E_eV"]),
                "identifiable": bool(P.t_identifiable(i["E_eV"], i["eps"], i["T_hat_K"], i["tau"])),
            }
            kap = P.condition_number(i["E_eV"])
            bnd = P.t_rel_error_bound(i["E_eV"], i["eps"], i["T_hat_K"])
            ok = (
                close(got["energy_spread"], e["energy_spread"], c["rtol"])
                and got["identifiable"] == e["identifiable"]
                and close(None if math.isinf(kap) else kap, e["condition_number"], c["rtol"])
                and close(None if math.isinf(bnd) else bnd, e["rel_T_bound"], c["rtol"])
            )
        elif kind == "t_identifiable_fisher":
            ss = P.slope_sigma(i["E_eV"], i["sigma"])
            r = P.t_rel_sigma(i["E_eV"], i["sigma"], i["T_hat_K"])
            ok = (
                close(None if math.isinf(ss) else ss, e["slope_sigma"], c["rtol"])
                and close(None if math.isinf(r) else r, e["rel_T_sigma"], c["rtol"])
                and bool(P.t_identifiable_fisher(i["E_eV"], i["sigma"], i["T_hat_K"], i["tau"]))
                == e["identifiable"]
            )
        elif kind == "kappa_vs_fisher_witness":
            kb = [P.t_rel_error_bound(E, i["eps"], i["T_hat_K"]) for E in (i["E_mid_eV"], i["E_wide_eV"])]
            fs = [P.t_rel_sigma(E, i["sigma"], i["T_hat_K"]) for E in (i["E_mid_eV"], i["E_wide_eV"])]
            ok = (kb[0] < kb[1]) == e["kappa_prefers_mid"] and (fs[1] < fs[0]) == e["fisher_prefers_wide"]
            ok = ok and e["kappa_prefers_mid"] and e["fisher_prefers_wide"]
        elif kind == "t_rel_error_bound_holds":
            # recompute the adversarial OLS refit and the candidate's bound from the inputs
            E = np.array(i["E_eV"])
            y = E / (ref.KB_EV_PER_K * i["T_true_K"])
            y_hat = y + i["eps"] * np.sign(E - E.mean())
            beta_hat = float(np.sum((E - E.mean()) * (y_hat - y_hat.mean())) / ref.energy_spread(E))
            t_hat = 1.0 / (ref.KB_EV_PER_K * beta_hat)
            realized = abs(t_hat - i["T_true_K"]) / i["T_true_K"]
            bound = P.t_rel_error_bound(i["E_eV"], i["eps"], t_hat)
            ok = realized <= bound and close(bound, e["bound_at_T_hat"], 1e-9)
        elif kind == "mcwhirter_ok":
            ok = bool(P.mcwhirter_ok(i["T_K"], i["dE_eV"], i["ne_cm3"])) == e["ok"]
        elif kind == "stark_opacity_lte_cert":
            got = bool(
                P.stark_opacity_lte_cert(i["T_K"], i["dE_eV"], i["w"], i["nRef"], i["width_meas"], i["k_opac"])
            )
            ok = got == e["ok"]
            if "stark_density" in e:
                ne = P.stark_density(i["w"], i["nRef"], i["width_meas"])
                raw = bool(P.mcwhirter_ok(i["T_K"], i["dE_eV"], ne))
                ok = ok and close(ne, e["stark_density"], 1e-12) and raw == e["raw_mcwhirter_ok"]
                ok = ok and (not got or raw)  # the tightening implication: cert => raw McWhirter
        else:
            ok = False
        bad += not ok
        print(("PASS " if ok else "FAIL ") + c["id"])
    print(f"{len(doc['cases']) - bad}/{len(doc['cases'])} cases agree")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
