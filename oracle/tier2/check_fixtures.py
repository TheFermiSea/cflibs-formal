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
        elif kind == "t_identifiable_total":
            tot = P.t_rel_total(i["E_eV"], i["sigma"], i["T_hat_K"], i["delta_sys"])
            ok = (
                close(tot, e["rel_T_total"], c["rtol"])
                and bool(P.t_identifiable_total(i["E_eV"], i["sigma"], i["T_hat_K"],
                                                i["delta_sys"], i["tau"])) == e["identifiable"]
                and tot >= i["delta_sys"] * (1.0 - 1e-12)  # the systematic floor
            )
        elif kind == "comb_recall_conditioned":
            inf = P.informative_lines(i["R"], i["I"], i["floor"])
            rec = P.comb_recall_conditioned(i["R"], i["I"], i["detected"], i["floor"],
                                            i["min_informative"])
            # LineEvidence.conditionedRecall_ge / _le_one: the informative detections score at
            # least as high over the informative lines as over the whole comb, and at most 1.
            # There is no bound against the naive recall that counts non-informative detections.
            naive_inf = len(set(inf) & set(i["detected"])) / len(i["R"])
            ok = (inf == e["informative"] and close(rec, e["recall"], 1e-12)
                  and close(naive_inf, e["naive_recall_informative"], 1e-12)
                  and (rec is None or naive_inf - 1e-12 <= rec <= 1.0 + 1e-12))
        elif kind == "line_is_evidence":
            ok = bool(P.line_is_evidence(i["R"], i["I"], i["floor"])) == e["evidence"]
        elif kind == "shift_applicable":
            ok = (bool(P.shift_at_boundary(i["shift"], i["lo"], i["hi"], i["eps"])) == e["at_boundary"]
                  and bool(P.shift_applicable(i["shift"], i["lo"], i["hi"], i["eps"])) == e["applicable"])
        elif kind == "shared_level_consistent":
            # SharedUpperLevel: recompute every ordinate and every pair verdict through the
            # candidate. A correct triplet must agree; a wrong weight opens a gap of ln 3.
            ys = [P.boltzmann_ordinate(i["intensity"][k], i["g"][k], i["A"][k])
                  for k in range(len(i["g"]))]
            verdicts = [bool(P.shared_level_consistent(ys[j], ys[k], i["eps"], i["eps"]))
                        for j, k in i["pairs"]]
            gap = max(abs(ys[j] - ys[k]) for j, k in i["pairs"])
            det = bool(P.shared_level_detects(1.0 / 3.0, i["eps"], i["eps"]))
            ok = (len(ys) == len(e["ordinates"])  # zip would silently truncate a short list
                  and all(close(a, b, 1e-12) for a, b in zip(ys, e["ordinates"]))
                  and verdicts == e["consistent"] and abs(gap - e["max_gap"]) <= 1e-9
                  and det == e["ln3_detectable"]
                  # the sufficient threshold must not over-promise: detectable => some pair fails
                  and (not det or len(set(i["g"])) == 1 or not all(verdicts)))
        elif kind == "shared_level_wavelength":
            n = len(i["g"])
            ys = [P.boltzmann_ordinate(i["intensity"][k], i["g"][k], i["A"][k], i["lam"][k])
                  for k in range(n)]
            ys0 = [P.boltzmann_ordinate(i["intensity"][k], i["g"][k], i["A"][k]) for k in range(n)]
            cons = all(P.shared_level_consistent(ys[j], ys[k], i["eps"], i["eps"])
                       for j in range(n) for k in range(j + 1, n))
            ok = (len(ys) == len(e["ordinates"])
                  and all(close(a, b, 1e-12) for a, b in zip(ys, e["ordinates"]))
                  and cons == e["consistent_with_lam"]
                  and abs(abs(ys0[0] - ys0[-1]) - e["gap_without_lam"]) <= 1e-9)
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
