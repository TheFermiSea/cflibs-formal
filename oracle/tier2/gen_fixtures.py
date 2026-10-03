"""Generate fixtures.json for the Tier-2 predicates. `python3 gen_fixtures.py > fixtures.json`."""

import json

import numpy as np

import predicates as P

cases = []


def add(cid, predicate, lean, inputs, expected, **kw):
    cases.append({"id": cid, "predicate": predicate, "lean": lean, "inputs": inputs,
                  "expected": expected, **kw})  # fmt: skip


# --- T-identifiability from the energies of the lines that entered the fit ------------------
# STYLIZED upper-level energy sets (eV), not NIST data: `wide` spans ~5 eV, `narrow` ~1 eV
# (the regime of the NIST Al window, whose Al I upper levels span about 1 eV), `degenerate` is flat.
E_SETS = {
    "wide": [2.5, 3.2, 4.1, 4.9, 5.6, 6.3, 7.0, 7.8],
    "narrow": [3.14, 3.14, 3.60, 4.02, 4.09, 3.95],
    "degenerate": [4.0, 4.0, 4.0, 4.0],
}
EPS, T_HAT, TAU = 0.05, 10000.0, 0.2
for name, E, eps in [("wide", E_SETS["wide"], 0.05), ("narrow", E_SETS["narrow"], 0.05),
                     ("narrow_noisy", E_SETS["narrow"], 0.15), ("wide_noisy", E_SETS["wide"], 0.15),
                     ("degenerate", E_SETS["degenerate"], 0.05)]:
    ss, kap = P.energy_spread(E), P.condition_number(E)
    bound = P.t_rel_error_bound(E, eps, T_HAT)
    add(f"t_ident_{name}", "t_identifiable", "temp_rel_error_le_sqrt_conditionNumber",
        {"E_eV": E, "eps": eps, "T_hat_K": T_HAT, "tau": TAU},
        {"energy_spread": ss, "condition_number": None if kap == float("inf") else kap,
         "rel_T_bound": None if bound == float("inf") else bound,
         "identifiable": P.t_identifiable(E, eps, T_HAT, TAU)},
        rtol=1e-12)  # fmt: skip

# Fisher/OLS-variance gate (preferred): first-order 1-sigma relative T error, monotone in spread.
SIGMA, TAU1 = 0.05, 0.03
for name in ("wide", "narrow", "degenerate"):
    E = E_SETS[name]
    r = P.t_rel_sigma(E, SIGMA, T_HAT)
    add(f"t_fisher_{name}", "t_identifiable_fisher", "crlb_slope",
        {"E_eV": E, "sigma": SIGMA, "T_hat_K": T_HAT, "tau": TAU1},
        {"slope_sigma": None if P.slope_sigma(E, SIGMA) == float("inf") else P.slope_sigma(E, SIGMA),
         "rel_T_sigma": None if r == float("inf") else r,
         "identifiable": P.t_identifiable_fisher(E, SIGMA, T_HAT, TAU1)}, rtol=1e-12)  # fmt: skip
# Statistical + systematic term. delta_sys is a per-(kernel, instrument) INPUT. The values below
# are ILLUSTRATIVE signed-median T biases measured on synthetic oracles with a flank-baselined,
# 2.5 x FWHM kernel (steel, brass, FeCo, NIST Al, ChemCam, SuperCam, CSA); they are not constants.
DELTA_SYS = {"steel": 0.055, "brass": 0.097, "FeCo": 0.019, "NIST_Al": 0.0, "ChemCam": 0.165,
             "SuperCam": 0.158, "CSA": 0.030}
TAU_TOT = 0.1
for ds, dsys in DELTA_SYS.items():
    for name in ("wide", "narrow"):
        E = E_SETS[name]
        tot = P.t_rel_total(E, SIGMA, T_HAT, dsys)
        add(f"t_total_{ds}_{name}", "t_identifiable_total", "crlb_slope",
            {"E_eV": E, "sigma": SIGMA, "T_hat_K": T_HAT, "delta_sys": dsys, "tau": TAU_TOT},
            {"rel_T_total": tot, "identifiable": P.t_identifiable_total(E, SIGMA, T_HAT, dsys, TAU_TOT)},
            rtol=1e-12, note="delta_sys illustrative")  # fmt: skip
# delta_sys above tau: even an enormous energy spread cannot pass (the total is >= delta_sys).
E_huge = [0.0, 10.0, 20.0, 30.0, 40.0, 50.0, 60.0, 70.0]
add("t_total_systematic_floor", "t_identifiable_total", "crlb_slope",
    {"E_eV": E_huge, "sigma": SIGMA, "T_hat_K": T_HAT, "delta_sys": 0.165, "tau": TAU_TOT},
    {"rel_T_total": P.t_rel_total(E_huge, SIGMA, T_HAT, 0.165),
     "identifiable": P.t_identifiable_total(E_huge, SIGMA, T_HAT, 0.165, TAU_TOT)},
    rtol=1e-12, note="the Fisher gate alone WOULD pass this set")  # fmt: skip
assert P.t_identifiable_fisher(E_huge, SIGMA, T_HAT, TAU_TOT)

# WITNESS that the raw-kappa bound is not monotone in spread (ConditionNumber honest limitations):
# once SS_E > n, kappa = SS_E / n GROWS with spread, so a wider line set gets a WORSE kappa bound
# while its Fisher sigma is better. Use the Fisher gate to rank/select; kappa only as a ceiling.
E_mid = [4.0 + 0.4364357804719848 * (k - 3.5) for k in range(8)]  # SS_E = 8 = n  => kappa = 1
assert abs(P.energy_spread(E_mid) - 8.0) < 1e-9
kb_mid, kb_wide = (P.t_rel_error_bound(E, EPS, T_HAT) for E in (E_mid, E_SETS["wide"]))
fs_mid, fs_wide = (P.t_rel_sigma(E, SIGMA, T_HAT) for E in (E_mid, E_SETS["wide"]))
add("kappa_not_monotone_in_spread", "kappa_vs_fisher_witness", "conditionNumber_disagrees_with_dOptimality",
    {"E_mid_eV": E_mid, "E_wide_eV": E_SETS["wide"], "eps": EPS, "sigma": SIGMA, "T_hat_K": T_HAT},
    {"kappa_bound_mid": kb_mid, "kappa_bound_wide": kb_wide, "fisher_mid": fs_mid,
     "fisher_wide": fs_wide, "kappa_prefers_mid": bool(kb_mid < kb_wide),
     "fisher_prefers_wide": bool(fs_wide < fs_mid)})  # fmt: skip

# Empirical validity of the bound: an adversarial hard-eps ordinate perturbation (delta_k =
# eps * sign(E_k - mean E), the Cauchy-Schwarz-tight direction) refit by OLS must stay inside it.
for name in ("wide", "narrow"):
    E = np.array(E_SETS[name])
    T_true = 10000.0
    y = E / (P.KB_EV_PER_K * T_true)  # sign-normalized Boltzmann ordinate (alpha = 0)
    y_hat = y + EPS * np.sign(E - E.mean())
    beta_hat = float(np.sum((E - E.mean()) * (y_hat - y_hat.mean())) / P.energy_spread(E))
    t_hat = 1.0 / (P.KB_EV_PER_K * beta_hat)
    realized = abs(t_hat - T_true) / T_true
    bound = P.KB_EV_PER_K * t_hat * EPS * np.sqrt(P.condition_number(E))
    add(f"t_bound_valid_{name}", "t_rel_error_bound_holds", "temp_rel_error_le_sqrt_conditionNumber",
        {"E_eV": E_SETS[name], "eps": EPS, "T_true_K": T_true},
        {"realized_rel_T_error": realized, "bound_at_T_hat": float(bound), "holds": bool(realized <= bound)},
        note="bound is evaluated at the RECOVERED T_hat, as in the Lean statement")  # fmt: skip

# --- McWhirter (necessary, not sufficient, for LTE) ------------------------------------------
T_K = 10000.0  # sqrt(T) = 100 exactly
for de in (0.5, 1.0, 2.0):
    b = P.mcwhirter_bound(T_K, de)
    for tag, ne in (("below", b * (1 - 1e-9)), ("at", b), ("above", b * (1 + 1e-9))):
        add(f"mcwhirter_dE{de}_{tag}", "mcwhirter_ok", "mcWhirter_certificate_sound",
            {"T_K": T_K, "dE_eV": de, "ne_cm3": ne}, {"bound": b, "ok": P.mcwhirter_ok(T_K, de, ne)},
            note="NECESSARY, not sufficient, for LTE")  # fmt: skip

# --- Stark / opacity guard (the repaired gate) ------------------------------------------------
W_, NREF = 0.01, 1.0e17  # Griem width parameter (nm), reference density (cm^-3)
for width, kop, tag in ((0.2, 1.0, "k1"), (0.2, 3.0, "k3"), (0.6, 3.0, "wide")):
    ne_est = P.stark_density(W_, NREF, width)
    add(f"stark_opacity_{tag}", "stark_opacity_lte_cert", "starkOpacity_certificate_sound",
        {"T_K": T_K, "dE_eV": 2.0, "w": W_, "nRef": NREF, "width_meas": width, "k_opac": kop},
        {"stark_density": ne_est, "ok": P.stark_opacity_lte_cert(T_K, 2.0, W_, NREF, width, kop),
         "raw_mcwhirter_ok": P.mcwhirter_ok(T_K, 2.0, ne_est)},
        note="ok => raw_mcwhirter_ok (starkOpacityLteCert_imp_mcWhirterCert); the converse fails")  # fmt: skip
# the repaired gate rejects what the raw McWhirter gate accepts (bound at dE=2, T=1e4 is 1.28e15)
ne_est = P.stark_density(W_, NREF, 0.0003)
add("stark_opacity_tightens", "stark_opacity_lte_cert", "starkOpacityLteCert_imp_mcWhirterCert",
    {"T_K": T_K, "dE_eV": 2.0, "w": W_, "nRef": NREF, "width_meas": 0.0003, "k_opac": 3.0},
    {"stark_density": ne_est, "ok": P.stark_opacity_lte_cert(T_K, 2.0, W_, NREF, 0.0003, 3.0),
     "raw_mcwhirter_ok": P.mcwhirter_ok(T_K, 2.0, ne_est)})  # fmt: skip
for bad, inputs in (("w_nonpositive", (0.0, NREF, 0.2, 1.0)), ("kopac_below_1", (W_, NREF, 0.2, 0.5))):
    add(f"stark_opacity_refuses_{bad}", "stark_opacity_lte_cert", "starkOpacityLteCert",
        {"T_K": T_K, "dE_eV": 2.0, "w": inputs[0], "nRef": inputs[1], "width_meas": inputs[2],
         "k_opac": inputs[3]}, {"ok": False})  # fmt: skip

# --- Detectability conditioned on the instrument response (LineEvidence) ----------------------
# STYLIZED comb modeled on a brass element whose expected lines fall partly below a detector's
# usable band: 6 teeth in the dead band (R = 0), 4 weak teeth (R * I just under the floor) and 1
# strong visible tooth. Not measured data.
FLOOR = 1.0
R_ZN = [0.0] * 6 + [0.8] * 4 + [1.0]
I_ZN = [50.0] * 6 + [1.2] * 4 + [400.0]  # R * I = 0 x6, 0.96 x4 (< floor), 400
def _naive_inf(R, I, det):
    """|detected & informative| / |comb|: the left side of LineEvidence.conditionedRecall_ge."""
    return len(set(P.informative_lines(R, I, FLOOR)) & set(det)) / len(R)


# The last two cases detect sub-floor teeth (indices 6..9): those detections are ignored, so the
# conditioned recall is BELOW the naive recall that counts them (0 against 4/11, 1 against 5/11
# is above). A kernel that counts every detection in the numerator fails them.
for tag, det, mn in (("single_informative_line_abstains", [10], 2), ("single_line_min1", [10], 1),
                     ("nothing_detected", [], 1),
                     ("subfloor_detections_ignored", [6, 7, 8, 9], 1),
                     ("subfloor_and_strong", [6, 7, 8, 9, 10], 1)):
    rec = P.comb_recall_conditioned(R_ZN, I_ZN, det, FLOOR, mn)
    add(f"evidence_{tag}", "comb_recall_conditioned", "conditionedRecall_ge",
        {"R": R_ZN, "I": I_ZN, "detected": det, "floor": FLOOR, "min_informative": mn},
        {"informative": P.informative_lines(R_ZN, I_ZN, FLOOR), "recall": rec,
         "naive_recall": len(det) / len(R_ZN),
         "naive_recall_informative": _naive_inf(R_ZN, I_ZN, det)})  # fmt: skip
# A comb with enough informative lines and every detection informative: dead teeth deflate the
# naive recall, not the conditioned one
R_B = [0.0, 0.0, 0.0, 1.0, 1.0, 1.0, 1.0, 1.0]
I_B = [100.0] * 8
det_b = [3, 4, 5]
add("evidence_dead_teeth_deflate_naive", "comb_recall_conditioned", "conditionedRecall_ge",
    {"R": R_B, "I": I_B, "detected": det_b, "floor": FLOOR, "min_informative": 2},
    {"informative": P.informative_lines(R_B, I_B, FLOOR),
     "recall": P.comb_recall_conditioned(R_B, I_B, det_b, FLOOR, 2),
     "naive_recall": len(det_b) / len(R_B),
     "naive_recall_informative": _naive_inf(R_B, I_B, det_b)})  # fmt: skip
add("evidence_dead_band_is_not_evidence", "line_is_evidence", "not_isEvidence_of_dead",
    {"R": 0.0, "I": 1.0e9, "floor": 0.0}, {"evidence": False})

# --- A registration shift at the edge of its scan (LineEvidence.AtScanBoundary) ----------------
for tag, shift, lo, hi, eps in (("applied_at_lower_edge", -0.3, -0.3, 0.3, 0.01),
                                ("near_upper_edge", 0.29, -0.3, 0.3, 0.02),
                                ("interior", 0.0, -0.3, 0.3, 0.01),
                                ("just_inside_tolerance", -0.28, -0.3, 0.3, 0.01)):
    add(f"shift_{tag}", "shift_applicable", "atScanBoundary_of_strictMonoOn",
        {"shift": shift, "lo": lo, "hi": hi, "eps": eps},
        {"at_boundary": P.shift_at_boundary(shift, lo, hi, eps),
         "applicable": P.shift_applicable(shift, lo, hi, eps)})  # fmt: skip

doc = {
    "schema": "cflibs-tier2-predicate-fixtures-v1",
    "units": {"E": "eV", "T": "K", "n_e": "cm^-3", "dE": "eV", "kB": P.KB_EV_PER_K},
    "scope": "Predicates certify STRUCTURE (a necessary or sufficient condition inside an idealized "
    "model), not accuracy. Identifiability/conditioning belong to the answer/abstain decision and "
    "the post-solve validity gate on the SELECTED LINE SET, not to the extraction kernel.",
    "notes": [
        "kappa is the raw unit-carrying max/min of (SS_E, n) with E in eV; it is not scale-invariant.",
        "eps is a HARD per-line bound on the log-intensity ordinate error, not a standard deviation.",
        "Lean's sahaFactor is ideal Saha (REDUCED, no ionization-potential depression); the pipeline "
        "applies Debye-Hueckel IPD by default (SCI-2). No predicate here uses the Saha factor; any "
        "Saha-consistency predicate pinned later must declare its IPD treatment.",
        "McWhirter is necessary, not sufficient, for LTE (Cristoforetti et al. 2010).",
    ],
    "cases": cases,
}
print(json.dumps(doc, indent=1))
