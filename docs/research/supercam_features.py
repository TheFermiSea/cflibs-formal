#!/usr/bin/env python3
"""Reduce the SuperCam LIBS lab-calibration library to a slim, AutoDiscovery-sized table.

Input : data/supercam_calib/raw/labcal/libs_spectral_library_reference.csv (two header rows:
        group in row 1 = meta | comp | wvl; name in row 2). 8,351 records = 1,193 base spectra x 7
        wavelength-shift variants of 334 standards (Anderson et al. 2022). Only shift == 0 rows are kept.
Output: one row per base spectrum with metadata, certified composition, and per-line shape features
        for a fixed list of strong lines inside the three SuperCam spectrometer ranges
        (UV 243.8-340, VIO 385-465, VNIR 536-853 nm; lines outside are skipped).
Per-line features (all instrument-calibration-free EXCEPT peak_net/area_net, which are in DN):
  cont       local continuum (median of the two side windows +-0.6..1.0 nm)
  peak_net   max in +-0.20 nm minus cont
  area_net   sum over +-0.25 nm of (I - cont) x channel width  (a proxy for the line's integral)
  fwhm_nm    full width at half of peak_net from the half-max crossings (interpolated)
  shape      area_net / (peak_net x fwhm_nm)  (1.06 Gaussian, 1.57 Lorentzian, larger when saturated/flat)
  peak_over_cont  peak_net / cont
Plus per-spectrometer integrated intensity (uv_sum, vio_sum, vnir_sum) and total_sum.
Nothing here depends on the pipeline; numpy only. Run from the companion repo root.
"""
import csv, sys, json, math
import numpy as np

SRC = sys.argv[1] if len(sys.argv) > 1 else "data/supercam_calib/raw/labcal/libs_spectral_library_reference.csv"
OUT = sys.argv[2] if len(sys.argv) > 2 else "supercam_line_features.csv"

LINES = {  # name: center nm  (NIST wavelengths in air)
    "SiI_288.16": 288.158, "SiI_251.61": 251.611, "SiI_390.55": 390.552,
    "TiII_334.94": 334.941, "TiII_336.12": 336.121, "TiII_368.52": 368.520,
    "AlI_394.40": 394.401, "AlI_396.15": 396.152, "AlI_308.22": 308.215, "AlI_309.27": 309.271,
    "FeI_404.58": 404.581, "FeI_438.35": 438.354, "FeI_371.99": 371.993, "FeI_373.71": 373.713,
    "FeII_259.94": 259.940, "FeII_275.57": 275.574,
    "MgI_285.21": 285.213, "MgII_279.55": 279.553, "MgII_280.27": 280.271,
    "CaI_422.67": 422.673, "CaI_445.48": 445.478, "CaII_393.37": 393.366, "CaII_396.85": 396.847, "CaII_317.93": 317.933,
    "NaI_589.00": 588.995, "NaI_589.59": 589.592, "NaI_819.48": 819.482,
    "KI_766.49": 766.490, "KI_769.90": 769.896,
    "HI_656.28": 656.279, "OI_777.19": 777.194, "CI_247.86": 247.856, "NI_746.83": 746.831,
    "LiI_670.78": 670.776, "SrII_407.77": 407.771, "SrII_421.55": 421.552,
    "BaII_455.40": 455.403, "BaII_493.41": 493.409,
    "MnI_403.08": 403.076, "MnI_403.31": 403.307, "CrI_425.43": 425.435,
}
RANGES = {"uv": (243.8, 340.0), "vio": (385.0, 465.0), "vnir": (536.0, 853.0)}
COMP_KEEP = ["SiO2", "TiO2", "Al2O3", "FeOT", "MnO", "MgO", "CaO", "Na2O", "K2O", "P2O5",
             "loss_on_ignition", "Sr", "Ba", "Li", "Cr", "Ni", "Zn", "Rb", "V", "Cu", "H2O+_structural", "C_total", "S"]
META_KEEP = ["file", "Target_Name", "composition_type", "geology", "location", "distance_mm", "shift", "Remove_from_all"]

def line_features(wl, I, c):
    core = (wl >= c - 0.20) & (wl <= c + 0.20)
    side = ((wl >= c - 1.0) & (wl <= c - 0.6)) | ((wl >= c + 0.6) & (wl <= c + 1.0))
    if core.sum() < 3 or side.sum() < 3:
        return None
    cont = float(np.median(I[side]))
    j = np.argmax(np.where(core, I, -np.inf))
    peak_net = float(I[j] - cont)
    band = (wl >= c - 0.25) & (wl <= c + 0.25)
    dwl = np.gradient(wl)
    area_net = float(np.sum((I[band] - cont) * dwl[band]))
    # FWHM from half-max crossings around j
    half = cont + peak_net / 2.0
    k = j
    while k > 0 and I[k] > half:
        k -= 1
    m = j
    while m < len(I) - 1 and I[m] > half:
        m += 1
    def interp(a, b):  # crossing between indices a (below) and b (above)
        if I[b] == I[a]:
            return wl[a]
        return wl[a] + (half - I[a]) * (wl[b] - wl[a]) / (I[b] - I[a])
    left = interp(k, k + 1) if k < j else wl[j]
    right = interp(m, m - 1) if m > j else wl[j]
    fwhm = float(right - left)
    shape = area_net / (peak_net * fwhm) if peak_net > 0 and fwhm > 0 else float("nan")
    return {"cont": cont, "peak_net": peak_net, "area_net": area_net, "fwhm_nm": fwhm,
            "shape": shape, "peak_over_cont": peak_net / cont if cont > 0 else float("nan")}

def main():
    with open(SRC, newline="", encoding="latin-1") as f:
        r = csv.reader(f)
        g = next(r); names = next(r)
        meta_idx = {names[i]: i for i in range(len(g)) if g[i] == "meta"}
        comp_idx = {names[i]: i for i in range(len(g)) if g[i] == "comp"}
        spec_idx = [i for i in range(len(g)) if g[i] == "wvl"]
        wl = np.array([float(names[i]) for i in spec_idx])
        usable = {n: c for n, c in LINES.items() if any(lo <= c <= hi for lo, hi in RANGES.values())}
        skipped = sorted(set(LINES) - set(usable))
        rows_out = []
        n_in = n_shift0 = 0
        for row in r:
            n_in += 1
            if row[meta_idx["shift"]].strip() not in ("0", "0.0"):
                continue
            n_shift0 += 1
            I = np.array([float(row[i]) if row[i] not in ("", "nan") else np.nan for i in spec_idx])
            out = {k: row[meta_idx[k]] for k in META_KEEP if k in meta_idx}
            for k in COMP_KEEP:
                if k in comp_idx:
                    v = row[comp_idx[k]].strip()
                    out["comp_" + k] = v if v != "" else ""
            for band, (lo, hi) in RANGES.items():
                sel = (wl >= lo) & (wl <= hi)
                out[band + "_sum"] = float(np.nansum(I[sel]))
            out["total_sum"] = float(np.nansum(I))
            for n, c in usable.items():
                fx = line_features(wl, np.nan_to_num(I), c)
                if fx is None:
                    continue
                for fk, fv in fx.items():
                    out[f"{n}__{fk}"] = fv
            rows_out.append(out)
    cols = list(rows_out[0].keys())
    with open(OUT, "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=cols); w.writeheader(); w.writerows(rows_out)
    print(json.dumps({"records_in": n_in, "shift0_rows": n_shift0, "rows_out": len(rows_out), "columns": len(cols),
                      "lines_used": len(usable), "lines_skipped_out_of_range": skipped}, indent=1))

if __name__ == "__main__":
    main()
