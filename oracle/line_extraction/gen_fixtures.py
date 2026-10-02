"""Generate fixtures.json: metamorphic relations for a line-extraction kernel.

Each case pairs two inputs of `extract_line(wavelength, intensity, peak_idx, half_width_px,
wl_step)` with the relation that must hold between the outputs, a tolerance, and the Lean theorem
(CflibsFormal/LineExtraction.lean) that proves the relation for the trapezoid kernel. Truth-free.
Deterministic: `python3 gen_fixtures.py > fixtures.json` must reproduce the committed file.
"""

import json
import math

import numpy as np

from reference import extract_line, window

STEP = 0.0625  # nm, dyadic so the wavelength axis is exact in binary floating point
N = 161
PEAK = 80
HALF = 24  # window = peak +/- 24 samples = +/- 1.5 nm
WL = (300.0 + STEP * np.arange(N)).astype(np.float64)
CENTER = float(WL[PEAK])
SIG = 0.2  # nm, Gaussian sigma
FWHM = SIG * 2.0 * math.sqrt(2.0 * math.log(2.0))
AMP = 1000.0
# window width W = x_n - x_0 for the (unclipped) window
_s, _e = window(N, PEAK, HALF)
W = float(WL[_e - 1] - WL[_s])


def gauss(center, amp=AMP, sig=SIG):
    return amp * np.exp(-0.5 * ((WL - center) / sig) ** 2)


def lorentz(center, amp, fwhm):
    return amp / (1.0 + (2.0 * (WL - center) / fwhm) ** 2)


spectra = {}


def add(name, y):
    spectra[name] = [float(v) for v in y]
    return name


def inp(name):
    return {"spectrum": name, "peak_idx": PEAK, "half_width_px": HALF, "wl_step": STEP}


def obs(name):
    out = extract_line(WL, np.array(spectra[name]), PEAK, HALF, STEP)
    return None if out is None else {"area": out[0], "sigma": out[1]}


cases = []


def case(cid, relation, theorem, a, b, **kw):
    cases.append(
        {"id": cid, "relation": relation, "lean_theorem": theorem, "base": inp(a),
         "transformed": inp(b), "seed_observed": {"base": obs(a), "transformed": obs(b)}, **kw}
    )  # fmt: skip


line = gauss(CENTER)
add("line", line)

# (a) linearity in amplitude: scaling the line by k scales the area by k (no pedestal)
for k in (0.5, 2.0, 3.7):
    add(f"line_x{k}", k * line)
    case(f"a_scale_{k}", "area_t == k * area_0", "trapArea_smul", "line", f"line_x{k}",
         k=k, rtol=1e-12)

# (a) additivity: area(f + g) = area(f) + area(g) on the same window (g a second, nearer line)
g_near = gauss(CENTER + 0.6, amp=300.0, sig=0.15)
add("g_near", g_near)
add("line_plus_g_near", line + g_near)
case("a_add", "area(f+g) == area(f) + area(g)", "trapArea_add", "line", "line_plus_g_near",
     addend=inp("g_near"), rtol=1e-12)

# (b) additive constant pedestal c. A RAW-integral kernel shifts by exactly c * W (Lean theorem);
# a baseline-aware kernel must instead be invariant (shift 0). The kernel declares neither: either
# outcome passes, anything else fails (e.g. a partial or scale-dependent baseline removal).
for c in (5.0, 120.5, -3.0):
    add(f"line_ped_{c}", line + c)
    case(f"b_pedestal_{c}", "area_t - area_0 == c * W (raw) or == 0 (baseline-invariant)",
         "trapArea_line_pedestal", "line", f"line_ped_{c}", c=c, window_width_nm=W, atol=1e-9, rtol=1e-12)

# (c) sub-pixel shift of a Gaussian: |area_t - area_0| <= W * L * |delta|, L = max|f'|
lip = AMP / (SIG * math.sqrt(math.e))
for frac in (0.25, 0.5, 1.0):
    delta = frac * STEP
    add(f"line_shift_{frac}px", gauss(CENTER + delta))
    case(f"c_shift_{frac}px", "|area_t - area_0| <= W * L * |delta|", "trapArea_shift_le",
         "line", f"line_shift_{frac}px", delta_nm=delta, lipschitz=lip, window_width_nm=W,
         bound=W * lip * delta, atol=1e-9)

# (d) separated blend: a second line at k FWHM contributes at most W * max|g| on the window
for kf in (6.0, 8.0, 12.0):
    g = gauss(CENTER + kf * FWHM, amp=800.0)
    add(f"blend_gauss_{kf}fwhm", line + g)
    eps = float(np.max(np.abs(g[_s:_e])))
    case(f"d_blend_gauss_{kf}fwhm", "|area_t - area_0| <= W * eps", "trapArea_blend_le", "line",
         f"blend_gauss_{kf}fwhm", separation_fwhm=kf, eps=eps, bound=W * eps, atol=1e-9)
# Lorentzian wings fall only as 1/(1+4k^2): the bound still holds but is not negligible.
for kf in (6.0, 12.0):
    g = lorentz(CENTER + kf * FWHM, 800.0, FWHM)
    add(f"blend_lorentz_{kf}fwhm", line + g)
    eps = float(np.max(np.abs(g[_s:_e])))
    case(f"d_blend_lorentz_{kf}fwhm", "|area_t - area_0| <= W * eps", "trapArea_blend_le", "line",
         f"blend_lorentz_{kf}fwhm", separation_fwhm=kf, eps=eps, bound=W * eps, atol=1e-9)
# exact: a second line that vanishes on the window leaves the area unchanged
g_out = np.where((np.arange(N) >= _s) & (np.arange(N) < _e), 0.0, gauss(CENTER + 1.8, 800.0))
add("blend_outside_window", line + g_out)
case("d_blend_vanishing", "area_t == area_0", "trapArea_blend_eq", "line",
     "blend_outside_window", atol=0.0, rtol=0.0)

# (e) sigma: positive and finite (incl. an all-zero spectrum, max(counts,1) floor) ...
add("line_ped_20", line + 20.0)
add("dark", np.zeros(N))
case("e_sigma_positive", "0 < sigma_t < inf (and area_t is None or finite)", "shotSigma_pos",
     "line_ped_20", "line_ped_20", sigma_only=True)
case("e_sigma_positive_zero_counts", "0 < sigma_t < inf when the kernel returns a result",
     "shotSigma_pos", "line", "dark", sigma_only=True, may_refuse=True)
# ... and non-decreasing when the counts increase pointwise
add("line_more_counts", line + 20.0 + 50.0 * np.exp(-0.5 * ((WL - CENTER) / 0.4) ** 2))
case("e_sigma_monotone", "sigma_t >= sigma_0 when intensity_t >= intensity_0 pointwise",
     "shotSigma_mono", "line_ped_20", "line_more_counts", rtol=1e-12)

doc = {
    "schema": "cflibs-line-extraction-fixtures-v1",
    "kernel_contract": "extract_line(wavelength, intensity, peak_idx, half_width_px, wl_step) "
    "-> (area, sigma) | None",
    "lean_module": "CflibsFormal/LineExtraction.lean",
    "scope": "PURE-MATH metamorphic relations; main branch only (positive trapezoid area). "
    "They certify structure, not accuracy, and not that the area is the physical line intensity.",
    "wavelength": [float(v) for v in WL],
    "window_width_nm": W,
    "fwhm_nm": FWHM,
    "spectra": spectra,
    "cases": cases,
}
print(json.dumps(doc, indent=1))
