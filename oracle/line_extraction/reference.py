"""Reference line-extraction kernel (the incumbent trapezoid seed), numpy only.

Mirror of `extract_line` in CF-LIBS-improved `tools/cflibs_evo/seeds/line_extraction.py` (the
main branch: positive trapezoid area; the Gaussian-equivalent fallback is omitted because the
fixtures only exercise the main branch, see CflibsFormal/LineExtraction.lean, "Honest limitations").
Contract: extract_line(wavelength, intensity, peak_idx, half_width_px, wl_step) -> (area, sigma) | None.
"""

import numpy as np


def window(n_samples, peak_idx, half_width_px):
    start = max(0, peak_idx - half_width_px)
    end = min(n_samples, peak_idx + half_width_px + 1)
    return start, end


def extract_line(wavelength, intensity, peak_idx, half_width_px, wl_step):
    start, end = window(len(intensity), peak_idx, half_width_px)
    seg_wl, seg_y = wavelength[start:end], intensity[start:end]
    area = float(np.trapezoid(seg_y, seg_wl))
    if not np.isfinite(area) or area <= 0.0:
        return None
    sigma = float(np.sqrt(np.sum(np.maximum(seg_y, 1.0))) * wl_step)
    return area, sigma
