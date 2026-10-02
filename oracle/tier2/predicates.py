"""Reference implementations of the Tier-2 physical-validity predicates (floats).

Each mirrors a Lean definition/theorem; the module and name are cited per function. The Lean side
proves the *relations*; these are the executable twins the evaluator may reimplement and must agree
with on every fixture in fixtures.json.
"""

import math

import numpy as np

KB_EV_PER_K = 8.617333262e-5  # CODATA 2018, eV/K (energies in eV, T in K)
MCWHIRTER_C = 1.6e12  # cm^-3 K^-1/2 eV^-3 (StarkBroadening.mcWhirterBound)


def energy_spread(E):
    """SS_E = sum (E_k - mean E)^2   (OLS.lean; the Boltzmann-plot slope's Gram entry)."""
    E = np.asarray(E, dtype=float)
    return float(np.sum((E - E.mean()) ** 2))


def condition_number(E):
    """kappa = max(SS_E, n) / min(SS_E, n)   (ConditionNumber.boltzmannConditionNumber).

    Raw, unit-carrying (E in eV): NOT scale-invariant (see that module's honest limitations).
    Infinite when SS_E = 0 (all upper-level energies equal)."""
    ss, n = energy_spread(E), float(len(E))
    return math.inf if ss <= 0.0 else max(ss, n) / min(ss, n)


def t_rel_error_bound(E, eps, t_hat_k):
    """|T_hat - T| / T <= kB * T_hat * eps * sqrt(kappa)
    (ConditionNumber.temp_rel_error_le_sqrt_conditionNumber; REDUCED: sign-normalized
    Boltzmann plot, `eps` a HARD per-line bound on the ordinate (log-intensity) error)."""
    k = condition_number(E)
    return math.inf if math.isinf(k) else KB_EV_PER_K * t_hat_k * eps * math.sqrt(k)


def t_identifiable(E, eps, t_hat_k, tau):
    """Answer/abstain gate: the proven worst-case relative T error is within `tau`.
    SS_E = 0 is provably NOT identifiable (Identifiability.temperature_not_identifiable_of_degenerate)."""
    return len(E) >= 2 and energy_spread(E) > 0.0 and t_rel_error_bound(E, eps, t_hat_k) <= tau


def mcwhirter_bound(t_k, de_ev):
    """n_e >= 1.6e12 sqrt(T) dE^3 (StarkBroadening.mcWhirterBound; T in K, dE in eV, n_e in cm^-3)."""
    return MCWHIRTER_C * math.sqrt(t_k) * de_ev**3


def mcwhirter_ok(t_k, de_ev, ne_cm3):
    """Certificates.mcWhirterCert: NECESSARY, not sufficient, for LTE."""
    return mcwhirter_bound(t_k, de_ev) <= ne_cm3


def stark_density(w, n_ref, width):
    """n_e = n_ref * width / (2 w)   (StarkBroadening.starkDensity)."""
    return n_ref * width / (2.0 * w)


def stark_opacity_lte_cert(t_k, de_ev, w, n_ref, width_meas, k_opac):
    """StarkOpacityGuard.starkOpacityLteCert: McWhirter at the conservative LOWER density
    starkDensity/kOpac. Sound only under the ASSUMED budget width_meas <= kOpac * starkFWHM(true)."""
    return (
        w > 0.0
        and n_ref > 0.0
        and k_opac >= 1.0
        and mcwhirter_ok(t_k, de_ev, stark_density(w, n_ref, width_meas) / k_opac)
    )


def slope_sigma(E, sigma):
    """Standard deviation of the OLS Boltzmann-plot slope: sigma / sqrt(SS_E)
    (Alt.OLSVariance.olsSlope_variance_eq; FisherLineSelection.crlb_slope; i.i.d. ordinate noise of
    standard deviation `sigma`). Infinite when SS_E = 0."""
    ss = energy_spread(E)
    return math.inf if ss <= 0.0 else sigma / math.sqrt(ss)


def t_rel_sigma(E, sigma, t_k):
    """First-order (delta-method) 1-sigma relative T error: kB * T * slope_sigma.
    The slope variance and the exact identity T = 1/(kB*slope) are in Lean (OLSVariance,
    ErrorBudget.temp_rel_error_eq); the first-order step between them is NOT proved there.
    Monotone non-increasing in SS_E, unlike the raw-kappa worst-case bound above."""
    return KB_EV_PER_K * t_k * slope_sigma(E, sigma)


def t_identifiable_fisher(E, sigma, t_k, tau):
    """Preferred answer/abstain gate: >= 2 lines, SS_E > 0 and the first-order 1-sigma relative T
    error is within `tau`. (Adding a line never hurts: FisherLineSelection.spreadOn_insert_ge.)"""
    return len(E) >= 2 and energy_spread(E) > 0.0 and t_rel_sigma(E, sigma, t_k) <= tau
