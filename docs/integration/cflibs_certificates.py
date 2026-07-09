#!/usr/bin/env python3
# Reference implementation PROPOSED for CF-LIBS-improved — mirrors
# CflibsFormal/Certificates.lean; do not edit without updating the Lean twin.
"""Runtime certificates for CF-LIBS — the float mirror of the verified spec.

Each function below is the 1:1 floating-point twin of a `def …Cert` in the verified Lean
module `CflibsFormal/Certificates.lean`. When a certificate evaluates ``True`` on the
pipeline's actual floats, the *named* soundness theorem — not a heuristic — guarantees the
corresponding well-posedness / convergence / error property. Each function returns

    (passed: bool, theorem: str, value: float)

where ``theorem`` is the wrapped Lean guarantee and ``value`` is the certificate's decisive
scalar (the margin quantity), so a caller can log which theorem a gate activated and how far
from the boundary it sat.

HONEST SCOPE (mirrors Certificates.lean's module doc and the dossier §5 refusals):

* A certificate is SUFFICIENT for its guarantee, generally NOT necessary. A ``False`` verdict
  names which proven precondition failed; it does not prove the guarantee false.
* Only runtime-checkable arithmetic lives in a certificate. Distances to an UNKNOWN truth stay
  out and remain assumptions of the soundness theorem: the per-line error ``eps`` (C4) and
  per-species density error ``delta`` (C6) are distances to true intensities/densities (R1);
  the atomic-data aliasing ``delta`` (C14) is unknowable in principle (R2 — the A* mark:
  report "conditional on the atomic-data uncertainty," never "proven").
* C10 is UNCONDITIONAL: the damped multi-element iteration converges with no smallness /
  contraction side-condition — the certificate is only positivity.
* Float != R near a threshold (R6): near a boundary (``SSe ~ 0``, ``delta ~ 1``) the IEEE-754
  verdict may disagree with the proven real-number verdict. Callers should carry an interval
  margin; the ``value`` returned is exactly that margin quantity.

Pure stdlib (no numpy). Run ``python3 cflibs_certificates.py`` to self-check every certificate
on the non-vacuity witness data used by the Lean ``example``s.
"""
from __future__ import annotations

import math

# McWhirter prefactor (CGS), matching PartialLTE.lteValid_iff_thermalized (1.6e12).
MCWHIRTER_C = 1.6e12


# ======================= shared design quantities ==================================
def _mean(xs):
    """Sample mean ``(sum xs) / len xs`` — mirrors ``CflibsFormal.mean``."""
    return sum(xs) / len(xs)


def _ss(xs):
    """Centered sum of squares ``SS = sum_k (x_k - xbar)^2``."""
    xbar = _mean(xs)
    return sum((x - xbar) ** 2 for x in xs)


def _cross(xs, ys):
    """Centered cross term ``S_xy = sum_k (x_k - xbar)(y_k - ybar)``."""
    xbar, ybar = _mean(xs), _mean(ys)
    return sum((x - xbar) * (y - ybar) for x, y in zip(xs, ys))


def _saha_equilibrium_ne(S, Ntot):
    """Closed-form single-element two-stage electron density
    ``(-S + sqrt(S^2 + 4 S Ntot)) / 2`` — mirrors ``CflibsFormal.sahaEquilibriumNe``."""
    return (-S + math.sqrt(S ** 2 + 4 * S * Ntot)) / 2


# ======================= the certificates ==========================================
def energy_spread_certificate(E):
    """C1 — mirrors ``energySpreadCert`` / thm ``designNormalMatrix_det_ne_zero_iff``.

    Predicate: ``0 < SSe``. Guarantee: the Boltzmann-plot normal matrix is nonsingular, so
    the slope -> T fit is well-posed (T-identifiable).
    """
    sse = _ss(E)
    return (sse > 0.0, "designNormalMatrix_det_ne_zero_iff", sse)


def joint_rank_certificate(E, s):
    """C2 — mirrors ``jointRankCert`` / thm ``jointDesign_det_pos_iff``.

    Predicate: ``0 < SSe*SSs - S_Es^2``. Guarantee: centered energies and ion-stage indicator
    are not collinear, so the joint (T, n_e) fit is identifiable.
    """
    val = _ss(E) * _ss(s) - _cross(E, s) ** 2
    return (val > 0.0, "jointDesign_det_pos_iff", val)


def conditioning_certificate(E):
    """C3 — mirrors ``conditioningCert`` / thms ``boltzmannConditionNumber_ge_one`` +
    ``centeredScaledDesign_orthonormal``.

    Predicate: ``0 < SSe`` (same as C1). Guarantee: kappa >= 1 and the scaled centered design
    is orthonormal (kappa_scaled = 1); the only scale-free sensitivity is the slope gain 1/SSe.
    """
    sse = _ss(E)
    return (sse > 0.0, "boltzmannConditionNumber_ge_one", sse)


def slope_budget_certificate(eps, tau_beta, SSe, n):
    """C4 — mirrors ``slopeBudgetCert`` / thm ``maxPerLineError_sufficient``.

    Predicate: ``eps^2 * n <= tau_beta^2 * SSe``. Guarantee: the OLS slope (inverse-temperature)
    error is <= tau_beta. NOTE (R1): ``eps`` is a distance to the true ordinates — an ASSUMED
    SNR bound, not measured; soundness is conditional on the noise model.
    """
    lhs = eps ** 2 * n
    rhs = tau_beta ** 2 * SSe
    return (lhs <= rhs, "maxPerLineError_sufficient", rhs - lhs)


def temp_budget_certificate(kB, THat, B, tauT):
    """C5 — mirrors ``tempBudgetCert`` / thm ``temp_rel_error_le``.

    Predicate: ``kB * THat * B <= tauT`` (exact identity |dT|/T = kB*THat*|dbeta|).
    Guarantee: the relative temperature error is <= tauT. NOTE (R1): ``B`` is a slope-error
    bound, an epistemic input.
    """
    lhs = kB * THat * B
    return (lhs <= tauT, "temp_rel_error_le", tauT - lhs)


def comp_budget_certificate(delta, tauC, Shat, n):
    """C6 — mirrors ``compBudgetCert`` / thm ``composition_target_sufficient``.

    Predicate: ``(n + 1) * delta <= tauC * Shat`` (n = species count, Shat = sum of N-hat).
    Guarantee: every composition fraction error is <= tauC. NOTE (R1): ``delta`` is the
    per-species distance to the true density — assumed, not measured.
    """
    lhs = (n + 1) * delta
    rhs = tauC * Shat
    return (lhs <= rhs, "composition_target_sufficient", rhs - lhs)


def mcwhirter_certificate(C, T, dE, ne):
    """C7 — mirrors ``mcWhirterCert`` / thm ``mcwhirter_iff_thermalizationLimit``.

    Predicate: ``C * sqrt(T) * dE^3 <= ne`` (C = 1.6e12 CGS). Guarantee: the transition gap dE
    is within the thermalization limit E* (collisionally LTE-admissible). NOTE (R3): a single
    diagnostic certifies INTERNAL consistency, not physical LTE — require the two-diagnostic
    Stark<->Saha gate before clearing McWhirter.
    """
    lhs = C * math.sqrt(T) * dE ** 3
    return (lhs <= ne, "mcwhirter_iff_thermalizationLimit", ne - lhs)


def saha_iter_certificate(S, Ntot, b):
    """C9 — mirrors ``sahaIterCert`` / thm ``sahaIter_tendsto``.

    Predicate (all four): ``b < Ntot`` AND ``sahaEquilibriumNe(S, Ntot) <= b`` AND
    ``sqrt(S)/(2 sqrt(Ntot - b)) < 1`` AND ``sqrt(S*Ntot) <= b``. Guarantee: the fixed-point
    iteration converges geometrically to the closed-form electron density. ``value`` is the
    contraction rate (smaller is faster; must be < 1).
    """
    root = _saha_equilibrium_ne(S, Ntot)
    rate = math.sqrt(S) / (2 * math.sqrt(Ntot - b)) if b < Ntot else float("inf")
    clauses = (
        b < Ntot
        and root <= b
        and rate < 1.0
        and math.sqrt(S * Ntot) <= b
    )
    return (clauses, "sahaIter_tendsto", rate)


def damped_iter_certificate(S, Ntot):
    """C10 (HEADLINE) — mirrors ``dampedIterCert`` / thm ``dampedMultiElementIter_tendsto``.

    Predicate: every Saha factor ``S[s] > 0`` and total density ``Ntot[s] > 0`` (physically
    always true). UNCONDITIONAL: with the canonical relaxation lam = 1/(1 + sum_s Ntot[s]/S[s])
    the damped multi-element closure iteration converges at rate 1 - lam < 1 with NO smallness
    / contraction side-condition. Use this lam in place of the guessed 0.5 damping. ``value`` is
    the proven convergence rate 1 - lam (in (0, 1)).
    """
    passed = all(s > 0.0 for s in S) and all(nt > 0.0 for nt in Ntot)
    if passed:
        lam = 1.0 / (1.0 + sum(nt / s for nt, s in zip(Ntot, S)))
        rate = 1.0 - lam
    else:
        rate = float("nan")
    return (passed, "dampedMultiElementIter_tendsto", rate)


def known_tau_certificate(tau):
    """C12 — mirrors ``knownTauCert`` / thm ``lineIntensity_eq_selfAbsorbedIntensity_div``.

    Predicate: ``0 <= tau`` (a known optical depth). Guarantee: dividing the measured intensity
    by SA(tau) recovers the optically-thin intensity exactly, I_thin = I_meas / SA(tau).
    """
    return (tau >= 0.0, "lineIntensity_eq_selfAbsorbedIntensity_div", tau)


def sa_distinct_certificate(w1, w2):
    """C13 — mirrors ``saDistinctCert`` / thm ``cogRatio_injOn``.

    Predicate: two lines with distinct positive curve-of-growth widths, ``0 < w2 < w1``.
    Guarantee: the source-free curve-of-growth ratio is injective in the column density, so N
    (hence relative composition) is recovered without the common source scale. The tau-known
    branch of the dossier's C13 disjunction is exactly C12 (``known_tau_certificate``); the
    failure mode without distinct widths is ``selfAbsorption_breaks_identifiability``.
    """
    passed = (0.0 < w2) and (w2 < w1)
    return (passed, "cogRatio_injOn", w1 - w2)


def alias_budget_certificate(delta):
    """C14 (A* — REFUSAL-flagged) — mirrors ``aliasBudgetCert`` / thm
    ``classicDensity_aliasing_error``.

    Predicate: ``0 <= delta < 1``. Guarantee: |N-hat - N| <= N * delta/(1 - delta).

    REFUSAL (R2): ``delta`` is the relative atomic-data error — a distance to an UNKNOWN truth
    (you use tabulated data precisely because truth is unknown). Only a literature-uncertainty
    delta (e.g. a NIST grade) can be plugged; the bound is exactly as honest as that catalog
    claim. Report "conditional on the atomic-data uncertainty," never "proven." ``value`` is the
    relative error amplification delta/(1 - delta).
    """
    passed = (0.0 <= delta) and (delta < 1.0)
    amp = delta / (1.0 - delta) if delta < 1.0 else float("inf")
    return (passed, "classicDensity_aliasing_error", amp)


# ======================= smoke test on the non-vacuity witnesses ====================
def _main():
    """Self-check each certificate on the exact witness data of the Lean ``example``s."""
    checks = [
        # (label, (passed, theorem, value), expected_passed)
        ("C1 energy_spread", energy_spread_certificate([0.0, 1.0]), True),
        ("C2 joint_rank", joint_rank_certificate([0.0, 1.0, 2.0], [0.0, 0.0, 1.0]), True),
        ("C3 conditioning", conditioning_certificate([0.0, 1.0]), True),
        ("C4 slope_budget", slope_budget_certificate(1.0, 2.0, 0.5, 2), True),
        ("C5 temp_budget", temp_budget_certificate(1.0, 2.0, 0.5, 1.0), True),
        ("C6 comp_budget", comp_budget_certificate(1.0, 2.0, 2.0, 2), True),
        ("C7 mcwhirter", mcwhirter_certificate(1.0, 1.0, 1.0, 2.0), True),
        ("C9 saha_iter", saha_iter_certificate(1.0, 3.0, 2.0), True),
        ("C10 damped_iter", damped_iter_certificate([1.0, 1.0], [1.0, 1.0]), True),
        ("C12 known_tau", known_tau_certificate(1.0), True),
        ("C13 sa_distinct", sa_distinct_certificate(2.0, 1.0), True),
        ("C14 alias_budget", alias_budget_certificate(0.5), True),
    ]
    # A few decisive FALSE cases (the honest-refusal side): equal energies, delta >= 1, etc.
    negatives = [
        ("C1 flat energies -> reject", energy_spread_certificate([1.0, 1.0]), False),
        ("C2 collinear E,s -> reject", joint_rank_certificate([0.0, 1.0], [0.0, 2.0]), False),
        ("C10 nonpos S -> reject", damped_iter_certificate([0.0, 1.0], [1.0, 1.0]), False),
        ("C14 delta=1 -> reject", alias_budget_certificate(1.0), False),
    ]

    ok = True
    for label, (passed, theorem, value), expected in checks + negatives:
        status = "PASS" if passed == expected else "FAIL"
        if passed != expected:
            ok = False
        print(f"[{status}] {label:32s} verdict={passed!s:5s} "
              f"theorem={theorem:38s} value={value:.6g}")
    print("\nALL CERTIFICATES CONSISTENT" if ok else "\nMISMATCH — Lean/Python drift")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(_main())
