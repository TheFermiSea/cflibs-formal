"""Non-vacuity / validation numerics for ft13.escape-factor-slab-bound.

Independent scratch reproduction (this card's own re-implementation, from the closed-form
Gaussian curve-of-growth attenuation given in the cited literature (Gornushkin 1999) and the
Mihalas *Stellar Atmospheres* ch. 9 form the module docstring paraphrases; no CF-LIBS-improved
source is read or reproduced here). Backs two card claims:

(1) Section 3 "Hypothesis sharpness / non-vacuity": a strict witness for `escape_ge_slab`,
    ψ = exp(-x^2) (a Gaussian profile, 0 <= ψ <= 1), at τ0 = 3 and τ0 = 10, computed by direct
    quadrature of the equivalent width W(ψ, τ0) and compared against the flat-slab factor
    SA(τ0) = (1 - exp(-τ0)) / τ0.
(2) Section 5 "How it would be validated": the alternating-series closed form for the Gaussian
    escape factor (64 terms, matching the pipeline counterpart's algorithm in structure but
    computed here from scratch) agrees with quadrature up to tau0 = 20, then breaks down (goes
    negative, i.e. below SA and hence unphysical) by tau0 = 30 -- illustrating why a pipeline
    validity gate near tau0 ~ 3 matters, without asserting anything about the private pipeline's
    own numbers.

Run: `python3 numerics.py`.
"""
import math


def SA(tau0: float) -> float:
    """Flat-slab self-absorption factor (1 - exp(-tau)) / tau, tau > 0."""
    return (1 - math.exp(-tau0)) / tau0


def gaussian_W_and_thin(tau0: float, n: int = 400_000, xmax: float = 8.0):
    """Quadrature of W(psi, tau0) = int (1 - exp(-tau0 psi(x))) dx for psi(x) = exp(-x^2), and
    the optically-thin width tau0 * int psi = tau0 * sqrt(pi)."""
    dx = 2 * xmax / n
    total = 0.0
    for i in range(n + 1):
        x = -xmax + i * dx
        w = 0.5 if i in (0, n) else 1.0
        total += w * (1 - math.exp(-tau0 * math.exp(-x * x)))
    W = total * dx
    thin = tau0 * math.sqrt(math.pi)
    return W, thin


def gaussian_escape_series(tau0: float, n_terms: int = 64) -> float:
    """Alternating-series closed form for the Gaussian profile-integrated escape factor
    W / thin, sum_{n>=1} (-1)^(n+1) tau0^(n-1) / (n! sqrt(n))."""
    if tau0 < 1e-10:
        return 1.0
    total = 0.0
    term = 1.0  # tau0^(n-1) / n! at n = 1
    for n in range(1, n_terms + 1):
        total += ((-1.0) ** (n + 1)) * term / math.sqrt(n)
        term *= tau0 / (n + 1)
    return total


print("Claim (1): escape_ge_slab witness psi = exp(-x^2), quadrature vs SA")
for tau0 in (3, 10):
    W, thin = gaussian_W_and_thin(tau0)
    f_quad = W / thin
    sa = SA(tau0)
    print(f"  tau0={tau0}: escape factor (quadrature) = {f_quad:.4f}, SA(tau0) = {sa:.4f}, "
          f"W = {W:.4f} >= SA*thin = {sa * thin:.4f}: {W >= sa * thin}")

print()
print("Claim (2): alternating-series closed form vs quadrature, and its breakdown")
for tau0 in (3, 10, 20, 30):
    W, thin = gaussian_W_and_thin(tau0)
    f_quad = W / thin
    f_series = gaussian_escape_series(tau0)
    sa = SA(tau0)
    flag = "OK" if f_series >= sa - 1e-6 else "BELOW SA (unphysical -- series breakdown)"
    print(f"  tau0={tau0}: series={f_series:.4f}  quadrature={f_quad:.4f}  SA={sa:.4f}  {flag}")
