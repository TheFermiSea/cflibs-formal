"""Sharpness / non-vacuity witness for ft17.neutrality-newton-bracket.

Two checks against the exact Lean formulas of `CflibsFormal.neutralityNewton`,
`CflibsFormal.multiElementIonized` (CflibsFormal/SahaEquilibrium.lean):

(A) Non-vacuity: a concrete two-species instance where H1-H5 all hold simultaneously and the
    bracket N(x) <= r <= G(N(x)) is checked at several x >= 0 guesses, including x far from r.
(B) Sharpness of H4 (hr : 0 <= r): the single-species case S = Ntot = 1 has a second fixed point
    r = -(1+sqrt(5))/2 < 0 of G that satisfies H5 (r = G(r)) but not H4. At x = 0, N(0) = 0.5 > r,
    so the bracket's lower end N(x) <= r FAILS there -- demonstrating hr is load-bearing, not a
    redundant hypothesis the statement could drop.
"""
import math


def G(S, Ntot, x):
    return sum(Ntot[s] * S[s] / (x + S[s]) for s in S)


def D(S, Ntot, x):
    return sum(Ntot[s] * S[s] / (x + S[s]) ** 2 for s in S)


def N(S, Ntot, x):
    return x - (x - G(S, Ntot, x)) / (1 + D(S, Ntot, x))


def find_root(S, Ntot, lo=0.0, hi=None, iters=200):
    """Bisection on f(x) = x - G(x), which is strictly increasing on [0, inf) here."""
    if hi is None:
        hi = sum(Ntot.values()) + 1.0
    flo = lo - G(S, Ntot, lo)
    fhi = hi - G(S, Ntot, hi)
    assert flo <= 0 <= fhi, (flo, fhi)
    for _ in range(iters):
        mid = (lo + hi) / 2
        fmid = mid - G(S, Ntot, mid)
        if fmid < 0:
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2


results = {}

# --- (A) Non-vacuity: two species, S = [2, 3], Ntot = [5, 1] ---
S = {"a": 2.0, "b": 3.0}
Ntot = {"a": 5.0, "b": 1.0}
assert all(S[s] > 0 for s in S)   # H1 (hS)
assert all(Ntot[s] >= 0 for s in Ntot)  # H2 (hN)
r = find_root(S, Ntot)
assert r >= 0  # H4 (hr)
resid = r - G(S, Ntot, r)
assert abs(resid) < 1e-9  # H5 (hfix), to solver tolerance
checks = []
for x in [0.0, 0.001, 1.0, 3.7, 50.0, 1000.0]:
    assert x >= 0  # H3 (hx)
    nx = N(S, Ntot, x)
    lower_ok = nx <= r + 1e-9
    upper_ok = r <= G(S, Ntot, nx) + 1e-9
    checks.append((x, nx, lower_ok, upper_ok))
results["A_root_r"] = r
results["A_checks"] = checks
results["A_all_pass"] = all(lo and up for _, _, lo, up in checks)

# --- (B) Sharpness of H4: single species S = Ntot = 1 ---
S1 = {"s": 1.0}
Ntot1 = {"s": 1.0}
r_neg = -(1 + math.sqrt(5)) / 2  # the algebraic other root of r = G(r) = 1/(r+1)
resid_neg = r_neg - G(S1, Ntot1, r_neg)
n0 = N(S1, Ntot1, 0.0)
results["B_r_neg"] = r_neg
results["B_resid_neg"] = resid_neg          # should be ~0: H5 holds at r_neg despite r_neg < 0
results["B_N0"] = n0                        # should be 0.5
results["B_bracket_lower_holds"] = n0 <= r_neg  # must be FALSE: bracket fails without H4

for k, v in results.items():
    print(k, "=", v)

assert abs(resid_neg) < 1e-9, "r_neg must solve r = G(r) (H5) for the witness to be meaningful"
assert results["A_all_pass"], "part (A) non-vacuity check failed"
assert results["B_bracket_lower_holds"] is False, "part (B) must show the bracket FAILING at hr's boundary"
print("ALL ASSERTIONS PASSED")
