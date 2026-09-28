import math

def stepW(eta, M, tau):
    return (1 - math.exp(-tau * (1 + eta))) + (M - 1) * (1 - math.exp(-tau * eta))

def R(n):
    return stepW(0.01, 20, 2 * n) / stepW(0.01, 20, n)

for n in [1, 3, 10]:
    print(f"R({n}) = {R(n):.6f}")

# scan for extrema
import numpy as np
ns = np.linspace(0.01, 40, 400000)
vals = [R(n) for n in ns]
# find local minima/maxima by sign change of derivative
best_min = None
best_max = None
for i in range(1, len(vals) - 1):
    if vals[i] < vals[i-1] and vals[i] < vals[i+1]:
        if best_min is None or vals[i] < best_min[1]:
            best_min = (ns[i], vals[i])
    if vals[i] > vals[i-1] and vals[i] > vals[i+1]:
        if best_max is None or vals[i] > best_max[1]:
            best_max = (ns[i], vals[i])
print(f"interior minimum ~ n={best_min[0]:.3f}, R={best_min[1]:.4f}")
print(f"interior maximum ~ n={best_max[0]:.3f}, R={best_max[1]:.4f}")
print(f"limit n->0+: R~{R(1e-6):.6f} (expect 2)")
print(f"R(40)={R(40):.6f} (past the interior maximum at n~20.18, still falling toward 1)")

# flat-kernel comparator: cogRatio 2 1 n = (1-exp(-2n))/(1-exp(-n)) = 1+exp(-n), which is
# strictly decreasing by elementary calculus. A naive strict float comparison at a 1e-4
# grid step over [1e-4, 30] spuriously reports "False" past n ~ 27, where consecutive grid
# points' cog(n) values differ by less than float64 resolution (both round to the same
# double) -- a step-size/precision artifact of *this script*, not a property of cog. The
# check below therefore compares with a tolerance rather than strictly (an earlier version
# of this script scanned the full [0.01, 40] range with a strict `>` and printed the same
# spurious "False").
def cog(n):
    return (1 - math.exp(-2*n)) / (1 - math.exp(-n))
ns_bracket = [n for n in ns if 1e-4 <= n <= 30]
TOL = 1e-9
print("flat kernel antitone on [1e-4, 30] (tolerance 1e-9 for float noise):",
      all(cog(a) - cog(b) > -TOL for a, b in zip(ns_bracket[:-1], ns_bracket[1:])))

# find two n with R(n) = 29/20 = 1.45 as in proof witnesses (bisection)
target = 29/20
def bisect(lo, hi):
    flo, fhi = R(lo) - target, R(hi) - target
    assert flo * fhi < 0
    for _ in range(200):
        mid = (lo + hi) / 2
        fm = R(mid) - target
        if flo * fm <= 0:
            hi, fhi = mid, fm
        else:
            lo, flo = mid, fm
    return (lo + hi) / 2

x = bisect(1, 3)
y = bisect(3, 10)
# a third crossing exists past the interior maximum (n ~ 20.18), where R is still falling
# back toward 1: R(30) > 29/20 > R(60), bracket it there.
z = bisect(30, 100)
print(f"witnesses at R=29/20: n1={x:.6f}, n2={y:.6f}, n3={z:.6f}, "
      f"R(n1)={R(x):.6f}, R(n2)={R(y):.6f}, R(n3)={R(z):.6f}")

print(f"R(1e4)={R(1e4):.8f} (expect -> 1)")
print(f"R(100)={R(100):.8f}, R(60)={R(60):.8f}, R(30)={R(30):.8f}")
diffs = [cog(a) - cog(b) for a, b in zip(ns_bracket[:-1], ns_bracket[1:])]
print("flat kernel min diff on [1e-4, 30] (should be > -1e-9):", min(diffs))

# H1 (1 <= M) sharpness of equivWidth_stepProfile: for 0 <= M < 1 the closed form `stepW`
# (only proved equal to the true width for M >= 1) disagrees with the true width of the
# M < 1 profile (height 1+eta on [0,M], height 1 on (M,1], 0 elsewhere) by exactly
# -(1-M)*(1-exp(-tau))*(1-exp(-tau*eta)) -- verified below at the docstring's own point
# (M=0, eta=tau=1) and at three more points with 0 <= M < 1.
def true_width_M_lt_1(eta, M, tau):
    assert 0 <= M < 1
    return M * (1 - math.exp(-tau * (1 + eta))) + (1 - M) * (1 - math.exp(-tau))

def predicted_gap(eta, M, tau):
    return -(1 - M) * (1 - math.exp(-tau)) * (1 - math.exp(-tau * eta))

for (eta, M, tau) in [(1.0, 0.0, 1.0), (0.3, 0.5, 0.7), (2.0, 0.2, 0.05), (0.01, 0.9, 3.0)]:
    true_w = true_width_M_lt_1(eta, M, tau)
    rhs = stepW(eta, M, tau)
    gap = rhs - true_w
    pred = predicted_gap(eta, M, tau)
    print(f"eta={eta}, M={M}, tau={tau}: true={true_w:.6f}, stepW(rhs)={rhs:.6f}, "
          f"rhs-true={gap:.6f}, predicted -(1-M)(1-e^-tau)(1-e^-(tau*eta))={pred:.6f}, "
          f"match={math.isclose(gap, pred, rel_tol=1e-9, abs_tol=1e-12)}")
