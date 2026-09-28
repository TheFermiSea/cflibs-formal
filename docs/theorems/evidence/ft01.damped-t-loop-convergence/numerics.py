"""Non-vacuity / sharpness numerics for ft01.damped-t-loop-convergence.

Replays three numeric claims made in the card's "Scope and validity" and "Physical meaning"
sections, independent of any pipeline run: (1) the local contraction rate and its 20-step
shrink factor at the geology-regime gain used as an illustration; (2) the linearized
a-posteriori distance the theorem's window permits at that gain, for the pipeline's default
100 K stop step; (3) a witness that `exists_weights_iff`'s weighted gate is non-vacuous where
the unweighted row-sum gate it replaces already fails. All inputs are illustrative constants
chosen to exhibit the claimed behaviour, not measurements of any real spectrum.
Run: `python3 numerics.py`.
"""

lam, g = 0.5, 0.964
q = 1 - lam + lam * g
print(f"local rate q = 1 - lam + lam*g = {q}")
print(f"q**20 = {q**20:.4f}  (20 iterations shrink a linearized error to this fraction)")

step_K = 100.0
dist_K = step_K / (lam * (1 - g))
print(f"a-posteriori distance bound = {step_K} / (lam*(1-g)) = {dist_K:.1f} K")

a, b, c, d = 0.5, 100.0, 0.001, 0.5
assert a + b >= 1, "unweighted row-sum gate must fail for this witness to be informative"
assert b * c < (1 - a) * (1 - d), "exists_weights_iff's RHS condition must hold"
r = 0.5 * (c / (1 - d) + (1 - a) / b)  # weights_of_gate's b > 0 branch
gate = max(a + b * r, c / r + d)
assert gate < 1
print(f"unweighted a+b = {a + b} (fails); weighted gate at r={r} is {gate:.3f} (holds)")


def damped_mobius(T: float, lam: float, g: float, c: float) -> float:
    phi = T / (g + c * T)
    return (1 - lam) * T + lam * phi


c_demo = 1.0
Tstar = (1 - g) / c_demo
for T0 in (2e3, 8e3, 1.6e4, 4e4):
    T = T0
    for _ in range(2000):
        T = damped_mobius(T, lam, g, c_demo)
    print(f"T0={T0}: after 2000 iters |T - Tstar| = {abs(T - Tstar):.3e}")
