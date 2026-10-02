"""Non-vacuity / sharpness numerics for ft02.ipd-saha-inverse-gauge.

Two independent, replayable checks backing claims made in the card's "Scope and validity"
section. All arithmetic here is standalone (plain Python, the public Debye-Hueckel-lowering
formula already recorded in docs/research/audit-2026-09-24/frontier.json's own verdict text for
FT-02); nothing is read from or copied out of CF-LIBS-improved.

(1) Reproduces the audit's own worked slope example for `q = Delta_chi / (2 kT)` at a chosen
    (T, n_e) illustration point, and the fold density where q(n_e) = 1 at that T, as a sanity
    cross-check of the numbers quoted in the card's "Role in the composition-extraction
    pipeline" section (not a claim proved by any Lean declaration in this family).
(2) Independently re-derives both hypothesis-sharpness counterexamples cited in the card's
    "Hypothesis sharpness" subsection: the unguarded (no `0 < a1`) and the unguarded (no `0 <= b`)
    forms of the two-point sensitivity bracket each have an instance satisfying every OTHER
    hypothesis (`hq`, `h1`, `h2`, `ha`, `hreg`) while the lower bound of the conclusion fails.
    This is a plain-arithmetic replay, independent of the Lean proof; it does not touch the
    landed `ipdInverse_twoPoint_sensitivity`, which has both guards and is not falsified.

Run: `python3 numerics.py`.
"""
import math


def ipd_log_map(a: float, b: float, ell: float) -> float:
    """`CflibsFormal.ipdLogMap`: F(ell) = log(a) + b*exp(ell/2). `math.log` raises on a <= 0,
    unlike Lean's total `Real.log` (junk value log|a|, and log(0) = 0); the junk value is
    substituted explicitly below wherever a counterexample instance needs it."""
    return math.log(a) + b * math.exp(ell / 2)


def real_log_junk(a: float) -> float:
    """Lean's `Real.log`: log|a| for a < 0, 0 for a == 0, log(a) for a > 0."""
    if a == 0.0:
        return 0.0
    return math.log(abs(a))


# --- (1) worked slope example (illustration only; not a Lean claim) -----------------------
EV_TO_K = 11604.5  # K per eV, standard value
T_K = 11000.0
n_e_cm3 = 1.0e17
kT_eV = T_K / EV_TO_K
lambda_D_cm = 6.9 * math.sqrt(kT_eV * EV_TO_K / n_e_cm3)  # standard Debye length, electron-only
delta_chi_eV = 1.44e-7 / lambda_D_cm
q = delta_chi_eV / (2 * kT_eV)
print(f"(1) T={T_K:.0f} K, n_e={n_e_cm3:.0e} cm^-3: "
      f"Delta_chi={delta_chi_eV:.4f} eV, q={q:.4f}, q**3={q**3:.3e}")

# fold density: solve q(n_e) = 1 for n_e at fixed T (bisection on n_e, standard case)
lo, hi = 1e15, 1e22
for _ in range(200):
    mid = math.sqrt(lo * hi)
    lam = 6.9 * math.sqrt(kT_eV * EV_TO_K / mid)
    dchi = 1.44e-7 / lam
    qmid = dchi / (2 * kT_eV)
    if qmid > 1:
        hi = mid
    else:
        lo = mid
print(f"    fold (q=1) near n_e = {math.sqrt(lo * hi):.3e} cm^-3 at T={T_K:.0f} K")

# --- (2) hypothesis-sharpness counterexamples --------------------------------------------
# (2a) drop `0 < a1` (a1 negative): a1 = -exp(-1/2), b = q = 1/2, l1 = 0, l2 = -2,
#      a2 chosen so h2 holds.
a1, b, q2, l1, l2 = -math.exp(-0.5), 0.5, 0.5, 0.0, -2.0
a2 = math.exp(l2 - b * math.exp(l2 / 2))
h1_lhs = real_log_junk(a1) + b * math.exp(l1 / 2)
h2_lhs = real_log_junk(a2) + b * math.exp(l2 / 2)
assert abs(h1_lhs - l1) < 1e-9 and abs(h2_lhs - l2) < 1e-9, "h1/h2 must hold at this instance"
assert a1 <= a2 and q2 < 1.0
hreg = b * math.exp(max(l1, l2) / 2) / 2
assert hreg <= q2, "hreg must hold"
lower_claim = real_log_junk(a2) - real_log_junk(a1) <= l2 - l1
print(f"(2a) a1<0 counterexample: log(a2)-log(a1) = {real_log_junk(a2) - real_log_junk(a1):.5f}, "
      f"l2-l1 = {l2 - l1:.5f} -> lower bound holds: {lower_claim} (must be False)")
assert lower_claim is False, "this instance must falsify the unguarded (no 0<a1) lower bound"

# (2b) drop `0 <= b` (b negative): 0 < a1, b = -1/2, l1 = 0, l2 = 2, q = 0.
b, q3, l1, l2 = -0.5, 0.0, 0.0, 2.0
a1 = math.exp(l1 - b * math.exp(l1 / 2))
a2 = math.exp(l2 - b * math.exp(l2 / 2))
assert a1 > 0 and a2 > 0 and a1 <= a2
hreg = b * math.exp(max(l1, l2) / 2) / 2
assert hreg <= q3, "hreg must hold (b<0 makes hreg very negative, so any q works)"
lower_claim = math.log(a2) - math.log(a1) <= l2 - l1
print(f"(2b) b<0 counterexample: log(a2)-log(a1) = {math.log(a2) - math.log(a1):.5f}, "
      f"l2-l1 = {l2 - l1:.5f} -> lower bound holds: {lower_claim} (must be False)")
assert lower_claim is False, "this instance must falsify the unguarded (no 0<=b) lower bound"

print("all sharpness assertions passed")
