# Card-A illustration (numerics, NOT a proved result): two-zone line-of-sight mixture,
# uniform n_e, optically thin, LTE per zone. Compares two-line apparent temperatures.
import math
kB = 8.617333262e-5  # eV/K
SAHA = 4.8286e15     # 2*(2*pi*m_e*k/h^2)^{3/2} in cm^-3 K^-3/2 (standard value; not from a repo source)
def T_app(pair, w, T):
    (E1, E2) = pair
    y = lambda E: math.log(sum(wz*math.exp(-E/(kB*Tz)) for wz, Tz in zip(w, T)))
    beta = (y(E1) - y(E2)) / (E2 - E1)
    return 1.0/(kB*beta)
T = [8000.0, 14000.0]      # cool and hot zone [K]
wI = [1.0, 0.3]            # neutral zone weights Fcal*N_I/U_I (arbitrary units)
ne, chi = 1e17, 7.9024     # uniform n_e [cm^-3]; Fe I ionization energy [eV] (textbook value)
rho = [SAHA*Tz**1.5*math.exp(-chi/(kB*Tz))/ne for Tz in T]
wII = [a*b for a, b in zip(wI, rho)]
neutral = (3.2, 5.0)       # neutral upper-level energies [eV] (illustrative)
for label, ion in [("strict anchor holds (5.0 <= 5.5)", (5.5, 7.7)),
                   ("strict anchor fails, weak holds (5.0 > 2.8, 5.0 <= 2.8+7.9)", (2.8, 5.5))]:
    tn, ti = T_app(neutral, wI, T), T_app(ion, wII, T)
    print(f"{label}: T_app neutral = {tn:.0f} K, T_app ion = {ti:.0f} K, ion >= neutral: {ti >= tn}")
print("zone reweights rho (cool, hot):", [f"{r:.3g}" for r in rho])
