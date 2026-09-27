"""Execute the pipeline's own SB-graph T-leg and sb_offset n_e-leg (IPD off, equal sigmas)
and measure the undamped reduced-map gain dT_new/dT at the fixed point, against the closed form
g = (sum_e b_e D_e) * D_med / sum_e (W_e + b_e D_e^2)  (b_e = n_I n_II / n, D_e = mean x*_II - mean x*_I,
W_e = within-stage SS of shifted abscissa)."""
import warnings; warnings.filterwarnings("ignore")
import numpy as np
from cflibs.inversion.solve import iterative as it
from cflibs.domain.observations import LineObservation
from cflibs.core.constants import KB_EV, SAHA_CONST_CM3, EV_TO_K

solver = it.IterativeCFLIBSSolver.__new__(it.IterativeCFLIBSSolver)
solver.aki_uncertainty_weighting = False

def make_obs(elements, T_K, ne):
    T_eV = T_K / EV_TO_K
    lnS = np.log(SAHA_CONST_CM3 * T_eV**1.5 / ne)
    obs = {}
    for el, (ip, q, En, Ei) in elements.items():
        L = []
        for E in En:   # neutral
            y = q - E / T_eV
            L.append(LineObservation(500.0, np.exp(y) * 1.0 * 1.0e8 / 500.0, 0.05 * np.exp(y) * 1e8 / 500.0,
                                     el, 1, E, 1, 1.0e8))
        for E in Ei:   # ion: y_ion = q + lnS - (E+IP)/T  (same Saha-Boltzmann transform the pipeline inverts)
            y = q + lnS - (E + ip) / T_eV
            L.append(LineObservation(500.0, np.exp(y) * 1e8 / 500.0, 0.05 * np.exp(y) * 1e8 / 500.0,
                                     el, 2, E, 1, 1.0e8))
        obs[el] = L
    return obs

def T_leg(obs, ips, T, ne):
    fit = solver._fit_saha_boltzmann_graph(obs, T, ne, ips)
    return -1.0 / (fit.slope * KB_EV)

def ne_leg(obs, ips, T):
    ne, n_used, _ = solver._estimate_ne_from_sb_offset(obs, T, ips)
    return ne

def Phi(obs, ips, T):
    return T_leg(obs, ips, T, ne_leg(obs, ips, T))

def closed_form(elements, med_el):
    num = 0.0; den = 0.0; D = {}
    for el, (ip, q, En, Ei) in elements.items():
        xn = np.array(En, float); xi = np.array(Ei, float) + ip
        nI, nII = len(xn), len(xi); n = nI + nII
        De = xi.mean() - xn.mean(); D[el] = De
        be = nI * nII / n
        We = ((xn - xn.mean())**2).sum() + ((xi - xi.mean())**2).sum()
        num += be * De; den += We + be * De**2
    return num * D[med_el] / den

def run(name, elements, med_el, Ttrue=11000.0, netrue=1e17):
    ips = {el: v[0] for el, v in elements.items()}
    obs = make_obs(elements, Ttrue, netrue)
    Tfp = Phi(obs, ips, Ttrue)
    h = 1.0
    g_num = (Phi(obs, ips, Ttrue + h) - Phi(obs, ips, Ttrue - h)) / (2 * h)
    # the map is affine in u=1/kT; its u-gain equals dT'/dT at the fixed point (T'=T there)
    print(f"{name}: Phi(T*)={Tfp:.3f} (T*={Ttrue})  ne_hat(T*)={ne_leg(obs, ips, Ttrue):.4e}  "
          f"gain numeric={g_num:.5f}  closed form={closed_form(elements, med_el):.5f}")
    return obs, ips

# one element, Ti-like: IP 6.83, neutral lines 1-3.5 eV, ion lines 3-5.5 eV
one = {"Ti": (6.83, 0.0, [1.0, 1.5, 2.0, 2.5, 3.0, 3.5], [3.0, 3.5, 4.0, 4.5, 5.0, 5.5])}
run("1 element", one, "Ti")
# tight clusters -> gain -> 1 (rho -> 1)
tight = {"Ti": (6.83, 0.0, [2.0, 2.05, 2.1], [4.0, 4.05, 4.1])}
run("1 element, tight stages", tight, "Ti")
# three elements; median element (by n_e estimate: all equal at truth, perturb IP ordering)
three = {"Al": (5.99, 0.0, [3.14, 3.14], [11.8]),
         "Ti": (6.83, 0.0, [1.0, 1.5], [3.0, 3.5, 4.0, 4.5, 5.0, 5.5, 3.2, 3.7, 4.2, 4.7]),
         "V":  (6.75, 0.0, [2.5, 3.0], [3.5, 4.0, 4.5, 5.0])}
obs, ips = run("3 elements (DED-like budgets)", three, "Ti")
for T in (10000.0, 10500.0, 11000.0, 11500.0, 12000.0):
    per = {el: solver._estimate_ne_from_sb_offset({el: obs[el]}, T, ips)[0] for el in obs}
    print(f"  T={T:.0f}: per-element ne_hat " + ", ".join(f"{el}={v:.3e}" for el, v in per.items())
          + f" | Phi(T)={Phi(obs, ips, T):.1f}")

print("--- constructed g>1 case: low-D element carries most lines, median element has the middle D")
exp3 = {"A": (4.0, 0.0, [1.0, 1.0, 1.0, 1.0, 1.0, 1.0], [1.0, 1.0, 1.0, 1.0, 1.0, 1.0]),   # D = 4
        "B": (8.0, 0.0, [1.0], [1.0]),                                                    # D = 8 (median)
        "C": (11.0, 0.0, [1.0], [2.0])}                                                   # D = 12
obs, ips = run("3 elements, g>1", exp3, "B")
T = 11100.0
traj = [T]
for k in range(8):   # plain Picard with the pipeline's 0.5 damping in T and n_e, pipeline order
    pass
# damped Gauss-Seidel iteration exactly as _run_python_iteration orders it (IPD off)
T, ne = 11100.0, 1e17
for k in range(40):
    Tn = T_leg(obs, ips, T, ne); Tk = 0.5 * T + 0.5 * Tn
    nen = ne_leg(obs, ips, Tk); ne = 0.5 * ne + 0.5 * nen; T = Tk
    if k % 8 == 7: print(f"  iter {k+1}: T={T:.1f} K  ne={ne:.3e}")
