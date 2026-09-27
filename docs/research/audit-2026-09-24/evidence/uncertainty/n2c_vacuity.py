# Evaluate NoiseToComposition.noise_to_composition's RHS at realistic LIBS parameters,
# mirroring the Lean defs verbatim (noiseTempGapBound, tempResponseErrorBoundOfGap,
# compositionErrorBound). Read-only on the companion DB.
import sqlite3, math
import numpy as np
kB = 8.617333262e-5  # eV/K
con = sqlite3.connect("file:/home/brian/code/CF-LIBS-improved/ASD_da/libs_production.db?mode=ro", uri=True)
def levels(el, sp, emax=None):
    q = "select g_level, energy_ev from energy_levels where element=? and sp_num=? and g_level is not null and energy_ev is not null"
    rows = con.execute(q, (el, sp)).fetchall()
    g = np.array([r[0] for r in rows], float); E = np.array([r[1] for r in rows], float)
    if emax is not None:
        m = E <= emax; g, E = g[m], E[m]
    return g, E
def gapbound(Tmax, ET, eps):
    Eb = ET.mean(); SS = ((ET-Eb)**2).sum()
    return kB*Tmax**2*(np.abs(ET-Eb)*eps).sum()/SS
def Phi(Tmin, d, g, E, Eu):
    k0 = np.argmin(E)  # ground level as the single-term partition floor (best case)
    a = math.exp(Eu*d/(kB*Tmin**2)) - 1
    t = (g*E).sum()*d/(kB*Tmin**2)/(g[k0]*math.exp(-E[k0]/(kB*Tmin)))
    return (a+t)/(1-a), a
def compbound(C, s, Phi_):
    # N = C (S = 1); Nmax = max C; Shat ~ S = 1 (recovered total, take ~1)
    Nmax = max(C); delta = Nmax*Phi_; Shat = 1.0
    return delta/Shat + (C[s]/(1.0*Shat))*len(C)*delta
ET = np.linspace(3.3, 6.6, 10)   # Fe I Boltzmann-plot upper levels, eV
C = [0.70, 0.19, 0.11]           # Fe, Cr, Ni (steel-like)
species = [("Fe",1,3.33), ("Cr",1,3.44), ("Ni",1,3.54)]  # (element, sp_num, analysis-line E_u [eV])
for eps in [0.05, 0.02, 0.01, 0.005]:
  for (Tmin,Tmax) in [(8000,12000),(9000,11000)]:
    d = gapbound(Tmax, ET, np.full(10, eps))
    print(f"eps={eps} box=[{Tmin},{Tmax}] K  dmax={d:.1f} K ({100*d/10000:.1f}% of 10kK)")
    for emax in [None, 3.0, 1.0]:
      phis=[]; ok=True
      for el,sp,Eu in species:
        g,E = levels(el,sp,emax)
        p,a = Phi(Tmin,d,g,E,Eu)
        if not a < 1: ok=False
        phis.append((el,len(g),a,p))
      if not ok:
        print(f"   levels<= {emax}: hsmallmax FAILS for some species: " + ", ".join(f"{el}: exp-1={a:.2f}" for el,n,a,p in phis)); continue
      P = max(p for *_,p in phis)
      print(f"   levels<= {emax}: Phi per species " + ", ".join(f"{el}(n={n}):{p:.3g}" for el,n,a,p in phis) + f"  -> comp bound (Ni) {compbound(C,2,P):.3g}, (Fe) {compbound(C,0,P):.3g}")

print("\n--- sharper U-channel via mean excitation energy <E>_T (d lnU/d beta = -<E>) ---")
def meanE(g,E,T):
    w = g*np.exp(-E/(kB*T)); return (w*E).sum()/w.sum()
for el,sp,Eu in species:
    g,E = levels(el,sp)
    for (Tmin,Tmax) in [(8000,12000)]:
        mE = meanE(g,E,Tmax)
        for eps in [0.05,0.01]:
            d = gapbound(Tmax, ET, np.full(10, eps))
            dbeta = d/(kB*Tmin**2)            # |1/kT1 - 1/kT2| <= d/(kB Tmin^2)
            crude = (g*E).sum()*dbeta/(g[np.argmin(E)])
            sharp = math.exp(mE*dbeta)-1
            print(f"{el}: <E>_Tmax={mE:.3f} eV, eps={eps}: crude U-channel {crude:.3g} vs log-derivative U-channel {sharp:.3g}")

print("\n--- DifferentialEstimator constant (sum gE)/U(Tmin) vs <E>_Tmax ---")
for el,sp,Eu in species:
    g,E = levels(el,sp)
    U = lambda T: (g*np.exp(-E/(kB*T))).sum()
    print(f"{el}: sum gE = {(g*E).sum():.4g} eV, U(8000K) = {U(8000):.3g}, (sum gE)/U(Tmin) = {(g*E).sum()/U(8000):.3g} eV vs <E>_12000K = {meanE(g,E,12000):.3g} eV")
