import math
k=8.617333e-5
def dchi(ne,T):  # electron-only Debye-Hueckel, anchored to R1-07: 0.0660 eV at 1e17 cm^-3, 1e4 K
    return 0.0660*math.sqrt((ne/1e17)*(1e4/T))
for ne,T in [(1e17,11000),(1e18,12000),(8.3e18,18183),(1.2e19,19308)]:
    d=dchi(ne,T); kT=k*T; q=d/(2*kT)
    print(f"ne={ne:.1e} T={T}: dchi={d:.4f} eV  exp(-dchi/kT)={math.exp(-d/kT):.4f}  q=dchi/2kT={q:.3f}  1/(1-q)={1/(1-q):.3f}")
# fold of n = a*exp(dchi(n)/kT): q=1 <=> dchi = 2kT
for T in (8000,11000,15000,20000):
    kT=k*T; n=1e17*(2*kT/0.0660)**2*(T/1e4)
    print(f"T={T}: IPD fold (no/non-unique fixed point beyond) at ne={n:.2e}")
