import math
# FT-01: reduced map affine in u (u=1/kT, k=1); pipeline damps T, not u.
def run(g, Tstar, T0, lam=0.5, n=6, mode="T"):
    ustar = 1/Tstar; c = ustar*(1-g)
    T = T0; out=[]
    for _ in range(n):
        u = 1/T; unew = g*u + c
        if mode == "T":
            T = (1-lam)*T + lam*(1/unew)
        else:
            T = 1/((1-lam)*u + lam*unew)
        out.append(T)
    return out
g, Ts = 0.964, 11000.0
rho = 1-0.5+0.5*g
for T0 in (8000.0, 16000.0):
    Td = run(g, Ts, T0, mode="T"); Ud = run(g, Ts, T0, mode="u")
    u0 = 1/T0; us = 1/Ts
    ratT = [ (1/t - us)/(u0-us) / rho**(i+1) for i,t in enumerate(Td)]
    ratU = [ (1/t - us)/(u0-us) / rho**(i+1) for i,t in enumerate(Ud)]
    print(f"T0={T0}: T-damped (u_n-u*)/(rho^n (u0-u*)) =", [round(x,4) for x in ratT])
    print(f"         u-damped same ratio               =", [round(x,4) for x in ratU])
# g<0 inside the claimed window (-3,1): T-damping leaves T>0
print("g=-1, T*=2, T0=0.5: T-damped", run(-1.0, 2.0, 0.5, n=2, mode="T"), " u-damped", run(-1.0, 2.0, 0.5, n=2, mode="u"))
# FT-01(e) stop rule arithmetic
print("FT-01(e) 100 K /(0.5*(1-0.964)) =", 100/(0.5*(1-0.964)))
# FT-02 numbers (pipeline DH constants, jitpipe/solve.py:860-862)
T=11000.0; ne=1e17; kT=T/11604.518
lamD=6.9*math.sqrt(T/ne); dchi=1.44e-7/lamD; q=dchi/(2*kT)
print(f"FT-02: dchi={dchi:.5f} eV  exp(-dchi/kT)={math.exp(-dchi/kT):.4f}  q={q:.4f}  q^3={q**3:.3e}")
# fold: q=1
nf = ne*(2*kT/dchi)**2
print(f"FT-02 fold density (q=1) = {nf:.3e} cm^-3")
# FT-10 counterexample
E3=[0,1,2]; s2=[1,1,1e4]
def olsvar(E,s2):
    m=sum(E)/len(E); SS=sum((e-m)**2 for e in E)
    return sum(((e-m)/SS)**2*v for e,v in zip(E,s2))
print("FT-10: 2-line var", olsvar(E3[:2],s2[:2]), " 3-line var", olsvar(E3,s2))
# FT-10 interceptDiff weights
Ea=[1.0,2.0,4.0]; Eb=[3.0,5.0]
ma=sum(Ea)/3; mb=sum(Eb)/2; SS=sum((e-ma)**2 for e in Ea)+sum((e-mb)**2 for e in Eb); D=ma-mb
wa=[1/3 - D*(e-ma)/SS for e in Ea]; wb=[-1/2 - D*(e-mb)/SS for e in Eb]
print("FT-10 interceptDiff: sum w^2 =", sum(w*w for w in wa+wb), " formula =", 1/3+1/2+D*D/SS)
# FT-07 numbers
eta=0.05; C=0.005
print("FT-07 bound", 2*eta/(1-eta)*C, " actual worst", C*1.05/(C*1.05+(1-C)*0.95)-C)
