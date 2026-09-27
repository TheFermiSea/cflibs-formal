import numpy as np
from scipy.special import voigt_profile
# independent check: trapezoid on a huge nonuniform grid (x>=0, symmetric profile)
x = np.concatenate([np.linspace(0,50,200001), np.logspace(np.log10(50.0001), 8, 200000)])
def Wall(ts, sig, gam):
    p = voigt_profile(x, sig, gam); p0 = voigt_profile(0, sig, gam); ps = p/p0
    out=[]
    for t in ts:
        f = -np.expm1(-t*ps)
        out.append(2*np.trapezoid(f, x))
    return np.array(out)
for a in [0.01,0.03,0.1,0.93]:
    ts=np.logspace(-1, np.log10(200), 300)
    W1=Wall(ts,1.0,a); W2=Wall(2*ts,1.0,a)
    r=W2/W1
    i=int(np.argmin(r))
    print(f"gam/sig {a}: min ratio {r[i]:.4f} at smaller-line tau0 {ts[i]:.2f}; r(tau0=15)={np.interp(15,ts,r):.4f}; r(tau0=30)={np.interp(30,ts,r):.4f}; r(200)={r[-1]:.4f}")
