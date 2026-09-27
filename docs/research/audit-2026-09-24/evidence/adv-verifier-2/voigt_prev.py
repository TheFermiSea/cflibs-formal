import numpy as np
from scipy.special import voigt_profile
from scipy.integrate import quad
def W(t0, sig, gam):
    p0 = voigt_profile(0, sig, gam)
    f = lambda x: 1-np.exp(-t0*voigt_profile(x, sig, gam)/p0)
    L = 50*(sig+gam)+ 200*np.sqrt(t0*gam*sig) + 50
    return 2*quad(f, 0, np.inf, limit=500)[0]
def thin(t0, sig, gam):
    p0 = voigt_profile(0, sig, gam); return t0/p0
# escape factor Gaussian vs SA
for t0 in [3,10]:
    g = W(t0,1.0,0.0)/thin(t0,1.0,0.0); sa=(1-np.exp(-t0))/t0
    print("tau0",t0,"gauss esc",round(g,3),"SA",round(sa,3))
for a in [0.01,0.1,0.93]:
    ts = np.logspace(-1, 4, 120)
    r = [W(2*t,1.0,a)/W(t,1.0,a) for t in ts]
    i = int(np.argmin(r))
    print("gam/sig",a,"min ratio",round(r[i],3),"at tau0",round(ts[i],2),"ratio at 1e4",round(r[-1],3), "monotone?", all(np.diff(r)<0))
print("--- restricted to smaller-line tau0 in [0.1,15] (both lines <= 30)")
for a in [0.0,0.01,0.1,0.3,0.93]:
    ts=np.logspace(-1,np.log10(15),80)
    r=[W(2*t,1.0,a)/W(t,1.0,a) for t in ts]
    d=np.diff(r)
    print("gam/sig",a,"monotone decreasing on range?",bool(np.all(d<0)),"min",round(min(r),4),"end",round(r[-1],4))
