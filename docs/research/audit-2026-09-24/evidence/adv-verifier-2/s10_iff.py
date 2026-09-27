import numpy as np
S0=[1.0,1e-8]; c=1.2
def m(n):
    phi=c*np.sqrt(n)
    w=[1.0, S0[0]*np.exp(phi)/n, S0[0]*S0[1]*np.exp(phi)*np.exp(2*phi)/n**2]
    return (w[1]+2*w[2])/sum(w)
ns=np.linspace(1,2,20001); ms=m(ns)
print("strictly decreasing on [1,2]:", bool(np.all(np.diff(ms)<0)))
# hMLR at edge z=1 (factor 2) fails for close pairs:
n1,n2=1.5,1.5001
print("edge z=0 ok:", 1*c*(np.sqrt(n2)-np.sqrt(n1)) < np.log(n2/n1), " edge z=1 ok:", 2*c*(np.sqrt(n2)-np.sqrt(n1)) < np.log(n2/n1))
