import numpy as np
def W(t, eta=0.01, M=20.0):
    return (1-np.exp(-t*(1+eta))) + (M-1)*(1-np.exp(-t*eta))
def R(n): return W(2*n)/W(n)
for n in [0.01,0.1,0.5,1,2,3,4,5,7,10,15,20,50,100,1000]:
    print(n, R(n))
ns=np.logspace(-2,3,20000)
r=R(ns)
d=np.diff(r)
sc=np.where(np.sign(d[1:])!=np.sign(d[:-1]))[0]
print("turning points:",[(float(ns[i+1]),float(r[i+1])) for i in sc])
# peak-normalised tau: peak of profile is 1+eta, so line-centre tau = n*(1+eta)
