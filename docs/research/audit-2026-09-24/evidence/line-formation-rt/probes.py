import numpy as np
# 1) SelfReversal: hdip holds but no central dip along the profile x in (0,1], tau_c=a x, tau_s=b x
def I(Sc,Ss,a,b,x): return Sc*(1-np.exp(-a*x))*np.exp(-b*x)+Ss*(1-np.exp(-b*x))
Sc,Ss,a,b=1.0,0.0,1.0,0.1
print("hdip at center:", Ss < Sc*(1-np.exp(-a)))
x=np.linspace(1e-4,1,100001); y=I(Sc,Ss,a,b,x)
print("profile monotone increasing toward center:", np.all(np.diff(y)>0), "argmax x=",x[np.argmax(y)])
# analytic dip criterion: b*(Sc(1-e^-a)-Ss) > Sc*a*e^-a
for b in [0.1,0.5,0.6,1.0,3.0]:
    crit = b*(Sc*(1-np.exp(-a))-Ss) > Sc*a*np.exp(-a)
    y=I(Sc,Ss,a,b,x); dip = y[-1] < y.max()-1e-12
    print(f"b={b}: criterion={crit}, numeric dip={dip}")
# 2) log SA Lipschitz constant: d/dtau log SA = 1/(e^t-1) - 1/t in (-1/2,0)
t=np.logspace(-6,3,200001); d=1/np.expm1(t)-1/t
print("dlogSA range:", d.min(), d.max())
# 3) OpacityBroadening numbers
tau=2.0; h=(np.log(2)-np.log1p(np.exp(-tau)))/tau; SA=(1-np.exp(-tau))/tau
print("R(2)=",np.sqrt(1/h-1)," kOpac(2)=",np.sqrt(2/SA-1), " SA^-0.54=",SA**-0.54)
# 4) Voigt enclosure width vs OL claimed accuracy at wL=wG=1
wL=wG=1.0; ol=0.5346*wL+np.sqrt(0.2166*wL**2+wG**2)
print("OL(1,1)=",ol," enclosure width=",min(wL,wG)+(0.5346+np.sqrt(0.2166)-1)*wL, " rel=",(min(wL,wG))/ol)
