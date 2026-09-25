# Mirror of the Lean constants in OuterLoopModelB.outerLoop_contracts (SI units, consistent).
import math
kB=1.380649e-23; me=9.1093837e-31; h=6.62607015e-34; eV=1.602176634e-19
chi=6.83*eV            # Ti I ionization energy
gZ=[30.0]; EZ=[0.0]    # single-level partition functions (U const): partition channels vanish
gZ1=[60.0]; EZ1=[0.0]
def U(T,g,E): return sum(gi*math.exp(-Ei/(kB*T)) for gi,Ei in zip(g,E))
def B(T): return 2*math.pi*me*kB*T/h**2
def S(T): return 2*(U(T,gZ1,EZ1)/U(T,gZ,EZ))*B(T)**1.5*math.exp(-chi/(kB*T))
def sahaLip(Tmin,Tmax):
    Ka=sum(gZ1)/U(Tmin,gZ,EZ); Kb=B(Tmax)**1.5
    Lc=chi/(kB*Tmin**2)
    Lb=(math.sqrt(B(Tmax))+B(Tmax)/(2*math.sqrt(B(Tmin))))*(2*math.pi*me*kB/h**2)
    La=(sum(g*E for g,E in zip(gZ1,EZ1))/(kB*Tmin**2))/U(Tmin,gZ,EZ)+sum(gZ1)*(sum(g*E for g,E in zip(gZ,EZ))/(kB*Tmin**2))/U(Tmin,gZ,EZ)**2
    return 2*(Ka*Kb*Lc+(Ka*Lb+Kb*La))
Ttrue=11000.0; ne_true=1e23  # 1e17 cm^-3
R=S(Ttrue)/ne_true
# neutral lines E 1..3.5 eV, ion lines (unshifted abscissa, as in the Lean model) 3..5.5 eV
En=[1.0,1.5,2.0,2.5,3.0,3.5]; Ei=[3.0,3.5,4.0,4.5,5.0,5.5]
E=[e*eV for e in En+Ei]; s=[0]*6+[1]*6
Eb=sum(E)/len(E); SS=sum((e-Eb)**2 for e in E); Kc=abs(sum((e-Eb)*si for e,si in zip(E,s)))/SS
for (Tmin,Tmax) in [(10500,11500),(10000,12000),(9000,13000)]:
    L1=sahaLip(Tmin,Tmax)/R
    nemin=S(Tmin)/R; nemax=S(Tmax)/R          # exact density range of the n_e leg on the box
    smin=1/(kB*Tmax)                          # slope floor = 1/(kB*Tmax) (T-leg must land in box)
    L2=Kc/(kB*smin**2*nemin)
    # true local derivative of the n_e leg and of the T leg at the true point
    dT=1.0; dSdT=(S(Ttrue+dT)-S(Ttrue-dT))/(2*dT)/R
    local=abs(dSdT)*(kB*Ttrue**2)*Kc/ne_true   # |dT'/dne|*|dne/dT| at fixed point
    print(f"box[{Tmin},{Tmax}] L1={L1:.3e} m^-3/K  L2={L2:.3e} K m^3  gate L1*L2={L1*L2:.1f}  "
          f"sup|S'|/R={abs((S(Tmax+1)-S(Tmax-1))/2)/R:.3e}  L1/sup|S'|={L1/(abs((S(Tmax+1)-S(Tmax-1))/2)/R):.0f}  local gain={local:.3f}")
