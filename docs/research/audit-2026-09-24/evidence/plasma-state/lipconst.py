# Compare SahaStability.sahaFactorLipConst (as defined at SahaStability.lean:500) with the true
# sup |dS/dT| on a box, using production-DB levels below the IP (sharp cutoff). Units: kB=1, T in eV,
# S in cm^-3; c = 2*pi*me*kB/h^2 in cm^-2/eV so that c^1.5 = SAHA/2.
import sqlite3, math
SAHA=6.03713e21; c=(SAHA/2)**(2/3)
con=sqlite3.connect("file:/home/brian/code/CF-LIBS-improved/ASD_da/libs_production.db?mode=ro",uri=True)
def levels(el,sp):
    ip=con.execute("select ip_ev from species_physics where element=? and sp_num=?",(el,sp)).fetchone()[0]
    rows=con.execute("select g_level,energy_ev from energy_levels where element=? and sp_num=?",(el,sp)).fetchall()
    return [(g,e) for g,e in rows if e is not None and g and e<ip], ip
def U(lv,T): return sum(g*math.exp(-e/T) for g,e in lv)
def S(l0,l1,chi,T): return 2*U(l1,T)/U(l0,T)*(c*T)**1.5*math.exp(-chi/T)
def lipconst(l0,l1,chi,Tmin,Tmax):
    B=lambda T:c*T; U0=U(l0,Tmin); sg1=sum(g for g,_ in l1)
    sgE1=sum(g*e for g,e in l1); sgE0=sum(g*e for g,e in l0)
    return 2*(sg1/U0*B(Tmax)**1.5*(chi/Tmin**2)
      +(sg1/U0*((math.sqrt(B(Tmax))+B(Tmax)/(2*math.sqrt(B(Tmin))))*c)
        +B(Tmax)**1.5*(sgE1/Tmin**2/U0+sg1*(sgE0/Tmin**2)/U0**2)))
Tmin,Tmax=0.8,1.2
for el in ["Fe","Ti","Al","Ca","V"]:
    l0,chi=levels(el,1); l1,_=levels(el,2)
    n=400; Ts=[Tmin+(Tmax-Tmin)*i/n for i in range(n+1)]
    true=max(abs(S(l0,l1,chi,Ts[i+1])-S(l0,l1,chi,Ts[i]))/(Ts[i+1]-Ts[i]) for i in range(n))
    L=lipconst(l0,l1,chi,Tmin,Tmax)
    print(f"{el}: levels I={len(l0)} II={len(l1)}  true sup|dS/dT|={true:.3e}  sahaFactorLipConst={L:.3e}  overestimate x{L/true:.2e}")
print("--- candidate tight constant: S(Tmax)*(3/(2Tmin) + (chi + <E1>(Tmax))/Tmin^2) (valid when EZ<=chi, S monotone)")
def meanE(lv,T): return sum(g*e*math.exp(-e/T) for g,e in lv)/U(lv,T)
for el in ["Fe","Ti","Al","Ca","V"]:
    l0,chi=levels(el,1); l1,_=levels(el,2)
    n=400; Ts=[Tmin+(Tmax-Tmin)*i/n for i in range(n+1)]
    true=max(abs(S(l0,l1,chi,Ts[i+1])-S(l0,l1,chi,Ts[i]))/(Ts[i+1]-Ts[i]) for i in range(n))
    Lt=S(l0,l1,chi,Tmax)*(1.5/Tmin+(chi+meanE(l1,Tmax))/Tmin**2)
    Lmax=S(l0,l1,chi,Tmax)*(1.5/Tmin+(chi+max(e for _,e in l1))/Tmin**2)
    print(f"{el}: tight/true = {Lt/true:.2f}   (with max E1 instead of <E1>: {Lmax/true:.2f})")
