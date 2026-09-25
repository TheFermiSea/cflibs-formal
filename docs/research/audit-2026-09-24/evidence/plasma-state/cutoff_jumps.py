# Size of the discontinuities of a sharp n_e-dependent (Debye-Hueckel) level cutoff in U(T, n_e):
# as n_e rises, levels with E in [ip - dchi(n_e), ip) drop out one by one.
import sqlite3, math
k=8.617333e-5
con=sqlite3.connect("file:/home/brian/code/CF-LIBS-improved/ASD_da/libs_production.db?mode=ro",uri=True)
def dchi(ne,T): return 0.0660*math.sqrt((ne/1e17)*(1e4/T))
T=11000; kT=k*T
for el in ["Ca","Na","K","Al","Mg","Ti","Fe"]:
    ip=con.execute("select ip_ev from species_physics where element=? and sp_num=1",(el,)).fetchone()[0]
    lv=[(g,e) for g,e in con.execute("select g_level,energy_ev from energy_levels where element=? and sp_num=1",(el,)) if e is not None and g and e<ip]
    U=lambda cut: sum(g*math.exp(-e/kT) for g,e in lv if e<cut)
    lo,hi=ip-dchi(1e18,T),ip-dchi(1e16,T)
    crossing=[(g,e) for g,e in lv if lo<=e<hi]
    jumps=[g*math.exp(-e/kT)/U(ip) for g,e in crossing]
    print(f"{el} I: levels crossing cutoff for ne in [1e16,1e18] at 11kK: {len(crossing)}; "
          f"largest single jump in U = {100*max(jumps,default=0):.2f}%; total U change {100*(1-U(lo)/U(hi)):.1f}%")
