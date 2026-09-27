# Line-to-continuum ratio: repo's reduced form vs the form obtained by substituting the repo's own
# Saha law (Saha.sahaFactor) for n_{z+1}/n_z inside Continuum's "B".
import math
chi, Ek, hnu, ne = 7.9, 4.0, 3.0, 1e17        # eV, eV, eV (lambda~413 nm), cm^-3
SAHA = 6.037e21                                 # 2(2 pi m_e/h^2)^1.5 in cm^-3 eV^-1.5
U0 = U1 = 1.0
def S(T): return SAHA * (U1/U0) * T**1.5 * math.exp(-chi/T)
def R_spec(T):   # Continuum.lineToContRatio with B=1, a=(Ek-hnu)/kB
    return math.sqrt(T) * math.exp(-(Ek - hnu)/T)
def R_saha(T):   # [n_z e^{-Ek/T}/U0] / [n_e n_{z+1} e^{-hnu/T}/sqrt T], n_{z+1}=n_z S/n_e
    return (math.exp(-Ek/T)/U0) / (ne * (S(T)/ne) * math.exp(-hnu/T) / math.sqrt(T))
for T in (0.6, 0.8, 1.0, 1.2, 1.5):
    print(f"T={T:4.2f} eV  spec={R_spec(T):.4e}  saha-substituted={R_saha(T):.4e}")
