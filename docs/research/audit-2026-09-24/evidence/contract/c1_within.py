from types import SimpleNamespace as NS
from cflibs.inversion.physics.certificates_wiring import collect_certificate_inputs
from cflibs.inversion.physics.certificates import evaluate_certificates
# Two elements, each with two lines at the SAME upper energy (no within-element lever arm)
obs = [NS(E_k_ev=3.0, ionization_stage=1), NS(E_k_ev=3.0, ionization_stage=1),   # Fe I pair
       NS(E_k_ev=5.0, ionization_stage=1), NS(E_k_ev=5.0, ionization_stage=1)]   # Ti I pair
res = NS(temperature_K=10000.0, electron_density_cm3=1e17, quality_metrics={})
rep = evaluate_certificates(**collect_certificate_inputs(res, obs))
for r in rep.results: print(r.name, r.passed, r.value)
within = sum((e-3.0)**2 for e in (3.0,3.0)) + sum((e-5.0)**2 for e in (5.0,5.0))
print("within-element SS_E (the common-slope fit denominator):", within)
