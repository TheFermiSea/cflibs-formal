# Early-loaded pytest plugin: install a dimensional mutant into the pipeline BEFORE test collection.
import numpy as np
import cflibs.radiation.emissivity as em

def _mut(state, g_k, E_k_ev, T_e_eV):
    if E_k_ev > state.max_energy_ev:
        return 0.0
    # MUTANT: kT multiplied instead of divided (exp(-E*kT) instead of exp(-E/kT))
    return state.number_density_cm3 * (g_k / state.partition_function) * float(np.exp(-E_k_ev * T_e_eV))

em.upper_level_population_cm3 = _mut
