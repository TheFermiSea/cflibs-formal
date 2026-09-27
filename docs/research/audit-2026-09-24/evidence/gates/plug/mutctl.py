# Positive control: a grossly wrong population (drops the Boltzmann factor) must be caught.
import cflibs.radiation.emissivity as em
def _bad(state, g_k, E_k_ev, T_e_eV):
    return state.number_density_cm3 * (g_k / state.partition_function)
em.upper_level_population_cm3 = _bad
