import CflibsFormal.MatrixIonizationCoupling
open CflibsFormal
-- Two elements with different Saha factors (S_s = 1, S_t = 2), equal totals (Ntot = 1):
-- the ratio of their NEUTRAL (emitting-stage) densities -- what a homologous neutral pair
-- measures -- changes when the shared n_e moves 1 -> 2, i.e. an n_e shift DOES perturb
-- a homologous-pair subcomposition read on element totals.
example : sahaNeutralDensity 1 1 1 / sahaNeutralDensity 2 1 1
    ≠ sahaNeutralDensity 1 1 2 / sahaNeutralDensity 2 1 2 := by
  norm_num [sahaNeutralDensity]
