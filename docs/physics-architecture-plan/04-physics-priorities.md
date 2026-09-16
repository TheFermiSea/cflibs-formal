# 04 — Prioritize physical equation chains

[Plan index](README.md)

These are proposed scientific work packages, not claims that the missing theorems exist. Existing
laws and conventions come from the source modules and their literature ledgers. Before adding a
new physical claim, locate its exact equation in a primary source and record the assumptions;
this architecture review does not promote unverified citations.

## Priority order

| Priority | Chain | Why it belongs here | Completion evidence |
|---|---|---|---|
| P0 | Finite atomic levels → partition → populations → line emission | Common foundation for laboratory and astronomical spectra | One canonical definition per quantity; normalization, positivity, convention bridge, nondegenerate witness |
| P0 | Saha factors → ion-stage balance → charge neutrality → electron-density equilibrium | Plasma closure needed by composition recovery | Explicit stage truncation, conservation, existence/uniqueness, iteration distinguished from physical equilibration |
| P0 | Emissivity/opacity → transfer → line observable | Connects plasma state to what instruments observe | Defined geometry and source function; thin/thick/domain limits; photon/energy conventions |
| P1 | Gaussian/Lorentz profiles → broadening → Stark/Doppler diagnostics | Current width formulas need a clearer profile-level foundation | Normalized profiles, convolution obligations, FWHM definition, approximate formula boundaries |
| P1 | Element totals → number fractions → mass fractions → material-composition assumptions | Materials interpretation requires more than normalized intensities | Explicit masses and conversion; distinguish plume composition from bulk material |
| P1 | Measurement perturbations → conditional inverse stability | Protect existing practical value | No confusion between deterministic envelopes, stochastic variance, and model error |
| P2 | Finite rate equations → positivity/conservation → steady states → relaxation | Extends the reduced non-LTE model with actual dynamics | Rates and invariant state space specified; existence and convergence independently justified |
| P2 | Depth/time aggregation and diagnostic bias | Real measurements integrate nonuniform evolving states | Weighting and integration declared; cancellation assumptions and counterexamples retained |
| P3 | Microscopic Saha derivation, kinetic limits, broader material thermodynamics | Valuable deeper foundations, larger research cost | A concrete spectroscopy consumer and bounded statement before new infrastructure |

P0 means organize and audit existing material first. P1–P3 are separately scoped theorem work
following the mechanical migration. Do not combine missing science with moves of established proofs.

## A. Atomic populations and ionization

Begin with the finite-level weighted partition already used by `Boltzmann`. State whether a level
weight is a physical integer degeneracy or a generalized positive weight; finite truncation must
remain visible. Record excitation energies relative to the relevant ion-stage ground state.

The first complete readable slice should exhibit population normalization, nonnegativity, emission,
and the nondegenerate line-pair temperature result. Add energy-origin invariance and truncation-error
results only as new theorem tasks after checking what the current corpus already supplies.

For Saha, distinguish three layers:

1. **Law:** current factor with stage partitions, ionization energy, electron factor, thermal bracket.
2. **Plasma balance:** conservation and charge neutrality under the selected ion-stage model.
3. **Numerical iteration:** a particular damped map converges to the equilibrium under stated bounds.

Convergence of a numerical fixed-point algorithm is not time evolution of the plasma. The existing
two-stage equilibrium is not arbitrary multi-stage ionization. An extension must account for all
included charges and prove its own positivity, normalization, and solvability.

## B. Radiation and transport

Organize `ForwardMap`, `ForwardMapEnergy`, `OpticalDepth`, `SelfAbsorption`, `EquivalentWidth`, and
`RadiativeTransferDepth` around explicitly named observables. A source function, integrated line
strength, spectral radiance, and detector count are not interchangeable `ℝ` values merely because
their algebra looks similar.

For the transfer model, state propagation direction, optical-depth orientation, boundary intensity,
zone ordering, scattering exclusions, and whether the source function is supplied or physically
constructed. Preserve both discrete-zone and continuous-integral results. A future differential
transfer-equation bridge must establish regularity before differentiating the formal solution.

Acceptance examples: zero optical depth returns the boundary signal where the definition supports
that extension; a uniform source recovers the existing slab result; reversing zones with different
source functions need not preserve intensity. Never state a converse such as “uniform output implies
isothermality” from a one-way uniform-source theorem.

## C. Line profiles and widths

The current `gaussQuadrature` algebra does not establish convolution of profiles (GAP-01).
A suitable independent work package is:

1. Choose the spectral coordinate and define normalized Gaussian and Lorentzian profiles.
2. State positive widths and prove integrability, positivity, and unit area.
3. Reuse mathlib Gaussian/convolution results where available; prove the missing representation
   bridge and Gaussian variance addition.
4. Define FWHM through half-maximum points and connect it to the width parameter.
5. Derive `gaussQuadrature` for Gaussian components; retain a separate degenerate-width convention.
6. Define Voigt via real convolution and prove basic normalization. A Faddeeva API can be useful
   later, but is not a prerequisite to defining convolution or proving area properties.
7. Keep empirical Voigt-width fits and Gaussian-only deconvolution outside exact profile identities.

A wavelength-space Gaussian is generally a narrow-line modeling approximation to transformed
frequency-space data; a nonlinear coordinate change requires its Jacobian. Do not silently promote
an approximate Doppler coordinate treatment into an exact transport theorem.

## D. Materials and composition

Retain closure and Aitchison geometry as mathematical support. In the physical narrative identify
whether fractions are number, mole, or mass fractions. A mass-fraction extension needs atomic masses
and a normalization proof; it cannot reuse a number-fraction result without a conversion theorem.

The composition inferred for emitting material is not automatically the original solid composition.
Stoichiometric ablation, representativeness, missing species, phase segregation, and matrix effects
must be assumptions or explicit error sources. `TemporalEvolution` already exposes common dilution;
use it as an example of honest material-to-plasma scope. Defer adsorption or solid-state theory
unless a specific measurement interpretation requires it.

## E. Non-LTE and shared astronomy needs

Preserve the existing two-level steady-state departure model. The next useful physical extension is
a finite rate network with clear collisional and radiative terms, not a universal plasma simulator.
Prove conservation of the chosen closed population, positivity, and an equilibrium characterization
before promising relaxation. Separate fixed-temperature/fixed-electron-density kinetics from a
coupled energy/charge model. Necessary LTE criteria do not establish LTE.

The most useful astronomy overlap is atomic populations, line ratios, opacity, source functions,
equivalent widths, and abundance inference. Extract reusable laws without embedding LIBS-specific
`Fcal`, gate schedules, or certificate formats in them. Cosmology and orbital mechanics are not
priorities solely because their formalizations exist. The surveyed kinetic libraries are deeper
research references, not evidence of LTE for this experiment.

## F. Inference stays downstream

Keep the strongest current conditional results: identifiability, deterministic stability, noise
propagation, and certificates. Stop adding generic optimizer or statistical results without a named
physical model and observable that needs them. Every work package should answer: **which physical
conclusion becomes justified, and which assumption remains supplied?**
