# 02 — Reuse existing formal mathematics deliberately

[Plan index](README.md)

## Research method and decision

Survey date: **2026-09-15**. Public sources were searched for the four requested projects,
plasma/astronomy formalization, chemical physics, and reaction networks. Six repositories were
shallow-cloned for source inspection; their revisions are pinned below. External packages were
**not built, axiom-audited, or integrated**. Source matches are candidates, not certified drop-in
replacements. The current core remains Lean/mathlib `v4.33.1`, mathlib-only.

Use this order:

1. Reuse a theorem already in the pinned mathlib, possibly through a short domain adapter.
2. Check whether an external project's useful result has since landed in mathlib.
3. For a missing general result, consider a small attributed mathlib-compatible port or upstream
   contribution. Audit its complete proof dependencies and license; do not vendor a whole library.
4. Consider a separate external adapter target only after a successful compatibility experiment and
   an explicit dependency-policy decision. Never upgrade the production lockfile to explore a match.
5. Retain a concise local lemma when a more general abstraction makes the physics harder to read.

## Source snapshots and disposition

| Project | Inspected revision | Toolchain at revision | Best fit | Recommendation |
|---|---|---|---|---|
| [mathlib](https://github.com/leanprover-community/mathlib4/tree/v4.33.1) | Existing project pin `v4.33.1` | 4.33.1 | Analysis, finite sums, probability, convolution, fixed points | Reuse now, after exact statement comparison |
| [physlib](https://github.com/leanprover-community/physlib/tree/a542a19fddc4eb12250ab90ac6ac67965073de41) | `a542a19fddc4eb12250ab90ac6ac67965073de41` | 4.33.0 | Statistical mechanics, temperature, dimensions, physics organization | Primary alignment/upstream target; bridge experiment later |
| [SciLean](https://github.com/lecopivo/SciLean/tree/95f8119a2884e9c41f82136523bd5568ea7075c5) | `95f8119a2884e9c41f82136523bd5568ea7075c5` | 4.28.0-rc1 | Differentiable scientific programs and numerical methods | Design reference; no core dependency proposed |
| [LML](https://github.com/LeanMachineLearning/LML/tree/a6c27a7d07255891de939ee565131d5f79dbf6d4) | `a6c27a7d07255891de939ee565131d5f79dbf6d4` | 4.34.0-rc2 | Probability kernels, sequential learning, concentration tools | Optional statistical theorem search; not a spectroscopy layer |
| [DynamicalSystems](https://github.com/mcdoll/DynamicalSystems/tree/8f848e4d317138a3694b956b66560c15d669cdff) | `8f848e4d317138a3694b956b66560c15d669cdff` | 4.34.0-rc2 | ODE flows, Lyapunov/LaSalle stability | Candidate for future rate-equation dynamics, not Saha algebra |
| [crnt-lean](https://github.com/marpaia/crnt-lean/tree/99137993e729c8add247388718a22a0e0f393dab) | `99137993e729c8add247388718a22a0e0f393dab` | 4.31.0 | Mass-action kinetics and conserved quantities | Candidate for a restricted kinetics bridge |
| [Clawristotle / landau](https://github.com/Vilin97/Clawristotle/tree/67dc1cea2c192d4dd5a19d9106e8621df0dde9fb/landau) | `67dc1cea2c192d4dd5a19d9106e8621df0dde9fb` | 4.24.0 | Vlasov–Maxwell–Landau steady-state theory | Research reference; beyond immediate emission-model refactor |

Pins differ even where patch versions look close. The community
[downstream dashboard](https://leanprover-community.github.io/downstream-reports/) is a useful
compatibility signal, but it tests particular revisions and targets, not this project's combination.
Its September 14 report flagged physlib compatibility with mathlib 4.33.1; that report used a
*different physlib revision* from this snapshot. Neither the dashboard nor matching version numbers
replaces building a pinned proposed combination. Existing `docs/upstream-physlib-plan.md` remains
historical context, not proof of current compatibility.

## mathlib: near-term candidates with known source locations

These declarations were located in the installed pinned source. No replacement proof was written
in this planning pass. “Candidate” means the result exists, not that its assumptions match every use.

| Local responsibility | Existing mathlib API/source | Adapter obligations and keep/delete decision |
|---|---|---|
| Derivative bounds → perturbation bounds in `Analysis`, `PartitionLipschitz`, `SahaStability` | `Convex.norm_image_sub_le_of_norm_deriv_le`, `Mathlib/Analysis/Calculus/MeanValue.lean` | Establish convex physical interval, differentiability, uniform bound, norm/absolute-value conversion. Keep sharper domain constants and simple local wrappers |
| Iteration error and uniqueness in `SahaEquilibrium`, convergence modules | `ContractingWith.dist_le_of_fixedPoint`, `apriori_dist_iterate_fixedPoint_le`, `tendsto_iterate_fixedPoint`; `Mathlib/Topology/MetricSpace/Contracting.lean` | Establish invariant complete domain and contraction constant <1. Closed nonnegative interval/subtype can be complete; the open positive half-line is not automatically complete. Retain Saha existence, positivity, and damping estimates |
| Exponential inequalities in `Analysis` | `Real.add_one_le_exp` and standard exponential algebra | Local `exp_sub_le_mul` already uses this. A short adapter is not waste; replacing it with a much larger MVT proof may be a regression |
| Dimension exponent algebra | Standard pointwise rational vector operations and `Multiplicative` | Candidate representation `Multiplicative (BaseDimension → ℚ)` for finite bases. Prove correspondence to existing four-field structure before replacing operations; no inverse-core type change |
| Profile area normalization | `integral_convolution`, `Mathlib/Analysis/Convolution.lean` | Supply integrability, measure, continuous bilinear multiplication, and normalized factors. This supports a real Gaussian–Lorentz convolution route without first formalizing Faddeeva |
| Regression and compositional geometry | Existing finite sums / real inner-product structures | Search specific OLS normal equations and Aitchison isometry obligations. No exact imported replacement identified here; do not delete these proofs based on topic similarity |

[Mean-value source](https://github.com/leanprover-community/mathlib4/blob/v4.33.1/Mathlib/Analysis/Calculus/MeanValue.lean),
[contracting maps](https://github.com/leanprover-community/mathlib4/blob/v4.33.1/Mathlib/Topology/MetricSpace/Contracting.lean),
[convolution](https://github.com/leanprover-community/mathlib4/blob/v4.33.1/Mathlib/Analysis/Convolution.lean).

## physlib: closest physical alignment, with real representation gaps

The finite canonical-ensemble file exposes `partitionFunction_of_fintype`,
`partitionFunction_pos_finite`, `probability_nonneg_finite`, and `sum_probability_eq_one`.
These overlap the conceptual role of `Boltzmann`, but not necessarily its representation.
[Inspected finite ensemble source](https://github.com/leanprover-community/physlib/blob/a542a19fddc4eb12250ab90ac6ac67965073de41/Physlib/StatisticalMechanics/CanonicalEnsemble/Finite.lean).

A bridge must address:

- Local degeneracy weights are arbitrary positive reals. A finite microstate expansion reproduces
  integer degeneracies, not arbitrary real weights. Either restrict the bridge explicitly or use
  a weighted measure with the required equivalence proof.
- Local `kB` is an explicit parameter. physlib's temperature API uses its Boltzmann constant.
  An equality after specialization is weaker than preserving a universally quantified local API.
- `Temperature` is based on nonnegative reals, so physical results still need strict positivity.
  Type conversion alone does not discharge `T > 0`.
- Energy offsets, normalization, partition-function conventions, and finite-state assumptions must
  match before probability normalization can replace population normalization.

[Temperature source](https://github.com/leanprover-community/physlib/blob/a542a19fddc4eb12250ab90ac6ac67965073de41/Physlib/Thermodynamics/Temperature/Basic.lean)
and [dimension source](https://github.com/leanprover-community/physlib/blob/a542a19fddc4eb12250ab90ac6ac67965073de41/Physlib/Units/Dimension.lean)
provide concrete comparison targets. physlib's basis-parametric exponent representation is worth
aligning with in the separate homogeneity layer. Do not force unit-carrying quantities into the
existing inverse API.

No ready Saha or atomic line-transfer replacement was identified in the inspected source tree.
That is a bounded search result, not proof of absence from the ecosystem. Retain the local
mathlib-only Saha seed and physics proofs. A future upstream contribution should be a coherent law
and its properties, not a pile of application-specific solver certificates. Upstream submission and
maintainer communication are outside this planning task.

## SciLean: useful numerical design, different trust obligations

The inspected package includes ODE solvers and differentiation infrastructure, depends on LeanBLAS,
and configures native BLAS/C linking. Its weak-integral and GMM files contain proof placeholders.
These observations prevent assuming the entire package meets this project's axiom policy; they do
**not** prove every SciLean theorem depends on a placeholder.
[Package configuration](https://github.com/lecopivo/SciLean/blob/95f8119a2884e9c41f82136523bd5568ea7075c5/lakefile.lean),
[weak-integral source](https://github.com/lecopivo/SciLean/blob/95f8119a2884e9c41f82136523bd5568ea7075c5/SciLean/MeasureTheory/WeakIntegral.lean).

For any selected result, inspect its complete axiom closure and distinguish mathematical real
semantics from floating-point/native execution. There is no current reason to make a formal
spectroscopy library depend on an executable numerical stack merely to shorten elementary calculus.

## LML: separate probability infrastructure from the name

The source includes probability-kernel support, sequential learning, and bandit algorithms.
[Library entry point](https://github.com/LeanMachineLearning/LML/blob/a6c27a7d07255891de939ee565131d5f79dbf6d4/LeanMachineLearning.lean).
Its name does not make a mathematical probability theorem unsuitable for physics; neither does it
make the library a source of ready-made CF-LIBS uncertainty guarantees. No exact replacement for
`ExchangeableRank` or the current OLS variance chain was established. Search individual probability
results only when a real statistical theorem needs them. Keep physical noise assumptions explicit.

## DynamicalSystems and reaction networks: for actual kinetics

DynamicalSystems defines Lyapunov predicates over flows and develops stability tools.
Its `Basic/Autonomous.lean` itself says its definitions should retire in favor of mathlib:
check upstream status before inheriting another compatibility layer.
[Lyapunov source](https://github.com/mcdoll/DynamicalSystems/blob/8f848e4d317138a3694b956b66560c15d669cdff/DynamicalSystems/Stability/Lyapunov.lean),
[autonomous source](https://github.com/mcdoll/DynamicalSystems/blob/8f848e4d317138a3694b956b66560c15d669cdff/DynamicalSystems/Basic/Autonomous.lean).
A Lyapunov theorem cannot establish plasma relaxation until the rate equations, solution existence,
positive invariant state space, and Lyapunov conditions have been supplied or proved.

crnt-lean's `Network.massActionVectorField` and `conservationLaw_const_along_solution` are concrete
candidates for finite collisional-radiative networks. The latter assumes a differentiable solution
on the time interval; it does not by itself construct one.
[Mass-action definition](https://github.com/marpaia/crnt-lean/blob/99137993e729c8add247388718a22a0e0f393dab/CRNT/Kinetics/MassAction.lean),
[conservation theorem](https://github.com/marpaia/crnt-lean/blob/99137993e729c8add247388718a22a0e0f393dab/CRNT/Dynamics/ConservationLaw.lean).
The plasma bridge must account for electrons, ionization, radiation loss, and whether temperature
and electron density are fixed parameters. A closed reaction network is not automatically a laser
plume with transport and external pumping. Inspected license: MIT; preserve notices in any port.

## Astronomy, astrophysics, and materials: what the search actually found

**Relevant plasma mathematics exists.** Clawristotle's Landau development has a concrete theorem
for a positive smooth single-species steady state on a three-torus, with explicit decay and
polynomial logarithmic-gradient bounds and supplied Vlasov/Maxwell equations. It concludes a uniform
Maxwellian and restricted fields. The inspected theorem is not a proof of finite-time relaxation or
LTE for an evolving LIBS plume. Its source is more informative than a “zero sorry” headline.
[Concrete theorem](https://github.com/Vilin97/Clawristotle/blob/67dc1cea2c192d4dd5a19d9106e8621df0dde9fb/landau/Aristotle/Landau/main/CoulombConcreteTheorem42.lean).

The separate [Vlasov mean-field project](https://github.com/Hydrodynamical/Vlasov_Meanfield_Formalization)
is another research lead for kinetic limits and stability. Only its public project description was
reviewed here; toolchain, hypotheses, license, and proof closure remain unassessed. It is not an
approved dependency or replacement candidate.

physlib also contains FLRW cosmology. This is evidence of astronomy-adjacent formalization, but
cosmological expansion results do not replace line opacity, emissivity, or abundance inference.
[FLRW source tree](https://github.com/leanprover-community/physlib/tree/a542a19fddc4eb12250ab90ac6ac67965073de41/Physlib/Cosmology/FLRW).
No maintained drop-in Lean stellar spectroscopy/radiative-transfer library was established by this
search. The best near-term shared contribution is therefore a **reusable atomic-population and
radiation layer**, independent of the LIBS instrument and estimator.

For materials, [LeanChemicalTheories](https://github.com/ATOMSLab/LeanChemicalTheories) and the
[authors' chemical-physics paper](https://pubs.rsc.org/en/content/articlehtml/2024/dd/d3dd00077j)
provide precedents such as adsorption and thermodynamic modeling. The published formalization is
Lean 3.51.1. The repository discusses future Lean 4 work, but this review does not establish a
compatible Lean 4 package. Treat it as a specification/porting reference, not an installable reuse
solution. The [physics formalization archive](https://github.com/lean-phys-community/ITPsInPhysicsArchive)
is a discovery index, not proof-quality evidence.

## Required evidence before claiming successful reuse

For each replacement, record the local fully qualified declaration, exact external revision and
license, imported theorem type, adapter proof, assumptions gained/lost, required conversions,
transitive axiom set, downstream consumers, and before/after build cost. Compile under the intended
pins and replay changed proofs. Delete the old implementation only after its callers use the new
one and the compatibility policy is satisfied. No estimated percentage reduction in boilerplate is
credible before this exercise.
