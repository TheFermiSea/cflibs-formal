# Mathematical and Physical Symmetries of Gated-Delay Two-Dimensional Correlation Spectroscopy in Laser-Induced Breakdown Spectroscopy

**Master document.** This is the single source of record for the 2DCOS-LIBS work. It is
simultaneously (i) a first-draft manuscript intended for peer review and (ii) the formalization
guide for this repository: §7 and Appendix A map every algebraic result to its machine-checked
Lean 4 counterpart in `CflibsFormal/TwoDCOS.lean` and `CflibsFormal/Aitchison.lean`. Equations are
written in inline LaTeX. Provenance and the correction history are in `docs/2dcos/ERRATA.md` and
`docs/2dcos/adversarial-critique.md`.

*Author:* Brian Squires (with formal-verification companion, `cflibs-formal`).
*Target class:* methods / diagnostics (e.g. *Spectrochimica Acta Part B*, *J. Anal. At. Spectrom.*, *Appl. Spectrosc.*).

## Abstract

Traditional Calibration-Free Laser-Induced Breakdown Spectroscopy (CF-LIBS) and its multi-line
derivatives remain structurally constrained by their reliance on static, one-zone local
thermodynamic equilibrium (LTE) snapshots, exhibiting high sensitivity to uncertainties in the
free electron density (N_e) and to transient spatial–temporal gradients. Time-resolved,
gated-delay Two-Dimensional Linear Correlation Spectroscopy (2DCOS) has been proposed to bypass
these limitations, but prior formulations rested on physically inconsistent assumptions of
standardless, electron-density-free, and temperature-free quantification ("Model B"). This work
presents a mathematically rigorous deconstruction and reformulation of gated-delay 2DCOS for
laser-produced plasmas (LPPs). We prove that under a first-order, single-driver thermal cooling
model the dynamic-spectrum matrix is rank-1 to that order (separable), forcing the asynchronous
correlation matrix to be identically zero (\mathbf{\Psi} \equiv \mathbf{0}) regardless of the
signs of the individual line thermal sensitivities; physical asynchronicity therefore requires a
rank \ge 2 system driven by non-equilibrium kinetics or spatial–temporal gradients. We reframe the
standard zero-diagonal property of the asynchronous matrix as motivation to construct an
off-diagonal "butterfly" phase-lag *hypothesis* for self-absorption, and specify the
radiative-transfer simulation that would test it. We resolve prior compositional-projection errors
on the simplex \mathcal{S}^{D-1} by replacing softmax-log closure with a correct Isometric
Log-Ratio (ILR) transformation on an orthonormal basis of the clr-hyperplane (classically a Helmert
basis; the machine-checked isometry `ilr_isometry` uses the canonical `stdOrthonormalBasis` — any
orthonormal basis would serve). Distinctively, the algebraic
symmetry results reported here are **machine-verified**: they have been formalized and proved in
the Lean 4 proof assistant against the mathlib library, with proofs certified to rely only on the
standard foundational axioms (§7).

## 1. Introduction

Laser-Induced Breakdown Spectroscopy (LIBS) is an indispensable tool for rapid, in-situ
multi-elemental analysis [1, 2]. Its transition into a highly quantitative, standardless
methodology has historically been hindered by physical matrix effects [3]. To circumvent these
without matrix-matched standards, Ciucci et al. (1999) formulated the classical Calibration-Free
LIBS (CF-LIBS) algorithm [4], which operates under three assumptions:

1. **Local Thermodynamic Equilibrium (LTE):** collisional processes dominate over radiative ones,
   so electronic-state populations follow a Maxwell–Boltzmann distribution at a single temperature T.
2. **Spatial Homogeneity:** the LPP is a uniform, isothermal zone of volume V and thickness L.
3. **Optically Thin Emission:** self-absorption is negligible, so integrated line intensity is
   proportional to species number density.

Under these conditions the line-integrated emissivity I_{ki} of a transition from an upper level k
to a lower level i of species s of element \alpha is

I_{ki} = \frac{hc}{4\pi\lambda_{ki}} A_{ki} g_k \frac{N_{\alpha,s}}{U_{\alpha,s}(T)} \exp\!\left(-\frac{E_k}{k_B T}\right),

with A_{ki} the transition probability, g_k the upper-level statistical weight, E_k the
upper-level energy, U_{\alpha,s}(T) the partition function, and N_{\alpha,s} the species density.
A linear regression of the normalized log-intensities against E_k (the Boltzmann plot) yields T
from the slope and the species densities from the intercepts. Ionization stages are coupled by the
Saha–Eggert equation [5]

\frac{N_{\alpha,s+1}\,N_e}{N_{\alpha,s}} = 2\left(\frac{2\pi m_e k_B T}{h^2}\right)^{3/2}\frac{U_{\alpha,s+1}(T)}{U_{\alpha,s}(T)}\exp\!\left(-\frac{E_{\infty,\alpha,s}-\Delta E_{\infty}}{k_B T}\right),

where N_e is the free electron density and E_{\infty,\alpha,s} the ionization potential, corrected
by the ionization-potential depression \Delta E_{\infty} (Stewart & Pyatt formulation; see [5, 6]).
Absolute concentrations C_\alpha follow by enforcing the compositional closure \sum_\alpha C_\alpha = 1.

Despite its elegance, classical CF-LIBS carries two metrological bottlenecks. First, computing N_e
from the Stark-broadened FWHM of a single line (e.g. H_\alpha at 656.3 nm or isolated Ar I lines)
is highly sensitive to line blending, background, and self-absorption [7]. Second, real LPP plumes
have steep spatial–temporal thermal and density gradients; integrating over a single wide ICCD
gate collapses this kinetic history into an unphysical average and can introduce substantial
systematic composition errors in inhomogeneous matrices [5, 6]. First-principles
collisional-radiative modeling confirms the sensitivity of single-zone LTE spectra to atomic-data
and plasma-state assumptions [8].

To capture this temporal trajectory, recent work has applied 2DCOS to time-resolved, gated-delay
LIBS datasets [9]. However, prior literature asserted that 2DCOS could achieve "standardless,
electron-density-free, and temperature-free" composition retrieval ("Model B") by identifying the
asynchronous correlation with the physical three-body recombination rate. This paper deconstructs
those circular and physically invalid claims and presents a mathematically rigorous, physically
consistent, and machine-verified framework for gated-delay 2DCOS diagnostics.

## 2. Mathematical Foundation of Gated-Delay 2DCOS

Gated-delay 2DCOS maps a time-resolved sequence of m centered dynamic spectra y(\lambda, t_\ell),
collected over gate delays t_1 < t_2 < \dots < t_m, into a symmetric synchronous matrix
\mathbf{\Phi} and an antisymmetric asynchronous matrix \mathbf{\Psi} [10]. The dynamic (mean-centered)
spectrum is

y(\lambda, t_\ell) = I(\lambda, t_\ell) - \bar{I}(\lambda), \qquad \bar{I}(\lambda) = \frac{1}{m}\sum_{\ell=1}^{m} I(\lambda, t_\ell).

### 2.1 The Synchronous Matrix

The synchronous map is the sample covariance of the temporal emission profiles,

\Phi(\lambda_1,\lambda_2) = \frac{1}{m-1}\sum_{\ell=1}^{m} y(\lambda_1, t_\ell)\, y(\lambda_2, t_\ell).

It is symmetric, \Phi(\lambda_1,\lambda_2)=\Phi(\lambda_2,\lambda_1), and its diagonal is the
temporal variance of each line, \Phi(\lambda,\lambda)=\mathrm{Var}_t[I(\lambda,\cdot)]\ge 0.
*(Formalized: `syncMatrix_symm`, `syncMatrix_diag_eq_variance`, `syncMatrix_diag_nonneg`.)*

### 2.2 The Asynchronous Matrix and Noda's Hilbert Operator

The asynchronous map measures the out-of-phase temporal variation,

\Psi(\lambda_1,\lambda_2) = \frac{1}{m-1}\sum_{j=1}^{m} y(\lambda_1, t_j)\, \hat{y}(\lambda_2, t_j), \qquad \hat{y}(\lambda, t_j) = \sum_{k=1}^{m} N_{jk}\, y(\lambda, t_k),

with Noda's discrete Hilbert transformation matrix \mathbf{N}\in\mathbb{R}^{m\times m} [11]

N_{jk} = \begin{cases} 0 & j = k \\ \dfrac{1}{\pi(k-j)} & j \neq k. \end{cases}

**Standard property (antisymmetry and zero diagonal).** Since N_{jk} = -N_{kj} for j\neq k and the
diagonal is zero, \mathbf{N} is skew-symmetric, \mathbf{N}^T = -\mathbf{N}. For any single-channel
dynamic vector \mathbf{y}\in\mathbb{R}^m the diagonal element is the quadratic form
\Psi(\lambda,\lambda) = \tfrac{1}{m-1}\,\mathbf{y}^T\mathbf{N}\mathbf{y}. Because this scalar equals
its own transpose,

\mathbf{y}^T\mathbf{N}\mathbf{y} = (\mathbf{y}^T\mathbf{N}\mathbf{y})^T = \mathbf{y}^T\mathbf{N}^T\mathbf{y} = -\mathbf{y}^T\mathbf{N}\mathbf{y}.

Hence 2\,\mathbf{y}^T\mathbf{N}\mathbf{y} = 0, so \Psi(\lambda,\lambda) \equiv 0 for all \lambda.
This is a universal property of any antisymmetric operator — independent of the plasma physics or
of measurement noise. Consequently the asynchronous diagonal is identically zero under all
conditions, and any diagonal-based self-absorption indicator is unphysical (self-absorption
information, if present, must reside off-diagonal; §5). *(Formalized: `hilbertNoda_transpose_neg`,
`asyncMatrix_antisymm`, `asyncMatrix_diag_zero`, via the lemma `skew_quadForm_zero`.)*

## 3. Deconstruction of the Recombination-Flux and N_e-Elimination Fallacies

"Model B" asserted that N_e(t) could be analytically eliminated from the Saha–Boltzmann equations
by identifying the ionic–neutral asynchronous cross-peak with a three-body recombination flux,
\partial_t N_{\alpha,0}(t) = \beta(T(t))\,N_{\alpha,1}(t)\,[N_e(t)]^2. We deconstruct the three
fatal defects.

### 3.1 The Mean Value Theorem fallacy

The model applied the First Generalized Mean Value Theorem for integrals to pull the transient
[N_e(t)]^2 outside the asynchronous integral,
\Psi \approx K^{*}\,\bar{\beta}\,\bar{N}_e^{2}\int [N_{\alpha,1}(t)]^2\,dt. The theorem states only
that for continuous f and sign-definite integrable g there **exists** \tau\in(a,b) with
\int_a^b f g\,dt = f(\tau)\int_a^b g\,dt. It is an existence theorem; it provides no value for
\tau. Defining \bar{N}_e \equiv N_e(\tau) maps the time-varying N_e(t) onto an unknown,
uncomputable constant. The parameter is relabeled, not eliminated.

### 3.2 Mathematical circularity

To "solve" for \bar{N}_e, the prior framework set \int[N_{\alpha,1}(t)]^2\,dt \propto
\Phi(\lambda_{\text{ion}},\lambda_{\text{ion}}) and inverted
\bar{N}_e^2 \propto \Psi(\lambda_{\text{ion}},\lambda_{\text{atom}})/\Phi(\lambda_{\text{ion}},\lambda_{\text{ion}}).
But \Psi was *defined* in §3.1 through \Psi \propto \bar{N}_e^2\,\Phi(\lambda_{\text{ion}},\lambda_{\text{ion}});
taking the ratio merely inverts the exact relation fed in. No independent observable enters — a
tautology, not a determination.

### 3.3 The non-Wronskian nature of 2DCOS

\mathbf{\Psi} evaluates the inner product of a signal with the Hilbert transform of another,
\Psi(\lambda_1,\lambda_2) = \tfrac{1}{m-1}\mathbf{y}(\lambda_1)^T\mathbf{N}\mathbf{y}(\lambda_2). The
Hilbert transform is a non-local integral operator that shifts every frequency component by
-\pi/2; it is not a local derivative, so \mathbf{\Psi} is not a time-derivative or a Wronskian
W(f,g)=f g' - g f'. The asynchronous cross-peak therefore does not map onto the continuity
equation or a recombination population flux.

**Consequence.** 2DCOS reorganizes information; it neither creates nor destroys it. Standardless
quantitative LIBS still strictly requires independent metrological determinations of T(t) and
N_e(t) (e.g. Stark broadening [7] and Boltzmann plots [4]).

## 4. Rank-1 Separability under Single-Driver Thermodynamics

Consider the dynamic spectrum under a first-order, single-driver thermal cooling model, with all
lines responding to a common perturbation \Delta T(t_\ell) = T(t_\ell)-\bar{T}. A first-order
Taylor expansion gives

y(\lambda, t_\ell) \approx \left(\frac{\partial I(\lambda,T)}{\partial T}\right)_{T=\bar{T}}\!\Delta T(t_\ell).

Let S(\lambda,\bar{T}) \equiv (\partial \ln I/\partial T)_{\bar{T}} be the temperature sensitivity,

S(\lambda,\bar{T}) = \frac{E_k}{k_B \bar{T}^2} - \frac{3}{2\bar{T}} - \frac{U_{\alpha,s}'(\bar{T})}{U_{\alpha,s}(\bar{T})},

where the -3/(2\bar{T}) term arises from the translational T^{3/2} factor and U'(T) is the
partition-function derivative. The centered dynamic-spectrum matrix \mathbf{Y}\in\mathbb{R}^{m\times n}
then factorizes, *at this first order*, as Y_{\ell,\lambda} = d_\ell\,c(\lambda) with d_\ell = \Delta T(t_\ell) purely
temporal (\mathbf{d}\in\mathbb{R}^m) and c(\lambda) = I(\lambda,\bar{T})\,S(\lambda,\bar{T}) purely
spectral (\mathbf{c}\in\mathbb{R}^n).

### 4.1 The rank-1 separability proof

The dynamic spectrum is a rank-1 outer product, \mathbf{Y} = \mathbf{d}\,\mathbf{c}^T, so any two
channels are collinear in time, \mathbf{y}(\lambda_1) = c(\lambda_1)\mathbf{d} and
\mathbf{y}(\lambda_2) = c(\lambda_2)\mathbf{d}. The asynchronous element is

\Psi(\lambda_1,\lambda_2) = \frac{c(\lambda_1)c(\lambda_2)}{m-1}\,\big(\mathbf{d}^T\mathbf{N}\mathbf{d}\big).

Because \mathbf{N} is skew-symmetric, \mathbf{d}^T\mathbf{N}\mathbf{d} = 0, hence
\mathbf{\Psi} \equiv \mathbf{0} for all channel pairs. *(Formalized in full generality — the
statement holds for arbitrary spectral weights c(\lambda) of either sign — as
`asyncMatrix_singleDriver_zero`. Note the Lean theorem takes the rank-1 factorization as an **exact**
hypothesis and proves \mathbf{\Psi}\equiv\mathbf{0} exactly; a physical dynamic spectrum is rank-1
only to the first order above, so its \mathbf{\Psi} is generically nonzero (its magnitude is not
bounded here), not identically \mathbf{0}.)*

### 4.2 Physical implications

A sign inversion of the sensitivity (S(\lambda_i,\bar{T}) < 0, possible for low-excitation lines at
high T once the -3/(2\bar{T}) and -U'/U terms dominate) does **not** generate phase diversity. It
makes one line's temporal vector anti-parallel to another's, producing anti-correlation in the
*synchronous* map,

\Phi(\lambda_1,\lambda_2) \approx c(\lambda_1)c(\lambda_2)\,\mathrm{Var}_t[T(t)] < 0,

while the asynchronous map remains identically zero. Phase diversity is a structural (rank)
property, not a sign property: a non-vanishing \mathbf{\Psi} requires the plasma to break temporal
collinearity (rank \ge 2), via

- **decoupled ionization/recombination kinetics** (ion populations decaying on a different
  timescale than neutrals are replenished);
- **spatial–temporal thermal gradients** integrated along the line of sight (hot core and cool
  boundary cooling at different rates, making \mathbf{Y} non-separable);
- **line-specific radiative transport / self-absorption** (optical-depth variations delaying the
  escape of line-center photons — §5).

This is the correct, and machine-checked, statement of *when* 2DCOS asynchronicity carries
physical information, and it is the structural reason the "flux" identity of §3 cannot hold.

## 5. Off-Diagonal Phase-Lag Symmetry for Self-Absorption (hypothesis)

Because \Psi(\lambda_0,\lambda_0)\equiv 0, self-absorption cannot be read from the diagonal. A
physically motivated off-diagonal phase lag may nonetheless arise between a self-absorbed line's
reversed center \lambda_0 and its optically thin wings \lambda_0\pm\Delta\lambda — a genuine
rank-\ge 2 mechanism (§4.2), so a non-zero cross-peak is admissible.

### 5.1 Physical mechanism

The optical depth is highest at line center, \tau_0(t)=\int_{-L/2}^{L/2}\kappa(\lambda_0,x,t)\,dx.
At early delays, intense self-reversal flattens the center; as the outer boundary cools and thins,
the center intensity slowly recovers before final decay, whereas the optically thin wings track
the hot core and decay rapidly without boundary-layer delay. This spatial–temporal decoupling
would introduce a real phase lag between wing and center profiles and a non-zero off-diagonal
cross-peak \Psi(\lambda_0,\lambda_0\pm\Delta\lambda)\neq 0, forming a four-quadrant "butterfly"
pattern centered at (\lambda_0,\lambda_0):

```
        Asynchronous map (Ψ) near a self-absorbed line

                 λ_wing   λ_center   λ_wing
       λ_wing      0        (+)        0
     λ_center     (-)        0        (-)    ← identically zero diagonal
       λ_wing      0        (+)        0
```

**This is a conjecture, not an established result** — it has not been demonstrated in the
time-resolved 2DCOS-LIBS literature.

### 5.2 Diagnostic refinement path

We propose the dimensionless butterfly phase-diversity index

k_{\text{SA}} \equiv \frac{\big|\Psi(\lambda_0,\lambda_0+\Delta\lambda)\big|}{\sqrt{\Phi(\lambda_0+\Delta\lambda,\lambda_0+\Delta\lambda)}\;\bar{I}(\lambda_0)}.

The hypothesis must be validated by 1-D stratified radiative-transfer forward simulation (e.g. a
two-zone solution of the transfer equation, sweeping \tau_0) to test (a) whether the butterfly
pattern emerges and (b) whether k_{\text{SA}} is a monotone — and, ideally, *derived* rather than
fitted — function of the core optical depth \tau_0, before any application to measured spectra.

## 6. Statistical Rigor on the Simplex

Prior implementations projected concentrations to the simplex as \text{softmax}(\log\mathbf{x})
and called it an Isometric Log-Ratio (ILR) transform. This is algebraically incorrect.

### 6.1 The softmax identity

For positive abundances x_i>0,

\text{softmax}(\log\mathbf{x})_i = \frac{\exp(\log x_i)}{\sum_{j}\exp(\log x_j)} = \frac{x_i}{\sum_j x_j} \equiv \mathcal{C}(\mathbf{x})_i,

the Aitchison closure operator (normalization to \sum_i C_i = 1). It provides no dimension
reduction, no orthonormal basis, and is not an isometry. *(Formalized: `softmax_log_eq_closure`;
see also `closure_sum_one`, `softmax_sum_one`.)*

### 6.2 True Isometric Log-Ratio transformation

For statistically rigorous operations on \mathcal{S}^{D-1} without boundary anomalies, use a
genuine ILR (Egozcue et al. 2003) [12]:

\mathbf{z} = \text{ilr}(\mathbf{x}) = \mathbf{V}^T\,\text{clr}(\mathbf{x}) = \mathbf{V}^T\log\mathbf{x}\in\mathbb{R}^{D-1},

with \text{clr}(\mathbf{x}) = [\log(x_1/g),\dots,\log(x_D/g)]^T, g=(\prod_i x_i)^{1/D}, and
\mathbf{V}\in\mathbb{R}^{D\times(D-1)} an orthonormal basis of the clr-hyperplane satisfying
\mathbf{V}^T\mathbf{V}=\mathbf{I}_{D-1} and \mathbf{V}\mathbf{V}^T=\mathbf{I}_D-\tfrac{1}{D}\mathbf{1}\mathbf{1}^T
(the projector onto the hyperplane; this is why \mathbf{V}^T\text{clr}(\mathbf{x})=\mathbf{V}^T\log\mathbf{x},
since \mathbf{V}^T\mathbf{1}=\mathbf{0}). The inverse is \text{ilr}^{-1}(\mathbf{z})=\mathcal{C}(\exp(\mathbf{V}\mathbf{z})).
*(Machine-checked: `clr_sum_zero` (\sum_i \text{clr}(\mathbf{x})_i = 0) and now the **full isometry**
`ilr_isometry`: \|\text{ilr}(\mathbf{x})-\text{ilr}(\mathbf{y})\|=d_A(\mathbf{x},\mathbf{y}), realized via
an orthonormal-basis representation of the clr-hyperplane (`AitchisonIsometry.lean`; see Appendix A).)*

## 7. Formal Verification of the Symmetry Theorems

The algebraic results of §2.2 and §4 — the load-bearing symmetries of this framework — are not
merely asserted. They have been formalized and proved in the **Lean 4** interactive theorem prover
against **mathlib** (the community mathematics library), and the proofs are certified to depend
only on the three standard foundational axioms of the system (propositional extensionality, the
axiom of choice, and quotient soundness); in particular no unproved assumption or `sorry`
placeholder is used. This is, to our knowledge, the first machine-verified treatment of the 2DCOS
correlation algebra. Table 1 maps each claim to its formal counterpart.

**Table 1 — claims and their machine-checked Lean theorems** (repo `cflibs-formal`).

| Manuscript result | Lean theorem | Module |
|---|---|---|
| \mathbf{N}^T=-\mathbf{N} (Hilbert–Noda skew-symmetry) | `hilbertNoda_transpose_neg` | `TwoDCOS.lean` |
| \mathbf{\Phi}^T=\mathbf{\Phi} (synchronous symmetry) | `syncMatrix_symm` | `TwoDCOS.lean` |
| \Phi(\lambda,\lambda)=\mathrm{Var}_t\ge 0 | `syncMatrix_diag_eq_variance`, `syncMatrix_diag_nonneg` | `TwoDCOS.lean` |
| \mathbf{\Psi}^T=-\mathbf{\Psi} (asynchronous antisymmetry) | `asyncMatrix_antisymm` | `TwoDCOS.lean` |
| \Psi(\lambda,\lambda)\equiv 0 (zero-diagonal, §2.2) | `asyncMatrix_diag_zero` (via `skew_quadForm_zero`) | `TwoDCOS.lean` |
| rank-1 \Rightarrow \mathbf{\Psi}\equiv\mathbf{0} (§4) | `asyncMatrix_singleDriver_zero` | `TwoDCOS.lean` |
| \text{softmax}(\log\mathbf{x})=\mathcal{C}(\mathbf{x}) (§6.1) | `softmax_log_eq_closure` | `Aitchison.lean` |
| \sum \mathcal{C}(\mathbf{x})=1, \sum \text{softmax}=1 | `closure_sum_one`, `softmax_sum_one` | `Aitchison.lean` |
| \sum \text{clr}(\mathbf{x})=0 (§6.2) | `clr_sum_zero` | `Aitchison.lean` |
| \|\text{ilr}(\mathbf{x})-\text{ilr}(\mathbf{y})\|=d_A(\mathbf{x},\mathbf{y}) (ILR isometry, §6.2) | `ilr_isometry`, `ilr_inner` | `AitchisonIsometry.lean` |
| Noda cross-form antisymmetry \mathbf{B}(u,v)=-\mathbf{B}(v,u) (sequential-order sign backbone; the \mathbf{B}\to\mathbf{\Psi} bridge is not formalized) | `B_antisymm` (+ bilinearity, `B_stepDelay_pos`) | `TwoDCOSOrder.lean` |

The verification covers the mathematical *skeleton* of the framework — the symmetries and the
rank-1 vanishing theorem that discipline what 2DCOS can and cannot claim. It does **not** (and
cannot) certify the *physics*: the self-absorption butterfly (§5) is an empirical hypothesis
requiring simulation and measurement, and the plasma-kinetic content of §3 is refutation of an
unsound model, not a positive physical theorem. The value of the formal layer is precisely that it
fences the provable core from the empirical claims.

## 8. Conclusions

We have provided a mathematically rigorous, physically self-consistent, and machine-verified
deconstruction and reformulation of gated-delay 2DCOS for laser-produced plasmas. Specifically we
(1) retract the unphysical N_e-elimination, showing standardless quantitative LIBS still requires
independent T and N_e determinations; (2) prove that any first-order separable (rank-1) model
yields \mathbf{\Psi}\equiv\mathbf{0}, so a sign flip produces negative synchronous covariance but
no phase diversity, and genuine asynchronicity requires rank \ge 2 from kinetics or gradients;
(3) reframe the zero-diagonal property to motivate off-diagonal self-absorption diagnostics;
(4) formulate a testable off-diagonal "butterfly" phase-lag hypothesis with a concrete validation
route; (5) give a correct ILR projection on the clr-hyperplane (any orthonormal basis; classically Helmert); and (6) certify the
algebraic core (1)–(2), (5) in a machine-checked Lean/mathlib development. Future work is the
radiative-transfer simulation study of §5.2 and the experimental measurement of the butterfly
index k_{\text{SA}}.

## Appendix A — Formalization roadmap (repository guide)

*This appendix is the working guide for the machine-verification tasks in `cflibs-formal`. Planning
dossier: `docs/frontiers/13-2dcos-formalization.md`.*

**Modules.** `CflibsFormal/TwoDCOS.lean` (Noda correlation algebra) and `CflibsFormal/Aitchison.lean`
(compositional identities). Both are Mathlib-only. The whole spec is verified by
`lake build` + `lake exe axiom-audit --root CflibsFormal` (allowlist = {`propext`,
`Classical.choice`, `Quot.sound`}) + `lake exe runLinter CflibsFormal`.

**DONE (Milestone A — proved, axiom-clean).** All nine Milestone-A results in Table 1 (its first
nine rows; the last two rows are the Milestone-B additions below): the Hilbert–Noda
skew-symmetry, synchronous symmetry and non-negative variance diagonal, asynchronous antisymmetry,
the zero-diagonal theorem, the rank-1 ⇒ \Psi\equiv 0 theorem, the softmax=closure identity, the
closure/softmax normalization, and clr-sum-zero. Most carry a non-vacuity witness (several on
concrete small data; a few are universally-quantified sanity `example`s).

**DONE (Milestone B — since proved, axiom-clean).**
- *B — Noda sequential-order sign algebra.* Formalized in `TwoDCOSOrder.lean`: the Noda cross-form
  `B m u v = u ⬝ᵥ (N *ᵥ v)` is antisymmetric (`B_antisymm`, from \mathbf{N}^T=-\mathbf{N}) and bilinear
  (`B_add_left`/`B_smul_left`/…) — the sign backbone of the lead/lag rule (the `B`→\mathbf{\Psi}
  bridge to the asynchronous matrix itself is not formalized) — with a concrete
  non-vacuous computed sign on a step-vs-one-gate-delayed model (`B_stepDelay_pos`/`_rev_neg`). The
  physical lead/lag *interpretation* (which band changes first) remains an empirical reading layered on
  the sign — declared, not proved.
- *B/C — full ILR isometry.* Proved in `AitchisonIsometry.lean`: an orthonormal-basis representation
  of the clr sum-zero hyperplane (`ilrBasis`) gives `ilr` with `ilr_isometry`,
  \|\text{ilr}(\mathbf{x})-\text{ilr}(\mathbf{y})\|=d_A(\mathbf{x},\mathbf{y}), plus the
  inner-product-preservation companion `ilr_inner`. Uses mathlib `OrthonormalBasis.repr` (a
  `LinearIsometryEquiv`); it is proved for the canonical `stdOrthonormalBasis` (`ilrBasis`) — any
  orthonormal basis would serve, so no specific Helmert construction is required.

**REFUSED (unsound — must not be formalized).** Model B (n_e elimination / standardless /
temperature-free quantification), Model A (dynamic-temperature composition inversion), the
async-as-Wronskian-flux identity, and any energy-weighted-covariance quantification claim; the
self-absorption butterfly is an empirical hypothesis (§5), not a theorem. These are recorded, with
their refutations, in `docs/2dcos/ERRATA.md` and `docs/2dcos/adversarial-critique.md`.

## References

1. Noll R. (2012) *Laser-Induced Breakdown Spectroscopy: Fundamentals and Applications*, Springer-Verlag, Berlin.
2. Thomas J., Joshi H. C. (2023) "Review on Laser-Induced Breakdown Spectroscopy: Methodology and Technical Developments," *arXiv* 2302.13272.
3. Poggialini F., Campanella B., Cocciaro B., Lorenzetti G., Palleschi V., Legnaioli S. (2023) "Catching up on calibration-free LIBS," *J. Anal. At. Spectrom.* 38(9), 1751–1759. DOI: 10.1039/d3ja00130j.
4. Ciucci A., Corsi M., Palleschi V., Rastelli S., Salvetti A., Tognoni E. (1999) "New procedure for quantitative elemental analysis by laser-induced plasma spectroscopy," *Appl. Spectrosc.* 53(8), 960–964. DOI: 10.1366/0003702991947612.
5. Tognoni E., Cristoforetti G., Legnaioli S., Palleschi V. (2010) "Calibration-Free Laser-Induced Breakdown Spectroscopy: State of the Art," *Spectrochim. Acta B* 65(1), 1–14. DOI: 10.1016/j.sab.2009.11.006.
6. Aguilera J. A., Aragón C. (2007) "Multi-element Saha–Boltzmann and Boltzmann plots in laser-induced plasmas," *Spectrochim. Acta B* 62(5), 378–385. DOI: 10.1016/j.sab.2007.03.024.
7. Griem H. R. (1974) *Spectral Line Broadening by Plasmas*, Academic Press, New York. ISBN: 9780123028501.
8. Colgan J., Judge E. J., Kilcrease D. P., Barefield J. E. (2014) "Ab-initio modeling of an iron laser-induced plasma: comparison between theoretical and experimental atomic emission spectra," *Spectrochim. Acta B* 97, 65–73. DOI: 10.1016/j.sab.2014.04.015.
9. Narlagiri R., Soma V. R. (2021) "Two-dimensional correlation spectroscopy for signal-to-noise ratio enhancement and weak line recovery in laser-induced breakdown spectroscopy," *OSA Continuum* 4(9), 2423–2434. DOI: 10.1364/OSAC.433894.
10. Noda I., Ozaki Y. (2004) *Two-Dimensional Correlation Spectroscopy: Applications in Vibrational and Optical Spectroscopy*, John Wiley & Sons, Chichester.
11. Noda I. (2000) "Determination of Two-Dimensional Correlation Spectra Using the Hilbert Transform," *Appl. Spectrosc.* 54(7), 994–999. DOI: 10.1366/0003702001950715.
12. Egozcue J. J., Pawlowsky-Glahn V., Mateu-Figueras G., Barceló-Vidal C. (2003) "Isometric logratio transformations for compositional data analysis," *Math. Geol.* 35(3), 279–300. DOI: 10.1023/A:1023818214614.
13. Aitchison J. (1986) *The Statistical Analysis of Compositional Data*, Chapman and Hall, London. ISBN: 9780412280604.
14. Noda I. (1993) "Generalized Two-Dimensional Correlation Method Applicable to Infrared, Raman, and other Types of Spectroscopy," *Appl. Spectrosc.* 47(9), 1329–1336. DOI: 10.1366/0003702934067694.
15. de Moura L., Ullrich S. (2021) "The Lean 4 Theorem Prover and Programming Language," *CADE-28*, LNCS 12699, 625–635. DOI: 10.1007/978-3-030-79876-5_37.
16. The mathlib Community (2020) "The Lean Mathematical Library," *CPP 2020*, 367–381. DOI: 10.1145/3372885.3373824.
