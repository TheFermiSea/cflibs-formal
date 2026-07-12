<!--
MUTABLE WORKING DRAFT — see ./README.md and ./ERRATA.md.
Faithful transcription of the source. The source's LaTeX/math was lost in transfer and
arrived as U+FFFC (￼); those gaps are marked here as:
  ⟦MATH⟧  = a display equation whose content did not survive (re-supply needed)
  ⟦?⟧     = an inline symbol/variable whose content did not survive
Prose is preserved as given. Do NOT treat ⟦…⟧ as author intent — they are transfer holes.
-->

# Gated-Delay 2D Correlation Spectroscopy (2DCOS) for Standardless Quantitative LIBS: A Rigorous Kinetic-Thermodynamic Formulation

**Author:** Senior Research Scientist in Laser-Produced Plasmas & Spectrochemical Diagnostics
**Date:** July 10, 2026

## Abstract

Traditional Calibration-Free Laser-Induced Breakdown Spectroscopy (CF-LIBS) and its derivatives (such as the ⟦?⟧-Sigma graph method) remain structurally constrained by their reliance on static, one-zone thermodynamic snapshots. These paradigms suffer from severe error propagation cascading from unconstrained free electron density (⟦?⟧) estimation and spatial plasma inhomogeneities. This monograph establishes the comprehensive, self-consistent physical, mathematical, and computational foundation for standardless elemental quantification using time-resolved, gated-delay Two-Dimensional Linear Correlation Spectroscopy (2DCOS). By leveraging the non-equilibrium kinetic pathways of a cooling laser-induced plasma (LPP), we derive the Electron Density Elimination Model (Model B). This model analytically decouples and eliminates the ⟦?⟧ coordinate from the state equations, mapping the relaxation trajectories directly onto the Aitchison compositional simplex ⟦?⟧. We provide the mathematical proof for the zero-diagonal property of the asynchronous correlation matrix, outline a novel off-diagonal wing-to-center phase-lag signature for self-absorption diagnostics, and formulate a JAX-accelerated, auto-differentiable numerical architecture for real-time compositional inversion.

> **⚠ ERRATA [C2] — FATAL:** The elimination is illusory. §5.2 invokes the First Generalized Mean Value Theorem for Integrals, which is *existence-only* (Apostol 1974, ref 21): it guarantees a coordinate ξ exists but gives no value, so the transient n_e(t) is relabeled as an undetermined constant n_e(ξ), not removed. The subsequent "solve for n_e" tautologically inverts the §5.1 identity that itself *defined* the async signal as recombination flux. No independent measurement of n_e ever enters. See also [C1] (T hidden inside ξ).

## 1. Introduction and Spectral Bottlenecks in Classical CF-LIBS

Laser-Induced Breakdown Spectroscopy (LIBS) has emerged as a cornerstone for rapid, in-situ multi-elemental analysis across diverse geo-analytical, space exploration, and industrial metallurgical domains [1, 2]. However, the transition of LIBS into a fully quantitative, standardless tool remains a major challenge due to the physical matrix effects that distort emission lines [3].

### 1.1 The Classical CF-LIBS Formulation

To overcome matrix effects without reference curves, Ciucci et al. (1999) introduced the foundational Calibration-Free LIBS (CF-LIBS) algorithm [4]. This approach models a single, time-gated spectrum under three fundamental assumptions:

1. **Local Thermodynamic Equilibrium (LTE):** Collisional processes dominate over radiative ones, forcing the electronic state populations of any species ⟦?⟧ to follow a Maxwell-Boltzmann distribution characterized by a single electron temperature ⟦?⟧.
2. **Spatial Homogeneity:** The plasma plume is represented as a single, uniform, isothermal zone of volume ⟦?⟧ and thickness ⟦?⟧.
3. **Optically Thin Emission:** Radiative self-absorption is negligible, meaning the emitted intensity is directly proportional to the species concentration in the ablated target mass.

Under these conditions, the line-integrated intensity ⟦?⟧ of a transition from an upper energy level ⟦?⟧ to a lower level ⟦?⟧ is written as:

⟦MATH⟧

where ⟦?⟧ is the transition wavelength, ⟦?⟧ is the upper-level statistical degeneracy, ⟦?⟧ is the transition probability (Einstein coefficient), ⟦?⟧ is the upper-level excitation energy, ⟦?⟧ is the Boltzmann constant, ⟦?⟧ is a global experimental calibration factor, ⟦?⟧ is the number density of element ⟦?⟧ in ionization stage ⟦?⟧, and ⟦?⟧ is the temperature-dependent partition function [5].

By constructing a linear regression (the "Boltzmann Plot") of ⟦?⟧ versus ⟦?⟧, the plasma temperature ⟦?⟧ is retrieved from the slope (⟦?⟧), and the species partition density (⟦?⟧) is extracted from the y-intercept. The total elemental density is obtained by summing over consecutive charge states (⟦?⟧ for neutrals, ⟦?⟧ for single ions) coupled via the Saha-Eggert equation:

⟦MATH⟧

where ⟦?⟧ is the free electron density, ⟦?⟧ is the electron rest mass, and ⟦?⟧ is the first ionization potential [6]. The absolute elemental weight fractions ⟦?⟧ are finally determined by enforcing the compositional closure equation:

⟦MATH⟧

where ⟦?⟧ is the atomic weight and ⟦?⟧ is the total plasma mass density.

### 1.2 Structural Bottlenecks of Gated Snapshots

Despite its elegant simplicity, the classical CF-LIBS algorithm exhibits critical vulnerabilities in real-world applications:

- **The ⟦?⟧ Measurement Bottleneck:** Resolving the Saha equation requires an explicit, external measurement of the free electron density ⟦?⟧. This is typically estimated by measuring the Full-Width at Half-Maximum (FWHM) of a Stark-broadened line, such as the Balmer ⟦?⟧ line at ⟦?⟧ or isolated ⟦?⟧ lines [7]. When these lines are weak, blended with adjacent emission features, or self-absorbed, ⟦?⟧ determination fails, which propagates exponentially through the Saha equation and distorts the calculated ion-to-atom ratios.
- **The Isothermal Zone Error:** An expanding laser-induced plasma is a highly transient, non-isothermal hydrodynamic system featuring steep spatial and temporal gradients [8]. Integrating emissions over a single wide ICCD gate convolutes these variations, leading to systematic temperature overestimations and composition errors up to ⟦?⟧ in complex geological and high-Z matrices [9].
- **The Self-Absorption (SA) Degeneracy:** Optically thick lines undergo self-reversal, flattening the peak center and artificially suppressing the measured integrated area. Standard SA corrections are highly sensitive to small errors in temperature and line-shape modeling [10].
- **The ⟦?⟧-Sigma Graph Limitations:** The ⟦?⟧-Sigma Graph method proposed by Corsi et al. (2000) elegantly models self-absorption via the Curve of Growth (CoG) [11]:

> **⚠ ERRATA [C7] — MAJOR:** The citation [9] does not support this claim. Colgan, Judge, Kilcrease & Barefield (2014), *Spectrochim. Acta B* 97:65–73, is an ab-initio emission model of a *pure* Fe₂O₃ (single-element, moderate-Z) plasma; it studies neither matrix effects nor inhomogeneity error and reports no such % figure. Cite a real spatially-resolved / inhomogeneous-plasma CF-LIBS source for the isothermal-zone error, or drop the numeric claim.

> **⚠ ERRATA [C4] — FATAL:** Fabricated/misattributed citation. No "Corsi et al. (2000), Appl. Spectrosc. 54(4) 623–633" exists; that page range is Mullins et al., and the DOI resolves to Panne et al. (54(4) 536–547). The Cσ / CSigma-graph method is Aragón & Aguilera, *JQSRT* 149:90–102 (2014) (corrigendum JQSRT 155, 2015), building on Aguilera & Aragón (2007). Delete ref 11 and re-attribute.

  ⟦MATH⟧

  where ⟦?⟧ is the line-center optical depth. However, because ⟦?⟧-Sigma solves the radiative transfer equation using static isothermal parameters, it remains highly sensitive to local plasma fluctuations and requires complex, non-linear multi-parameter optimization loops that often suffer from parameter degeneracy (coupling of ⟦?⟧ and ⟦?⟧) [12].

> **⚠ ERRATA [C10] — MAJOR:** The supporting citation [12] cannot be confirmed to exist. No "Moon et al. (2020), Curve of Growth… *Spectrochim. Acta B* 164, 105741" is findable; the nearest real paper (Moon, Herrera, Omenetto, Smith & Winefordner, 2009, *Spectrochim. Acta B* 64:702–713) is a mirror-duplication self-absorption method, not a Curve-of-Growth T/τ fit, and does not support this degeneracy claim. Remove ref 12 or re-source to a real paper.

## 2. Gated-Delay 2DCOS: The Thermodynamic & Statistical Context

To resolve these limitations, we formulate a dynamic, time-resolved methodology. Instead of acquiring a single time-gated snapshot, we collect an array of ⟦?⟧ sequential, highly resolved emission spectra ⟦?⟧ over successive gate delays ⟦?⟧.

### 2.1 The Dynamic Ionization State Space

At any instantaneous temporal coordinate ⟦?⟧ during the time-resolved sweep, the local state populations of element ⟦?⟧ are coupled to the transient electron temperature ⟦?⟧ and density ⟦?⟧. We define the generalized Saha Ionization Partition Function Kernel ⟦?⟧ as:

⟦MATH⟧

The temperature-dependent partition functions are evaluated via explicit summation over the electronic configurations tabulated within the NIST Atomic Spectra Database (ASD v5.12) [13]:

⟦MATH⟧

The transient ionization potential depression (IPD) ⟦?⟧ is rigorously computed using the Stewart-Pyatt formulation to account for dense electrostatic shielding at early delays [14]:

⟦MATH⟧

where ⟦?⟧ is the average interionic radius and ⟦?⟧ is the plasma Debye length. This contracts the dynamic ionization stage coupling down to:

⟦MATH⟧

### 2.2 Simplex Geometry Constraints

To preserve physical conservation laws during optimization, the concentrations ⟦?⟧ must reside strictly on the Aitchison simplex manifold ⟦?⟧ [15]:

⟦MATH⟧

To bypass the boundary vulnerabilities of standard Euclidean optimization (which can produce unphysical negative concentrations), we project the unconstrained parameter space ⟦?⟧ into the simplex using the Isometric Log-Ratio (ILR) transformation [16]:

> **⚠ ERRATA [C3] — FATAL:** This is not ILR. The engine computes softmax(log x) = x/Σx, which is exactly the Aitchison **closure** operator C(x) (Aitchison 1986, ref 15) — plain re-normalization onto S^D, with no orthonormal basis, no dimension reduction, and no isometry. True ILR (Egozcue et al. 2003, ref 16) is ilr(x)=V^T·clr(x), an isometry S^D → R^{D−1}. The log and softmax's internal exp cancel identically, so `softmax(log(x))` ≡ `x/sum(x)`. Relabel as compositional closure; the metric-respecting benefits implied by "ILR" are not obtained.

⟦MATH⟧

## 3. The Non-Equilibrium Kinetic Bridge

The core physical premise of Gate-Delay 2DCOS is that the temporal decay rate of an ion and the corresponding birth rate of a neutral atom are coupled through the transient local recombination flux.

### 3.1 Three-Body Recombination Kinetics

In a rapidly cooling, highly collisional laser plasma at late delays (⟦?⟧), the destruction of singly ionized species (⟦?⟧) and the simultaneous creation of neutral atoms (⟦?⟧) is driven by collisional Three-Body Recombination:

⟦MATH⟧

The rate of change of the neutral atomic number density is governed by the differential continuity equation [17]:

⟦MATH⟧

where ⟦?⟧ is the macroscopic three-body recombination coefficient. This coefficient is governed by the Hinnov-Hirschberg electron-temperature power-law relation [18]:

⟦MATH⟧

where ⟦?⟧ is a universal quantum-mechanical coupling constant.

> **⚠ ERRATA [C6] — MAJOR:** Mislabeled physics. The three-body (e–e–ion) recombination prefactor is *classical*, not quantum-mechanical, and not universal: it carries the ion charge-state dependence (≈Z³), a Coulomb/threshold logarithm, and reduced-mass factors. The governing scaling is K_3b ∝ T_e^(−9/2) (effective α ∝ n_e·T_e^(−9/2)), from classical detailed-balance/Thomson kinetics — Mansbach & Keck, Phys. Rev. A 12:1246 (1975); confirmed in Fletcher, Guo & Rolston, PRL 99:145001 (2007). This T-dependence is precisely what makes ξ temperature-dependent (see [C1]).

## 4. Mathematical Mapping of the 2DCOS Transformation Space

Two-Dimensional Correlation Spectroscopy (2DCOS) maps a 1D spectroscopic dataset varying under an external perturbation (time-resolved decay) into a pair of 2D correlation matrices [19].

Let ⟦?⟧ represent the centered dynamic spectrum over the temporal observation interval ⟦?⟧, where the temporal mean spectrum ⟦?⟧ is defined as:

⟦MATH⟧

### 4.1 The Synchronous Map and Thermal Taylor Expansion

The synchronous correlation map ⟦?⟧ measures the in-phase covariance of the emission intensities at two distinct channels:

⟦MATH⟧

In previous works, it was incorrectly stated that the synchronous cross-peak amplitude scales with the difference in upper-level energies (⟦?⟧). We resolve this error. Because the primary driver of temporal variation in late LPPs is monotonic thermal cooling (⟦?⟧), both intensities vary in-phase (both decay together).

> **⚠ ERRATA [C20] — MAJOR (fabricated foil):** No source in the 2DCOS-or-LIBS literature actually claims the synchronous cross-peak amplitude scales with ΔE (upper-level energy difference); a Semantic Scholar/WebSearch sweep found none. This "correction" resolves an error no one made. (ΔE→T is *Boltzmann-plot* usage — a different quantity.) See ERRATA C20.

To model this, we perform a first-order Taylor expansion of the Boltzmann intensity with respect to a thermal perturbation ⟦?⟧:

⟦MATH⟧

Substituting this physical sensitivity relation into the synchronous integral yields:

⟦MATH⟧

This proves that the synchronous map acts as an energy-weighted intensity covariance space, where transitions with higher upper-level energies (⟦?⟧) naturally amplify the synchronous peak volume.

> **⚠ ERRATA [C21] — MAJOR (oversimplified):** The synchronous element ∝ (∂I_a/∂T)(∂I_b/∂T)·Var(T) — a *bilinear product* ~E_a·E_b (each weighted by its own intensity), not a monotone "higher-E amplifies." It also drops the −3/(2T) and −U′/U sensitivity terms (~⅓ the E-term at LIBS conditions), and low-E lines can flip sign — generating asynchronicity that contradicts the "in-phase" premise. See ERRATA C21.

### 4.2 The Asynchronous Map and Skew-Symmetric Hilbert-Noda Kernel

The asynchronous correlation map ⟦?⟧ measures the out-of-phase variations:

⟦MATH⟧

where the Hilbert transform ⟦?⟧ is defined via the Cauchy Principal Value (⟦?⟧) integral:

⟦MATH⟧

For a discrete, digitized dataset consisting of ⟦?⟧ gate-delay time steps, the transformation is calculated via Noda's transformation matrix ⟦?⟧ [20]:

⟦MATH⟧

**Theorem: The Skew-Symmetric Zero-Diagonal Law of the Asynchronous Matrix**

The assertion that self-absorption creates a non-zero asynchronous auto-peak (⟦?⟧) is mathematically impossible.

*Proof:* Let ⟦?⟧ represent the dynamic spectrum vector at a single wavelength channel ⟦?⟧ over ⟦?⟧ time steps. The discrete asynchronous correlation at this coordinate is a quadratic form governed by Noda's transformation matrix ⟦?⟧:

⟦MATH⟧

By definition of the elements ⟦?⟧, we have:

⟦MATH⟧

Therefore, Noda's matrix ⟦?⟧ is strictly skew-symmetric:

⟦MATH⟧

Evaluating the transpose of the scalar quadratic form ⟦?⟧:

⟦MATH⟧

Combining terms:

⟦MATH⟧

This analytical proof demonstrates that the diagonal of any asynchronous map is mathematically forced to be exactly zero under all physical conditions, including severe self-absorption or extreme measurement noise.

## 5. Derivation of the Electron Density Elimination Model (Model B)

To extract absolute concentrations without measuring ⟦?⟧, we construct an analytical bridge between the continuous temporal Wronskian of 2DCOS and the physical three-body recombination rate.

### 5.1 The Temporal Cross-Peak Wronskian

For monotonic, non-periodic relaxation profiles typical of cooling plasmas, Noda showed that the asynchronous correlation represents a temporal cross-peak Wronskian integral:

> **⚠ ERRATA [C5] — MAJOR:** Unsupported attribution. Noda's asynchronous spectrum is defined via the Hilbert-Noda transform — a nonlocal Hilbert integral, not a derivative — and reads as dissimilarity / sequential order of intensity changes (Noda 1993, ref 20; He et al.; Nagpal et al. arXiv:2010.06017, 2020). No Noda result equates it to a Wronskian ∫(f·g′−f′·g), and since the Hilbert transform is not a time-derivative, the async is not a flux. The async↔three-body-recombination-flux bridge is therefore not a mathematical identity, and it ignores hydrodynamic expansion and radiative recombination.

⟦MATH⟧

where ⟦?⟧ is the absolute optical collection factor of the spectrometer. Let ⟦?⟧ match the coordinate of an unblended ionic line, and let ⟦?⟧ match an unblended neutral atomic transition of the same element.

Because the ionic population decays rapidly at early delays while the atomic population is replenished by recombination flux, the first term under the integral dominates over the second, reducing the relation to:

⟦MATH⟧

Mapping the measured line intensities directly to the physical populations (⟦?⟧ and ⟦?⟧), and substituting the three-body recombination rate equation from Section 3.1:

⟦MATH⟧

where ⟦?⟧.

### 5.2 Decoupling via the First Generalized Mean Value Theorem

To decouple the highly transient free electron density ⟦?⟧ from the integration loop, we apply the First Generalized Mean Value Theorem for Integrals [21].

**Theorem:** If ⟦?⟧ is continuous and ⟦?⟧ is an integrable function that does not change sign on ⟦?⟧, then there exists a coordinate ⟦?⟧ such that:

⟦MATH⟧

We map our physical parameters onto this theorem:

- Let ⟦?⟧. Because species number densities are strictly non-negative real values, ⟦?⟧, satisfying the invariant sign condition.
- Let ⟦?⟧.

The theorem proves the existence of an integrated mean plasma coordinate ⟦?⟧ that allows us to extract the terms outside the integration boundary:

> **⚠ ERRATA [C2] — FATAL:** "Existence" is the whole problem. The First Mean Value Theorem for Integrals (Apostol 1974, ref 21) guarantees ∃ξ with ∫f·g = f(ξ)∫g but supplies *no value* for ξ. Extracting ⟨n_e⟩ = n_e(ξ) therefore replaces the transient function n_e(t) with an unknown constant — the unknown is renamed, not eliminated. Any numerical value later assigned to ⟨n_e⟩ comes from the assumed §5.1 kinetic identity, not from data.

⟦MATH⟧

We define these isolated coordinates as the effective mean electron density (⟦?⟧) and the effective mean recombination rate (⟦?⟧):

⟦MATH⟧

Yielding:

⟦MATH⟧

### 5.3 Substituting the Synchronous Auto-Peak Variance

We now evaluate the remaining integral ⟦?⟧. Let us analyze the exact mathematical definition of the synchronous auto-peak evaluated at the coordinate of the ionic line (⟦?⟧):

⟦MATH⟧

Expanding this using the dynamic centering formula ⟦?⟧ reveals the variance structure:

⟦MATH⟧

Using the algebraic relation ⟦?⟧:

⟦MATH⟧

For rapidly decaying transient charge states typical of the late ionic recombination timeline, the late-time population decays to zero (⟦?⟧). In this regime, the mean squared value dominates over the squared mean by a scaling factor bounded by the relaxation profile. We define the profile geometric factor ⟦?⟧ as:

⟦MATH⟧

This allows a clean, direct substitution:

⟦MATH⟧

Substituting this integral equation back into our asynchronous relation completes the elimination loop:

⟦MATH⟧

Canceling the constants ⟦?⟧ isolates the pure instrumental optical collection parameters:

⟦MATH⟧

We can now solve explicitly for the average free electron density parameter (⟦?⟧) purely in terms of 2DCOS coordinate values:

⟦MATH⟧

## 6. Construction of the Invariant No-⟦?⟧ Saha Model

We return to our total elemental population state equation, evaluated using our temporal mean representations:

⟦MATH⟧

Substituting our derived expression for the decoupled electron density ⟦?⟧ directly into the denominator of the ionization fraction:

⟦MATH⟧

Inverting the nested radical fraction simplifies the structure to a product of covariant matrices:

⟦MATH⟧

To express this framework purely in terms of measurable spectroscopic observables from our raw digital acquisition hardware, we map our absolute number densities back to the synchronous 2DCOS auto-peaks. Since the line-integrated intensity scales linearly with population, the auto-peak volume maps quadratically (⟦?⟧):

⟦MATH⟧

where ⟦?⟧ is the Invariant Multi-Element Saha-2DCOS Parameter, grouping all remaining physical constants, atomic transitions, and partition paths:

> **⚠ ERRATA [C1] — FATAL:** ξ is not a bundle of constants. The paper's own substitution chain forces ξ = S(T)·√(k_r(T)·T·optical), so ξ carries the partition functions U(T) (the "partition paths" admit this), the Saha/Boltzmann factor exp(−E_ion/kT), the T^{3/2} term, the three-body scaling k_r ∝ T_e^(−9/2), and the absolute optical collection factor. A T- and instrument-dependent ξ cannot be a precomputed constant — the engine's `xi(T)` symbol and "Precomputed" wording confirm it. The method is therefore neither temperature-free nor standardless (Saha-Eggert; Tognoni et al. 2010, ref 5; Hinnov–Hirschberg 1962, ref 18).

⟦MATH⟧

Factoring out the shared scale term and combining the radicals inside the secondary numerator yields the final Model B Matrix Composition Equation:

⟦MATH⟧

## 7. Optical Depth & Self-Absorption Diagnostics

As proven mathematically in Section 4.2, the diagonal of any asynchronous map is identically zero (⟦?⟧), rendering the classical formulation of Model C unphysical. We resolve this by deriving a physically sound spatial self-absorption signature using off-diagonal wing-to-center phase-lag correlations.

> **⚠ ERRATA [C8] — MAJOR:** Non-sequitur. A zero asynchronous diagonal is a *universal* property of Noda's antisymmetric operator, Ψ(ν,ν)=0 for *every* dynamic dataset (Noda 1993, ref 20) — it would "falsify" every model equally and discriminates nothing. "Model C" is a strawman. Keep the correct zero-diagonal proof, but conclude only that self-absorption diagnostics must use off-diagonal cross-peaks; do not claim any competing model is disproven.

### 7.1 Wing-to-Center Phase Lag Mechanics

When an emission line undergoes self-absorption, radiative transport is localized. In a typical hemispherical LPP plume, the core is extremely hot and dense, while the outer boundaries are cooler and less ionized [22].

At the resonant transition wavelength ⟦?⟧, photons emitted from the hot core are strongly re-absorbed by the cooler peripheral layer, reducing the emergent line-center intensity. However, at the optically thin wings (⟦?⟧), the absorption cross-section drops rapidly, allowing wing photons to escape without attenuation.

Because the outer boundary cools and expands at a different rate than the core, the emission profile at the line wings decays out-of-phase relative to the self-reversed line center. This temporal phase mismatch generates a non-zero asynchronous cross-peak between the center and the wings:

⟦MATH⟧

This creates a characteristic four-quadrant "butterfly" pattern in the asynchronous map around the self-absorbed line coordinate.

> **⚠ ERRATA [C9] — MAJOR:** Presented as fact, but this is an unvalidated conjecture. No time-resolved-2DCOS study of LIBS self-absorption demonstrates the butterfly signature; the only genuine 2DCOS-of-LIBS paper concerns SNR, and time-resolved self-absorption is studied via line-shape evolution (Tang et al., *Opt. Express* 27:4261, 2019), not an asynchronous four-quadrant pattern. Re-frame as a hypothesis to be tested by simulation/measurement.

### 7.2 Optical Depth Correction Protocol

The magnitude of this off-diagonal asynchronous cross-peak is monotonic to the line-center optical depth ⟦?⟧. We define the Self-Absorption Correction Factor ⟦?⟧ using the classical escape factor formulation for a homogeneous slab [23]:

⟦MATH⟧

We construct a numerical calibration function linking the wing-to-center asynchronous volume to the optical depth ⟦?⟧:

⟦MATH⟧

where ⟦?⟧ is an empirical spectrometer alignment factor. The corrected synchronous matrix (restoring the unabsorbed line-center intensity) is then recovered via:

⟦MATH⟧

## 8. Peer-Reviewed References and Bibliography

1. Noll R. (2012) *Laser-Induced Breakdown Spectroscopy: Fundamentals and Applications*, Springer-Verlag, Berlin.
2. Thomas J., Joshi H. C. (2023) "Review On Laser Induced Breakdown spectroscopy: Methodology and Technical Developments," arXiv preprint, arXiv:2302.13272.
3. Poggialini F., Campanella B., Cocciaro B., Lorenzetti G., Palleschi V., Legnaioli S. (2023) "Catching up on calibration-free LIBS," *Journal of Analytical Atomic Spectrometry*, 38(9), 1751-1759. DOI: 10.1039/d3ja00130j.
4. Ciucci A., Corsi M., Palleschi V., Rastelli S., Salvetti A., Tognoni E. (1999) "New procedure for quantitative elemental analysis by laser-induced plasma spectroscopy," *Applied Spectroscopy*, 53(8), 960-964. DOI: 10.1366/0003702991947612.
5. Tognoni E., Cristoforetti G., Legnaioli S., Palleschi V. (2010) "Calibration-Free Laser-Induced Breakdown Spectroscopy: State of the Art," *Spectrochimica Acta Part B*, 65(1), 1-14. DOI: 10.1016/j.sab.2009.11.006.
6. Salzmann D. (1998) *Atomic Physics in Hot Plasmas*, Oxford University Press, Oxford. ISBN: 9780195109306.
7. Griem H. R. (1974) *Spectral Line Broadening by Plasmas*, Academic Press, New York. ISBN: 9780123028501.
8. Cristoforetti G., De Giacomo A., Dell'Aglio M., Legnaioli S., Tognoni E., Palleschi V., Omenetto N. (2010) "Local thermodynamic equilibrium in laser-induced breakdown spectroscopy: Beyond the McWhirter criterion," *Spectrochimica Acta Part B*, 65(1), 86-95. DOI: 10.1016/j.sab.2009.11.005.
9. Colgan J., Judge E. J., Kilcrease D. P., Barefield J. E. (2014) "Ab-initio modeling of an iron laser-induced plasma: Comparison between theoretical and experimental atomic emission spectra," *Spectrochimica Acta Part B*, 97, 65-73. DOI: 10.1016/j.sab.2014.04.007.
10. Völker T., Gornushkin I. B. (2023) "Investigation of a method for the correction of self-absorption by Planck function in laser induced breakdown spectroscopy," *Journal of Analytical Atomic Spectrometry*, 38(4), 911-916. DOI: 10.1039/d2ja00352j.
11. Corsi M., Cristoforetti G., Hidalgo M., Iriarte D., Legnaioli S., Palleschi V., Salvetti A., Tognoni E. (2000) "C-sigma graphs: a new approach for plasma characterization in laser-induced breakdown spectroscopy," *Applied Spectroscopy*, 54(4), 623-633. DOI: 10.1366/0003702001949717.
12. Moon H.-Y., Smith B. W., Omenetto N., Winefordner J. D. (2020) "Curve of Growth analysis for simultaneous temperature and optical depth determination in laser-induced plasmas," *Spectrochimica Acta Part B*, 164, 105741.
13. Kramida A., Ralchenko Yu., Reader J., and NIST ASD Team (2024) *NIST Atomic Spectra Database (ver. 5.12)*, National Institute of Standards and Technology, Gaithersburg, MD. Available: https://physics.nist.gov/asd.
14. Stewart J. C., Pyatt K. D. (1966) "Lowering of ionization potentials in hot, dense plasmas," *The Astrophysical Journal*, 144, 1203. DOI: 10.1086/148714.
15. Aitchison J. (1986) *The Statistical Analysis of Compositional Data*, Chapman and Hall, London.
16. Egozcue J. J., Pawlowsky-Glahn V., Mateu-Figueras G., Barceló-Vidal C. (2003) "Isometric logratio transformations for compositional data analysis," *Mathematical Geology*, 35(3), 279-300.
17. Bultel A., Morel V., Annaloro J. (2018) "Thermochemical Non-Equilibrium in Thermal Plasmas," *Atoms*, 7(1), 5. DOI: 10.3390/atoms7010005.
18. Hinnov E., Hirschberg J. G. (1962) "Electron-ion recombination in a dense hydrogen plasma," *Physical Review*, 125(3), 795-801. DOI: 10.1103/PhysRev.125.795.
19. Noda I., Ozaki Y. (2004) *Two-Dimensional Correlation Spectroscopy: Applications in Vibrational and Optical Spectroscopy*, John Wiley & Sons, Chichester.
20. Noda I. (1993) "Generalized Two-Dimensional Correlation Spectroscopy," *Applied Spectroscopy*, 47(9), 1329-1336. DOI: 10.1366/0003702934067520.
21. Apostol T. M. (1974) *Mathematical Analysis*, Addison-Wesley, Reading, MA.
22. Zaytsev S. M., Popov A. M., Labutin T. A. (2016) "Stationary model of laser-induced plasma: Critical evaluation and applications," *Spectrochimica Acta Part B*, 118, 37-39. DOI: 10.1016/j.sab.2016.02.001.
23. El Sherbini A. M., El Sherbini T. M., Hegazy H. (2005) "Evaluation of self-absorption coefficients of aluminum emission lines in laser-induced breakdown spectroscopy measurements," *Spectrochimica Acta Part B*, 60(12), 1573-1579. DOI: 10.1016/j.sab.2005.10.005.
