# Time-Resolved 2D Correlation Spectroscopy for LIBS: A Literature-Grounded Formulation

## Provenance & corrections

This document is a **literature-grounded rebuild** of an earlier, AI-generated draft that a
formal audit found scientifically unsound. The audit is recorded in
`docs/2dcos/ERRATA.md`; the annotated original is `docs/2dcos/monograph.md`. The central
construct of that draft — a "Model B" claiming **standardless, electron-density-free,
temperature-free** elemental quantification via gate-delay 2DCOS — was refuted on two
independent, fatal grounds (ERRATA C1, C2, C5) and has been **removed in full**. It is not
resurrected, restated as tentative, or reformulated anywhere below. Section 4.3 gives the
explicit retraction and the reasons.

Everything retained here is either (i) a **standard, cited** result of Noda 2DCOS or of
plasma spectroscopy, or (ii) a clearly-labelled **derived consequence** of such a result, or
(iii) a clearly-labelled **testable hypothesis** (never asserted as established). Fabricated
or misattributed citations from the original draft (a nonexistent "Corsi et al. 2000" Cσ
paper; a nonexistent "Moon et al. 2020" curve-of-growth paper) have been struck and replaced
with the real sources (see *References → Removed*). Every substantive claim carries a numbered
reference; every reference in the list was verified against Semantic Scholar / DOI resolution
during the rebuild, and residual verification uncertainties are stated honestly rather than
hidden.

---

## Abstract

Time-resolved (gate-delay) two-dimensional correlation spectroscopy (2DCOS), in Noda's
generalized formalism [20, 21, 19], is a **model-free, second-order statistical
re-organization** of a stack of `m` background-subtracted LIBS spectra acquired at successive
gate delays. Applied to the cooling trajectory of a laser-produced plasma (LPP), it delivers
three genuinely useful, **qualitative / preprocessing-level** capabilities: (i) denoising and
line-contrast enhancement through the synchronous autopeak diagonal `Φ(ν,ν) = Var_t[I(ν,·)]`
[27]; (ii) separation of analyte emission from background/continuum by shared response to the
perturbation [28]; and (iii) recovery of the **sequential order** in which spectral features
rise and fall during plasma relaxation, via Noda's sign rules [20, 30].

This document states plainly **what time-resolved 2DCOS does not do**. It is not a
quantification engine. It yields no absolute number densities, no weight fractions, no
electron density `n_e`, and no temperature `T`. Because the synchronous and asynchronous maps
are, respectively, the covariance and the Hilbert-transform (quadrature) covariance of the
intensity-versus-delay traces, 2DCOS introduces no new physics and **removes no unknown**.
Quantification of LIBS spectra therefore still requires the standard apparatus:
Boltzmann/Saha analysis under local thermodynamic equilibrium (LTE), an **independent** `n_e`
(typically from Stark broadening), a temperature retrieval, and either instrument calibration
or the calibration-free (CF-LIBS) closure [4, 5]. Any claim that a correlation map is
"standardless," "n_e-free," or "temperature-free" is refuted here (Section 4.3). What 2DCOS
offers LIBS is a rigorous exploratory and preprocessing tool, and a small set of clearly
labelled, still-**untested hypotheses** worth simulating and measuring — not a new
quantification law.

---

## Notation

| Symbol | Meaning |
|---|---|
| `ν, ν₁, ν₂` | spectral coordinate (wavelength / wavenumber / detector channel) |
| `t`; `t₁ < … < t_m` | perturbation variable = gate delay; the `m` sampled delays |
| `m` | number of gated spectra in the series (`m ≥ 3` for a meaningful asynchronous map) |
| `I(ν, t)` | background-subtracted line-integrated intensity |
| `Ī(ν)` | perturbation-mean (reference) spectrum |
| `ỹ(ν, t)` | dynamic (mean-centered) spectrum, `I(ν,t) − Ī(ν)` |
| `Φ(ν₁,ν₂)` | synchronous correlation (in-phase covariance) |
| `Ψ(ν₁,ν₂)` | asynchronous correlation (out-of-phase / Hilbert-transform) |
| `N_{jk}` | discrete Hilbert–Noda matrix |
| `T`, `n_e` | electron temperature, electron number density |
| `I_{ki}` | intensity of the line `k → i` (upper level `k`) |
| `F` | global optical/experimental collection factor |
| `g_k, A_{ki}, E_k` | upper-level degeneracy, Einstein `A`, upper-level energy |
| `U_s(T)` | internal partition function of species `s` |
| `N_s` | number density of species `s` (element in ionization stage `z`) |
| `S_x ≡ d(ln I_x)/dT` | per-line temperature sensitivity |
| `α, K_3b` | three-body recombination coefficient and rate constant |
| `S^D, C(x)` | Aitchison simplex; closure operator |
| `clr, ilr, V` | centered / isometric log-ratio transforms; orthonormal basis of the clr hyperplane |

---

## 1. CF-LIBS background and the real limitations of single-gate analysis

Laser-induced breakdown spectroscopy (LIBS) is a widely used method for rapid, in-situ,
multi-element analysis across geoanalytical, planetary, industrial, and environmental
settings [1, 2]. Its promise as a *quantitative, calibration-free* technique is limited by
matrix effects and by the strongly transient, spatially inhomogeneous nature of the emitting
plasma [3, 5].

### 1.1 The CF-LIBS master equation and the Boltzmann plot

For an optically thin line `k → i` of species `s` (an element in ionization stage `z`) in
LTE, the line-integrated intensity is the canonical CF-LIBS form [4, 5]:

`I_{ki} = (F / λ_{ki}) · (g_k A_{ki} / U_s(T)) · N_s · exp(−E_k / (k_B T))`

where `F` is a global collection factor (spectral efficiency, solid angle, plasma volume;
taken slowly varying), `λ_{ki}` the transition wavelength, `g_k` and `A_{ki}` the upper-level
statistical weight and Einstein coefficient, `E_k` the upper-level energy,
`U_s(T) = Σ_j g_j exp(−E_j / (k_B T))` the internal partition function (evaluated from
tabulated levels, e.g. NIST ASD [13]), and `N_s` the emitting-species number density. Taking
logarithms linearizes this into the **Boltzmann plot**:

`ln( I_{ki} λ_{ki} / (g_k A_{ki}) ) = ln( F N_s / U_s(T) ) − E_k / (k_B T)`

A least-squares fit over several lines of one species gives temperature from the slope
`−1/(k_B T)` and `N_s` (up to `F`) from the intercept. Crucially, the intercept returns `N_s`
only **relative to the calibration factor `F`**; an absolute number density needs `F`, and
coupling the neutral and ionic stages of an element needs the Saha–Eggert balance, which
carries `n_e` explicitly (Section 1.2). There is no route from this equation to composition
without either calibration or an independent `n_e`.

### 1.2 Saha–Eggert and the electron-density bottleneck

Consecutive ionization stages `z` and `z+1` in LTE are coupled by the Saha–Eggert equation
[5, 6, 38]:

`(n_{z+1} · n_e) / n_z = 2 · (U_{z+1}(T)/U_z(T)) · (2π m_e k_B T / h²)^{3/2} · exp(−E_ion^{(z)} / (k_B T))`

The leading factor `2` is the free-electron statistical weight (`g_e = 2`); the
`(2π m_e k_B T/h²)^{3/2}` factor is the inverse cube of the electron thermal de Broglie
wavelength; `E_ion^{(z)}` is the ionization energy of stage `z`, reduced by the
ionization-potential depression (Section 3.6). Because Saha carries `n_e` explicitly,
summing a stage-resolved Boltzmann result to a **total element density** requires an
**independent** `n_e` — standardly obtained from the Stark broadening of an isolated line or
of H-β [7]. This is the "`n_e` bottleneck," and it is real: when the diagnostic line is weak,
blended, or self-absorbed, the `n_e` estimate degrades and the error propagates through Saha
into the ion/atom ratio [5].

### 1.3 The real limitations of a single wide-gate snapshot

An expanding LPP is **not** a steady, uniform, isothermal source. Four concrete limitations
of the classical single-gate CF-LIBS snapshot are well documented:

- **Transience / isothermal-zone error.** `T` and `n_e` fall by large factors within the
  observation window. Integrating over a single wide ICCD gate convolves a range of
  thermodynamic states; the single retrieved `T` is a gate-weighted average biased toward the
  brighter (earlier, hotter) part of the window [5, 8].
- **Spatial inhomogeneity.** The line of sight integrates a hot, dense core and a cooler,
  less-ionized periphery. A one-zone model assigns all emission to one `(T, n_e)`; the
  residual is the inhomogeneity error, which motivated spatially/temporally resolved and
  explicitly inhomogeneous-plasma CF-LIBS treatments [5, 8]. (Detailed ab-initio spectral
  models of even a *single-element* plasma — e.g. Fe₂O₃ [9] — show how much microphysics a
  one-zone fit compresses; note [9] concerns a pure single-element sample and does **not**
  itself quantify a geological/high-Z matrix error, correcting a misattribution in the
  original draft, ERRATA C7.)
- **Self-absorption.** Optically thick lines self-reverse, suppressing the measured
  integrated area; standard corrections are sensitive to temperature and line-shape errors
  [10, 24, 25].
- **Multi-parameter degeneracy.** Curve-of-growth and Cσ-graph methods model self-absorption
  by solving the radiative-transfer problem with static isothermal parameters [11, 12], but
  the resulting nonlinear fits can couple temperature and optical depth. (The Cσ-graph method
  is correctly attributed to **Aragón & Aguilera 2014** [11], building on Aguilera & Aragón
  2007 [12]; the "Corsi et al. 2000" citation in the original draft was fabricated, ERRATA
  C4.) Stationary one-zone plasma models have themselves been critically evaluated [23].

Time-resolving the series does **not** remove any of these errors. It converts them into an
*evolution* that can be tracked and organized. That, and not any new quantification law, is
the honest premise of gate-delay 2DCOS.

---

## 2. Foundations of generalized 2D correlation spectroscopy

This section builds the correct mathematical foundation of 2DCOS for a gate-delay LIBS
series. Every equation is a standard Noda result or an elementary consequence of one.

### 2.1 The data object and the dynamic spectrum

A gate-delay experiment yields `m` background-subtracted spectra at delays `t₁ < … < t_m`,
`I(ν, t_ℓ)`, `ℓ = 1 … m`. The perturbation variable is the gate delay `t`; the physical agent
driving spectral change is the (to first order) monotonic cooling and recombination of the
decaying plasma. Define the **reference spectrum** as the perturbation-mean (the standard,
most common choice [20, 19]),

`Ī(ν) = (1/m) · Σ_{ℓ=1}^{m} I(ν, t_ℓ)`,

and the **dynamic spectrum** as the mean-centered deviation,

`ỹ(ν, t_ℓ) = I(ν, t_ℓ) − Ī(ν)`.

All correlation quantities are built from `ỹ`, so a static baseline that does not change with
delay contributes nothing. A meaningful asynchronous map requires `m ≥ 3` (the `1/(m−1)`
normalization is singular at `m = 1`; the engine guards this, ERRATA C19).

### 2.2 The synchronous map Φ (in-phase covariance)

The continuous synchronous correlation over the perturbation interval `[t_min, t_max]` is
[20]:

`Φ(ν₁, ν₂) = 1/(t_max − t_min) · ∫_{t_min}^{t_max} ỹ(ν₁, t) · ỹ(ν₂, t) dt`,

and the discrete form actually used on a sampled series [21] is

`Φ(ν₁, ν₂) = 1/(m − 1) · Σ_{ℓ=1}^{m} ỹ(ν₁, t_ℓ) · ỹ(ν₂, t_ℓ)`.

This is exactly the **sample covariance** of the two intensity-versus-delay traces (the
`1/(m−1)` is the unbiased normalization). Its standard properties:

- **Symmetric:** `Φ(ν₁, ν₂) = Φ(ν₂, ν₁)`, i.e. `Φ = Φᵀ`.
- **Nonnegative autopeaks:** `Φ(ν, ν) = Var_t[I(ν, ·)] ≥ 0` — the synchronous diagonal is the
  temporal variance of each channel, largest where the spectrum changes most over the decay.
- **Sign of a cross-peak:** `Φ(ν₁,ν₂) > 0` means the two intensities move in the **same**
  direction over the series; `< 0` means opposite directions.

The physical content of the synchronous map for a cooling plasma is derived, correctly, in
Section 3.2: it is a **bilinear product of per-line temperature sensitivities** scaled by
`Var_t(T)`, not a monotone "higher upper-level energy amplifies the peak" rule. (The original
draft's claim to "correct" a prior ΔE-scaling error is deleted: no such prior claim exists in
the 2DCOS or LIBS literature, ERRATA C20; the corrected structure is ERRATA C21.)

### 2.3 The asynchronous map Ψ and the Hilbert–Noda matrix

The asynchronous correlation correlates `ỹ(ν₁, t)` with the **out-of-phase (quadrature)**
component of `ỹ(ν₂, t)` — its Hilbert transform in the perturbation variable [21]:

`Ψ(ν₁, ν₂) = 1/(t_max − t_min) · ∫_{t_min}^{t_max} ỹ(ν₁, t) · z̃(ν₂, t) dt`,

with the Hilbert transform the Cauchy principal-value integral

`z̃(ν₂, t) = (1/π) · PV ∫_{−∞}^{∞} ỹ(ν₂, t') / (t' − t) dt'`.

The discrete determination Noda gave, and the form implemented in the engine, is

`Ψ(ν₁, ν₂) = 1/(m − 1) · ỹ₁ᵀ N ỹ₂ = 1/(m−1) · Σ_{j,k} ỹ(ν₁,t_j) N_{jk} ỹ(ν₂,t_k)`,

with the **Hilbert–Noda matrix**

`N_{jk} = 0` for `j = k`, and `N_{jk} = 1 / (π (k − j))` for `j ≠ k`.

This exact kernel — zero on the diagonal, `1/(π(k−j))` off it, correctly oriented — is Noda's
published discrete Hilbert–Noda form [21]; the audit confirmed it as the soundest element of
the original draft and it is retained unchanged (ERRATA C23).

Key properties, all standard:

- `N` is **antisymmetric**: `N_{kj} = 1/(π(j−k)) = −N_{jk}`, so `Nᵀ = −N`.
- `Ψ` is **antisymmetric**: `Ψ(ν₂,ν₁) = 1/(m−1) ỹ₂ᵀ N ỹ₁ = 1/(m−1) ỹ₁ᵀ Nᵀ ỹ₂ = −Ψ(ν₁,ν₂)`.
- **Sign of a cross-peak** encodes lead/lag (Section 2.5).

### 2.4 The zero asynchronous diagonal — a standard, universal property

For the auto-coordinate, `Ψ(ν, ν) = 1/(m−1) · ỹᵀ N ỹ` is a real quadratic form of the
antisymmetric matrix `N`, and any such form vanishes:

`ỹᵀ N ỹ = (ỹᵀ N ỹ)ᵀ = ỹᵀ Nᵀ ỹ = −ỹᵀ N ỹ ⇒ ỹᵀ N ỹ = 0`, hence `Ψ(ν, ν) = 0` for all `ν`.

This "asynchronous maps have no autopeaks" fact is **elementary, universally-known textbook
2DCOS** [20, 21]. Two corrections to the original draft follow (ERRATA C22, C8):

1. It is a **standard property**, not a novel named "law." It holds for *every* dynamic
   dataset regardless of the underlying physics, so it should be stated as a known property,
   not "proven" as a new theorem.
2. Precisely **because** it is universal, it can **falsify nothing**. Using the zero diagonal
   to declare any self-absorption model "unphysical" is a non-sequitur against a strawman. Any
   self-absorption signature must instead live in the **off-diagonal** cross-peaks — and even
   the specific "butterfly" pattern proposed for that is only a hypothesis (Section 4.2), not
   an established result.

### 2.5 Noda's sequential-order rules (and their limits)

The **combined sign** of `Φ` and `Ψ` at `(ν₁, ν₂)` encodes the temporal order in which the
two features change under the perturbation [20, 19, 30]:

1. **Direction (from Φ):** `Φ > 0` ⇒ same-direction change; `Φ < 0` ⇒ opposite-direction.
2. **Order (from Ψ read with Φ):**
   - `Φ(ν₁,ν₂) · Ψ(ν₁,ν₂) > 0` ⇒ the change at **ν₁ occurs earlier** (shorter gate delay).
   - `Φ(ν₁,ν₂) · Ψ(ν₁,ν₂) < 0` ⇒ the change at **ν₁ occurs later**.
   - `Ψ(ν₁,ν₂) = 0` ⇒ the two changes are simultaneous.

Equivalently, ν₁ precedes ν₂ iff `sign[Φ(ν₁,ν₂)] = sign[Ψ(ν₁,ν₂)]`; "earlier" means "at
shorter gate delay." A physically expected reading in an LPP decay: an ionic line and the
neutral line it feeds by recombination should show `Φ < 0` (anti-correlated), with a nonzero
`Ψ` ordering the ionic decay ahead of the neutral rise — a **qualitative, sign-level**
diagnostic of the recombination *sequence*, not a rate.

**Caveat (cyclical asynchronicity) [29].** The sequential-order rules assume an effectively
monotonic, single-directional order of events. When features evolve non-monotonically or in a
cyclical order (e.g. an ionic population that rises then falls within the window), the simple
two-event reading can *apparently* break down. LIBS decay over a single cooling window is
largely monotonic, so the rules usually apply, but overlapping rise-then-fall kinetics near
the ion→neutral crossover can violate the naïve interpretation — a real limit on how far the
sign rules can be pushed. Ordering inferences must therefore be checked against the
monotonicity assumption.

---

## 3. The cooling-plasma trajectory: transient and inhomogeneous physics

This section supplies the standard plasma physics that a gate-delay 2DCOS analysis actually
rests on. Its purpose is twofold: to make the 2DCOS signal *physically legible*, and to make
explicit **why the ion↔neutral coupling is not self-calibrating** — the recombination
coefficient that couples the stages depends on the very `T_e(t)` and `n_e(t)` any standardless
scheme would need to already know.

### 3.1 The object: a transient, inhomogeneous plasma sampled as a trajectory

A gate-delay series samples an evolving plasma, so each gate returns a spectrum drawn from a
different point on a **cooling trajectory**: `T = T(t)` falling (order ~1–2 eV early to
<0.5 eV late) and `n_e = n_e(t)` falling (order 10¹⁷–10¹⁹ cm⁻³ early to ≤10¹⁶ late). (These
ranges are order-of-magnitude orientation values, not a cited measurement.) The transience
and inhomogeneity of Section 1.3 are not removed by time-resolving; they become an evolution
to track.

### 3.2 Line temperature sensitivity — the driver of the 2DCOS signal

2DCOS keys on how each line's intensity changes as the perturbation (delay → cooling)
advances, i.e. on `∂(ln I)/∂T`. Differentiating the master equation (Section 1.1) at **fixed
emitting-stage population** `N_s` gives the clean Boltzmann core:

`S_x^{core} ≡ ∂(ln I_{ki})/∂T |_{N_s} = E_k/(k_B T²) − U_s′(T)/U_s(T)`.

The first term is the dominant, positive driver: high-`E_k` lines fall fastest as `T` drops.
Over the cooling trajectory, however, `N_s` is itself temperature-dependent, because the
ionization balance (Section 3.3) shifts population between stages. Differentiating the Saha
`T^{3/2}` factor adds a `±3/(2T)` contribution, and a compact composite quoted in the LIBS
line-sensitivity literature is [5, 32]

`S_x ≡ d(ln I_x)/dT ≈ E_k/(k_B T²) − 3/(2T) − U_s′/U_s`.

**Honest labelling (ERRATA C21).** The `−3/(2T)` is the Saha `T^{3/2}` ionization-balance
term, not an independent Boltzmann term; the exact companion ionization-energy factor and the
sign of the `3/(2T)` piece depend on which stage is tracked and whether the total-element or
stage density is held fixed. For a *neutral* line fed by a dominant ion reservoir one obtains
`(E_k − E_ion)/(k_B T²) − 3/(2T) − U_ion′/U_ion`, which can be **negative** — neutral lines
*brighten* as the plasma recombines. The load-bearing structural claim (a bilinear product of
sensitivities, with possible sign flips) is robust to this detail.

Linearizing each line about the mean temperature `T̄` (small-fluctuation limit,
`δT(t) = T(t) − T̄`), the dynamic fluctuation is `ỹ_a(t) ≈ I_a S_a δT(t)`, so the synchronous
element **factorizes** as a bilinear product of sensitivities:

`Φ(a, b) ≈ (∂I_a/∂T)(∂I_b/∂T) · Var_t(T) ≈ I_a I_b · S_a S_b · Var_t(T)`.

This is a **forward, interpretive** relation — it explains the structure of the maps under a
single cooling driver; it is **not** an inversion for `T`. Two consequences the original draft
missed: the subtracted terms (`−3/(2T)`, `−U′/U`) are non-negligible (order ⅓ of the E-term
at typical LIBS conditions), and `S_x` can **change sign** for low-`E` lines. Opposite-sign
sensitivities give `Φ(a,b) < 0` (anti-correlated lines) and can generate genuine
asynchronicity even under a single cooling driver — which directly undercuts a naïve
"everything decays in phase" premise.

*Scope of the factorization:* it assumes temperature is the single dominant driver of temporal
change and a small-fluctuation linearization. Near the ion→neutral crossover, competing
kinetics (recombination, hydrodynamic expansion) and non-monotonic populations break the
single-driver picture.

### 3.3 Saha–Eggert on the trajectory

The Saha–Eggert balance of Section 1.2 holds locally at each delay. Its structural point for
2DCOS: retrieving stage ratios `n_{z+1}/n_z` (needed to sum a stage-resolved Boltzmann result
to a total element density) **requires an independent `n_e`**, standardly from Stark
broadening [7]. This bottleneck is not removed by 2DCOS.

### 3.4 LTE validity — McWhirter is necessary, not sufficient

LTE (Maxwell–Boltzmann level populations at a single `T`, Saha ionization at that `T`) is
required for the master and Saha equations to hold. The McWhirter criterion gives a lower
bound on `n_e` for collisional rates to dominate radiative ones by ≥10× [33]:

`n_e ≥ 1.6 × 10¹² · T^{1/2} · (ΔE)³` (`n_e` in cm⁻³, `T` in K, `ΔE` the largest relevant
transition-energy gap in eV).

For a **transient, inhomogeneous** plasma this is explicitly **necessary but not sufficient**
[8]. Two further conditions must hold: (1) a **relaxation** criterion — the collisional
relaxation time must be short compared with the timescale on which `T(t)`, `n_e(t)` change (in
a fast-cooling LPP the populations can lag the falling temperature even when the density bound
is met); and (2) a **diffusion** criterion — the distance a species diffuses in a relaxation
time must be small compared with the plasma gradient scale. Passing McWhirter at one gate does
not license LTE across the whole series; late, low-density gates are the likely failure
points, and thermochemical non-equilibrium can set in [17]. This bounds how far down the
cooling trajectory a 2DCOS analysis can be physically trusted.

### 3.5 Three-body recombination — the ion→neutral coupling

The process that ties a decaying ion line to a growing neutral line late in the trajectory is
electron-driven three-body (collisional) recombination, `A⁺ + e + e → A + e`, entering the
neutral continuity equation as

`dn_a/dt = α · n_e · n_ion − (losses: re-ionization, expansion/advection, diffusion)`, with
`α = K_3b · n_e`,

so the volumetric recombination rate scales as `K_3b · n_e² · n_ion`. The **temperature
scaling** is the classical detailed-balance result

`K_3b ∝ T_e^{−9/2}`, hence `α ∝ n_e · T_e^{−9/2}`.

**Correct physical labelling (ERRATA C6, C11).** This `T_e^{−9/2}` law is a **classical**
result — it follows from detailed balance of three-body recombination against electron-impact
ionization (Thomson-type cross-section) plus Saha, and in this clean limit it predates the
collisional-radiative literature. It is **not** a "universal quantum-mechanical coupling
constant"; the prefactor carries the ion charge-state dependence (roughly `∝ Z³` for
hydrogenic ions), a Coulomb/threshold logarithm, and reduced-mass/cross-section factors.
Load-bearing sources, correctly attributed: Mansbach & Keck (1969), a classical Monte-Carlo
trajectory calculation [26]; Hinnov & Hirschberg (1962), the collisional-radiative
coefficient [18]; Stevefelt, Boulmer & Delpech (1975), the widely used collisional-radiative
fitting formula [34]; and Fletcher, Zhang & Rolston (2007), the experimental confirmation of
the `T_e^{−9/2}` scaling in an ultracold neutral plasma [35]. (Note: the original audit trail
conflated Mansbach & Keck with the 1975 Phys. Rev. A paper, which is actually Stevefelt et
al., and mislisted the 2007 middle author; both are corrected here.)

### 3.6 Ionization-potential depression (Stewart–Pyatt)

At early delays the plasma is dense enough that continuum lowering (IPD) shifts `E_ion` in
Saha. The standard closed-form interpolation is Stewart & Pyatt (1966) [14], which bridges two
limits: the **weak-coupling (Debye–Hückel)** regime,
`ΔE_ion ≈ (z+1) e² / (4πε₀ λ_D)` with `λ_D = (ε₀ k_B T / (n_e e²))^{1/2}`; and the
**strong-coupling (ion-sphere)** regime set by the average interionic radius
`R_0 = (3/(4π n_ion))^{1/3}`. Stewart–Pyatt interpolates via the ratio `R_0/λ_D`, degrading
gracefully as `n_e, T` evolve. IPD matters mainly at the earliest, densest gates; it is a
correction to `E_ion`, not an independent diagnostic.

### 3.7 Honest scope — the trajectory coupling is not self-calibrating

Collecting the above makes the boundary explicit. The ion→neutral coupling that gate-delay
2DCOS exploits runs through `α ∝ n_e · T_e^{−9/2}` (Section 3.5), whose magnitude depends on
the very `T_e(t)` and `n_e(t)` a standardless scheme would need to avoid measuring. One cannot
convert an observed ionic/neutral phase relationship into an absolute rate — and thence a
composition — without knowing (or independently measuring) the trajectory. Saha carries `n_e`
explicitly and the partition/Boltzmann factors carry `T`; the line intensity carries the
calibration `F`. Any lumped parameter that claims to "absorb" these is therefore itself a
function of `T`, `U(T)`, `E_ion`, `α(T)`, and `F` — temperature- and instrument-dependent,
hence not a precomputable constant. This is the structural reason the refuted Model B fails
(Section 4.3), stated from the physics rather than from the audit.

---

## 4. What time-resolved 2DCOS delivers for LIBS

Every claim below is tagged **ESTABLISHED**, **HYPOTHESIS**, or **RETRACTED**. The essential
framing: 2DCOS is a model-free, second-order statistical re-organization of the data. It adds
no physics; it redistributes existing variance and lead/lag information into a 2D plane for
visualization and discrimination [31]. It therefore offers LIBS qualitative and
preprocessing-level gains, never a new quantification law.

### 4.1 Established / demonstrated uses

The verifiable peer-reviewed footprint of Noda-2DCOS applied specifically to LIBS is **small
— two dedicated papers** — and every demonstrated use is qualitative or preprocessing-level.
(The project's 75-source CF-LIBS corpus contains *zero* dedicated 2DCOS-LIBS entries; this
scarcity is itself a finding.)

- **(a-1) Signal-to-noise / contrast enhancement — ESTABLISHED [27].** Narlagiri & Soma (2021)
  applied 2D correlation analysis to time-resolved LIBS of Al, Cu, brass, and Au–Ag
  bimetallics and showed that the **synchronous diagonal** `Φ(ν,ν) = Var_t[I(ν,·)]` acts as a
  denoised proxy spectrum: coherent line-intensity variation across the gate series reinforces
  on the diagonal, while ICCD noise (uncorrelated across delays) averages down. They reported
  large peak-contrast gains and improved PCA class separation. *Honest scope:* this improves
  contrast and classification, not absolute calibration.
- **(a-2) Component / background discrimination — ESTABLISHED [28].** Xue et al. (2024)
  combined high-repetition-rate LIBS with the 2D correlation method for sea-salt aerosols,
  using the pulse-train / repetition-rate response as the perturbation, and separated
  particle-related analyte emission from air-species and continuum background. This is the
  classic 2DCOS strength: grouping features by *shared response* to a perturbation. (The full
  text could not be fetched during verification; the description rests on the verified
  title/venue plus a search summary.)
- **(a-3) Sequential-order (Noda's rules) of species rise/decay — METHOD ESTABLISHED,
  LIBS-specific demonstration thin.** Noda's sequential-order rules are a rigorously
  established result of the *general* formalism [20, 30]; applied to a gate-delay LIBS series
  they rank the temporal order in which continuum, multiply-ionized, singly-ionized, and
  neutral lines fall/rise during cooling — and the expected ordering
  (continuum → higher ion stages → lower ion stages → neutrals) is independently well
  established in LIBS plasma physics. **Honest status:** no dedicated peer-reviewed LIBS study
  was found that presents this 2DCOS sequential-order analysis as its result; this is a
  well-grounded *application of an established method*, not yet an independently demonstrated
  LIBS finding, and is presented as such.
- **(a-4) A distinction, honestly drawn.** LIBS elemental *mapping* via **linear correlation
  statistics** (pixel-to-pixel Pearson correlation between element channels) is established in
  the imaging literature, but that is ordinary linear correlation — **not** Noda generalized
  2DCOS (no Hilbert-transform asynchronous spectrum, no perturbation-ordered lead/lag). A
  specific Noda-2DCOS mapping paper claimed by the original draft could not be verified; do not
  conflate co-localization mapping by linear correlation with Noda 2DCOS.

> **Summary for §4.1.** The entire *demonstrated* Noda-2DCOS-of-LIBS record is two
> qualitative/preprocessing papers (SNR [27]; component separation [28]). None performs
> quantification. Any claim beyond "denoising, discrimination, and sequential-order
> visualization" is not supported by existing literature.

### 4.2 Testable hypotheses (proposals, not results)

These are physically motivated but **unvalidated** for LIBS. Each is labelled a **HYPOTHESIS**
and paired with a concrete test. Neither is asserted as true.

- **(b-1) HYPOTHESIS — a center-vs-wing asynchronous "butterfly" as a self-absorption
  fingerprint.** *Rationale:* a self-reversed (optically thick) line center and its
  optically-thin wings evolve on different effective timescales as the plume cools and thins,
  so their dynamic intensities are partly out of phase, producing a nonzero off-diagonal
  `Ψ(ν_center, ν_wing)` with a characteristic four-quadrant sign pattern. *Status:* an
  unvalidated conjecture; no 2DCOS-LIBS self-absorption study demonstrates it, and the nearest
  real work studies time-resolved self-absorption via line-shape/intensity evolution, not an
  asynchronous butterfly [37]. *Test:* forward-model a radiative-transfer LIBS cooling series
  with and without self-absorption, compute `Ψ`, and check whether the predicted quadrant
  pattern appears and whether its amplitude is monotonic in line-center optical depth `τ₀`;
  then verify experimentally on a known thick resonance line vs. a thin line. Until then, any
  async→optical-depth calibration is an uncalibrated heuristic (the original draft's admittedly
  ad hoc "empirical spectrometer alignment factor," ERRATA C18).
- **(b-2) HYPOTHESIS — ionic-vs-neutral asynchronous cross-peaks as a QUALITATIVE
  recombination-order indicator (explicitly NOT a quantitative `n_e` probe).** *Rationale:*
  during recombination-dominated cooling, ionic decay leads neutral replenishment, so the
  *sign* of `Ψ(ion, neutral)` (via the sequential-order rule) should reflect that ordering.
  *Status:* physically motivated, unvalidated for LIBS, and strictly **qualitative**. It must
  not be read as an electron-density measurement: the asynchronous spectrum is a
  dissimilarity / lead-lag quantity, and its magnitude conflates temperature evolution,
  hydrodynamic expansion/advection, line blends, and opacity — none of which it can
  disentangle. *Test:* a collisional-radiative + hydrodynamic simulation sweeping `n_e` and
  `T_e` to check whether the async *sign* robustly tracks recombination order, and how badly
  expansion losses confound it, before any experimental claim.

### 4.3 What time-resolved 2DCOS does NOT do — explicit retraction

The original monograph's core construct — a "Model B" claiming **standardless,
electron-density-free, temperature-free** LIBS quantification by treating the gate-delay
asynchronous map as a recombination flux and "solving for `n_e`" — is **RETRACTED**. It fails
for three independent, concrete reasons (ERRATA C1, C2, C5).

- **(c-1) It does not remove the electron density.** The "decoupling" invokes the First
  Generalized Mean Value Theorem for Integrals, which is **existence-only** [22]: it guarantees
  some coordinate `ξ` with `∫ f·g = f(ξ)∫g` but supplies **no value** for `ξ`. The transient
  `n_e(t)` is therefore merely **relabeled** as an undetermined constant `n_e(ξ)`, not removed.
  The subsequent "solve for `n_e`" only closes by *inverting the very identity that defined*
  the asynchronous signal as a recombination flux — a tautology returning the assumed `n_e`.
  No independent measurement of `n_e` ever enters. The claim to "eliminate the electron
  density" is thus false.
- **(c-2) The asynchronous spectrum is not a recombination flux.** Noda's asynchronous map is
  a **Hilbert transform** — a nonlocal principal-value integral operator, not a time
  derivative — whose accepted reading is *dissimilarity / sequential order* of intensity
  changes [20, 21]. It is **not** a `∫(f·g′ − f′·g)` "Wronskian" and not a flux. Because the
  Hilbert transform is not a derivative, the claimed `async ↔ three-body-recombination-flux`
  bridge is **not a mathematical identity**; it also silently discards hydrodynamic expansion
  and radiative recombination, which dominate neutral birth/loss in a real expanding plume.
- **(c-3) It does not remove the temperature dependence.** All `T`-dependence survives, hidden
  inside the lumped parameter. Tracing the draft's own substitution chain, the "invariant"
  parameter is forced to be `ξ = S(T)·√(k_r(T)·T·optical)`, carrying the partition functions
  `U(T)`, the Saha/Boltzmann factor `exp(−E_ion/(k_B T))`, the `T^{3/2}` term, the three-body
  scaling `k_r ∝ T_e^{−9/2}`, and the absolute optical/rate calibration [5, 18]. A `T`- and
  instrument-dependent `ξ` cannot be a precomputed constant; the method still requires an
  independent temperature determination and absolute calibration — trading a measurable
  unknown (`n_e` via Stark broadening) for an unmeasured `ξ(T)`, arguably worse than classical
  CF-LIBS. Hence the method is neither "temperature-free" nor "standardless."

**What genuinely survives (positive residual).** The zero asynchronous diagonal `Ψ(ν,ν) = 0`
is a correct, universal property (Section 2.4) — but precisely because it holds for *every*
dataset it cannot falsify any physical model, so it does not render any competing
self-absorption model "unphysical" (ERRATA C8). The discrete Hilbert–Noda kernel is
implemented correctly (ERRATA C23). The SNR/discrimination/sequential-order uses of Section
4.1 are real. **Net:** time-resolved 2DCOS is a legitimate qualitative, model-free exploratory
and preprocessing tool for LIBS — denoising, component separation, and lead/lag ordering — and
is not a route to electron-density-independent or temperature-independent elemental
quantification.

---

## 5. Compositional data: closure versus a correct ILR

LIBS finally reports an elemental composition — a vector of positive fractions that sum to a
constant. Such data live on the **Aitchison simplex**, and how one transforms them for
statistics or optimization matters. This section corrects a fatal mislabeling in the original
draft (ERRATA C3) and states the correct constructions. It is deliberately **agnostic about
how the composition vector was obtained**; it neither uses nor rehabilitates any part of the
refuted Model B.

### 5.1 The simplex and closure

The `D`-part simplex is `S^D = { x ∈ ℝ^D : x_i > 0, Σ_i x_i = κ }` for a constant `κ` (e.g. 1
or 100%). The **closure operator** `C(y) = y / Σ_j y_j` is *only* a renormalization onto the
simplex [15]: it applies no metric correction, changes no dimension, and is the appropriate
**last step for reporting** a composition that must sum to 1.

### 5.2 clr and the correct ILR

The **centered log-ratio** is `clr(x) = log(x) − mean(log x) = ln(x / g(x))`, with `g(x)` the
geometric mean [15]. It maps `S^D` isometrically onto the hyperplane
`H = { u ∈ ℝ^D : Σ_i u_i = 0 }`, but that image is still `D`-dimensional with one redundant
linear relation (rank `D−1`), i.e. rank-deficient for unconstrained optimization.

The **isometric log-ratio** repairs this. Pick an orthonormal basis `V` (a `D × (D−1)` matrix
with `VᵀV = I` and `1ᵀV = 0`) of `H`; then

`ilr(x) = Vᵀ clr(x) ∈ ℝ^{D−1}`,

an **isometry** `S^D → ℝ^{D−1}` that strictly reduces dimension [16]. It preserves the
Aitchison distance, `‖ilr(x) − ilr(y)‖ = ‖clr(x) − clr(y)‖ = d_A(x, y)`, directly from `V`'s
orthonormality, with inverse `ilr⁻¹(z) = C(exp(V z))` (from `clr⁻¹(u) = C(exp(u))`). Standard,
non-fabricated constructions of `V` include Gram–Schmidt, the classical Helmert contrast
sub-matrix, and sequential-binary-partition ("balances") bases [36]. All rotation-invariant
statistics (Aitchison distance, PCA eigenvalues) are basis-independent; only the
per-coordinate interpretation changes with `V`.

### 5.3 The correction: `softmax(log x)` is closure, not ILR

The original draft computed `softmax(log x)` and called it an ILR transform. Algebraically,

`softmax(log x)_i = exp(log x_i) / Σ_j exp(log x_j) = x_i / Σ_j x_j = C(x)_i`,

because the outer log and softmax's internal exp cancel exactly. This is plain Aitchison
**closure** `C(x)`, **not** ILR: it has no orthonormal basis, no `D → D−1` reduction, no
isometry, and it stays simplex-constrained. The metric-respecting benefits ILR would confer
(Aitchison-metric-respecting gradients, subcompositional coherence) are therefore **not**
obtained by that operation. This is decidable by algebra alone.

| property | closure `C(x)` | ILR `Vᵀ clr(x)` |
|---|---|---|
| output space | simplex `S^D` | unconstrained `ℝ^{D−1}` |
| orthonormal basis required | no | yes |
| dimension reduction | none (`D → D`) | `D → D−1` |
| isometry (Aitchison metric) | no | yes |
| suitable for unconstrained optimization/statistics | no | yes |
| suitable for final Σ=1 reporting | yes | (map back first) |

### 5.4 Practical recipe and non-claims

*Recipe for a LIBS composition vector:* use **closure once for reporting** (final Σ=1
fractions); use **ILR coordinates for any optimization, inference, or cross-sample
comparison** that must respect Aitchison geometry; map back via `ilr⁻¹` only at the reporting
step. *Non-claims:* this coordinate-geometry fix says nothing about, and does not
rehabilitate, the refuted Model B, the accuracy of the underlying elemental fractions, or any
self-absorption / asynchronous-2DCOS diagnostic. It is purely a correct treatment of
compositional coordinates.

---

## 6. Computational architecture (brief)

The corrected engine (`docs/2dcos/rebuild/twodcos_engine.py`, NumPy-only, float64 throughout)
implements only the **legitimate, model-free** analyses of Sections 2 and 5, and
**deliberately omits** the Model B inversion. Its surface:

- `dynamic_spectrum(spectra_matrix)` → `(ỹ, Ī)`: mean-centering (Section 2.1); requires
  `m ≥ 2`, with a warning below `m = 3` for the asynchronous map (ERRATA C19).
- `hilbert_noda_matrix(m)` → `N`: the exact `N_{jk} = 0 (j=k)`, `1/(π(k−j))` otherwise kernel
  (Section 2.3; ERRATA C23), antisymmetric by construction.
- `synchronous_matrix(ỹ)` → `Φ`: sample covariance `1/(m−1) · ỹᵀỹ`, explicitly symmetrized to
  clean floating-point matmul asymmetry.
- `asynchronous_matrix(ỹ)` → `Ψ`: `1/(m−1) · ỹᵀ N ỹ`, explicitly antisymmetrized with an
  exactly-zeroed diagonal (Section 2.4).
- `sequential_order(Φ_ij, Ψ_ij)` → lead/lag code: Noda's `sign(Φ)·sign(Ψ)` rule (Section 2.5),
  with the cyclical-asynchronicity caveat [29] documented in-code.
- `synchronous_autopeak_diagnostic(Φ, noise_variance=None)` → `Φ(ν,ν)` (and an optional SNR
  ratio if an independent noise variance is supplied): the denoising/contrast diagnostic of
  Narlagiri & Soma [27], explicitly labelled an S/N *diagnostic*, not a quantification.
- Compositional utilities `closure`, `clr`, `clr_inv`, `helmert_basis`, `ilr`, `ilr_inv`,
  `aitchison_distance`: closure and ILR kept as **separate, correctly-named** functions
  (Section 5), precisely so the closure↔ILR conflation cannot recur.

The class name that made the original module fail to parse (`2DCOSMetrics`, an invalid Python
identifier) is corrected (`TwoDCOSMetrics`/`TwoDCOSResult`, ERRATA M2). There is **no
`process_gated_delay_2dcos` / `solve for n_e` path**: the module returns correlation maps,
sequential-order readings, an SNR diagnostic, and correct compositional coordinates. Any
elemental quantification downstream must come from the standard LIBS apparatus (Boltzmann/Saha
with an independent `n_e` and a temperature retrieval, plus calibration or the CF-LIBS
closure), not from these maps. The original draft's JAX-accelerated auto-differentiable
framing is legitimate *only* for these sound analyses (and for gradients through a standard
CF-LIBS fit expressed in ILR coordinates); it confers nothing on the removed inversion.

---

## 7. Limitations and open questions

**Established limitations.**

1. **2DCOS is qualitative for LIBS.** It yields sequential order and correlated/anti-correlated
   line groupings, not concentrations, `n_e`, or `T`. Quantification still needs Boltzmann/Saha,
   an independent `n_e` (Stark), a temperature retrieval, and calibration or CF-LIBS closure
   [4, 5, 7].
2. **The single-driver factorization is a linearization.** `Φ(a,b) ≈ I_a I_b S_a S_b Var_t(T)`
   holds only when temperature is the dominant driver and fluctuations are small; competing
   kinetics and non-monotonic populations near the ion→neutral crossover break it (Section 3.2).
3. **Sequential-order rules assume monotonicity.** Cyclical/non-monotonic kinetics can make the
   sign rules apparently break down [29]; ordering inferences must be checked against the
   monotonicity assumption.
4. **LTE is not guaranteed across the series.** McWhirter is necessary but not sufficient for a
   transient, inhomogeneous plasma; late, low-density gates are the likely LTE-failure points
   [8, 17].
5. **The demonstrated 2DCOS-LIBS literature is thin** — two dedicated qualitative papers [27,
   28]; the sequential-order application, though method-sound, lacks a dedicated LIBS
   demonstration.

**Open questions / testable hypotheses (not results).**

- Does a center-vs-wing asynchronous "butterfly" reliably fingerprint self-absorption, and is
  its amplitude monotonic in optical depth? (Section 4.2, b-1; test by radiative-transfer
  forward model then experiment [37].)
- Does the *sign* of `Ψ(ion, neutral)` robustly track recombination order across realistic
  `n_e, T_e` sweeps, and how badly do expansion losses confound it? (Section 4.2, b-2; test by
  collisional-radiative + hydrodynamic simulation.)
- Can 2DCOS-derived line groupings *organize* the transient/inhomogeneity structure well enough
  to reduce the isothermal-zone bias of a downstream, physically standard CF-LIBS retrieval —
  as a preprocessing aid, not a replacement for the physics? (Open; requires controlled
  reference samples.)

**Verification caveats carried forward from the foundations.** A few reference-level
uncertainties are stated honestly: the exact volume/page/DOI of Noda (2007) "sequential order
rules" [30] were not independently confirmed (author/title/venue are); the Aragón & Aguilera
(2008) review DOI [32] and the McWhirter (1965) book-chapter attribution [33] are
high-confidence from standard bibliography but were not fully resolver-verified; and the Xue
et al. (2024) volume number [28] was corroborated by search rather than a rendered publisher
page. None of these affects a load-bearing scientific claim.

---

## References

*Verified against Semantic Scholar and/or DOI resolution during the rebuild. Entries 1–28 are
the core corrected bibliography; entries 29–38 are additional verified sources cited by the
foundations, each with its honest confidence flag. Corrections relative to the original draft
are marked [FIXED]/[ADDED].*

1. Noll R. (2012) *Laser-Induced Breakdown Spectroscopy: Fundamentals and Applications*.
   Springer-Verlag, Berlin. ISBN 978-3-642-20668-2.
2. Thomas J., Joshi H. C. (2023) "Review on Laser-Induced Breakdown Spectroscopy: Methodology
   and Technical Developments." arXiv:2302.13272 (also *Applied Spectroscopy Reviews*, DOI
   10.1080/05704928.2023.2187817).
3. Poggialini F., Campanella B., Cocciaro B., Lorenzetti G., Legnaioli S., Palleschi V. (2023)
   "Catching up on Calibration-Free LIBS." *J. Anal. At. Spectrom.* 38(9):1751–1759. DOI
   10.1039/D3JA00130J.
4. Ciucci A., Corsi M., Palleschi V., Rastelli S., Salvetti A., Tognoni E. (1999) "New
   Procedure for Quantitative Elemental Analysis by Laser-Induced Plasma Spectroscopy." *Appl.
   Spectrosc.* 53(8):960–964. DOI 10.1366/0003702991947612.
5. Tognoni E., Cristoforetti G., Legnaioli S., Palleschi V. (2010) "Calibration-Free
   Laser-Induced Breakdown Spectroscopy: State of the Art." *Spectrochim. Acta B* 65(1):1–14.
   DOI 10.1016/j.sab.2009.11.006.
6. Salzmann D. (1998) *Atomic Physics in Hot Plasmas*. Oxford University Press. ISBN
   978-0-19-510930-6.
7. Griem H. R. (1974) *Spectral Line Broadening by Plasmas*. Academic Press. ISBN
   978-0-12-302850-1. (Stark broadening for independent `n_e`.)
8. Cristoforetti G., De Giacomo A., Dell'Aglio M., Legnaioli S., Tognoni E., Palleschi V.,
   Omenetto N. (2010) "Local Thermodynamic Equilibrium in Laser-Induced Breakdown
   Spectroscopy: Beyond the McWhirter Criterion." *Spectrochim. Acta B* 65(1):86–95. DOI
   10.1016/j.sab.2009.11.005.
9. Colgan J., Judge E. J., Kilcrease D. P., Barefield J. E. (2014) "Ab-initio Modeling of an
   Iron Laser-Induced Plasma: Comparison Between Theoretical and Experimental Atomic Emission
   Spectra." *Spectrochim. Acta B* 97:65–73. DOI 10.1016/j.sab.2014.04.015 [FIXED DOI]. *Scope
   note:* a pure single-element Fe₂O₃ ab-initio spectral-modeling study; it does **not**
   support any geological-matrix or high-Z composition-error claim (ERRATA C7).
10. Völker T., Gornushkin I. B. (2023) "Investigation of a Method for the Correction of
    Self-Absorption by Planck Function in Laser Induced Breakdown Spectroscopy." *J. Anal. At.
    Spectrom.* 38(4):911–916. DOI 10.1039/D2JA00352J.
11. Aragón C., Aguilera J. A. (2014) "CSigma Graphs: A New Approach for Plasma Characterization
    in Laser-Induced Breakdown Spectroscopy." *J. Quant. Spectrosc. Radiat. Transf.*
    149:90–102. DOI 10.1016/j.jqsrt.2014.07.026 (corrigendum *JQSRT* 155, 2015). [ADDED —
    replaces the fabricated "Corsi et al. 2000," ERRATA C4.]
12. Aguilera J. A., Aragón C. (2007) "Multi-element Saha–Boltzmann and Boltzmann Plots in
    Laser-Induced Plasmas." *Spectrochim. Acta B* 62(4):378–385. DOI 10.1016/j.sab.2007.03.024.
    [ADDED — the Cσ conceptual precursor.]
13. Kramida A., Ralchenko Yu., Reader J., and NIST ASD Team (2024) *NIST Atomic Spectra
    Database* (ver. 5.12). NIST, Gaithersburg, MD. https://physics.nist.gov/asd.
14. Stewart J. C., Pyatt K. D. (1966) "Lowering of Ionization Potentials in Plasmas." *Astrophys.
    J.* 144:1203. DOI 10.1086/148714. [FIXED title — "hot, dense" qualifier removed, ERRATA C12.]
15. Aitchison J. (1986) *The Statistical Analysis of Compositional Data*. Chapman and Hall,
    London.
16. Egozcue J. J., Pawlowsky-Glahn V., Mateu-Figueras G., Barceló-Vidal C. (2003) "Isometric
    Logratio Transformations for Compositional Data Analysis." *Math. Geol.* 35(3):279–300. DOI
    10.1023/A:1023818214614.
17. Bultel A., Morel V., Annaloro J. (2019) "Thermochemical Non-Equilibrium in Thermal
    Plasmas." *Atoms* 7(1):5. DOI 10.3390/atoms7010005. [FIXED year — 2019, ERRATA C13.]
18. Hinnov E., Hirschberg J. G. (1962) "Electron-Ion Recombination in Dense Plasmas." *Phys.
    Rev.* 125(3):795–801. DOI 10.1103/PhysRev.125.795. [FIXED title — "hydrogen" removed, ERRATA
    C11.]
19. Noda I., Ozaki Y. (2004) *Two-Dimensional Correlation Spectroscopy: Applications in
    Vibrational and Optical Spectroscopy*. John Wiley & Sons, Chichester. DOI 10.1002/0470012404.
20. Noda I. (1993) "Generalized Two-Dimensional Correlation Method Applicable to Infrared,
    Raman, and Other Types of Spectroscopy." *Appl. Spectrosc.* 47(9):1329–1336. DOI
    10.1366/0003702934067694 [FIXED DOI and title, ERRATA C15]. Load-bearing for the
    Hilbert–Noda formalism.
21. Noda I. (2000) "Determination of Two-Dimensional Correlation Spectra Using the Hilbert
    Transform." *Appl. Spectrosc.* 54(7):994–999. DOI 10.1366/0003702001950472. [ADDED — the
    explicit Hilbert-transform formulation.]
22. Apostol T. M. (1974) *Mathematical Analysis* (2nd ed.). Addison-Wesley, Reading, MA.
    (*Reminder, ERRATA C2:* supports only the existence-only Mean Value Theorem — it does not
    license any "elimination" of `n_e`.)
23. Zaytsev S. M., Popov A. M., Labutin T. A. (2019) "Stationary Model of Laser-Induced Plasma:
    Critical Evaluation and Applications." *Spectrochim. Acta B* 158:105632. DOI
    10.1016/j.sab.2019.06.002. [FIXED year/volume/DOI, ERRATA C16.]
24. El Sherbini A. M., El Sherbini T. M., Hegazy H., Cristoforetti G., Legnaioli S., Palleschi
    V., Pardini L., Salvetti A., Tognoni E. (2005) "Evaluation of Self-Absorption Coefficients of
    Aluminum Emission Lines in Laser-Induced Breakdown Spectroscopy Measurements." *Spectrochim.
    Acta B* 60(12):1573–1579. DOI 10.1016/j.sab.2005.10.011 [FIXED DOI + full 9-author byline,
    ERRATA C17].
25. Bulajić D., Corsi M., Cristoforetti G., Legnaioli S., Palleschi V., Salvetti A., Tognoni E.
    (2002) "A Procedure for Correcting Self-Absorption in Calibration Free-Laser Induced
    Breakdown Spectroscopy." *Spectrochim. Acta B* 57(2):339–353. DOI
    10.1016/S0584-8547(01)00398-6. [ADDED — real self-absorption source replacing the fabricated
    "Moon et al. 2020."]
26. Mansbach P., Keck J. (1969) "Monte Carlo Trajectory Calculations of Atomic Excitation and
    Ionization by Thermal Electrons." *Phys. Rev.* 181:275–290. DOI 10.1103/PhysRev.181.275.
    [ADDED — the real Mansbach & Keck paper; the "Phys. Rev. A 12:1246 (1975)" cited in the
    original audit is actually Stevefelt et al., ref. 34.]
27. Narlagiri L. M., Soma V. R. (2021) "Improving the Signal-to-Noise Ratio of Atomic
    Transitions in LIBS Using Two-Dimensional Correlation Analysis." *OSA Continuum*
    4(9):2423–2441. DOI 10.1364/OSAC.426995; arXiv:2103.13585. [ADDED — real 2DCOS-LIBS S/N
    paper.]
28. Xue B., Wang Z., Zhu T., Gu Y., Sun W., Chen C., Li Z., Riedel J., You Y. (2024) "High
    Repetition-Rate Laser-Induced Breakdown Spectroscopy Combined with Two-Dimensional
    Correlation Method for Analysis of Sea-Salt Aerosols." *Spectrochim. Acta B* 221:107048. DOI
    10.1016/j.sab.2024.107048. [ADDED — real 2DCOS-LIBS component-separation paper; volume
    corroborated by search.]
29. Noda I. (2006) "Cyclical Asynchronicity in Two-Dimensional (2D) Correlation Spectroscopy."
    *J. Mol. Struct.* 799(1–3):41–47. DOI 10.1016/j.molstruc.2005.12.060. (Sequential-order
    rules and their cyclical-order breakdown; DOI verified via Crossref/ADS.)
30. Noda I. (2007) "'Sequential Order' Rules in Generalized Two-Dimensional Correlation
    Spectroscopy." *Anal. Chem.* (Author/title/venue verified; exact volume/page/DOI **not**
    independently confirmed — honest caveat.)
31. Park Y., Noda I., Jung Y. M. (2024) "Diverse Applications of Two-Dimensional Correlation
    Spectroscopy (2D-COS)." *Appl. Spectrosc.* (Authoritative review co-authored by Noda;
    verified via Semantic Scholar.)
32. Aragón C., Aguilera J. A. (2008) "Characterization of Laser Induced Plasmas by Optical
    Emission Spectroscopy: A Review of Experiments and Methods." *Spectrochim. Acta B*
    63(9):893–916. DOI 10.1016/j.sab.2008.05.010. (Per-line temperature-sensitivity structure;
    DOI moderate confidence.)
33. McWhirter R. W. P. (1965) "Spectral Intensities," in Huddlestone R. H., Leonard S. L. (Eds.),
    *Plasma Diagnostic Techniques*, Academic Press, New York, pp. 201–264. (Original McWhirter
    LTE criterion; standard secondary attribution.)
34. Stevefelt J., Boulmer J., Delpech J.-F. (1975) "Collisional-Radiative Recombination in Cold
    Plasmas." *Phys. Rev. A* 12(4):1246. DOI 10.1103/PhysRevA.12.1246. (Widely used
    collisional-radiative fitting formula; verified.)
35. Fletcher R. S., Zhang X. L., Rolston S. L. (2007) "Using Three-Body Recombination to Extract
    Electron Temperatures of Ultracold Plasmas." *Phys. Rev. Lett.* 99:145001. DOI
    10.1103/PhysRevLett.99.145001. (Experimental confirmation of `T_e^{−9/2}`; middle author is
    X. L. Zhang — corrects a "Guo" mis-listing in the original audit.)
36. Egozcue J. J., Pawlowsky-Glahn V. (2005) "Groups of Parts and Their Balances in Compositional
    Data Analysis." *Math. Geol.* 37(7):795–828. DOI 10.1007/s11004-005-7381-9. (Supplementary —
    sourcing the sequential-binary-partition/"balances" basis of §5.2.)
37. Tang Z. et al. (2019) time-resolved self-absorption in LIBS, *Opt. Express* 27:4261. (Nearest
    real work to the butterfly hypothesis of §4.2; **non-2DCOS**, cited only as the closest
    existing study.)
38. Griem H. R. (1997) *Principles of Plasma Spectroscopy*. Cambridge University Press. (Standard
    text for Saha/LTE; specific edition/pages not machine-verified.)

### Removed (fabricated / non-existent — do not resurrect)

- **"Corsi M. et al. (2000), 'C-sigma graphs…,' *Appl. Spectrosc.* 54(4):623–633, DOI
  10.1366/0003702001949717."** Confirmed non-existent (ERRATA C4). The title belongs to Aragón &
  Aguilera 2014 (ref. 11); the DOI resolves to an unrelated Panne et al. paper. Replaced by
  refs. 11–12.
- **"Moon H.-Y., Smith B. W., Omenetto N., Winefordner J. D. (2020), 'Curve of Growth
  analysis…,' *Spectrochim. Acta B* 164:105741."** Confirmed non-existent (ERRATA C10). Replaced
  by real self-absorption sources (refs. 24, 25).

---

*Integrity statement.* This rebuild asserts no standardless, electron-density-independent, or
temperature-independent LIBS quantification anywhere. Time-resolved 2DCOS is presented, per the
verified literature, as a qualitative, model-free correlation and preprocessing tool
(denoising, component separation, sequential-order visualization), plus two clearly labelled
testable hypotheses. The refuted "Model B" and its mean-value-theorem `n_e`-elimination,
"Wronskian"/flux reading of the asynchronous map, and `softmax(log x)`-as-ILR mislabeling have
been removed and are discussed only where explicitly retracted or corrected.
