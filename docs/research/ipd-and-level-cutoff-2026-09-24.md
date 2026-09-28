# IPD model and partition-function level cutoff for LIBS plasmas: research memo

**Date:** 2026-09-24. **Status:** research memo for the owner's decision. Nothing here is decided and
nothing is committed. **Scope:** (1) the ionization-potential-depression (IPD) model used as the
CF-LIBS-improved default, and (2) the partition-function level-cutoff policy. Conditions: n_e
1e15–1e18 cm⁻³, T 0.5–2 eV, stages I–III, geology and alloy element sets.

**Evidence tags.** `[read]` means I opened the primary text this session and located the quoted
equation or sentence. `[secondary]` means the claim comes from a paper I read that describes the
primary; the primary itself was not opened. `[abstract]` and `[snippet]` mean only an abstract or a
search snippet was seen. `[read-SA]` and `[read-SB]` mean one of the two literature sub-agents read
the full text this session; "checked" means I also viewed the page. `[verified-file]` means the
source is in `docs/citation-whitelist.tsv` or in the `cflibs-literature` memory. Unless a sentence is marked as inference ("I infer" / "my
computation"), it reports what the cited source states.

---

## 1. Executive summary

1. **IPD default: Debye–Hückel with electron and ion screening (DH-ei).** Δχ_z = z e²/λ_D, λ_D⁻² = 4πe²(n_e+Σz_i²n_i)/kT, z = charge after ionization (II→III: 2Δχ₁). It is the standard DH chemical-potential result (Piron 2023 eq. 57–59, re-derived in §3.2), the form every retrieved LIBS/laser-plasma paper that prints an IPD formula uses (Griem 1962; ions in λ_D wherever λ_D is defined), the weak limit of SP, EK and Lin, and the removed 3e-8 formula. No retrieved source supports the current electron-only form.
2. **Stewart–Pyatt: not the default, keep it as a sensitivity arm.** Its XFEL/Orion failures are at Γ = 2–50,000 (LIBS ≤ 0.46) and do not transfer. But LIBS sits in SP's crossover (λ_D/R₀ = 0.6–3.8, SP = 0.70–1.00 × DH-ei). SP depends on the charge-state distribution, falls outside the formal √n_e family, and its own recipe deletes levels at the lowered limit.
3. **Cutoff: make U continuous in n_e and decouple it from Δχ.** Hummer–Mihalas occupation probabilities (HHL94 fit) are the physics candidate. A fixed cutoff at the unperturbed IP is the baseline (the inverse already uses it). Let PAS choose. Retire the moving sharp cutoff, which makes U jump discontinuously in n_e. HM88 says of cutoff procedures generally that they are "not physically related to a 'lowering of the ionization potential'", which argues for decoupling the cutoff from Δχ.
4. **Consistency matters more than either choice.** U_I differs ×1.05–4 across policies for Ca/Na/K/Al I (R1-02; sub-agent calc: Na I 9.9 → 4.7 from fixed to HM at 1 eV / 1e17). Using different U in the Boltzmann and Saha steps of one solver passes that factor straight into the ionic term. With one consistent policy, the choice moves an element's total only by f_I·Δln U_I: ≤ 1.4% at ≤ 1e17 / 1 eV, up to 5–12% for Na/K/Ca/Mg/Al at 1e18 (§5.3). The effect is element-specific, so it survives closure. The IPD choice moves the reported n_e (×1.001–1.25 for DH-e → DH-ei, ×1.03 at 1e17 / 1 eV) but reaches composition only through stage III or a Stark-anchored n_e. The Saha–Boltzmann offset n_e does not depend on the cutoff.
5. **Key uncertainty.** LIBS is marginally weakly coupled (N_D 0.6–5 and Γ up to 0.46 at ≥ 1e17 cm⁻³ with ≤ 1 eV), where the models differ by 10–40%. Crowley's static-vs-thermodynamic IPD dispute is unresolved, HHL94 is outside its fit range in that corner, and no LIBS paper tests any of it. So: one `PopulationContext`, forward = inverse, and the coefficient treated as a bounded nuisance.

---

## 2. Models

Notation (Gaussian units): e² = 1.439965×10⁻⁷ eV·cm. λ_De = (kT/4πn_e e²)^½ = 743.4 (T_eV/n_e)^½ cm.
R₀ = (3/4πN_i)^⅓. Γ = e²/(a kT) with a = (3/4πn_e)^⅓. N_D = (4π/3) n_e λ_De³. z is the charge of the
ion produced (1 for I→II, 2 for II→III). The "family" column asks whether Δχ = c·z·(n_e/T)^½ at
fixed charge-state distribution (CSD), i.e. whether the model fits the FT-02 form Δχ = kT·b·√n_e.

| Model | Formula as printed / reduced (constants) | Derivation assumptions | Validity regime | Low-density limit | √(n_e/T) family? | Source |
|---|---|---|---|---|---|---|
| **DH, electron-only (DH-e)**; current pipeline | Δχ = z e²/λ_De = **2.087×10⁻⁸** z (n_e[cm⁻³]/T[K])^½ eV (my evaluation of the code's formula) | Linearized Poisson–Boltzmann; only free electrons screen; ions are a uniform background | Γ ≪ 1, N_D ≫ 1 | itself | **Yes**, c = 2.087×10⁻⁸ | pipeline `partition.py:88-116` (docstring cites Mihalas 9-106 and Alimohamadi & Ferland 2022, but see next rows) |
| **DH, electron + ion (DH-ei)** | ΔI_α = −(Z*_α+1)e²/λ_D, λ_D = (4πβe² Σ_{α=1..M,e} n_α Z_α²)^−½ [Piron eq. 59]. μ_ex,α = −½ Z*_α² e²/λ_D [eq. 58]. F_ex = −1/(12πβ n_i λ_D³) [eq. 57]. With all ions singly charged: **2.951×10⁻⁸** z (n_e/T)^½ eV | Classical DH excess free energy of point ions + electrons; Saha IPD from chemical potentials. Piron: "equivalent to applying the correction … using the upper charge state, as in [SP]" | Γ ≪ 1, N_D ≫ 1 | itself | **Yes** at fixed CSD. With mixed charges c ∝ (1+z*)^½, z* = ⟨z²⟩/⟨z⟩, so b depends on the Saha solution | Piron 2023 [read]; Lin 2019 eq. 120–127 (quantum-statistical IPD reduces to (z_α+1)e²κ_scr/4πε₀ with κ²_scr = (1+z_p)κ²_e, "L ≡ 1") [read] |
| **"3e-8" formula** (removed from pipeline) | Δχ = 3×10⁻⁸ Z N_e^½ T^−½ eV | Rounded DH-ei (8π) | as DH | itself | **Yes**, c = 3.0×10⁻⁸ (DH-ei is 2.951×10⁻⁸, 1.7% lower) | Alimohamadi & Ferland 2022 eq. 13, "Equation 9−106 in Mihalas (1978) … due to Debye shielding" [read; Mihalas not opened]. Halenka et al. 2001 eq. 6 prints "Δχ = Ze²/D = 3 × 10⁻⁸ Z N_e^{1/2} T^{−1/2} [eV]" and recommends it [read-SB] |
| **Unsöld (1948)** nearest-neighbour microfield | Δχ ∝ N^⅓ (Ebeling 2017, search snippet: Unsöld showed "a lowering of the ionization energy going with the cubic root of the density"). No prefactor verified. Alimohamadi & Ferland quote the Milone & Merlo nearest-neighbour criterion as N_e = 2.91×10¹⁸ cm⁻³ for Δχ = 1 eV | Electric microfield between ions (Stark saddle) | moderate–strong coupling | no DH limit | **No** (n^⅓, T-independent) | Ebeling 2017 CTPP doi:10.1002/ctpp.201700094 [snippet]; Alimohamadi & Ferland §3.1 [read] |
| **Inglis–Teller (1939)**: a series-limit criterion, *not* an IPD | N n_max^7.5 = 0.027 a₀⁻³ (eq. 5), i.e. log N = 23.26 − 7.5 log n_max. N counts singly charged ions. For T < 10⁵/n K "the total number of ions, positive and negative, enters" | Static Stark broadening merges adjacent high-n lines | any density; merging of the *series*, not the Saha edge | n/a | **No** (n_max ∝ N^−2/15, gap ∝ N^4/15) | Inglis & Teller 1939, ApJ 90, 439 [read, ADS scan] |
| **Ecker–Kröll (1963)** | I_EK = ((z+1)e²/R₀)·(R₀/λ_D) if N_cr ≥ N_i(1+Z̄), else ((z+1)e²/R₀)·C(1+Z̄)^⅓; N_cr = (3/4π)(kT/Z̄²e²)³; C from continuity; "modified EK" uses C = 1 | Microfield-based; ad hoc switch radius (Crowley: "depends upon an ad hoc assumption") | Designed for strong coupling | **= DH-ei** (λ_D includes ions) | **In LIBS range, yes.** N_cr = 1.0×10¹⁹–6.4×10²⁰ cm⁻³ > 2n_e on the whole grid for Z̄ = 1 (my computation), so EK ≡ DH-ei here | Benredjem 2023 eq. 3 [read] (the paper's gloss "Z the atomic number" looks inconsistent with its own use of Z̄. I used the mean ion charge.) |
| **Stewart–Pyatt (1966)** | I_SP(z) = (3(z+1)e²/2R₀){[1+(λ_D/R₀)³]^⅔ − (λ_D/R₀)²}, λ_D = [kT/4π(N_e + Σ N_z z²)e²]^½, R₀ = (3/4πN_i)^⅓ (FLYCHK form, Benredjem eq. 1). Crowley eq. 14: ΔU_SP = −(kT/2Z_p)[(1+Λ)^⅔ − 1], Λ = (3Γ_j)^{3/2}, noting "Z_p … rather than Z_p + 1, as in Stewart and Pyatt's original formula" | Finite-temperature Thomas–Fermi-like average potential around the ion. Uniform electrons in the ion core (Crowley calls this "an inconsistency"). Average (static) electrostatic energy | Interpolates weak → strong coupling | **→ DH-ei** when λ_D ≫ R₀. High density → ion sphere | **No.** Log-elasticity d ln Δχ/d ln n_e = 0.40–0.50 on the grid (DH exactly 0.5), and the value depends on z*, N_i | Benredjem 2023 eq. 1 [read]; Crowley 2014 eq. 12–14, 22 [read]. Inference (my algebra, not stated in a source): with R₀ → R_z = (3z/4πn_e)^⅓ and Σz_i²n_i = z*n_e, the FLYCHK form equals kT/(2(1+z*))·[(1+Λ′)^⅔ − 1] with Λ′ = (R_z/λ_D)³, i.e. Crowley's eq. 14 with SP's original (Z_p+1) and a total (e+i) Debye length |
| **Ion sphere (IS)** | I = 3(z+1)e²/(2R₀) ("high-density limit of SP") | Neutral ion sphere, uniform electrons | Γ ≫ 1 | no DH limit | **No** (n^⅓, T-independent) | Benredjem 2023 eq. 2 [read]; Crowley eq. 17 [read] |
| **Crowley (2014)** SCL / TIPD / SIPD | SP-based analytic framework. States that the Saha equation needs the *thermodynamic* IPD, which in weak coupling "is two thirds of the static value". Spectroscopic IPD ħΔω > ΔU ≥ ΔW | Classical ions, arbitrary coupling, T_e ≠ T_i allowed | all | see §3(iii) | No (framework) | Crowley 2014 [read] |
| **Son et al. (2014)** two-step Hartree–Fock–Slater | Parameter-free finite-T HFS | WDM; XFEL/Orion Al | solid density | uses Debye screening at low T | No | Son 2014 PRX 4, 031004 [read] |
| **Lin et al. (2017, 2019)** structure-factor / self-energy | IPD from dynamical structure factors | WDM; **reduces exactly to DH-ei** in weak coupling (eq. 127–128, L ≡ 1) | all | DH-ei | family only in weak coupling | Lin 2017 PRE 96, 013202 [read]; Lin 2019 arXiv:1904.04456 [read] |
| **Wu et al. (2023, 2025)** non-LTE IPD; neighbouring-ion IPD | WDM/HDM models | warm/hot dense | solid density | — | No | arXiv:2305.09371, 2505.18593 [abstract] |

**What the pipeline has today, against this table (inference).** The forward's electron-only
Debye length has no support among the retrieved sources as the Saha-equation correction. Every
thermodynamic derivation I read screens with electrons and all ions (Piron eq. 59; Lin eq. 120;
Benredjem's λ_D; Crowley eq. 10–11, 22). The docstring attributes the 4π form to "Mihalas 1978 Eq.
9-106; Alimohamadi & Ferland 2022". Alimohamadi & Ferland print Mihalas eq. 9-106 as the
3×10⁻⁸ form, which is the 8π value. So the citation supports DH-ei, not DH-e. I did not open
Mihalas 1978 itself. The pipeline's charge convention (forward: 2Δχ₁ at II→III) agrees with
Piron's (Z*+1) and Benredjem's (z+1). The inverse's 1Δχ₁ at II→III does not.

Electron-only screening does have one physical rationale in the literature. Crowley argues that on
*fast (spectroscopic)* timescales ions cannot respond (§1.1: the response of the ions "is much
slower still, occurring on timescales determined by the inverse of the ion plasma frequency"). That
argument concerns photo-/collisional ionization thresholds, not the equilibrium Saha balance that
CF-LIBS inverts. Crowley's own conclusion is that the Saha equation takes the thermodynamic IPD
(§3(iii)).

---

## 3. Stewart–Pyatt: what is established, and what matters at LIBS densities

### 3.1 Established criticisms (all at solid density, Γ ≫ 1)

- **LCLS XFEL, solid-density Al (Vinko 2012 Nature 482, 59; Ciricosta 2012 PRL 109, 065002).**
  Charge-resolved K-edge thresholds disagreed with SP. A modified EK (C = 1) fitted better.
  [secondary: Son 2014: "a disagreement of the measured K-edges with the extensively used SP model
  was claimed. A modified EK model was proposed to fit the experimental data"; Crowley 2014 §1.1;
  Benredjem 2023 §1. Primaries not opened.] Benredjem adds that "the agreement is not satisfactory
  for the highest ion charges, i.e., from O-like to Be-like aluminum".
- **Orion laser, hot dense Al (Hoarty 2013 PRL 110, 265003; 500–700 eV, 1–10 g/cm³).** Son 2014
  and Benredjem 2023 say the K-shell spectra favoured SP over EK, in Son's words "could only be
  described with the SP model" [secondary]. Crowley reads the same data as consistent with a
  modified ion-sphere formula and SP as under-estimating the IPD [read, §8, Table 2]. Crowley on the
  two experiments together: "Neither model is capable of fitting both experiments."
- **Later work.** Ciricosta 2016 (Mg, Si, compounds): per Lin 2019, "the SP model fails to explain
  any of those measurements, because the validity of the SP model is restricted to weakly and
  intermediately coupled plasmas". Pérez-Callejo 2024 (solid Mg, LCLS) needs depressions "between
  those predicted by the well known Stewart-Pyatt and Ecker-Kroll models" [abstract]. Šmíd 2024 (Sci.
  Rep., K-shell emission of mid-charged ions) says the data "agree well with the Stewart-Pyatt
  model" [snippet of arXiv:2406.06233]. Reconciliations: Crowley 2014 (static, thermodynamic and
  spectroscopic IPD are distinct), Son 2014 (two-step HFS "lie[s] between the SP and mEK models"),
  Lin 2017/2019 (dynamical structure factor), Iglesias 2013 (fluctuations; Asta hit, not opened).
- **Conditions.**
  - XFEL: Crowley estimates "the ion plasma coupling parameter … in the range 3,000 to 50,000
    putting these plasmas clearly in the solid-state regime".
  - Orion: "the plasma coupling strength Γ is in the range 2 to 3, indicating a moderately-coupled
    fluid plasma" [read]. In Crowley's own analysis the Orion data are "inconsistent with both
    Stewart-Pyatt … and Ecker-Krӧll …, with the former under-estimating the IPD". Son 2014 and
    Benredjem 2023 describe the Orion data as favouring SP. Secondary accounts differ here.
  - Benredjem's Al test case (2.7 g/cm³, 50 eV) has Z̄ = 5.77 and λ_D/R₀ = 0.215, "which means
    that the high density limit of the Stewart-Pyatt IPD is a good approximation".
  - LIBS has Γ ≤ 0.46 (§6). The disputes therefore sit at the ion-sphere end of SP, at coupling one
    to five orders of magnitude above LIBS and densities 5–8 orders of magnitude higher.

**Transfer to LIBS (inference).** None of the mechanisms offered for the solid-density failures
bears on n_e ≤ 1e18 cm⁻³ and Γ ≤ 0.46: strong ionic correlation, Pauli blocking or degeneracy,
inner-shell (K-edge) spectroscopic versus thermodynamic thresholds, and non-thermal XFEL heating. Lin
2019 restricts SP's validity to "weakly and intermediately coupled plasmas", which is where LIBS sits. **The XFEL/Orion controversy is
not evidence against SP at LIBS densities.**

### 3.2 SP issues that do matter at LIBS densities

(i) **LIBS is in SP's crossover, not its DH limit.** SP reduces to DH-ei only when λ_D ≫ R₀.
My computation (§6): λ_D,ei/R₀ = 0.60 (1e18, 0.5 eV) to 3.8 (1e15, 2 eV), and (λ_D/R₀)³ equals
N_D computed with λ_D,ei. So SP/DH-ei = 0.93 at 1e17/1 eV, 0.83 at 1e18/1 eV and 0.70 at
1e18/0.5 eV. "SP ≈ DH at LIBS" holds only for n_e ≲ 1e16 or T ≳ 1.5 eV. Choosing SP therefore
changes Δχ by up to 30% relative to DH-ei, and in the opposite direction from the DH-e → DH-ei change.

(ii) **SP (and DH-ei) depend on the charge-state distribution.** Both need Σ z_i² n_i and N_i, and
SP also needs z* = ⟨z²⟩/⟨z⟩ [Benredjem eq. 1; Crowley eq. 4]. In a multi-element LIBS plasma these
come from the Saha solution itself, so Δχ is implicit in n_e and T. For DH-ei at LIBS temperatures
z* is close to 1, which makes this a small correction (inference: c ∝ (1+z*)^½, so z* = 1.1 changes c
by 2.4%). For SP the CSD also enters R₀ and the interpolation.

(iii) **Static versus thermodynamic IPD (unresolved).** Crowley: SP gives the static continuum
lowering (SCL); "the Saha equation … depends only on the thermodynamic IPD". In weak coupling "the
TIPD becomes … two thirds of the static value". Crowley's two weak-coupling SCL expressions differ
by charge convention: eq. 22 gives Z_j u_DH and eq. 76 ("no further approximation is necessary")
gives (Z_j + ½) u_DH. Piron 2023, deriving the Saha correction directly from the DH excess free
energy, gets the full (Z*+1)e²/λ_D (eq. 59) and says it coincides with SP's upper-charge-state
prescription. Piron's (Z*+½) (eq. 61) is the average-atom *eigenvalue* shift, not the Saha
correction. Lin 2019 also recovers the full (z+1)e²κ_scr.

My re-derivation from the DH free energy (Gaussian units) reproduces Piron.
- F_ex = −kTVκ³/12π with κ² = 4πe²Σ_j N_j z_j²/(VkT).
- So μ_s = ∂F_ex/∂N_s = −½ z_s² e²κ.
- The Saha shift is μ(Z+1) + μ(e) − μ(Z) = −½[(Z+1)² + 1 − Z²]e²κ = −(Z+1)e²κ. It includes the
  freed electron's own term and the change of κ with N.
- DH also has U_ex = (3/2)F_ex. An IPD computed from energy derivatives is therefore 3/2 times the
  free-energy one, so a factor ⅔ between "static" and "thermodynamic" forms is expected.

Crowley defines his SCL as the change when an ion ionizes "without affecting Z_p, n_e, T_i" (§2.3).
That excludes the κ-variation and possibly the free-electron term, which is a plausible origin of
his lower TIPD. **I could not fully reconcile Crowley's ⅔ factor with the DH limiting law.** Read literally, it would cut the weak-coupling Saha IPD to
roughly ⅓–⅔ of DH-ei. I mark it unresolved. The weight of the retrieved derivations favours
(z+1)e²/λ_D (Piron, Lin). It is still a live O(1) ambiguity in the coefficient, larger than the √2
the owner is weighing.

(iv) **Prefactor inconsistency in the intermediate regime.** Crowley, footnote to eq. 14: "here it
is Z_p that appears in the denominator, rather than Z_p + 1, as in Stewart and Pyatt's original
formula … This is due to an inconsistency in Stewart and Pyatt's argument in relation to the
assumption of uniformly distributed free electrons." Both versions reduce to DH-ei in the weak
limit. They differ in the crossover, which is exactly where LIBS sits (i). I did not quantify the
difference.

(v) **SP carries a cutoff prescription with it.** SP 1966 p. 1210 [read-SB, checked on the ADS
scan]: "Guess z* in order to get the Debye length; for each z, compute K and (from Fig. 1) J; in
each ionic species lower all ionization potentials by JkT and delete all ionic configurations in
which the least tightly bound electron is then free; use the Boltzmann-Saha equations to find a
revised z*, and iterate." Piron 2023 paraphrases this as "suppress any level for which the
ionization-potential correction is greater than the level energy". The same page shows that SP's
analytic formula (their eq. 5, the dotted F = 1 line of Fig. 1) departs from their full
Thomas–Fermi integrations by up to several percent for (z*+1)K ≈ 0.1–10. I read this off the figure
by eye. LIBS spans (z*+1)K ≈ 0.003–1.5 (my computation: 2Δχ_DH-ei/kT).
Adopting "SP" as a package therefore imports the sharp, n_e-moving cutoff that breaks continuity
(R1-02; §5). It also bakes in an iterate-on-z* loop. The IPD formula and the level-deletion rule
are separable, and they should be separated.

(vi) **Assumptions that hold for LIBS.** SP (and DH) assume classical point ions, non-degenerate
electrons and a common temperature (Crowley allows T_e ≠ T_i). In LTE LIBS these hold. Early-time
T_e ≠ T_h and non-LTE are outside the scope of every model here.

**Bottom line on SP (inference).** Its well-known failures do not apply to LIBS. What does apply is
milder: it is 3–30% below DH-ei where LIBS spectra are usually taken (n_e ≥ 1e17), it is a
functional of the CSD, it has an intermediate-regime prefactor ambiguity, and the SP package includes
a discontinuous level-suppression rule. None of these makes SP wrong for LIBS. Together they make it
harder to implement consistently and outside the formal family, and there is no LIBS evidence that it
is better. Use it as a sensitivity arm.

---

## 4. What the LIBS / CF-LIBS literature uses

Most of this section comes from a literature sub-search (a general-purpose sub-agent using Asta
snippet search, the HAL API, Europe PMC, publisher PDFs and the live NIST tool). Tags: `[read-SA]`
means the sub-agent read the full text; `[read-SA, checked]` means I also re-checked the printed
equation in the sub-agent's scratch copy (`/tmp/ipd_agentA/`).

### 4.1 Papers that print an IPD formula: all use Debye–Hückel (z+1)e²/λ_D, mostly citing Griem 1962

| Paper | Formula as printed | Screening | Charge factor | Stated magnitude | Tag |
|---|---|---|---|---|---|
| Shabanov & Gornushkin, Appl. Phys. A 124 (2018) 716, doi:10.1007/s00339-018-2129-9 (LIP modelling) | Δχ = (z+1)ΔE, ΔE = e²/r_d, r_d = [kT/4πe²(n_e + Σ_{s,z} z² n_{s,z})]^½ (eq. 7), cites Zel'dovich–Raizer. "If the value of Δχ … is not in a physical range 0.1 ≤ Δχ ≤ 3 eV, then it is set to the nearest value" (Drawin–Felenbok). U cut at I_vac − Δχ | **e+i**, explicit | z+1, z = charge before ionization | ΔE/kT ≪ 1 for typical lab LIPs (said of the pressure correction) | [read-SA, checked] |
| Favre, Bultel, Morel et al., "MERLIN", JQSRT 330 (2025) 109222, doi:10.1016/j.jqsrt.2024.109222 | ΔE_io[eV] = (Ze²/4πε₀)·√((Z+1)n_e/(ε₀k_BT)) (eq. 4), "the approach proposed by Griem [22]". Partition functions have no density dependence | e+i by inference: (Z+1)n_e = n_e + Z²n_i for Z-charged ions | Z = product-ion charge (inference) | "In the context of laser-induced plasmas, the ionization potential lowering is of the order of a few 10⁻² eV." | [read-SA, checked] |
| De Giacomo & Hermann, J. Phys. D 50 (2017) 183002, doi:10.1088/1361-6463/aa6585 | ΔI = e₀²(z_s+1)/(4πε₀λ_D) (eq. 14b), cites Griem 1962 | λ_D not defined | z_s+1 | "dramatic decrease" of the ionization energy only at 10¹⁹–10²² cm⁻³ | [read-SA] |
| Seitkozhanov, Dzhumagulova & Shalenov, Entropy 27 (2025) 253, doi:10.3390/e27030253 (not LIBS; quotes Griem 1962) | ΔI_i = (i+1)e²/(4πε₀λ_D), λ_D = √(ε₀k_BT/(e²(n_e + Σ_i i²n_i))). "For low-density and high-temperature plasmas, the approach introduced by Griem [30] is commonly employed." | **e+i** | i+1 | — | [read-SA]; Griem 1962 via this [secondary] |
| Lee et al., Sci. Rep. (2025), doi:10.1038/s41598-025-26615-8 | Δχ = ((Z̄+1)e³/4πε₀)√(Z̄(Z̄+1)n₀/(ε₀k_BT_e)), cites Griem 1962 | e+i (inference) | Z̄+1 | 12–24 eV at ~10²¹ cm⁻³, model output (out of LIBS range) | [read-SA] |

Piron 2023 (eq. 59) also cites Griem 1962 (Phys. Rev. 128, 997, "High-Density Corrections in Plasma
Spectroscopy") for the same (Z*+1)e²/λ_D with ions in λ_D [read]. Griem 1962 itself was seen only as
an abstract via WebFetch. It says an "internally consistent system of corrections is derived for Saha
equations, partition functions, and equations of state". The sub-agent could not open Griem's 1964 or
1997 books, so **whether Griem's books include ions in ρ_D is not verified**. Every secondary
statement of the Griem form that defines λ_D includes them.

### 4.2 CF-LIBS method and diagnostic papers: ΔE carried as a symbol, dropped, or absent

- **Symbolic, never evaluated.** Aguilera–Aragón lineage: J. Phys. Conf. Ser. 59 (2007) 210
  eq. 1d; Aragón & Aguilera JQSRT 2014 (doi:10.1016/j.jqsrt.2014.07.026); Aguilera, Aragón & Manrique
  JQSRT 2015; Aguilera & Aragón SAB 217 (2024) 106969. Quote: "ΔE^k_∞ is the correction of this
  quantity for interactions in the plasma" [read-SA]. Also Thomas & Joshi arXiv:2302.13272 and Fayyaz
  et al. Heliyon 2023 [read-SA]. The Saha–Boltzmann construction in `Alt/CSigma.lean` follows this
  lineage [verified-file: Aguilera & Aragón 2007; Aragón & Aguilera 2014]. The 2007 SAB paper itself
  is paywalled and was not re-opened.
- **Dropped as negligible, without a number.** Unnikrishnan et al., Pramana 74 (2010) 983: "The
  lowering of the ionization energy due to the interactions in the plasma is negligibly small which
  has been omitted" [read-SA, checked]. Zhang et al. 2022 (Frontiers review): ΔE_ion "is 1–2 orders
  of magnitude lower than the sum of (E_i^II + E_ion) and is generally negligible" [read].
- **Not mentioned.** Tognoni et al. SAB 65 (2010) 1 [read-SA; verified-file]; Hermann's CF-LIBS
  chapter (Wiley 2023) and SAB 2022 106595 [read-SA].
- **NIST LIBS database: no IPD.** The documentation (Ralchenko & Kramida, Atoms 8 (2020) 56,
  doi:10.3390/atoms8030056) lists only ionization energies, level energies, weights and A-values. The
  sub-agent also ran the live tool for pure Fe at T = 1–1.2 eV and n_e = 10¹⁶–10¹⁹. Fe II/Fe I rises
  ×9.98, ×9.70 and ×10.0 per decade of n_e, and Fe III/Fe II ×9.8 and ×10.0. DH-ei would give ×6.4
  (×6.9 for III/II) at the 10¹⁸ → 10¹⁹ step. So **the NIST tool applies no n_e-dependent IPD**
  [read-SA; ran tool].
- **Continuum lowering in a LIBS composition calculation.** Ristić, Krstevski, Ranković, Marković,
  Šajić & Kuzmanović, "The influence of continuum lowering on the equilibrium composition of plasma:
  case study of laser-induced plasma on a WC–Cu target", Plasma Phys. Control. Fusion 66 (2024),
  doi:10.1088/1361-6587/ad8b68. Abstract: "the correction to the partition functions due to the
  reduction of the ionization potential is of greater importance than the correction to the
  Boltzmann term at higher temperatures for atomic species" [abstract, Asta `papers get`; model and
  numbers not seen]. This is the only retrieved LIBS paper that separates the Saha-exponent effect
  from the partition-function effect. Its finding is consistent with §5.3: in the ionization
  balance, the U_I change is first-order for the minor neutral population, but in an element's
  total it is diluted by the neutral fraction.

### 4.3 Effect sizes

- **No retrieved paper quantifies an IPD-induced change in n_e, T or composition at 10¹⁶–10¹⁸ cm⁻³,
  and none compares DH vs SP vs no IPD for LIBS.** Searches that could have found one: Asta Paper
  Finder (thread `2026-09-24-ipd`, which reported none), Asta snippet search on "effect of
  ionization energy lowering on electron density" and on Saha–Boltzmann IPD neglect, HAL full-text
  API, arXiv site search. The Paper Finder negative is weak, because the same thread missed Ristić
  2024 (§8). One candidate was not retrieved: Rajačić et al., JQSRT 2025, doi:10.1016/j.jqsrt.2024.109338
  (closed access; title looks relevant). **Open it before claiming the gap.**
- **Stated magnitudes:**
  - "a few 10⁻² eV" (MERLIN).
  - "1–2 orders of magnitude lower than" E + E_ion (Zhang 2022).
  - "negligibly small" (Unnikrishnan).
- **Why "negligible" is the wrong test (inference).** The Saha factor responds to Δχ/kT, not to
  Δχ/E_ion. At 1e17 cm⁻³ / 1 eV, Δχ_DH-ei = 0.087 eV is < 1% of E_ion, yet it shifts a Saha-derived
  n_e by 9%. The pipeline's DED round trip shows exactly this: 0.9358× n_e with IPD off vs on (R1-07).
- **In-house numbers:** §6. The DH-e → DH-ei change moves an IPD-aware n_e by ×1.03 (1e17 / 1 eV)
  and ×1.08 (1e18 / 1 eV). Dropping IPD entirely moves it by e^{−Δχ/kT}: ×0.92 and ×0.76 respectively
  (DH-ei).

---

## 5. Level-cutoff policies and continuity of U(n_e, T)

Sources for this section: my own reads (Piron 2023, Alimohamadi & Ferland 2022, Crowley 2014, the
HM88 p. 797 scan, the SP 1966 p. 1210 scan) and a second sub-search. `[read-SB]` means the sub-agent
read the full text or the ADS scan (scratch in `/tmp/ipd_agentB/`); `[read-SB, checked]` means I
also viewed the page.

### 5.1 Policies and the continuity of U(n_e, T)

| Policy | Formula as printed | Continuity of U in n_e | Used by | Notes |
|---|---|---|---|---|
| **P0 All tabulated levels, no n_e** | Z = Σ g_i e^{−E_i/kT} over the whole list | Independent of n_e (C^∞) | NIST LIBS tool: `saha_lte.js` sums every ASD level, including the 284 Na I levels above the IP, identically at 10¹⁷ and 10¹⁹ [read-SB, code]; also Barklem & Collet 2016 ("all energy levels for which data are available") | U depends on how complete the database is. Autoionizing levels add 5% (Ca I, 1 eV) to 17% (2 eV) (sub-agent calc) |
| **P1 Fixed cutoff** at the unperturbed IP, or at IP − ΔE_fix | Irwin 1981: "truncated each Rydberg series at a cutoff energy ΔE below its continuum … adopted ΔE=0.1 eV". Irwin says Kurucz used "the DF tables (using a cutoff energy of 0.1 eV)" | **Independent of n_e** | Irwin 1981 ApJS 45, 621 [read-SB]; pipeline inverse today (`sharp_ip`, R1-02) | Irwin: "the partition function is insensitive to the exact value of ΔE except at high temperatures where the species is minor because of ionization". **Inference:** in CF-LIBS the argument largely carries over. The element total depends on U_I only through the neutral fraction f_I (§5.3). What does not carry over is the case where one solver uses different U in different steps |
| **P2 Sharp cutoff at the lowered limit** χ − Δχ(n_e) | SP 1966: "in each ionic species lower all ionization potentials by JkT and delete all ionic configurations in which the least tightly bound electron is then free". Halenka 2001 eq. 3, 6: E ≤ E_∞ − ΔE with "Δχ = Ze²/D = 3 × 10⁻⁸ Z N_e^{1/2} T^{−1/2}". Shabanov & Gornushkin 2018: cut at I_vac − Δχ, Δχ clamped to [0.1, 3] eV | **Discontinuous.** Piecewise constant, non-increasing, with a jump of g_i e^{−E_i/kT} at each crossing density | SP 1966 p. 1210 [read-SB, checked]; Halenka et al. 2001 astro-ph/0201238 [read-SB]; Shabanov & Gornushkin 2018 [read-SA, checked]; pipeline CPU forward (R1-02) | HM88 on models that delete states: "discontinuities in the internal partition function because states are abruptly deleted … lead to δ-function singularities in the pressure and internal energy tables, which is catastrophic in stellar structure codes requiring the tables to be not only continuous but continuously differentiable" [read-SB; confirmed by NotebookLM OCR]. Piron 2023: "a sharp suppression of the bound state does not correspond to what stems from a screened potential" and "any observable has to remain continuous" [read]. Jump sizes: 178 Ca I levels cross between 1e16 and 1e18 (formal audit). The largest single jump over 1e15–1e18 at 1 eV is Na I 3.2%, K I 1.8%, Al I 0.5%, Ca I 0.4% (sub-agent calc, NIST levels). **Inference:** Gornushkin's 0.1 eV floor makes this a *fixed* cutoff at I − 0.1 eV for n_e ≲ 10¹⁷ |
| **P3 Occupation probability** (HM88; HHL94 fit) | U = Σ w_i g_i e^{−E_i/kT}. HHL94 App. A: w = f/(1+f); f = 0.1402(x + 4Z_r a³)β_c³/(1 + 0.1285 x β_c^{3/2}); x = (1+a)^{3.15}; a = 0.09 n_e^{1/6} T^{−1/2} (n_e in cm⁻³, T in K); β_c = 8.3×10¹⁴ n_e^{−2/3} Z³ k j^{−4}; k = 1 (j ≤ 3), (16/3) j/(1+j)² (j > 3). HM88 eq. 4.42: n* = 1.20×10³ N_e^{−2/15} Z_a^{3/5} | **Smooth.** HM88: "The continuous state-by-state fadeout with decreasing w_ijk allows one to assure continuity not only of the internal partition function but also of all material properties … With a little care the w_ijk's can be made analytically differentiable." Inference: C^∞ for n_e > 0 | HM88 ApJ 331, 794 [read-SB]; HHL94 A&A 282, 151 [read-SB]; TLUSTY guide arXiv:1706.01935 [read-SB]; Alimohamadi & Ferland 2022 eq. 14–16 [read] ("by far the most widely used approach in stellar atmospheres") | **LIBS caveats:** (1) the fit is to W(β; a, Z_r) "for a ≤ 0.8", with "maximum error in general … of the order of 20 %". a = 0.80 at (0.5 eV, 1e17), 1.18 at (0.5 eV, 1e18) and 0.84 at (1 eV, 1e18), all outside the fit range (sub-agent calc). (2) Complex atoms: HM88 says "For nonhydrogenic systems n continues to be the principal quantum number", whereas practice (TLUSTY, Barklem & Collet) uses n* from the binding energy. (3) The constant is 8.3 vs 8.59×10¹⁴ (the C = 0.9 convention; < 1.5% in U), and K_n differs between HM88 and HHL94 at n = 4–6. (4) HM88: "plausible but nonrigorous corrections for the effects of ions other than protons." (5) Zaghloul 2010 vs Potekhin 2010 consistency dispute, resolved by Potekhin as a missing configurational factor [read-SB] |
| **P4 Planck–Larkin (PL)** | Rogers 1986: PLPF = Σ(2l+1)(e^{−βE_nl} − 1 + βE_nl) | Independent of n_e; "always convergent" | Rogers 1986 ApJ 310, 723; Trampedach et al. 2006 ApJ 646, 560 [read-SB] | **Not usable for level populations.** Rogers: it "does not give the actual occupation numbers". Trampedach: "despite its name the PLPF is not a partition function, but merely an auxiliary term in a virial coefficient". Henkel & González 2025 (Plasma Phys. Technol. 12, 46) put a PL-type Z into Boltzmann populations [read-SB]; that is not a cutoff study |
| **P4′ PL with IPD-shifted continuum** | Sengebusch et al. 2017 eq. 14; Bonitz & Kordts 2025 | Continuous. Sengebusch: "To avoid discontinuities due to pressure ionization, we apply a Planck-Larkin renormalization". Inference: C¹ but not C² at crossings | arXiv:1709.08493, 2502.10548 [read-SB] | Warm-dense-matter work, not LIBS. Same occupation-number objection as P4 |
| **P5 Zaghloul** | Q = [1 − w₀] + Σ g_i w_i e^{−ε_i/kT} (eq. 17) | Inherits w's continuity | Zaghloul 2013, arXiv:1210.0053 [read-SB] | Enforces "the internal partition function should not, in any case, be less than unity" |
| **P6 Moving cutoff frozen within the inner loop** | P2 evaluated at the outer-loop n_e | The inner map is continuous; the outer map is still piecewise constant | pipeline option | Inference: removes discontinuities from the inner fixed point only. The outer iteration can still cycle between level sets, so the Lipschitz theorems stay vacuous at outer level |

### 5.2 Should the cutoff be tied to the IPD model?

- **Sources that tie them (one lowering for both):**
  - SP 1966, the recipe quoted in P2, which applies one JkT to both. SP also writes that the plasma
    perturbation, "besides providing a natural cutoff to the bound-state partition function,
    effectively lowers all the ionization potentials" [read-SB].
  - Griem 1962: "An internally consistent system of corrections is derived for Saha equations,
    partition functions, and equations of state" [abstract, WebFetch].
  - Halenka 2001; Shabanov & Gornushkin 2018; Alimohamadi & Ferland 2022 eq. 12 (E_max = I_ion − Δχ).
- **Sources that untie them:**
  - HM88 (quoted by NotebookLM from its OCR of the ADS scan, in a passage next to the p. 798
    text): "the concept of a 'lowering of the ionization potential' … is only a mathematical
    construct with little, if any direct (i.e., observable) physical significance … the nonideal
    free-energy terms lead to terms in the exponential which one can interpret as a modified (not
    always decreased!) ionization potential … But this is only an interpretation."
  - HM88 p. 798: "cutoff procedures used to truncate internal partition functions are not physically
    related to a 'lowering of the ionization potential,' though they may formally imply this concept
    if the stoichiometric equations are rewritten in the form of Saha equations. Rather, such cutoffs
    either follow from, or imply, an interaction term in the free energy" [read-SB].
  - HM88 p. 797 on the lowered-Saha-plus-truncation procedure: "This procedure is thermodynamically
    inconsistent (Sweeney 1978) … The thermodynamically consistent way to account for nonideal effects
    in a plasma is to introduce into the free energy additional terms … and then carry out the
    minimization procedure … fully consistently" [read-SB, checked].
  - Crowley 2014 §1.1: "the microfield effects are distinct from the continuum lowering and should be
    treated separately" [read].
  - Piron 2023: "most of the effect of accounting for non-ideality corrections is in the modification
    of the partition function" [read].
- **What both camps agree on:** the Saha correction and the U truncation must come from *one*
  free-energy model and be used identically everywhere. They disagree on whether the truncation is a
  sharp cut at the lowered limit (SP, Griem-style) or a smooth weight (HM88).
- **Inference for CF-LIBS**, which needs level populations rather than an EOS:
  - The practical rule is one `PopulationContext`, a U that is smooth in n_e, and forward = inverse.
  - "DH-ei in the Saha exponent + HM w in U" is the MHD-style pairing of two nonideal free-energy
    terms. I did not verify which Coulomb term HM88's free energy carries (HM88 §III not read), so
    thermodynamic consistency of that exact pairing is **not established here**.
  - Under HM88, w also scales the *emitting* level's population. For low-n* analytical lines w ≈ 1,
    but PAS should confirm that no high-n* line is in the selected set.

### 5.3 How much U moves

- **R1-02**, production DB, U_sharp/U_DH-e cut:
  - 11 kK / 1e17: Ca I 1.278, K I 1.437, Na I 1.197, Al I 1.053, Mg I 1.035, Si I 1.014, Ti/V/Fe 1.000.
  - 15 kK / 1e18: Ca I 1.955, Na I 2.058, K I 2.376, Al I 1.288.
- **Sub-agent calc** (NIST ASD level lists pulled from the NIST LIBS tool; "cut" uses the 3e-8
  form, which is larger than the pipeline's DH-e and so gives a smaller U). T = 1 eV, n_e = 1e17,
  U for fixed-at-IP / DH-cut / HM (HHL94) / PL+IPD:

  | Species | fixed at IP | DH-cut | HM | PL+IPD | fixed ÷ HM |
  |---|---|---|---|---|---|
  | Na I | 9.92 | 7.50 | 4.67 | 2.87 | 2.1 |
  | K I | 16.3 | 10.0 | 6.89 | 3.54 | 2.4 |
  | Ca I | 10.07 | 7.29 | 6.03 | 4.23 | 1.7 |
  | Mg I | 2.38 | 2.22 | 1.96 | 1.68 | 1.2 |
  | Al I | 8.43 | 7.84 | 7.29 | 6.36 | 1.16 |
  | Si I | 12.44 | 12.16 | 11.99 | 11.56 | 1.04 |
  | Fe I | 78.5 | 78.5 | 78.3 | 72.2 | 1.00 |
  | Ti I | 112.4 | 112.4 | 112.2 | 98.7 | 1.00 |

  - At 2 eV / 1e17 (same column order): Na I 85.8 / 63.0 / 20.8 / 3.35; K I 104.8 / 59.3 / 25.2 /
    3.71; Ca I 118.2 / 66.4 / 35.3 / 8.4. Including Ca I's autoionizing levels raises its first value
    to 138.3. Fixed ÷ HM reaches 3.3–4.2 for Na/K/Ca I at 2 eV.
  - Ions differ by ≤ 1% at 1 eV and by up to ~20% at 2 eV.
  - The transition-metal neutrals look insensitive because the ASD lists stop well below their
    limits: an artifact of database completeness, not physics.
- **Literature:**
  - HM88 Fig. 1: "A physical theory is needed for the cutoff n* if the plotted ratio is not very close
    to unity". At I/kT ≈ 5, U "will depend sensitively upon how many states are included" [read-SB].
    LIBS neutrals at 1 eV have I/kT = 4.3 (K) to 8.2 (Si), inside that regime.
  - Barklem & Collet 2016: "differences for a cutoff of n* ≈ 12 are of order a couple of per cent"
    at stellar densities [read-SB]. LIBS n* ≈ 5–7 (HM88 eq. 4.42), so that figure is a lower bound.
  - Yang et al. 2024 (AIP Adv. 14, 035038; argon): cutoff criteria "have little impact on … the main
    components … but have a significant impact on … non-major components" [abstract].
  - Ristić et al. 2024: the partition-function part of continuum lowering dominates for atoms at
    higher T [abstract].
  - No LIBS paper quantifying CF-LIBS composition against the cutoff was found (searches listed in §8).
- **How a U change reaches composition (algebra, my derivation).**
  - The neutral Boltzmann-plot intercept fixes B = N_I/U_I, a per-weight level population with no U
    in it. The Saha step gives N_II = N_I·U_II·K(T)e^{Δχ/kT}/(U_I n_e), where
    K = 2(2πm_e kT/h²)^{3/2}e^{−χ/kT} = 6.04×10²¹ T_eV^{3/2} e^{−χ/kT} cm⁻³.
  - So an element's total is **N_s = B·(U_I + U_II K e^{Δχ/kT}/n_e)**, and d ln N_s/d ln U_I = f_I,
    the neutral fraction. A consistent change of U_I is diluted by f_I.
  - Mixing policies is different. If the Boltzmann step uses U_I^(b) and the Saha step U_I^(c), the
    ionic term is scaled by U_I^(b)/U_I^(c) *undiluted*. That is the within-solver mismatch
    R1-02 documents, e.g. a Saha exponent lowered by IPD alongside sharp-IP partition functions,
    or different U providers on the CPU and kernel paths. A forward/inverse mismatch with an
    internally consistent inverse is diluted by f_I, like a policy change. The forward's own
    ionization fractions still shift by the full U_I ratio for the minor neutral stage.
  - The Saha–Boltzmann-offset n_e is cutoff-invariant. Both stages enter as per-weight level
    populations, so no U survives; this matches the Cσ ordinate correction [verified-file:
    Aguilera & Aragón 2007]. Only the IPD moves it.
- **Consistent-policy composition effect**, from the sub-agent's U tables and the algebra above
  (`/tmp/ipd/composition_sensitivity.py`, reproduced below). Selected rows:

| element | T [eV] | n_e | f_I (fixed) | f_I (HM) | N_s(fixed)/N_s(HM) | N_s(DH-cut)/N_s(HM) |
|---|---|---|---|---|---|---|
| Na | 1.0 | 1e+17 | 0.0250 | 0.0119 | 1.0134 | 1.0072 |
| K | 1.0 | 1e+17 | 0.0186 | 0.0080 | 1.0109 | 1.0036 |
| Ca | 1.0 | 1e+17 | 0.0165 | 0.0099 | 1.0069 | 1.0024 |
| Mg | 1.0 | 1e+17 | 0.0350 | 0.0292 | 1.0061 | 1.0038 |
| Al | 1.0 | 1e+17 | 0.0446 | 0.0388 | 1.0061 | 1.0030 |
| Si | 1.0 | 1e+17 | 0.0994 | 0.0961 | 1.0037 | 1.0014 |
| Fe | 1.0 | 1e+17 | 0.0404 | 0.0403 | 1.0001 | 1.0001 |
| Ti | 1.0 | 1e+17 | 0.0166 | 0.0166 | 1.0000 | 1.0000 |
| Na | 1.0 | 1e+18 | 0.1750 | 0.0744 | 1.1219 | 1.0221 |
| K | 1.0 | 1e+18 | 0.1356 | 0.0504 | 1.0986 | 1.0160 |
| Ca | 1.0 | 1e+18 | 0.1215 | 0.0708 | 1.0587 | 1.0096 |
| Mg | 1.0 | 1e+18 | 0.2309 | 0.1889 | 1.0547 | 1.0201 |
| Al | 1.0 | 1e+18 | 0.2785 | 0.2416 | 1.0512 | 1.0146 |
| Si | 1.0 | 1e+18 | 0.4771 | 0.4649 | 1.0233 | 1.0074 |
| Fe | 1.0 | 1e+18 | 0.2580 | 0.2551 | 1.0039 | 1.0038 |
| Ti | 1.0 | 1e+18 | 0.1227 | 0.1213 | 1.0017 | 1.0017 |
| Na | 2.0 | 1e+18 | 0.0561 | 0.0079 | 1.0510 | 1.0161 |
| K | 2.0 | 1e+18 | 0.0464 | 0.0073 | 1.0410 | 1.0088 |
| Ca | 2.0 | 1e+18 | 0.0132 | 0.0033 | 1.0995 | 1.0769 |
| Mg | 2.0 | 1e+18 | 0.0215 | 0.0065 | 1.0873 | 1.0778 |
| Al | 2.0 | 1e+18 | 0.0189 | 0.0070 | 1.0541 | 1.0346 |
| Si | 2.0 | 1e+18 | 0.0232 | 0.0106 | 1.0245 | 1.0159 |
| Fe | 2.0 | 1e+18 | 0.0058 | 0.0051 | 1.0029 | 1.0026 |
| Ti | 2.0 | 1e+18 | 0.0044 | 0.0041 | 1.0007 | 1.0007 |

  - At 0.5 eV the neutral fractions are large, but U barely depends on the policy, so the effect
    is ≤ 2% except K (5.3% at 1e18).
  - At 2 eV / 1e18 the ionic U_II sensitivity takes over for Ca/Mg/Al (up to 10%).
  - Everywhere at ≤ 1e17 cm⁻³ and 1 eV the effect is ≤ 1.4%.
  - Because the factor differs between elements, it does *not* cancel in the closure. This makes
    the cutoff policy a real, if modest, element-specific composition effect at high n_e.

```python
"""Composition sensitivity to the partition-function policy under a CONSISTENT inverse (memo 5.3).

CF-LIBS total for element s from its neutral Boltzmann intercept B = N_I/U_I (U-independent):
  N_s = B * (U_I + U_II * K(T) * exp(dchi/kT) / n_e),  K = 6.0e21 * T_eV^1.5 * exp(-chi_I/kT) cm^-3
(Saha constant 2(2 pi m_e k T/h^2)^1.5 = 6.04e21 T_eV^1.5 cm^-3). Hence
  d ln N_s / d ln U_I = f_I = U_I / (U_I + U_II K e^{dchi/kT}/n_e)   (neutral fraction).
Switching policy P->Q with the SAME U in every step changes N_s by (U_I^Q + X)/(U_I^P + X), X = U_II K e^{dchi/kT}/n_e.
U values: sub-agent B's NIST-ASD-level calculation (/tmp/ipd_agentB/U_results.json); dchi = its 3e-8 form.
"""
import json, math
U = json.load(open('/tmp/ipd_agentB/U_results.json'))
IP = {'Na': 5.139, 'K': 4.341, 'Ca': 6.113, 'Mg': 7.646, 'Al': 5.986, 'Si': 8.152, 'Fe': 7.902, 'Ti': 6.828}
def row(el, T, ne):
    ui = U[f'{el} I T={T} ne={ne:.0e}'.replace('e+', 'e+')]
    uii = U[f'{el} II T={T} ne={ne:.0e}']
    out = {}
    for pol in ('ltIP', 'cut', 'hm'):
        K = 6.04e21 * T**1.5 * math.exp(-(IP[el] - ui['dchi']) / T)
        X = uii[pol] * K / ne
        out[pol] = (ui[pol], ui[pol] / (ui[pol] + X), ui[pol] + X)
    return out
print("el   T  n_e     f_I(fixed)  f_I(HM)  N_s(fixed)/N_s(HM)  N_s(DHcut)/N_s(HM)")
for T in (0.5, 1.0, 2.0):
    for ne in (1e15, 1e16, 1e17, 1e18):
        for el in IP:
            try:
                r = row(el, T, ne)
            except KeyError as e:
                continue
            print(f"{el:3s} {T:3.1f} {ne:.0e}  {r['ltIP'][1]:9.4f}  {r['hm'][1]:7.4f}  {r['ltIP'][2]/r['hm'][2]:12.4f}  {r['cut'][2]/r['hm'][2]:12.4f}")
```

### 5.4 Recommendation for the cutoff (reasoned, not decided)

1. **Require continuity.** Retire P2 (moving sharp cutoff) as a physics option. Keep it only as a
   frozen control arm (P6) for PAS comparison. It is discontinuous, HM88 and Piron argue against it
   physically, and it cuts 1.5–15× closer to the limit than the microfield dissolution (§6).
2. **Physics default candidate: P3 (HM88 w via HHL94).** It is smooth in n_e and T, it is the
   stellar-atmosphere standard, it keeps the real n_e-dependence of U, and it gives the formal spec an
   explicit Lipschitz bound (§7). Before promoting it, pin down four things: the n* convention for
   complex atoms (binding energy measured from the parent limit), the constant (8.59×10¹⁴ with C = 1
   for singly-ionized LIBS plasmas), and the K_n form; also flag states outside a ≤ 0.8.
3. **Baseline: P1 fixed at the unperturbed IP.** This is what the inverse already does, so adopting
   it in the forward is the minimal change that restores forward/inverse consistency and continuity
   immediately. Known bias against HM: U_I is 2.1–2.4× larger for Na/K I at 1 eV / 1e17. Used
   consistently, that moves the Na/K totals by ≈ 1% there and 10–12% at 1e18 / 1 eV (§5.3).
4. **Exclude levels at or above the unperturbed IP in every policy.** 202/324 production species list
   such levels. The NIST LIBS tool keeps them.
5. **Let PAS choose between P3 and P1 on the certified sets.** Geology Ca/Na/K are the discriminating
   elements; Ti/V/Fe alloys are insensitive. The owner's "let PAS pick among named policies" option is
   the right mechanism, but only continuous policies should be candidates.

---

## 6. Numbers over the LIBS grid

**Constants and sources.** CODATA 2022 via scipy 1.17.1 `scipy.constants`: e, ε₀ =
8.8541878188×10⁻¹² F/m, k_B, and Ry = 13.605693 eV. e²/4πε₀ = 1.439965×10⁻⁹ eV·m. Formula sources
are labelled in the script docstring. Checks reproduced: 0.0660 / 0.0933 eV at 1e17 cm⁻³ / 10⁴ K;
0.9358× at 1e17 / 11 kK (R1-07 and FT-02); 0.1905 / 0.2694 eV and ×1.079 at 1e18 / 12 kK.

Columns: Γ = e²/(akT). N_D uses λ_De. DH-e, DH-ei, 3e-8, SP (FLYCHK form, R₀ from N_i = n_e), SP_Z
(R₀ → R_z), IS and EK are Δχ in eV. `e^{Δχ/kT}` is the Saha-factor change. `ei/e n_e` =
exp((Δχ_ei − Δχ_e)/kT) is the factor by which an inverse n_e changes when DH-e is replaced by DH-ei.
q = Δχ_ei/2kT is the FT-02 contraction rate. n_max(HM) is the HM88 eq. 4.42 level with w = e⁻¹.
Its Z_a is the charge of the radiator's ionic core, taken as z: +1 for a neutral's Rydberg series,
+2 for a singly charged ion's. The sub-search read Z_a this way in the HM88 scan; Alimohamadi &
Ferland gloss Z_a as the perturber charge. z²Ry/n_max² is my hydrogenic conversion of that level to
an energy below the unlowered limit. It is not a published IPD.

| n_e[cm-3] | T[eV] | z | Γ | N_D | DH-e | DH-ei | 3e-8 | SP | SP_Z | IS | EK | SP/DHei | e^{DHe/kT} | e^{DHei/kT} | ei/e n_e | q=DHei/2kT | n_max(HM) | z²Ry/n_max² |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| 1e+15 | 0.5 | 1 | 0.046 | 19.2 | 0.0087 | 0.0123 | 0.0125 | 0.0120 | 0.0120 | 0.0348 | 0.0123 | 0.977 | 1.0175 | 1.0248 | 1.0072 | 0.0123 | 12.00 | 0.094 |
| 1e+15 | 1.0 | 1 | 0.023 | 54.4 | 0.0061 | 0.0087 | 0.0088 | 0.0086 | 0.0086 | 0.0348 | 0.0087 | 0.992 | 1.0061 | 1.0087 | 1.0025 | 0.0043 | 12.00 | 0.094 |
| 1e+15 | 1.5 | 1 | 0.015 | 100.0 | 0.0050 | 0.0071 | 0.0072 | 0.0070 | 0.0070 | 0.0348 | 0.0071 | 0.995 | 1.0033 | 1.0047 | 1.0014 | 0.0024 | 12.00 | 0.094 |
| 1e+15 | 2.0 | 1 | 0.012 | 153.9 | 0.0043 | 0.0061 | 0.0062 | 0.0061 | 0.0061 | 0.0348 | 0.0061 | 0.997 | 1.0022 | 1.0031 | 1.0009 | 0.0015 | 12.00 | 0.094 |
| 1e+16 | 0.5 | 1 | 0.100 | 6.1 | 0.0274 | 0.0387 | 0.0394 | 0.0362 | 0.0362 | 0.0750 | 0.0387 | 0.935 | 1.0563 | 1.0806 | 1.0230 | 0.0387 | 8.83 | 0.175 |
| 1e+16 | 1.0 | 1 | 0.050 | 17.2 | 0.0194 | 0.0274 | 0.0278 | 0.0267 | 0.0267 | 0.0750 | 0.0274 | 0.974 | 1.0196 | 1.0278 | 1.0081 | 0.0137 | 8.83 | 0.175 |
| 1e+16 | 1.5 | 1 | 0.033 | 31.6 | 0.0158 | 0.0224 | 0.0227 | 0.0220 | 0.0220 | 0.0750 | 0.0224 | 0.986 | 1.0106 | 1.0150 | 1.0044 | 0.0075 | 8.83 | 0.175 |
| 1e+16 | 2.0 | 1 | 0.025 | 48.7 | 0.0137 | 0.0194 | 0.0197 | 0.0192 | 0.0192 | 0.0750 | 0.0194 | 0.991 | 1.0069 | 1.0097 | 1.0028 | 0.0048 | 8.83 | 0.175 |
| 1e+17 | 0.5 | 1 | 0.215 | 1.9 | 0.0866 | 0.1225 | 0.1245 | 0.1034 | 0.1034 | 0.1616 | 0.1225 | 0.844 | 1.1892 | 1.2776 | 1.0744 | 0.1225 | 6.49 | 0.323 |
| 1e+17 | 1.0 | 1 | 0.108 | 5.4 | 0.0613 | 0.0866 | 0.0881 | 0.0805 | 0.0805 | 0.1616 | 0.0866 | 0.929 | 1.0632 | 1.0905 | 1.0257 | 0.0433 | 6.49 | 0.323 |
| 1e+17 | 1.5 | 1 | 0.072 | 10.0 | 0.0500 | 0.0707 | 0.0719 | 0.0678 | 0.0678 | 0.1616 | 0.0707 | 0.958 | 1.0339 | 1.0483 | 1.0139 | 0.0236 | 6.49 | 0.323 |
| 1e+17 | 2.0 | 1 | 0.054 | 15.4 | 0.0433 | 0.0613 | 0.0623 | 0.0595 | 0.0595 | 0.1616 | 0.0613 | 0.972 | 1.0219 | 1.0311 | 1.0090 | 0.0153 | 6.49 | 0.323 |
| 1e+18 | 0.5 | 1 | 0.464 | 0.6 | 0.2739 | 0.3874 | 0.3938 | 0.2715 | 0.2715 | 0.3482 | 0.3874 | 0.701 | 1.7296 | 2.1702 | 1.2547 | 0.3874 | 4.78 | 0.596 |
| 1e+18 | 1.0 | 1 | 0.232 | 1.7 | 0.1937 | 0.2739 | 0.2785 | 0.2280 | 0.2280 | 0.3482 | 0.2739 | 0.832 | 1.2137 | 1.3151 | 1.0835 | 0.1370 | 4.78 | 0.596 |
| 1e+18 | 1.5 | 1 | 0.155 | 3.2 | 0.1582 | 0.2237 | 0.2274 | 0.1992 | 0.1992 | 0.3482 | 0.2237 | 0.891 | 1.1112 | 1.1608 | 1.0446 | 0.0746 | 4.78 | 0.596 |
| 1e+18 | 2.0 | 1 | 0.116 | 4.9 | 0.1370 | 0.1937 | 0.1969 | 0.1786 | 0.1786 | 0.3482 | 0.1937 | 0.922 | 1.0709 | 1.1017 | 1.0288 | 0.0484 | 4.78 | 0.596 |
| 1e+15 | 0.5 | 2 | 0.046 | 19.2 | 0.0173 | 0.0245 | 0.0249 | 0.0239 | 0.0234 | 0.0696 | 0.0245 | 0.977 | 1.0353 | 1.0502 | 1.0145 | 0.0245 | 18.19 | 0.165 |
| 1e+15 | 1.0 | 2 | 0.023 | 54.4 | 0.0123 | 0.0173 | 0.0176 | 0.0172 | 0.0170 | 0.0696 | 0.0173 | 0.992 | 1.0123 | 1.0175 | 1.0051 | 0.0087 | 18.19 | 0.165 |
| 1e+15 | 1.5 | 2 | 0.015 | 100.0 | 0.0100 | 0.0141 | 0.0144 | 0.0141 | 0.0140 | 0.0696 | 0.0141 | 0.995 | 1.0067 | 1.0095 | 1.0028 | 0.0047 | 18.19 | 0.165 |
| 1e+15 | 2.0 | 2 | 0.012 | 153.9 | 0.0087 | 0.0123 | 0.0125 | 0.0122 | 0.0122 | 0.0696 | 0.0123 | 0.997 | 1.0043 | 1.0061 | 1.0018 | 0.0031 | 18.19 | 0.165 |
| 1e+16 | 0.5 | 2 | 0.100 | 6.1 | 0.0548 | 0.0775 | 0.0788 | 0.0725 | 0.0688 | 0.1500 | 0.0775 | 0.935 | 1.1158 | 1.1676 | 1.0464 | 0.0775 | 13.38 | 0.304 |
| 1e+16 | 1.0 | 2 | 0.050 | 17.2 | 0.0387 | 0.0548 | 0.0557 | 0.0534 | 0.0522 | 0.1500 | 0.0548 | 0.974 | 1.0395 | 1.0563 | 1.0162 | 0.0274 | 13.38 | 0.304 |
| 1e+16 | 1.5 | 2 | 0.033 | 31.6 | 0.0316 | 0.0447 | 0.0455 | 0.0441 | 0.0435 | 0.1500 | 0.0447 | 0.986 | 1.0213 | 1.0303 | 1.0088 | 0.0149 | 13.38 | 0.304 |
| 1e+16 | 2.0 | 2 | 0.025 | 48.7 | 0.0274 | 0.0387 | 0.0394 | 0.0384 | 0.0380 | 0.1500 | 0.0387 | 0.991 | 1.0138 | 1.0196 | 1.0057 | 0.0097 | 13.38 | 0.304 |
| 1e+17 | 0.5 | 2 | 0.215 | 1.9 | 0.1733 | 0.2450 | 0.2491 | 0.2068 | 0.1868 | 0.3232 | 0.2450 | 0.844 | 1.4141 | 1.6324 | 1.1543 | 0.2450 | 9.84 | 0.562 |
| 1e+17 | 1.0 | 2 | 0.108 | 5.4 | 0.1225 | 0.1733 | 0.1761 | 0.1609 | 0.1521 | 0.3232 | 0.1733 | 0.929 | 1.1303 | 1.1892 | 1.0521 | 0.0866 | 9.84 | 0.562 |
| 1e+17 | 1.5 | 2 | 0.072 | 10.0 | 0.1000 | 0.1415 | 0.1438 | 0.1355 | 0.1307 | 0.3232 | 0.1415 | 0.958 | 1.0690 | 1.0989 | 1.0280 | 0.0472 | 9.84 | 0.562 |
| 1e+17 | 2.0 | 2 | 0.054 | 15.4 | 0.0866 | 0.1225 | 0.1245 | 0.1190 | 0.1160 | 0.3232 | 0.1225 | 0.972 | 1.0443 | 1.0632 | 1.0181 | 0.0306 | 9.84 | 0.562 |
| 1e+18 | 0.5 | 2 | 0.464 | 0.6 | 0.5479 | 0.7748 | 0.7877 | 0.5429 | 0.4667 | 0.6964 | 0.7748 | 0.701 | 2.9914 | 4.7096 | 1.5744 | 0.7748 | 7.24 | 1.038 |
| 1e+18 | 1.0 | 2 | 0.232 | 1.7 | 0.3874 | 0.5479 | 0.5570 | 0.4559 | 0.4098 | 0.6964 | 0.5479 | 0.832 | 1.4731 | 1.7296 | 1.1741 | 0.2739 | 7.24 | 1.038 |
| 1e+18 | 1.5 | 2 | 0.155 | 3.2 | 0.3163 | 0.4473 | 0.4548 | 0.3984 | 0.3681 | 0.6964 | 0.4473 | 0.891 | 1.2348 | 1.3475 | 1.0913 | 0.1491 | 7.24 | 1.038 |
| 1e+18 | 2.0 | 2 | 0.116 | 4.9 | 0.2739 | 0.3874 | 0.3938 | 0.3572 | 0.3361 | 0.6964 | 0.3874 | 0.922 | 1.1468 | 1.2137 | 1.0584 | 0.0969 | 7.24 | 1.038 |

EK critical density (Z̄ = 1): N_cr = 1.0×10¹⁹ (0.5 eV), 8.0×10¹⁹ (1 eV), 2.7×10²⁰ (1.5 eV),
6.4×10²⁰ cm⁻³ (2 eV). All are above N_i(1+Z̄) = 2n_e, so EK stays on its DH-ei branch everywhere
on the grid.

**Readings (all my computation).**
- **Coupling.** Γ = 0.012–0.46 and N_D = 0.6–154. The Debye picture (N_D ≫ 1) holds for
  n_e ≤ 1e16. It is marginal at 1e17 (N_D 1.9–15) and fails at 1e18 with T ≤ 1 eV (N_D 0.6–1.7).
  Realized LIBS trajectories run roughly diagonally (high n_e with high T early, low n_e with low T
  late), so the 1e18 / 0.5 eV corner is rarely occupied in practice. 1e17 / 0.6–1 eV is common.
- **DH-e → DH-ei** raises n_e from an IPD-aware inverse by ×1.001–1.25 for z = 1: ×1.026 at
  1e17 / 1 eV and ×1.084 at 1e18 / 1 eV. At the II→III edge (z = 2) the factor is ×1.002–1.57.
- **SP/DH-ei** = 0.70–1.00. Model disagreement is largest exactly where Debye theory is marginal.
- **Microfield level dissolution (HM / Inglis–Teller) is larger than any IPD.**
  - At 1e17 the w = e⁻¹ level of a neutral's series sits about 0.32 eV below the limit
    (n_max ≈ 6.5), while Δχ_DH-ei = 0.06–0.12 eV.
  - At 1e15 it is 0.094 eV against Δχ ≈ 0.006–0.012 eV.
  - Over the grid the ratio (z²Ry/n_max²)/Δχ_DH-ei is 1.5–15 for z = 1 and 1.3–13 for z = 2
    (2.2–22 and 1.9–19 against DH-e). It is largest at low density and high T, where the DH Δχ is
    tiny.
  - A cutoff at χ − Δχ_DH therefore keeps levels the microfield has already largely dissolved. It
    is not a physically meaningful "last level" (see §5 for the HM88 statement that such cutoffs are
    "not physically related to a 'lowering of the ionization potential'").
- **FT-02 contraction rate.** q = Δχ/(2kT) ≤ 0.39 for z = 1 on the grid. The z = 2 edge reaches
  0.77 at 1e18 / 0.5 eV, which is still < 1 but close to the fold.
- **SP log-elasticity** d ln Δχ_SP / d ln n_e = 0.40–0.50 on the grid, against exactly 0.5 for DH
  (separate finite-difference check, not in the table).

**Script** (`/tmp/ipd/ipd_grid.py`, reproduced verbatim so it can be rerun):

```python
"""IPD / coupling numerics over the LIBS grid (memo section 6).

Constants: CODATA 2022 values via scipy.constants (scipy 1.17.1; eps0 = 8.8541878188e-12 F/m)
(e, epsilon_0, k_B, eV, Rydberg energy). Formulas and their sources:
  DH-e   : dchi = Z e^2/(4 pi eps0 lambda_De), lambda_De^2 = eps0 kT/(n_e e^2)          [pipeline partition.py; electron-only]
  DH-ei  : same with lambda_D^-2 = e^2 (n_e + sum_i z_i^2 n_i)/(eps0 kT)                 [Lin 2019 eq.120-127; Benredjem 2023 eq.1]
           here all ions singly charged, n_i = n_e  ->  lambda_D = lambda_De/sqrt(2)
  3e-8   : dchi = 3e-8 Z sqrt(n_e[cm^-3]/T[K]) eV                                       [Alimohamadi & Ferland 2022 eq.13, attributing Mihalas 1978 eq.9-106]
  SP     : dchi = 3 Z e^2/(2 R) * {[1+(lambda_D/R)^3]^(2/3) - (lambda_D/R)^2}           [Benredjem et al. 2023 eq.1, their (z+1) == our Z]
           R = R0 = (3/(4 pi N_i))^(1/3), N_i = n_e (Zbar = 1)
  SP_Z   : same with ion-sphere radius of the product ion R_Z = (3 Z/(4 pi n_e))^(1/3)   [algebraic identity with the original SP 1966 form; memo sec.3]
  IS     : dchi = 3 Z e^2/(2 R0)  (high-density limit of SP)                              [Benredjem 2023 eq.2]
  EK     : Benredjem 2023 eq.3 with Zbar = 1: DH-ei if N_cr >= N_i(1+Zbar), else ion-sphere-like branch;
           N_cr = (3/4pi) (kT/(Zbar^2 e^2))^3
  HM/IT  : n_max = 1.2e3 N_e^(-2/15) Za^(3/5) (HM88 eq.4.42; Alimohamadi & Ferland 2022 eq.16).
           Za = charge of the radiator's ionic core (HM88 text, read from the ADS scan by the sub-search;
           A&F gloss it as the perturber charge). Here Za = Z (core of an I-series is +1, of a II-series +2).
           Equivalent energy gap below the (unlowered) limit: dE = Za^2 Ry / n_max^2
           (hydrogenic; my conversion, not a published IPD)
Coupling: a_e = (3/(4 pi n_e))^(1/3); Gamma_e = e^2/(4 pi eps0 a_e kT); N_D = (4 pi/3) n_e lambda_De^3.
"""
import math
from scipy import constants as C

E2 = C.e**2 / (4 * math.pi * C.epsilon_0) / C.e      # e^2/(4 pi eps0) in eV*m  (1.43996e-9)
RY = C.physical_constants["Rydberg constant times hc in eV"][0]  # 13.605693 eV
KB_EV = C.k / C.e                                     # 8.617333e-5 eV/K

def grid_row(ne_cm3, T_eV, Z):
    n = ne_cm3 * 1e6                     # m^-3
    kT = T_eV                            # eV
    lam_e = math.sqrt(C.epsilon_0 * kT * C.e / (n * C.e**2))  # m  (kT in J = T_eV*e)
    lam_ei = lam_e / math.sqrt(2.0)
    a = (3.0 / (4 * math.pi * n)) ** (1 / 3)
    gam = E2 / (a * kT)
    ND = 4 * math.pi / 3 * n * lam_e**3
    dh_e = Z * E2 / lam_e
    dh_ei = Z * E2 / lam_ei
    T_K = T_eV / KB_EV
    f3e8 = 3e-8 * Z * math.sqrt(ne_cm3 / T_K)
    def sp(R):
        x = lam_ei / R
        return 1.5 * Z * E2 / R * ((1 + x**3) ** (2 / 3) - x**2)
    R0 = a                                  # N_i = n_e for Zbar = 1
    RZ = (3 * Z / (4 * math.pi * n)) ** (1 / 3)
    sp0, spZ = sp(R0), sp(RZ)
    ion_sphere = 1.5 * Z * E2 / R0
    Ncr = 3 / (4 * math.pi) * (kT / E2) ** 3 / 1e6   # cm^-3, Zbar = 1
    ek = dh_ei if Ncr >= ne_cm3 * 2 else None       # N_i(1+Zbar) = 2 n_e
    nmax = 1.2e3 * ne_cm3 ** (-2 / 15) * Z ** 0.6   # Za = Z (core charge)
    dE_hm = Z**2 * RY / nmax**2
    return dict(ne=ne_cm3, T=T_eV, Z=Z, Gamma=gam, ND=ND, lam_e_nm=lam_e * 1e9,
                dh_e=dh_e, dh_ei=dh_ei, f3e8=f3e8, sp=sp0, spZ=spZ, IS=ion_sphere,
                ek=ek, Ncr=Ncr, nmax=nmax, dE_hm=dE_hm,
                saha_e=math.exp(dh_e / kT), saha_ei=math.exp(dh_ei / kT),
                ei_over_e=math.exp((dh_ei - dh_e) / kT), sp_over_ei=sp0 / dh_ei,
                q_ei=dh_ei / (2 * kT))

if __name__ == "__main__":
    print(f"e^2/(4 pi eps0) = {E2:.6e} eV m ; Ry = {RY:.6f} eV ; k_B = {KB_EV:.6e} eV/K")
    # CGS-equivalent coefficient check: dchi[eV] = c * sqrt(n[cm^-3]/T[K])
    for lbl, fac in (("4pi (DH-e)", 1.0), ("8pi (DH-ei)", 2.0)):
        r = grid_row(1e17, 1e4 * KB_EV, 1)
        val = r["dh_e"] if fac == 1.0 else r["dh_ei"]
        print(f"coefficient {lbl}: {val / math.sqrt(1e17 / 1e4):.4e} eV (cm^-3/K)^-1/2 ; dchi(1e17,1e4K) = {val:.4f} eV")
    r = grid_row(1e17, 11000 * KB_EV, 1)
    print(f"check R1-07/FT-02: DH-e at 1e17/11kK: dchi={r['dh_e']:.4f} eV, exp(-dchi/kT)={1/r['saha_e']:.4f}")
    r = grid_row(1e18, 12000 * KB_EV, 1)
    print(f"check R1-07: 1e18/12kK DH-e {r['dh_e']:.4f} DH-ei {r['dh_ei']:.4f} eV, Saha ratio {r['ei_over_e']:.3f}")
    hdr = ("n_e[cm-3]", "T[eV]", "Z", "Gamma", "N_D", "DH-e", "DH-ei", "3e-8", "SP", "SP_Z", "IS", "EK", "SP/DHei",
           "e^{DHe/kT}", "e^{DHei/kT}", "ei/e n_e", "q=DHei/2kT", "n_max(HM)", "Z^2Ry/n_max^2")
    print("| " + " | ".join(hdr) + " |")
    print("|" + "---|" * len(hdr))
    for Z in (1, 2):
        for ne in (1e15, 1e16, 1e17, 1e18):
            for T in (0.5, 1.0, 1.5, 2.0):
                r = grid_row(ne, T, Z)
                ek = f"{r['ek']:.4f}" if r["ek"] is not None else "IS-branch"
                print(f"| {ne:.0e} | {T} | {Z} | {r['Gamma']:.3f} | {r['ND']:.1f} | {r['dh_e']:.4f} | {r['dh_ei']:.4f} | "
                      f"{r['f3e8']:.4f} | {r['sp']:.4f} | {r['spZ']:.4f} | {r['IS']:.4f} | {ek} | {r['sp_over_ei']:.3f} | "
                      f"{r['saha_e']:.4f} | {r['saha_ei']:.4f} | {r['ei_over_e']:.4f} | {r['q_ei']:.4f} | "
                      f"{r['nmax']:.2f} | {r['dE_hm']:.3f} |")
    # N_cr for EK over the T grid
    for T in (0.5, 1.0, 1.5, 2.0):
        print(f"EK critical density (Zbar=1) at T={T} eV: N_cr = {grid_row(1e17, T, 1)['Ncr']:.2e} cm^-3")
```

---

## 7. Implications

### 7.1 Formal spec (cflibs-formal)

- **No core module encodes IPD yet.** `rg -i "ipd|ionization potential depression|debye"` over
  `CflibsFormal/` matched only the substring in `Mlipdef` (SahaEquilibrium.lean:783). That match is
  the positive control that the pattern ran. IPD formal work lives in audit scratch:
  `evidence/plasma-state/IPDGauge.lean` (`sahaFactor_ipd_gauge`, `ne_ipd_mismatch`, re-checked rc = 0
  by the auditor) and the FT-02 slate (`frontier-proposer/Slate.lean`, `Slate.FT02`).
- **Family covered by FT-02 (Δχ = kT·b·√n_e, b abstract).** DH-e, DH-ei at fixed CSD, the 3e-8 form,
  EK on the LIBS grid, and the weak-coupling limit of SP and Lin all have the form Δχ = c·z·√(n_e/T).
  So **b = c·z/(k_B T·√T)** with c = 2.087×10⁻⁸ (DH-e), 2.951×10⁻⁸ (DH-ei, z* = 1) or 3.0×10⁻⁸
  eV·(cm⁻³/K)^−½. FT-02's gauge, unique-root, contraction (q = Δχ/2kT) and log-sensitivity
  −1/(1−q) results then cover every one of these by instantiation. **The coefficient choice does not
  need new theorems.**
- **In-family caveat.** For DH-ei with mixed charge states, c ∝ (1+z*)^½ and z* comes from the Saha
  solution. It is in the family only if the CSD shape is held fixed within the inner loop, as FT-02
  already assumes for T. Otherwise b = b(ℓ) and the contraction constant needs a bound on
  d ln b/dℓ. At LIBS z* ≈ 1 this is a few-percent effect (inference).
- **Out of family: SP proper, ion sphere, Unsöld, EK's strong branch.** Suggested generalization
  (not yet stated or proved): replace b·e^{ℓ/2} by any C¹ g(ℓ) = Δχ(e^ℓ)/kT with 0 ≤ g′ ≤ q̄ < 1 on
  the invariant set. Since g′ = ε(n)·Δχ/kT with log-elasticity ε ∈ [0, ½] for DH, SP and IS (SP
  0.40–0.50 measured above), and since Δχ_SP ≤ Δχ_DH-ei on the grid, q_SP ≤ q_DH-ei. A theorem over
  "monotone Δχ with log-elasticity ≤ ½, dominated by Δχ_DH" would cover all of them. The gauge part
  (a) holds for any Δχ that is element-independent.
- **Cutoff and the Lipschitz theorems.**
  - A sharp n_e-moving cutoff makes U(n_e) a step function, with 178 Ca I levels crossing between
    1e16 and 1e18 (audit). No Lipschitz constant exists, and every contraction or Lipschitz theorem
    that treats U as n_e-independent or Lipschitz in n_e is vacuous for it.
  - A **fixed** cutoff makes U independent of n_e, so the existing theorems apply unchanged.
  - **Occupation-probability weights** w_i(n_e, T) ∈ (0, 1] that are smooth and decreasing in n_e
    make U = Σ g_i w_i e^{−E_i/kT} smooth and monotone. |∂ ln U/∂ ln n_e| ≤ max_i |∂ ln w_i/∂ ln n_e|,
    which gives an explicit Lipschitz constant on any bounded box (inference; a proof obligation to
    state abstractly over w). The HHL94 closed form (§5.1 P3) is a rational function of powers of
    n_e and T, so the bound is computable. Its physics validity (a ≤ 0.8) is a separate, prose-level
    caveat.
  - Hummer–Mihalas weights are *not* an IPD. They change U, not χ.
- **Scope tags.** An IPD theorem instantiated at DH-ei should be tagged APPROXIMATION (weak-coupling
  model), with the N_D ≫ 1 caveat in prose. The gauge identity is EXACT (algebra). Any SP
  instantiation is APPROXIMATION.
  - Per the citation-integrity rule, none of the new sources here are in
    `docs/citation-whitelist.tsv`.
  - Candidates for VERIFIED rows with located equations (opened this session): Piron 2023 (eq. 57–59),
    Lin 2019 (eq. 120–128), Benredjem 2023 (eq. 1–3), Inglis–Teller 1939 (eq. 5), Alimohamadi–Ferland
    2022 (eq. 12–16), Stewart–Pyatt 1966 (p. 1210 recipe; ADS scan) and HM88 (p. 797–798; ADS scan).
  - Griem 1962 was seen only as an abstract. It stays UNVERIFIED until the paper is opened.

### 7.2 Pipeline (CF-LIBS-improved)

- **One IPD function, one setting, every path.** Forward (CPU and kernels), inverse (iterative, lax,
  jitpipe) and synthetic generators must share it. The jit inverse's duplicated constants
  (6.9·√(T/n_e), 1.44×10⁻⁷) go away (R1-07).
- **Fix the inverse II→III edge to 2Δχ₁.** Every source that states the charge factor uses the
  charge after ionization (Piron eq. 59, (Z*+1); Benredjem eq. 1–3, (z+1); Lin eq. 127, (z_α+1)).
- **The stage-III edge breaks the IPD gauge (inference, from the Saha gauge identity).** With only
  I→II lines, an IPD-off inverse identifies n_e·e^{−Δχ/kT}, and composition is unchanged because a
  common factor cancels (FT-02 (a)). With stage-III lines, n_III/n_II ∝ e^{2Δχ/kT}/n_e. Using the
  I→II-calibrated n̂ = n_e e^{−Δχ/kT} without IPD predicts III/II too low by e^{Δχ/kT}, which is
  1.09 at 1e17 / 1 eV (DH-ei). So for Ti/V alloys at high T, where III lines matter, the IPD choice
  (and the 1Δχ-vs-2Δχ bug) does reach composition.
- **Decouple the level cutoff from Δχ.**
  - If "debye_huckel" stays as a named cutoff arm for PAS, freeze it within the inner loop. It then
    cannot inject discontinuities into the fixed-point iteration.
  - Report it as a legacy/control arm, not a physics candidate: its cut sits 1.5–15× closer to the
    limit than the microfield dissolution energy (§6). HM88 states that such cutoffs are "not
    physically related to a 'lowering of the ionization potential'" (§5.2).
  - All policies exclude levels at or above the *unperturbed* IP (202/324 species list such levels).
- **PAS arms (suggested).**
  - IPD: {off, DH-e, DH-ei, SP}. DH-ei is the physics default; SP is a sensitivity arm; off and
    DH-e are controls.
  - Cutoff: {fixed at unperturbed IP, HM occupation probability, DH-moving (frozen, control)}.
  - Promote only arms that are forward/inverse consistent *and* use one U in both the Boltzmann and
    the Saha step. Mixed U is the only route by which the ×1.05–4 U spread reaches composition
    undiluted (§5.3).
  - With consistency enforced, the IPD arm should move reported n_e (×1.03–1.25) and composition
    only through stage III and Stark-anchored n_e.
  - The cutoff arm should move Na/K/Ca/Mg/Al totals by ≲ 1.5% at ≤ 1e17 and 5–12% at 1e18, and
    Ti/V/Fe negligibly.

---

## 8. Tools used and what each contributed

Tools are listed in order of how much they contributed. Where a tool failed, it says so.

| Tool | What it did here | Contribution | Failures and gotchas |
|---|---|---|---|
| **PDF download + `pdftotext` / `pdftoppm` + reading** (arXiv, ADS scans, HAL, OA publishers) | The primary evidence path | Every [read] tag. The equations in §2–§5 came from full texts (Piron, Lin, Crowley, Benredjem, Alimohamadi–Ferland, Inglis–Teller, Son, Zaghloul, Frontiers; SP 1966 and HM88 pages checked as images) | ADS scans have no text layer and tesseract is not installed, so they have to be read as images. ScienceDirect, SAGE and AIP return 403 |
| **arXiv MCP (`gpd-arxiv`)** | `search_papers` for IPD, SP, EK | None: every call returned "HTTP 406" from `export.arxiv.org`. `curl` to the same endpoint also gets 406, so the arXiv *API* was refusing requests on 2026-09-24 | Workaround: scrape `arxiv.org/search/` (HTML), then download the PDF. That found Crowley, Son, Lin ×3, Alimohamadi–Ferland, Zaghloul, Benredjem, Pérez-Callejo, Kasim, Šmíd, Wu ×2 and Gomez |
| **Asta Paper Finder** (`asta literature interactive`) | Three threads: `.asta/literature/threads/2026-09-24-ipd` (LIBS usage), `…-ipd-sp` (SP critiques, 2 turns), `…-ipd-cutoff` (cutoffs) | **cutoff thread: good.** It surfaced SP 1966's level-deletion text, Zaghloul 2012, Trampedach 2006, Sengebusch 2017, Halenka 2001, Henkel 2025, Potekhin and Lin 2026. **SP thread, turn 1 (broad): false negative.** "No papers were found … Confidence is very low", and the log shows it issuing *empty-string* searches. **Turn 2 (narrow)** returned the landmark papers (Vinko, Hoarty, Preston 2013, Pérez-Callejo, Lin, Iglesias). **LIBS thread: overconfident negative.** It reported no LIBS paper applies IPD "with high confidence", yet it missed Ristić et al. 2024 (PPCF, laser-induced plasma, continuum lowering) and the Gornushkin, MERLIN and De Giacomo–Hermann papers the sub-search then found | Treat its negatives as weak unless a narrow retry agrees. The memory note (broad queries exhaust the budget; retry narrow in the same thread) was confirmed |
| **Asta `papers snippet-search` / `papers get`** | Full-text snippet search; metadata and abstract by DOI | Leads for Aguilera 2021/2007, Dell'Aglio, Seitkozhanov, Lee, Fayyaz, the NIST *Atoms* paper, TLUSTY, Bonitz–Kordts; Ristić 2024 abstract (`papers get`) | Noisy: ranking is dominated by generic "Debye length" LIBS papers. No body text for paywalled Elsevier or SAGE |
| **NotebookLM** (new notebook **"IPD and partition-function cutoff for LIBS plasmas (2026-09)"**, id **`ebaaf203-4cbd-49f9-ad74-39c113ffb330`**, 25 sources) | Deep research, source ingestion, grounded Q&A | **Cross-check: useful.** Once the *PDFs* were uploaded, it quoted Piron eq. 58–59, Crowley's TIPD = ⅔·SCL passage, Crowley's Γ values for the XFEL/Orion experiments, the HM88 passages on cutoffs (p. 798) and on discontinuities from abruptly deleted states, and the SP 1966 recipe, all matching my reads. It OCR'd the ADS scans that `pdftotext` could not. It independently flagged the Piron–Crowley disagreement (§3.2 iii) | **Deep research (`research_start` mode=deep) never finished.** Still "in_progress" with 0 sources after ~1.5 h (task id `ChA5N2RiNTNjNWVkMTFiMzU2EAgaATAqA3VzYw`, later reported as `ead3665c-4bc3-4318-be58-c7eb6e820840`). **Adding arXiv `/abs/` URLs ingests only the abstract page,** so equation-level questions came back ungrounded. Upload the PDF instead. The old CF-LIBS notebook (`e1dd4578…`) answered an IPD question with `sources_used: []`, i.e. ungrounded; only its Frontiers claim was kept, after I read the PDF |
| **WebSearch / WebFetch** | Locating PDFs and DOIs | Found the Inglis–Teller 1939 ADS-scan mirror, the Piron 2023 review, the Frontiers PDF and Ebeling 2017 (snippet). The sub-agents used it for Griem 1962 (abstract) and several OA copies | WebFetch paraphrases unless asked for verbatim text |
| **Sub-agents (2 × general-purpose)** | Parallel literature extraction: LIBS usage (§4) and cutoff policies (§5) | Found and read about 30 more papers, rendered equations to images, **ran the live NIST LIBS tool** (showed it applies no IPD) and **read its `saha_lte.js`** (it sums all ASD levels) | I spot-checked Shabanov–Gornushkin eq. 7, the MERLIN eq. 4 text, HM88 p. 797 and SP 1966 p. 1210 myself. **Privacy slip, reported by the sub-agent:** one Unpaywall API call sent the user's e-mail address as the required `email` parameter, where a placeholder should have been used |
| **Consensus, Scholar Gateway MCPs** | — | Not used: only `authenticate` / `complete_authentication` tools are exposed, which means interactive OAuth | — |
| **Local Python** (`scipy.constants`, CODATA 2022) | §6 grid and elasticity check | All numbers in §6; reproduces R1-07 and FT-02 exactly | — |

**Tools not installed that would materially help** (named only; nothing installed):
- **A working arXiv search backend.** The `gpd-arxiv` MCP depends on `export.arxiv.org`, which returned 406. An OAI-PMH or HTML-scrape fallback inside the MCP would have saved the workaround.
- **An OCR engine (`tesseract`/`ocrmypdf`)**, because the pre-1990 ADS scans (SP 1966, HM88, Irwin 1981, Inglis–Teller 1939) have no text layer and could only be read as images or through NotebookLM.
- **An Unpaywall/OpenAlex-backed "legal OA PDF" fetcher with a project-level contact address** configured once (not the user's personal e-mail per call). This would have avoided the privacy slip and the 403 walls.

---

## 9. Bibliography

Tags: [read] = I opened the full text. [read-SA] / [read-SB] = a sub-agent opened the full text this
session ("checked" = I viewed the page too). [secondary] = known only through a paper I read.
[abstract] / [snippet] = abstract or snippet only. [verified-file] = in `docs/citation-whitelist.tsv`
or the `cflibs-literature` memory. Metadata was confirmed this session with `asta papers get` or the
arXiv abstract page unless marked otherwise.

**IPD models and theory**
1. Stewart, J. C. & Pyatt, K. D., Jr. (1966). Lowering of ionization potentials in plasmas. *ApJ* 144, 1203. doi:10.1086/148714. [read-SB, p. 1210 checked; NotebookLM OCR]
2. Ecker, G. & Kröll, W. (1963). Lowering of the ionization energy for a plasma in thermodynamic equilibrium. *Phys. Fluids* 6, 62. doi:10.1063/1.1724509. [secondary: Benredjem eq. 3, Son 2014, Crowley 2014]
3. Inglis, D. R. & Teller, E. (1939). Ionic depression of series limits in one-electron spectra. *ApJ* 90, 439. [read, ADS scan via ENEA mirror; eq. 5 and summary]
4. Griem, H. R. (1962). High-density corrections in plasma spectroscopy. *Phys. Rev.* 128, 997. doi:10.1103/PhysRev.128.997. [abstract via WebFetch; the (z+1)e²/λ_D form is secondary via Piron 2023 ref. 43, Seitkozhanov 2025, MERLIN 2025]
5. Crowley, B. J. B. (2014). Continuum lowering – a new perspective. *High Energy Density Physics* (ScienceDirect pii S1574181814000287); arXiv:1309.1456 (AWE Report 659/13). [read]
6. Son, S.-K., Thiele, R., Jurek, Z., Ziaja, B. & Santra, R. (2014). Quantum-mechanical calculation of ionization potential lowering in dense plasmas. *Phys. Rev. X* 4, 031004. doi:10.1103/PhysRevX.4.031004; arXiv:1404.5484. [read]
7. Lin, C., Röpke, G., Kraeft, W.-D. & Reinholz, H. (2017). Ionization-potential depression and dynamical structure factor in dense plasmas. *Phys. Rev. E* 96, 013202. doi:10.1103/PhysRevE.96.013202; arXiv:1703.00801. [read, partial]
8. Lin, C. (2019). Ionization potential depression and ionization balance in dense plasmas. arXiv:1904.04456. [read; §V A eq. 120–128]
9. Lin, C., Röpke, G., Reinholz, H. & Kraeft, W.-D. (2017). Ionization potential depression and optical spectra in a Debye plasma model. arXiv:1709.07279. [read, partial]
10. Benredjem, D., Pain, J.-C., Calisti, A. & Ferri, S. (2023). Ionization by electron impacts and ionization potential depression. arXiv:2309.06966. [read; eq. 1–3, 6]
11. Piron, R. (2023). Atomic models of dense plasmas, applications and current challenges. arXiv:2311.15418. [read; eq. 53–61, §II E]
12. Pérez-Callejo, G. et al. (2024). Dielectronic satellite emission from a solid-density Mg plasma: relationship to models of ionisation potential depression. arXiv:2310.03590 (*Phys. Rev. E*). [abstract + partial]
13. Kasim, M. F., Wark, J. S. & Vinko, S. M. (2018). Validating continuum lowering models via multi-wavelength measurements of integrated X-ray emission. arXiv:1802.01234. [skimmed]
14. Šmíd, M. et al. (2024). Plasma screening in mid-charged ions observed by K-shell line emission. arXiv:2406.06233 (*Sci. Rep.*). [snippet of full text]
15. Wu, C. et al. (2023). Non-LTE ionization potential depression model for warm and hot dense plasma. arXiv:2305.09371; Wu, C. et al. (2025). Ionization potential depression model with the influence of neighboring ions … arXiv:2505.18593. [abstract]
16. Ebeling, W. (2017). Max Planck and Albrecht Unsöld on plasma partition functions and lowering of ionization energy. *Contrib. Plasma Phys.* doi:10.1002/ctpp.201700094. [snippet]
17. Murillo, M. S. & Weisheit, J. C. (1998). Dense plasmas, screened interactions, and atomic ionization. *Phys. Rep.* 302, 1. [secondary: Son 2014 ref. 20; not used for any claim]

**Dense-plasma IPD experiments**
18. Vinko, S. M. et al. (2012). Creation and diagnosis of a solid-density plasma with an X-ray free-electron laser. *Nature* 482, 59. doi:10.1038/nature10746. [secondary + Asta metadata]
19. Ciricosta, O. et al. (2012). Direct measurements of the ionization potential depression in a dense plasma. *PRL* 109, 065002. doi:10.1103/PhysRevLett.109.065002. [secondary + Asta metadata]
20. Hoarty, D. J. et al. (2013). Observations of the effect of ionization-potential depression in hot dense plasma. *PRL* 110, 265003. doi:10.1103/PhysRevLett.110.265003. [secondary + Asta metadata]
21. Preston, T. R. et al. (2013). The effects of ionization potential depression on the spectra emitted by hot dense aluminium plasmas. *HEDP*. [Asta hit only]
22. Iglesias, C. A. (2013/14). Fluctuations and the ionization potential in dense plasmas. [Asta hit only]

**Partition functions and cutoffs**
23. Hummer, D. G. & Mihalas, D. (1988). The equation of state for stellar envelopes. I. An occupation probability formalism for the truncation of internal partition functions. *ApJ* 331, 794. doi:10.1086/166600. [read-SB, ADS scan; p. 797 checked; NotebookLM OCR]
24. Hubeny, I., Hummer, D. G. & Lanz, T. (1994). NLTE model stellar atmospheres with line blanketing near the series limits. *A&A* 282, 151. [read-SB, App. A; title via Asta search]
25. Hubeny, I. & Lanz, T. (2017). TLUSTY User's Guide II: Reference Manual. arXiv:1706.01935. [read-SB]
26. Irwin, A. W. (1981). Polynomial partition function approximations of 344 atomic and molecular species. *ApJS* 45, 621. doi:10.1086/190730. [read-SB, ADS scan]
27. Rogers, F. J. (1986). Occupation numbers for reacting plasmas: the role of the Planck–Larkin partition function. *ApJ* 310, 723. doi:10.1086/164725. [read-SB, ADS scan]
28. Trampedach, R., Däppen, W. & Baturin, V. A. (2006). A synoptic comparison of the Mihalas–Hummer–Däppen and OPAL equations of state. *ApJ* 646, 560. doi:10.1086/504883. [read-SB]
29. Halenka, J., Madej, J., Langer, K. et al. (2001). Tables of the partition functions for nickel, Ni I – Ni X. *Acta Astron.* 51, 347; astro-ph/0201238. [read-SB]
30. Zaghloul, M. R. (2013). Fundamental view on the calculation of internal partition functions using occupational probabilities. *Phys. Lett. A* 377, 1119. doi:10.1016/j.physleta.2013.02.044; arXiv:1210.0053. [read-SB; I grepped it]
31. Potekhin, A. Y. (2010). Comment on "On the ionization equilibrium of hot hydrogen plasma …". *Phys. Plasmas* 17, 124705; arXiv:1103.1621. [read-SB]
32. Alimohamadi, P. & Ferland, G. J. (2022). A practical guide to the partition function of atoms and ions. arXiv:2203.02188. [read; eq. 12–16]
33. Barklem, P. S. & Collet, R. (2016). Partition functions and equilibrium constants for diatomic molecules and atoms of astrophysical interest. *A&A* 588, A96; arXiv:1602.03304. [read-SB]
34. Sengebusch, A., Reinholz, H. & Röpke, G. (2017). Kα emission profiles of warm dense argon plasmas. arXiv:1709.08493. [read-SB]
35. Bonitz, M. & Kordts, L. (2025). Ionization potential depression and Fermi barrier in warm dense matter — a first-principles approach. *Contrib. Plasma Phys.* 65, e70001; arXiv:2502.10548. [read-SB]
36. Ebeling, W., Kraeft, W. D. & Röpke, G. (2012). Bound states in Coulomb systems – old problems and new solutions. arXiv:1110.1962 (*Contrib. Plasma Phys.* 52). [read-SB]
37. Henkel, M. & González, D. (2025). How reliable are line intensities for temperature calculation using the Boltzmann plot method. *Plasma Phys. Technol.* 12, 46. doi:10.14311/ppt.2025.1.46. [read-SB]
38. Yang, P., Liu, H., Wang, F. et al. (2024). The effects of partition function cutoff on spectral temperature measurement in argon plasma. *AIP Adv.* 14, 035038. doi:10.1063/5.0202284. [abstract]
39. Gomez, T. A. et al. (2016). Modeling the spectra of dense hydrogen plasmas: beyond occupation probability. arXiv:1610.02342. [read, partial]

**LIBS / CF-LIBS usage**
40. Shabanov, S. V. & Gornushkin, I. B. (2018). Chemistry in laser-induced plasmas at local thermodynamic equilibrium. *Appl. Phys. A* 124, 716. doi:10.1007/s00339-018-2129-9. [read-SA, eq. 7 checked]
41. Favre, A., Bultel, A., Morel, V. et al. (2025). MERLIN, an adaptative LTE radiative transfer model for any mixture: validation on Eurofer97 in argon atmosphere. *JQSRT* 330, 109222. doi:10.1016/j.jqsrt.2024.109222. [read-SA, eq. 4 checked]
42. De Giacomo, A. & Hermann, J. (2017). Laser-induced plasma emission: from atomic to molecular spectra. *J. Phys. D* 50, 183002. doi:10.1088/1361-6463/aa6585. [read-SA]
43. Seitkozhanov, Dzhumagulova & Shalenov (2025). *Entropy* 27, 253. doi:10.3390/e27030253. [read-SA]
44. Lee et al. (2025). *Sci. Rep.* doi:10.1038/s41598-025-26615-8. [read-SA]
45. Aguilera, J. A. & Aragón, C. (2007). *J. Phys. Conf. Ser.* 59, 210; Aragón & Aguilera (2014) *JQSRT* doi:10.1016/j.jqsrt.2014.07.026; Aguilera, Aragón & Manrique (2015) *JQSRT*; Aguilera & Aragón (2024) *SAB* 217, 106969. [read-SA]. Aguilera & Aragón (2007) *SAB* 62, 378 and Aragón & Aguilera (2014) are also [verified-file].
46. Unnikrishnan, V. K. et al. (2010). *Pramana* 74, 983. doi:10.1007/s12043-010-0089-5. [read-SA, quote checked]
47. Tognoni, E. et al. (2010). CF-LIBS: state of the art. *SAB* 65, 1. [verified-file; read-SA]
48. Zhang, N. et al. (2022). A brief review of calibration-free laser-induced breakdown spectroscopy. *Front. Phys.* 10, 887171. doi:10.3389/fphy.2022.887171. [read]
49. Ralchenko, Yu. & Kramida, A. (2020). Development of NIST atomic databases and online tools. *Atoms* 8, 56. doi:10.3390/atoms8030056. [read-SA]. NIST LIBS tool behaviour: [ran tool + read `saha_lte.js`, SA/SB]
50. Ristić, M. M., Krstevski, N., Ranković, D., Marković, M., Šajić, A. & Kuzmanović, M. (2024). The influence of continuum lowering on the equilibrium composition of plasma: case study of laser-induced plasma on a WC–Cu target. *Plasma Phys. Control. Fusion* 66. doi:10.1088/1361-6587/ad8b68. [abstract, Asta `papers get`]
51. Thomas & Joshi (2023), arXiv:2302.13272; Fayyaz et al. (2023) *Heliyon* 9, e13957; Hermann CF-LIBS chapter (Wiley 2023) doi:10.1002/9781119758396.ch5. [read-SA]
52. Not retrieved (flagged for follow-up): Rajačić et al., *JQSRT* (2025) doi:10.1016/j.jqsrt.2024.109338; Drawin & Felenbok (1965); Mihalas (1978) *Stellar Atmospheres* eq. 9-106; Griem's 1964 and 1997 books.

**Project sources**
- CF-LIBS-improved `docs/overhaul/findings/R1-forward-model-physics-and-atomic-data.md` (R1-02, R1-07) [read]; `cflibs/plasma/partition.py:60-216` [read].
- cflibs-formal `docs/research/audit-2026-09-24/frontier.json` (FT-02) and `evidence/plasma-state/{IPDGauge.lean, cutoff_jumps.py}` [read].
