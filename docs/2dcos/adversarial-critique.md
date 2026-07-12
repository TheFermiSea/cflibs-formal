# Adversarial Critique of the Gated-Delay 2DCOS-LIBS Framework
### A closed-form consolidation for model refinement

**Status:** working critique (mutable). Consolidates the literature-grounded audit in
`ERRATA.md` and the rebuild in `monograph.corrected.md` into a single self-contained argument,
organized so each defect points at a concrete refinement path. Every adjudication traces to a
primary source. Severity: **FATAL** (invalidates a core claim) · **MAJOR** (wrong but locally
repairable) · **OVERSTATED** (a real kernel, over-claimed) · **CITATION** · **CODE**.

---

## 0. How to read this

The original *Gated-Delay 2DCOS for Standardless Quantitative LIBS* monograph is scientifically
unsound in its headline claims, but it is **not worthless** — it sits on a correct mathematical
foundation (§2) and contains one genuinely interesting, *testable* idea (§4.3). The purpose of
this document is not to bury it but to separate the three strata so you can refine deliberately:

1. **Solid ground** (§2) — the 2DCOS algebra you can build on without reservation.
2. **Fatal cores** (§3) — claims that fail as a matter of mathematics; these cannot be patched,
   only replaced.
3. **Overstated-but-salvageable** (§4–§5) — claims with a real kernel that become defensible
   once restated carefully or demoted to testable hypotheses.

Each entry below follows a fixed template: **Claimed → Verdict → Why it fails → Correct
statement → Refinement path** (what a defensible version must supply). §7 gives the constructive
synthesis: what a scientifically honest time-resolved 2DCOS-LIBS paper *can* claim.

---

## 1. Executive verdict

The framework's headline — that gate-delay 2DCOS enables **standardless, electron-density-free,
temperature-free** elemental quantification ("Model B") — does not survive contact with the
mathematics or the literature. It fails on two independent, fatal grounds (§3.1, §3.2). The
supporting "Model A" temperature method and the "energy-weighted covariance" reading are
overstated but hold real kernels (§4.1, §4.2). The only genuinely novel *and* testable proposal
is the self-absorption asynchronous "butterfly" (§4.3) — currently a conjecture, not a result.
The compositional projection is mislabeled (softmax≠ILR; §5). Nine of twenty-three citations are
defective, two apparently fabricated (§6).

**What is true and usable:** the Noda 2DCOS formalism (definitions, the Hilbert–Noda matrix, the
zero-diagonal property, sequential-order rules), the standard LTE/Saha/Boltzmann/Stark plasma
physics, and the fact that a time-resolved series samples a genuine cooling trajectory whose
*correlation structure* (which lines co-vary, in what order) is real information.

**What collapses:** the n_e elimination, the "standardless/temperature-free" claim, the
async↔recombination-flux identity, and any inference that treats a 2DCOS map as a *quantitative
inversion* rather than a *qualitative/ordering* diagnostic.

---

## 2. The solid foundation (build on this without reservation)

These are standard, correct results (Noda 1993; Noda 2000; Noda & Ozaki 2004). They are being
machine-verified in Lean (`docs/frontiers/13-2dcos-formalization.md`, modules `TwoDCOS.lean` /
`Aitchison.lean`).

- **Dynamic spectrum:** `ỹ(ν,t_ℓ) = I(ν,t_ℓ) − Ī(ν)`, `Ī(ν) = (1/m)∑_ℓ I(ν,t_ℓ)`.
- **Synchronous matrix** `Φ(ν₁,ν₂) = 1/(m−1) · ∑_ℓ ỹ(ν₁,t_ℓ) ỹ(ν₂,t_ℓ)` — the sample covariance
  of the two intensity-vs-delay traces. Symmetric; diagonal `Φ(ν,ν)=Var_t[I(ν,·)] ≥ 0`.
- **Hilbert–Noda matrix** `N_{jk} = 0 (j=k), 1/(π(k−j)) (j≠k)`; **skew-symmetric** `Nᵀ = −N`.
  *(This is the soundest element of the original — its engine coded it exactly right.)*
- **Asynchronous matrix** `Ψ(ν₁,ν₂) = 1/(m−1) · ỹ(ν₁)ᵀ N ỹ(ν₂)` — **antisymmetric**; **zero
  diagonal** `Ψ(ν,ν)=0 ∀ν` (because `xᵀNx = −xᵀNx` for skew `N`).
- **Noda's sequential-order rule:** for a genuine cross-peak, `sign Φ(ν₁,ν₂)` and `sign Ψ(ν₁,ν₂)`
  together tell which change happens first (same sign ⇒ ν₁ leads ν₂; opposite ⇒ ν₂ leads ν₁).
- **A load-bearing structural fact for the critique below:** if a *single* temporal driver moves
  every line (`ỹ(ν,t)=s(ν)·δ(t)`), then `Ψ ≡ 0` entirely — asynchronicity **requires ≥2
  independent temporal profiles** (phase diversity). A purely monotone cooling that scales all
  lines together produces *no* asynchronous signal. This is why async carries sequential-order
  information — and why it cannot, by itself, be a flux.

---

## 3. The two fatal cores (cannot be patched — replace)

### 3.1 Model B — the electron-density elimination

**Claimed.** A bridge from the asynchronous ionic–neutral cross-peak to the three-body
recombination rate, combined with the First Mean Value Theorem (MVT), *eliminates* n_e and yields
absolute concentrations with **no n_e measurement, no temperature, no standards**.

**Verdict: FATAL** (three independent defects; ERRATA C1, C2, C5).

**Why it fails.**
1. **The MVT step relabels the unknown; it does not remove it.** The MVT states: for continuous
   `f` and sign-definite integrable `g`, `∫_a^b f g dt = f(ξ)·∫_a^b g dt` for *some* `ξ∈(a,b)`. It
   is an **existence** theorem — it supplies no value for `ξ`. Pulling `n_e²(t)` out as
   `⟨n_e⟩² = n_e(ξ)²` therefore replaces the transient function `n_e(t)` with an *unknown
   constant*. The unknown is renamed, not eliminated.
2. **The subsequent "solve for n_e" is circular.** The step that then "recovers" `⟨n_e⟩` inverts
   the *same* relation (`Ψ ∝ … n_e² …`) that was *assumed* in step 1 to define `Ψ`. Algebraically
   you get back exactly the `n_e` you fed in; no independent observable ever enters. A tautology,
   not a determination.
3. **It is not temperature-free even if you grant 1–2.** The "invariant" lumped parameter `ξ`
   provably contains `U(T)` (partition functions), the Saha/Boltzmann `exp(−E_ion/k_BT)`, the
   `T^{3/2}` translational factor, and the recombination scaling `∝T_e^{−9/2}`. The engine must
   receive `ξ` *precomputed*; computing it requires knowing `T` and absolute rate constants. So
   the headline "temperature-free/standardless" property is false by inspection of `ξ`.

**Correct statement.** 2DCOS reorganizes the covariance structure of the intensity–time data. It
introduces no new physics and removes no unknown. Quantification still needs the standard
apparatus: an independent `n_e` (Stark), a temperature retrieval (Boltzmann/Saha), and either
calibration or the CF-LIBS closure.

**Refinement path — to make *any* reduced-standard version defensible, you must:**
- Supply `n_e` (or `T`) from an observable that is **genuinely independent** of the async
  equation you are inverting — e.g. an actual Stark-width measurement, or a second, structurally
  different relation. Inverting the assumed `Ψ↔n_e²` relation cannot count.
- **Derive** the async↔kinetics relation from an explicit rate model (see §3.2), rather than
  asserting it, and show it survives the competing loss channels (plume expansion/advection,
  radiative recombination) that dominate real neutral birth/loss.
- **Drop** "temperature-free." If `ξ` contains `U(T)`, present the method honestly as
  *temperature-trajectory-informed*, not temperature-independent.
- Reframe the achievable goal: 2DCOS constrains the **ordering and correlation** of ionic vs.
  neutral relaxation — a qualitative check on a recombination picture — not a replacement for an
  `n_e`/`T` determination.

### 3.2 The asynchronous ↔ recombination-flux ("Wronskian") bridge

**Claimed.** "Noda showed the asynchronous correlation represents a temporal cross-peak
*Wronskian integral*," which is then identified with the three-body recombination flux (with one
integral term dropped).

**Verdict: FATAL** for Model B's engine; the identity is false and misattributed (ERRATA C5).

**Why it fails.**
- Noda's asynchronous spectrum is the correlation of one signal with the **Hilbert transform** of
  the other — a nonlocal integral (out-of-phase / sequential-order) operator. A **Wronskian**
  `W=f g′−g f′` involves **derivatives**. A Hilbert transform is *not* differentiation, so `Ψ` is
  not a flux and not a Wronskian. Noda never framed it this way; the term is invented.
- The superficial resemblance ("both vanish when the two signals are proportional/synchronous")
  does not make `Ψ` a Wronskian integral, and cannot license `Ψ = (optical)·k_r·n_e²·∫n_ion²`.
- Dropping "one term" of an antisymmetric object near the ion→neutral crossover is exactly where
  the neglected term is largest.

**Correct statement.** `Ψ(ν₁,ν₂)` is an out-of-phase correlation encoding the *order* of changes,
per Noda's rules — not a time-derivative, not a physical flux.

**Refinement path.** If you want a physically meaningful link between the async map and
recombination *ordering*, state it at the level 2DCOS actually supports: "the sign of the
ionic–neutral async cross-peak reports whether ionic decay leads neutral rise" (a **qualitative**
sequential-order claim, testable against a kinetic simulation). Do **not** promote it to a
quantitative flux identity; there is no derivation for that.

---

## 4. Overstated but salvageable (restate, or demote to testable hypothesis)

### 4.1 Model A — dynamic temperature integration

**Claimed.** Using two same-element lines with widely separated upper-level energies, the
synchronous covariance maps the temperature trajectory `T(t)` "explicitly," removing the
`T_eff` dependency before evaluating the concentration `C_A`.

**Verdict: OVERSTATED** (a reasonable direction sold as a solved method).

**Why it overreaches.** The synchronous matrix is a **second moment** (a covariance), not an
invertible map to `T(t)`. Its ratio for two lines does carry temperature-sensitivity information,
but extracting `T(t)` requires an explicit forward model, and even a perfect `T(t)` does not give
`C_A` without absolute calibration and partition functions. So it is neither "explicit" nor
`T_eff`-free-and-standardless.

**Correct kernel.** The two-line synchronous covariance ratio is a legitimate **temperature
diagnostic aid**: under the first-order model, `Φ(a,b) ≈ (∂I_a/∂T)(∂I_b/∂T)·Var_t(T)`, so a ratio
of synchronous elements isolates the ratio of temperature sensitivities `S_a/S_b`, which depends
on `(E_a−E_b)` — i.e. it behaves like a *time-integrated Boltzmann two-line thermometer weighted
by the cooling variance*.

**Refinement path — to make Model A defensible:**
- Write the **exact functional** of `Φ` you claim yields `T` (or its trajectory), with the
  forward model made explicit.
- Prove or **simulate** that this functional recovers the imposed `T(t)` on synthetic decaying
  spectra (a decisive numerical experiment).
- Keep the absolute-calibration / partition-function requirement visible: this is a temperature
  aid, **not** a standalone composition method.
- Compare against the plain time-resolved Boltzmann two-line temperature to show what the 2DCOS
  framing *adds* (e.g. robustness to which delays are averaged).

### 4.2 Synchronous "energy-weighted covariance"

**Claimed.** (i) "Previous works incorrectly stated the synchronous amplitude scales with the
upper-level energy *difference* ΔE; we correct this." (ii) "The synchronous map is an
energy-weighted covariance; higher upper-level energy amplifies the peak volume."

**Verdict: OVERSTATED + one fabricated premise** (ERRATA C20, C21).

**Why it fails as written.**
- (i) is a **fabricated foil** — no source in the 2DCOS or LIBS literature claims synchronous
  amplitude scales with ΔE. (ΔE→T is *Boltzmann-plot* usage, an unrelated quantity.) There is no
  prior error to correct.
- (ii) is an oversimplification. Under a single cooling driver,
  `Φ(a,b) ≈ I_a I_b · S_a S_b · Var_t(T)` with `S_x = d(ln I_x)/dT = E_x/(k_BT²) − 3/(2T) − U′/U`.
  The weighting is a **bilinear product** `~E_a·E_b` (each scaled by its own intensity), not a
  monotone "higher E amplifies." Two consequences: the subtracted terms `−3/(2T)`, `−U′/U` are
  not negligible (order ⅓ of the E-term at typical LIBS conditions), and `S_x` can go **negative**
  for low-E lines — giving anti-correlated pairs and genuine asynchronicity even under one driver.

**Refinement path.** Delete the ΔE foil. State the product-of-sensitivities form explicitly with
the sign caveat. If you want an amplitude-based **line-selection heuristic** ("prefer high-E,
bright lines for the strongest dynamic signal"), derive it from `Φ(a,a)=I_a² S_a² Var_t(T)` and
validate it on synthetic data — as a heuristic, not a scaling law.

### 4.3 Self-absorption asynchronous "butterfly" — the one worth pursuing

**Claimed.** A self-absorbed line's reversed center decays out-of-phase with its optically-thin
wings, producing a characteristic four-quadrant "butterfly" async pattern that diagnoses optical
depth.

**Verdict: OVERSTATED as established; but a genuine, novel, testable HYPOTHESIS** (ERRATA C9).

**Why it can't stand as written.** It is asserted as a known diagnostic. No time-resolved
2DCOS-of-LIBS study demonstrates it; time-resolved self-absorption is studied via line-shape/
intensity evolution, not an async butterfly. Its governing equation was also a transfer-loss gap
in the source, and the proposed async-volume→optical-depth map rests on an admittedly ad hoc
"empirical spectrometer alignment factor" (C18).

**Why it's the most promising thread.** The mechanism is physically motivated: center and wing
photons have different escape probabilities and the center/wing radiances evolve differently as
the plume cools and thins, which *would* introduce a phase difference — exactly the kind of thing
async 2DCOS is built to detect (off-diagonal, where self-absorption information legitimately
lives; the diagonal is uninformative — see §4.4).

**Refinement path — to convert conjecture into result:**
- Build a **radiative-transfer forward simulation** of a cooling, spatially-inhomogeneous plasma
  with a self-absorbed line (a two-zone or 1-D-stratified `S(τ)` model; you already have the
  optically-thin and two-layer machinery formalized in the repo). Sweep optical depth `τ₀`.
- Compute the 2DCOS async map of the synthetic center-vs-wing series and test **(a)** whether the
  butterfly pattern actually emerges, and **(b)** whether an off-diagonal async metric is
  **monotone** in `τ₀` (with a *derived* — not fitted — relationship).
- Only then test on real time-resolved data. Present it as: "hypothesis → simulation test →
  proposed diagnostic," never as an established correction.

### 4.4 The zero-diagonal "Law" and the "Model C is unphysical" argument

**Claimed.** A proven "Skew-Symmetric Zero-Diagonal Law" (`Ψ(ν,ν)=0`) renders a self-absorption
"Model C" unphysical.

**Verdict:** the theorem is **correct but standard** (not novel; ERRATA C22); the inference is a
**non-sequitur / strawman** (ERRATA C8).

**Why the inference fails.** `Ψ(ν,ν)=0` is a *universal* property of the antisymmetric operator —
true for **every** dataset regardless of physics. It therefore discriminates nothing and cannot
falsify any model; it would "refute" all models equally. "Model C" is an unattributed foil.

**Correct statement.** `Ψ(ν,ν)=0` is elementary, well-known 2DCOS. Its real content is *directional*:
self-absorption information cannot live on the async diagonal, so any self-absorption diagnostic
must be built from **off-diagonal** cross-peaks — which is exactly what §4.3 proposes.

**Refinement path.** Keep the (correct) zero-diagonal statement as motivation for looking
off-diagonal; drop the "Law"/novelty framing and the "Model C unphysical" claim entirely.

---

## 5. The compositional error: softmax(log x) is closure, not ILR

**Claimed.** The composition vector is projected to the simplex "using the Isometric Log-Ratio
(ILR) transformation," implemented in code as `softmax(log x)`.

**Verdict: FATAL mislabel** (decidable by algebra; ERRATA C3).

**Why it fails.** `softmax(log x)_i = exp(log x_i)/∑_j exp(log x_j) = x_i/∑_j x_j` for `x_i>0` —
this is exactly the **Aitchison closure** `C(x)` (plain normalization to `∑=1`). The log and
softmax's internal exp cancel identically. It has none of ILR's defining properties: no
orthonormal basis, no dimension reduction `S^D→ℝ^{D−1}`, no isometry.

**Correct statement.** Closure `C(x)=x/∑x` enforces `∑=1` and nothing more. A true ILR is
`ilr(x)=Vᵀ·clr(x)` with `clr(x)=log x−mean(log x)` and `V` a `D×(D−1)` **orthonormal** basis of
the clr-hyperplane (e.g. from a sequential binary partition); it is an isometry with inverse
`ilr⁻¹(z)=C(exp(Vz))`. The subcompositional-coherence / Aitchison-metric benefits ILR provides
are **not** obtained by closure.

**Refinement path.** Decide what you actually need. If you only need `∑=1`, call it closure and
move on. If you need unconstrained coordinates that respect compositional geometry for
optimization/statistics, implement the real ILR (orthonormal basis + inverse) — a correct
implementation is in the rebuilt `twodcos_engine.py`, and the identity `softmax∘log = closure` is
being machine-verified in `Aitchison.lean`.

---

## 6. Citation integrity (fix before circulation)

Nine of twenty-three references are defective; two appear fabricated. This matters independently
of the physics: fabricated citations invalidate the scholarship even where a claim is otherwise
reasonable. (Details: ERRATA C4, C10–C17; corrected forms in Appendix B.)

- **Fabricated (remove):** "Corsi et al. (2000), *Appl. Spectrosc.* 54(4) 623–633, C-sigma
  graphs" — does not exist; the title is lifted from Aragón & Aguilera (2014); the DOI resolves
  to an unrelated Panne et al. paper. The Cσ method is **Aragón & Aguilera 2014**, building on
  **Aguilera & Aragón 2007**. "Moon et al. (2020) Curve of Growth, *Spectrochim. Acta B* 164,
  105741" — unfindable via Semantic Scholar/WebSearch.
- **DOIs that resolve to the wrong paper:** ref 9 (Colgan), ref 20 (**Noda 1993 itself**), ref 22
  (Zaytsev), ref 23 (El Sherbini).
- **Wrong title/year:** ref 14 (Stewart–Pyatt title), ref 17 (Bultel year 2019), ref 18
  (Hinnov–Hirschberg title).
- **Misattributed content:** ref 9 (Colgan 2014 is a *pure single-element Fe₂O₃* ab-initio
  spectrum paper — it does not support the "geological/high-Z matrix % error" claim it is cited
  for; C7).
- **Physics mis-description:** the three-body recombination prefactor is called "a universal
  quantum-mechanical coupling constant"; it is a **classical**, charge-state- (`~Z³`) and
  Coulomb-logarithm-dependent quantity, with scaling `K_3b ∝ T_e^{−9/2}` (C6).

---

## 7. Constructive path: what a defensible time-resolved 2DCOS-LIBS paper *can* claim

Strip the quantification overclaims and a real, publishable contribution remains. In descending
order of how well the literature already supports it:

1. **Denoising / weak-line recovery (ESTABLISHED).** 2D correlation improves the S/N and
   separability of weak atomic lines in LIBS (Narlagiri & Soma 2021, *OSA Continuum* 4(9)). Frame
   as a preprocessing/diagnostic gain, not quantification.
2. **Sequential-order of species relaxation (ESTABLISHED method, novel application).** Apply
   Noda's rules to the cooling series to report the **order** in which lines/species rise and
   decay (ionic before neutral, resonance before non-resonance, etc.). This is qualitative,
   rigorous, and genuinely informative about the relaxation pathway.
3. **Correlation-structure mapping (ESTABLISHED).** Group lines into co-varying / anti-varying
   families across the decay (or across spatial position) — useful for line identification,
   interference detection, and species assignment (cf. Xue et al. 2024 for spatial mapping).
4. **Self-absorption off-diagonal signature (HYPOTHESIS → test it).** §4.3. If the simulation
   study confirms a monotone off-diagonal async↔τ relationship, this becomes a real, novel
   optical-depth diagnostic. This is your highest-upside thread.
5. **Temperature-trajectory diagnostic (HYPOTHESIS → derive + simulate).** §4.1, restated as a
   time-integrated two-line thermometer with an explicit functional and a numerical validation.

For each of 4–5: **state it as a hypothesis, give the decisive simulation/experiment, and label
results as results only after that test passes.** That discipline is exactly what separates this
from the original draft.

**What to abandon:** standardless / n_e-free / temperature-free quantification via 2DCOS. There is
no route to it through the correlation algebra; the algebra reorganizes information, it does not
create or remove unknowns.

---

## Appendix A — correct reference equations (self-contained)

*Standard forms, for the rebuild; sources in Appendix B.*

- **Optically-thin line intensity:** `I_{ki} = (hc/4π)·(1/λ)·(g_k A_{ki}/U_s(T))·N_s·exp(−E_k/(k_BT))`;
  Boltzmann-plot ordinate `ln(Iλ/(g_k A_{ki}))` has slope `−1/(k_BT)`. (Ciucci 1999; Tognoni 2010.)
- **Line temperature sensitivity:** `d(ln I)/dT = E_k/(k_BT²) − 3/(2T) − U′/U`.
- **Saha–Eggert:** `n_{z+1} n_e / n_z = 2 (U_{z+1}(T)/U_z(T))·(2π m_e k_BT/h²)^{3/2}·exp(−E_ion/(k_BT))`.
- **LTE (McWhirter, necessary not sufficient):** `n_e ≥ 1.6×10^{12}·T^{1/2}·(ΔE)³` cm⁻³.
  (Cristoforetti 2010 — beyond McWhirter for transient plasmas.)
- **Three-body / collisional-radiative recombination:** `A⁺ + e + e → A + e`, effective
  coefficient `α ∝ n_e·T_e^{−9/2}` (classical detailed-balance/Thomson limit; charge-state `~Z³`
  and Coulomb-log dependence in the prefactor).
- **Noda synchronous / asynchronous:** as in §2, with `N_{jk}=0 (j=k), 1/(π(k−j)) (j≠k)`.
- **Compositional:** closure `C(x)_i=x_i/∑x`; `clr(x)=log x−mean(log x)`;
  `ilr(x)=Vᵀclr(x)` with `V` orthonormal `D×(D−1)`, `ilr⁻¹(z)=C(exp(Vz))`; and the identity
  `softmax(log x)=C(x)` (i.e. **not** ILR).

## Appendix B — corrected citations (load-bearing subset)

| Cited as | Correct form |
|---|---|
| "Corsi et al. (2000) Cσ graphs" (fabricated) | **Removed.** Cσ method: Aragón & Aguilera (2014), *JQSRT* 149:90–102; on Aguilera & Aragón (2007). |
| "Moon et al. (2020) Curve of Growth" (fabricated) | **Removed.** For self-absorption/CoG use El Sherbini et al. (2005) / Bulajić et al. (2002). |
| Noda 1993 [ref 20], DOI …067520 | DOI **…067694**; title "Generalized Two-Dimensional Correlation Method Applicable to Infrared, Raman, and other Types of Spectroscopy," *Appl. Spectrosc.* 47:1329. |
| Noda (Hilbert transform) | Noda (2000) "Determination of Two-Dimensional Correlation Spectra Using the Hilbert Transform," *Appl. Spectrosc.* 54:994. |
| Hinnov & Hirschberg (1962) [ref 18] | Title "Electron-Ion Recombination in **Dense Plasmas**," *Phys. Rev.* 125:795. |
| Stewart & Pyatt (1966) [ref 14] | Title "Lowering of Ionization Potentials in Plasmas," *ApJ* 144:1203, DOI 10.1086/148714. |
| Colgan et al. (2014) [ref 9] | DOI **…04.015**; pure Fe₂O₃ ab-initio spectrum — does *not* support the geological/high-Z error claim. |
| Bultel et al. [ref 17] | Year **2019**, *Atoms* 7(1):5, DOI 10.3390/atoms7010005. |
| Zaytsev et al. [ref 22] | **2019**, *Spectrochim. Acta B* 158:105632, DOI 10.1016/j.sab.2019.06.002. |
| El Sherbini et al. (2005) [ref 23] | DOI **…10.011**; full 9-author byline; SA *coefficient* (Kunze optical depth), not a homogeneous-slab escape factor. |
| three-body recombination | Classical: Stevefelt, Boulmer & Delpech (1975), *Phys. Rev. A* 12:1246; Mansbach & Keck (1969), *Phys. Rev.* 181:275; `T_e^{−9/2}` in Fletcher, Zhang & Rolston (2007), *PRL* 99:145001. |
| ILR | Egozcue, Pawlowsky-Glahn, Mateu-Figueras & Barceló-Vidal (2003), *Math. Geol.* 35:279. Closure/simplex: Aitchison (1986). |
| 2DCOS-LIBS (real precedents) | S/N: Narlagiri & Soma (2021), *OSA Continuum* 4(9):2423. Mapping: Xue et al. (2024). |

---

## Provenance

This critique consolidates a literature-grounded audit (8 validators; Semantic Scholar / Asta,
NotebookLM "2DCOS-LIBS" notebook, DOI resolution) recorded in `ERRATA.md`, and the corrected
rebuild in `monograph.corrected.md` + `twodcos_engine.py`. The sound core is being machine-verified
in Lean (`docs/frontiers/13-2dcos-formalization.md`). Adjudications rest on the cited primary
sources, not on authority — where you have a source or corrected derivation that rescues a §3–§4
item, it moves back into scope, and this document should be updated to say so.
