# cflibs-formal deep audit: final synthesis

**Inputs.** lean-main @ fb1681d (82 modules). Dev spec v0.5 (`docs/formalization-spec`). Companion CF-LIBS-improved main, plus the overhaul branch `overhaul/2026-09` (104 findings, amendments A1–A11). Nine audit slices produced the findings below, prefixed PS, LF, INV, U, ARCH, G, SPC, LIT and FM. Twenty frontier proposals (FT-01…20) and thirty refactor proposals (RF-01…30) were each checked by an adversarial verifier.

**Reading rules.** Every item appears in the verifier's version. CONFIRMED means an auditor or verifier checked or executed it during this run. PLAUSIBLE means it was derived or quoted but not re-executed. Nothing was killed outright. Refuted sub-claims are listed in the Appendix.

---

## 1. Executive summary

1. **Health.** Proof engineering is sound: 82/82 modules are axiom-clean and kernel-replayed (weekly sweep, 2026-09-21), there are no heartbeat overrides, and the longest proof is 159 lines. Rigor fails at the statement and contract layer. Docstrings, scope tags, runtime certificates and CI gates repeatedly claim more than the Lean proves, or describe objects the pipeline never runs.
2. **Defect (integrity).** The proof queue's `verify.py` accepts forged proofs of `(2:ℕ)+2=5` in three ways: `addDeclCore (doCheck := false)`; `sorryAx` plus a spoofed `#print axioms` line; and spoofed type markers. The verifier reproduced this (RF-07).
3. **Defect (certificates).** C12 is `0 ≤ τ` and sits in the HARD gate. C1–C3 certify a pooled single-intercept design while the solver fits a within-element design; the false positive was executed. C10 and C11 describe loops that `iterative.py` never runs (RF-04, RF-16, RF-05, RF-11).
4. **Defect (vacuous quantitative spines).** `sahaFactorLipConst` is 10^6–10^8× too loose, so the C11 gate can never pass. Noise→composition bounds come out at 26–1400 on NIST levels (RF-11, RF-12, RF-18).
5. **Defect (physics scope and gates).** The Continuum "thermometer" runs backwards for neutral lines. The flat-profile self-absorption factor is presented as exact integrated radiative transfer (1.4–3.5× over-correction). IPD is absent. The oracle sits at kB=T=Fcal=me=h=1 and never reads 16 of its fields. ScopeCheck skips every Alt/Classic row (RF-01, RF-03, RF-19, RF-08, RF-09).
6. **Most valuable frontier theorems.**
   - FT-01: a gain, damped-window and residual-stop certificate for the loop `iterative.py` actually runs.
   - FT-04: a fixed-effects design-rank theorem, giving certificates C1g/C2g.
   - FT-03: a three-branch refuse-to-report policy on the Aitchison PAS loss.
   - FT-02: the IPD gauge identity and the implicit IPD-aware inverse.
   - FT-05: a cutoff-policy bias that no gA correction can absorb.
7. **Single most important alignment action.** Re-issue `docs/integration/m4-population-context.md` (RF-10) before W2-S3 and W3-A build to it under A11. It needs a per-stage (χ_eff, level list) pair contract, units, semantic tiers, no flat-slab tautologies, no Model-B loop rows and no Alt.CSigma↔csigma.py pairing. Runner-up: keep C1–C3 and C12 out of every answer or HARD path until C1g/C2g and the τ-error lemma land. That gate is dormant today (bead kixx), so it is less urgent than the adopted M4 doc.

---

## 2. Repo health by area

**Plasma state (PS-01…16).**
- The core physics is correct: g_e = 2, the thermal bracket via rpow, e^{-χ/kT}, the McWhirter √T·ΔE³ direction, and the Stark exponents. TemporalEvolution, StarkOpacityGuard and DoubletChannel are exemplary in scope.
- Physically wrong or overclaimed statements:
  - The Continuum line-to-continuum ratio has the wrong T-direction for neutral lines (PS-01; the verifier restricted this to neutral lines).
  - "Matrix effect zero" rests on free binders (PS-02).
  - hEχ is called "true for every real atom" but fails for 202/324 species on the production DB (PS-06; re-queried by the verifier: Ca I has 342 of 798 levels above an IP of 6.113 eV).
- The quantitative outer-loop machinery is vacuous: the Lipschitz constant is 10^6–10^8× loose (PS-03), and the density leg is not the leg the pipeline iterates (PS-04, PLAUSIBLE on the pipeline side).
- Missing physics: IPD (PS-05); an n_e-dependent level cutoff, which makes U discontinuous (PS-07); stage III (PS-08); Saha departure and Stark width uncertainty (PS-16).
- C8's source theorem needs exact equality (PS-09). The 2-D contraction gate depends on units (PS-10). The McWhirter constant carries units (PS-11). C9/C10 attach to the forward closure (PS-12, PLAUSIBLE).
- Minor prose: PS-13 (E*), PS-14 (parallel lines, not one line), PS-15 (optically thin chords not stated).

**Line formation (LF-01…15).**
- The pure mathematics is strong: the EquivalentWidth/LadenburgReiche sharp 2√(γτ) constant, the OpticalDepthBridge/OpacityBroadening limitation blocks, and the RadiativeTransferDepth sandwich.
- The structural weakness is the self-absorption layer. It applies the flat-profile, line-centre SA(τ) to integrated intensities with no flat-profile caveat and EXACT tags (LF-01, LF-05). The over-correction is 1.41/1.87× (Gaussian) and 1.85/3.48× (Lorentzian) at τ0 = 3/10, reproduced by the verifier.
- Thick intensity decreases with path length at fixed Fcal (LF-02; the verifier reframed this as an unstated Fcal∝ℓ coupling, P1).
- The M4 doc adopts flat-slab tautologies as acceptance fixtures (LF-03).
- Pair-ratio injectivity is a flat-kernel property (LF-04). The verifier narrowed it: inside the τ ≤ 30 gate, non-injectivity occurs only for γ/σ ≳ 0.1, and the second branch spans less than 1% in ratio.
- Other defects: a false "iff" dip criterion (LF-06), in-file drift (LF-07), an assumed common source function (LF-08), a vacuous Voigt enclosure (LF-09), a wrong Aragón–Aguilera title (LF-10), vacuous C12 (LF-11).
- LF-12 is a positive cross-check: the spec keeps the lower-level Boltzmann factor that the pipeline's `_tau_ratio` drops.

**Inverse and solvers (INV-01…14).**
- Identifiability proofs are sound. Faithfulness to the pipeline is poor. The only Lean citation on the default solver path is `sahaBoltzmann_shift_eq_log_saha` (iterative.py:1217, 1582), and it is faithful (SPC summary). The other 36 cited names sit in modules that G2 found dormant or dead.
- Model B is degenerate once the Saha offset is made consistent (INV-01, scratch theorem axiom-clean, re-checked).
- The pipeline's reduced map has gain g = (Σ b_e D_e)·D_m/Σ(W_e + b_e D_e²). The verifier re-ran this against the pipeline's own legs and the closed form matched to 5 decimals: 0.96394, 0.99991, 0.90076, and 1.15789 on a constructed set that drifts (INV-02). The C11 gate evaluates to 6e3–5e4 (INV-03).
- Other defects:
  - C1/C2 certify pooled designs (INV-04).
  - The C10 prose confuses the forward closure with the inverse loop (INV-05).
  - The joint "2-D upgrade" is a corollary (INV-06).
  - `Inverse.Sound` is uninhabited (INV-07).
  - The identifiability trio assumes known, equal Fcal and a shared U (INV-08, INV-09).
  - "Off-manifold" uniqueness assumes an exact fit (INV-10).
  - Homoscedastic BLUE is tagged Aitken (INV-11).
  - NeutralityScale is orthogonal to ratio mode (INV-12).

**Uncertainty and certificates (U-01…16).** Every certificate soundness theorem is a correct re-export. Their runtime value is small (U-04 ledger):
- C1 and C2 are informative but certify the wrong design (SPC-01).
- C3 is C1 verbatim (U-07).
- C4's premise is fed a 1σ scale; all-lines coverage is 0.683^n, 0.022 at n = 10 (U-03).
- C5, C6 and C14 are purely epistemic.
- C7 is circular.
- C9 is never fed.
- C10 certifies the wrong loop (U-02).
- C12 is vacuous (U-05).
- C13's inputs are misnamed (U-06).
- C8 and C11 are missing (U-11).

The headline noise→composition chain is vacuous at realistic noise (U-01; the verifier re-ran it: Ni 26.3 at 0.5% noise, Fe 1.42e3 at 5%). Other issues: ConformalCoverage proves only a counting step (U-08); the OLS aliasing bound depends on the energy origin (U-09, auditor-executed, not re-run); no theorem reaches the Aitchison PAS loss (U-10); a density tail is named as a composition tail and has no docstrings (U-12); witnesses sit at zero-error corners (U-13).

**Architecture (ARCH-01…19).** Proofs are not fragile. The debt is in the data model and definitions:
- There are three incompatible multi-species models, and the shared-U artifacts follow from that (ARCH-03, ARCH-04).
- 45 EXACT results are stated over the REDUCED λ-free `lineIntensity` (ARCH-02, PLAUSIBLE count).
- ForwardMapEnergy is imported by no module (ARCH-18).
- Duplicate definitions and proofs, and false "single home" claims (ARCH-06…10).
- Core modules import Alt (ARCH-11).
- Stale counts (ARCH-12).
- Identical statements carry different tags (ARCH-13).
- Tautologies are tagged EXACT (ARCH-14).

**Gates, tooling and oracle (G-01…18, LIT-04, FM-01/02).** The gates are sound at compile level: the 82/82 kernel replay and axiom-audit both hold. At the meaning level they are blind:
- `verify.py` can be forged (G-01, reproduced, plus a third type-marker spoof found by the verifier).
- The oracle is pinned at the unit fixed point of the bugs it should catch, and corrupted fields still pass (G-02, G-07). The corruption part was re-run; the mutant-survival table is PLAUSIBLE.
- ScopeCheck checks 133 of 163 EXACT rows (G-03, re-run).
- No def-level tags exist (G-04, G-05).
- The oracle is decoupled from the spec (G-06). `jNum` fabricates finite values from NaN (G-08).
- Vendored fixtures carry no provenance, and there is no pipeline Saha test (G-11, G-12).
- Citation, mutation, prereg and vacuity checks sit outside CI (G-13). Zero whitelist rows are VERIFIED (LIT-04).
- Two frontier refusals rest on false mathlib-absence claims (FM-01, FM-02).

---

## 3. Defects and refactors

P0 items come first. Effort: S < 1 day, M a few days, L a week or more. Every verdict is the verifier's. RF-15 was split by priority.

| ID | Pri | Title | Location | Problem | Proposal (verifier's version) | Effort | Verdict |
|---|---|---|---|---|---|---|---|
| RF-07 | P0 | Harden the proof-queue verifier | cflibs-formal `tools/openprover/queue/verify.py`:27-29, 69-73, 88-96 | Accepts forged proofs of (2:ℕ)+2=5 via addDeclCore doCheck:=false and via sorryAx plus a spoofed axioms line; also trusts candidate-printed TYPE markers. Reproduced. Verified counts feed the Phase-0 exit. | Compile the candidate to an .olean in a scratch root. Make `leanchecker` replay mandatory, because an olean-only axiom read reports [] for doCheck:=false. Compute the elaborated type in a separate probe that imports the olean, or use nonce markers. Add sorryAx, run_cmd, #eval, #print, #check, set_option, elab, initialize, addDecl(Core), doCheck and macro_rules to FORBIDDEN. Add all three forgeries to the falsification set. Re-verify F02 before counting it. | M | REVISE |
| RF-04 | P0 | Replace vacuous C12 | Certificates.lean:338-360; SelfAbsorption.lean:249-255; OpticalDepth.lean:202-214; scope-tags.tsv:469; companion certificate_gate.py:76-84, certificates_wiring.py:226-236, certificates.py:412 | knownTauCert τ := 0 ≤ τ. Its soundness is mul_div_cancel on the model. The companion feeds it the estimated max τ as a HARD gate. It is tagged EXACT. The pin SelfAbsorption.lean:237 is stale in both repos (the theorem is at :249). | Retag PURE-MATH and drop "closes the gap". Prove ln SA is ½-Lipschitz, then add the FT-13 τ-error propagation lemma with a C14-style REFUSAL, not as a HARD certificate. Replace line pins with names. Keep the name knownTauCert (OracleAnchors:73, Generate.lean:248). Companion: remove C12 from HARD. | M | KEEP |
| RF-01 | P0 | Retract the continuum "thermometer" for neutral lines | Continuum.lean:20-40, 76-84, 125-131; scope-tags.tsv:300 | For a neutral line, B carries 1/S(T), so the physical ratio goes as e^((χ−E_k+hν)/kT)/(T·U_{z+1}) and strictly decreases in T. The condition a ≥ 0 is an artifact. The header says "iff", but only "if" is proved. For an ionic line of the continuum-producing stage the reduced form holds at fixed n_e. | Retag PURE-MATH, or REDUCED scoped to "continuum-producing stage, fixed n_e, U frozen". Rewrite prose per stage and change "iff" to "if". Follow-up: lineToContRatio_neutral_saha is StrictAntiOn under E_k ≤ χ+hν, against the current contEmissivity. Add the ξ/G bracket only after opening the source. No IPD until RF-19. Run gen-docs. | S | REVISE |
| RF-03 | P0 | Flat-profile SA: scope blocks and tag policy | SelfAbsorption, SelfAbsorptionInverse, CurveOfGrowth, DoubletChannel, OpticalDepthBridge, Alt/SelfAbsorbed, Certificates C13; scope-tags.tsv:198-203, 217-218, 470 | SA called "exactly the radiative-transfer slab solution" on integrated intensity; 0 flat-profile caveats in 3 modules; 1.4–3.5× over-correction (reproduced); one model tagged EXACT, APPROXIMATION and REDUCED; cogRatio_injOn and C13 EXACT; a shared source S assumed across transitions; C13 names opacity coefficients "widths". Non-injectivity inside the gate occurs only for γ/σ ≳ 0.1, with a band under 1%. | REDUCED scope blocks. Policy: physics rows that consume SA are REDUCED; left-inverse algebra is PURE-MATH; record in conventions.md. Mark cogRatio_injOn, doubletRatio_injOn and C13 "flat kernel only". State the common-S assumption and delete "relative composition". Rename C13 binders, not the def, here and in the companion. Narrow selfAbsorption_breaks_composition_identifiability. The follow-up theorems moved to FT-13, FT-18 and FT-20. | M | REVISE |
| RF-05 | P0 | Retract "C10 replaces the 0.5 damping" | Certificates.lean:300-305; frontiers/12 §1.1, §2, §6 (stale iterative.py:2022); companion certificates.py:36-39, 384-385 | C10 is the fixed-T forward closure at known Ntot. The pipeline damps the outer (T, n_e) loop at iterative.py:908/937 (JAX) and 2454/2531. The companion marks C10 "skip: Ntot not materialized". C10 also does not model round_trip.py's isobaric three-stage loop. | Reword to its actual scope and fix the pins. Do not re-prove. Import SahaContraction and re-export `dampedMultiElementIter_converges_to_equilibrium` as dampedIter_certificate_sound_closed, with uniqueness and rate. Add a REDUCED scope row. Drop the SahaContraction headline edit, which is already scoped. Remove C10 from BL-35 evidence. | S | REVISE |
| RF-06 | P0 | Shared-U and known-Fcal EXACT artifacts | MatrixEffects.lean:289-352; MatrixIonizationCoupling.lean:59-63, 285-300; Inverse.lean:53-143; Joint/CompositionIdentifiability; scope-tags.tsv:148, 151, 163, 408; GAPS.md:135-181; m4 doc Tier 1b | The homologous-pair invariance is EXACT while its per-U sibling is REDUCED; the shared U is disclosed, so the defect is tag inconsistency. The identifiability trio assumes hFeq, which is removable (calibration-free version axiom-clean in scratch). "Matrix effect zero" holds on free binders Ns, Nt. Inverse.Sound quantifies over unknown g, E, A. GAPS #7/#11 overclaim. | Retag REDUCED ("shared level table/U"). Land the calibration-free headline. Restate envelope clause (c). Reword Inverse.lean:56. Fix GAPS. M4: move envelope_ionization_matrix_shift out of Tier 1b and annotate the Tier-2 homologousPair rows as shared-U. Structural fix in RF-28, with atomic data as a known input. | S | REVISE |
| RF-08 | P0 | Make the oracle discriminating | oracle/Generate.lean:265-273, 295-297, 313-314, 355, 409-410; check_fixtures.py; oracle/README.md:59, 65; OracleAnchors | All constants are 1, the fixed point of unit and placement bugs. 16 of 111 keys are never read: corrupted recovered_* fields still pass (re-run). calibration_free is only a round trip. jNum maps NaN to 0 and saturates at 1.8e10. The strictness of C6, C7, C9, C12 and C13 cannot be distinguished (PLAUSIBLE). A companion kT-placement mutant passes 68 tests (auditor-executed). | Use non-unit, incommensurate constants. Add a mutants.py self-test in CI. Check every emitted field. Rebuild calibration_free as fixed I with Fcal' = 1000. Make jNum honest. Add boundary witnesses. Mark the README "hand-mirrored". Land together with RF-25. | M | KEEP |
| RF-10 | P0 | Correct the M4 acceptance doc | m4-population-context.md (conditions 1-2, Tiers 1/1b/2, generator); SahaStability.lean:54-55, 762; PartialLTE.lean:61; Dimensions.lean:186-187; StarkBroadening.lean:100-101; companion M-spec-estimator-routing-policy.md:52 | The companion adopted this doc via A11. The IPD condition is incomplete: Δχ depends on the n_e being solved for and moves the cutoff, so the T-grid, Lipschitz and enclosure rows and C9/C10 do not transfer. hEχ fails for 202/324 species. The McWhirter constant carries units (T in eV makes the gate 108× laxer). A constants-mentioned filter put loop and estimator results in Tier 1, duplicates rows, and gives electronDensity_antitone the wrong fixture axis. SA tautologies are acceptance criteria. Alt.CSigma is credited as the csigma.py twin, and DifferentialEstimator as the opc.py twin. | Replace condition 2 with a per-stage pair contract: χ_eff, and a level list ⊆ {E ≤ χ_eff}. Put units into the mcWhirterBound docstring; the CGS wording fix goes in PartialLTE and Dimensions. Regenerate with a manual semantic-tier column. Drop outerLoop_contracts and jointConvergence. Move the SA/OpticalDepth rows to an annex. Move envelope out of Tier 1b. Fix routing row R1. Publish an old→new row changelog. Rewrite hEχ prose as a cutoff obligation. | M | REVISE |
| RF-11 | P0 | Outer-loop (Model B, C11) honesty | OuterLoopModelB.lean:36-50, 76-98; ErrorBudget.lean:484-494; SahaStability.lean:500-559; PartitionLipschitz.lean:49-53; JointConvergence.lean:18-29, 74-76; SahaRangeEnclosure.lean:79, 105; frontiers/12:70; GAPS:133 | The "real loop" is non-degenerate only because offConst is frozen at a reference T; with the consistent offset the composite map is constant (axiom-clean, re-checked). The fixed-R density leg is not the pipeline's sb_offset leg. sahaFactorLipConst is 7.7e5–9.7e7× loose (re-run). C11 cannot be satisfied. JointConvergence is the 1-D loop unrolled. Frontier 12 lists the n_e box as open, but electronDensityFromRatio_mem_Icc and outerLoop_contracts_apriori exist. | Keep the tag REDUCED and name the reduction; do not retag APPROXIMATION. Land the degeneracy witness as PURE-MATH. Quantify "non-sharp". Present JointConvergence as a corollary. In frontier 12, mark the box as discharged and C11 as not runtime-checkable. The companion must not wire L1·L2 < 1; the replacement is FT-01 and RF-17. | S | REVISE |
| RF-12 | P0 | Caveat the vacuity of noise→composition | NoiseToComposition.lean:106-120, 264-313, 358; EvaluatorSoundness.lean:216, 302; DifferentialEstimator; Certificates.lean:25-26, 167-172, 221-229, 417-424 | Bounds run from 26 (Ni, 0.5%) to 1.42e3 (Fe, 5%) on NIST levels (re-run). They are informative only with levels truncated to ≤ 1 eV. The Fe U channel is 83.1 against 0.0402 with a log-derivative leg. Witnesses at zero-error corners contradict the header promise. | Add non-vacuity-range paragraphs and soften the header. Add nonzero-error witnesses for C4, C6, C14 and a two-species chain. Stop advertising the evaluator bundle as a composition guarantee. The fix is RF-18 plus RF-23. | S | KEEP |
| RF-13 | P0 | Citation-integrity batch | CSigmaCurveOfGrowth.lean:44, 50-59; OpticalDepth.lean:92-94; MatrixEffects.lean:61-62; IntervalEnclosure.lean:54-57; VoigtWidth.lean:28-30; scope-tags.tsv:753-754; whitelist rows 52, 71, 72, 75, 83; reviews; docs/2dcos; check-citations.sh | (a) The IntechOpen chapter is by F. Rezaei 2016 (DOI 10.5772/61941), not Aragón & Aguilera, and its equation numbers are relied on. (b) JQSRT 149 (2014) 90 is quoted under a non-existent title (true: "CSigma graphs…"); corrigendum DOI 10.1016/J.JQSRT.2015.03.001 (vol 159 PLAUSIBLE). (c) Abbass 2016 is off-whitelist behind two EXACT rows, and check-citations exits 0. (d) Thouin, not Khelladi (PLAUSIBLE). (e) Borduchi 2022 has four authors. (f) Cristoforetti 2010 is the wrong source for the OLS design. (g) There are 0 VERIFIED rows. (h) The O–L accuracy figure (PLAUSIBLE). | Work through the citation-integrity skill. Re-attribute and fix titles and DOIs. Add an Abbass whitelist row as UNVERIFIED and retag rows 753-754 away from EXACT. Demote row 83. Make OFF-WHITELIST fatal in CI in the same PR. Track the VERIFIED count. Promote Tognoni 2010, Ciucci 1999 and Gornushkin 1999 first. | M | KEEP |
| RF-14 | P0 | Statistics and inverse overclaims | NonlinearLeastSquares.lean:635-655; Alt/GaussMarkov.lean:193-198; ConformalCoverage.lean:144-159; Alt/OLSAtomicDataPerturbation.lean:192-300; Alt/StochasticBudget.lean:500-509; FisherLineSelection.lean:23, 43; theorem-catalog:197-202, 369, 581; IntervalEnclosure.lean:12-26; LineSelection.lean:30-32 | (a) The off-manifold uniqueness theorem assumes an exact fit. (b) The homoscedastic ols_is_blue is tagged Aitken. (c) The conformal result is counting only. (d) The aliasing bound depends on the energy origin (PLAUSIBLE). (e) The density tail is named as a composition tail and lacks docstrings. (f) Header and catalog say "OLS is efficient", although the defined-not-derived caveat already exists at :88-97. (g) IntervalEnclosure is unreferenced. (h) C1 "already checked" sits behind a default-OFF flag. | Reword each. Retag ols_is_blue with the Gauss–Markov lineage. Rename the conformal and tail theorems, keeping deprecated aliases. olsDensity_aliasing_uncentred lives here only. Narrow (f) to the header and catalog. | M | REVISE |
| RF-15a | P0 | Physics prose overclaims | SelfReversal.lean:41-42, 95-101; RadiativeTransferDepth.lean:42, 186-204; StarkBroadening.lean:106-110, 169-207; SpatialForward.lean; Alt/CSigma, SahaInverse, CSigmaCurveOfGrowth | The "iff" dip criterion is only necessary. "No information iff isothermal" is proved only in the ⇐ direction, and it bounds intensity, not temperature. stark_saha_lte_consistent is EXACT but restates its hypotheses. lteValid names the McWhirter test "LTE validity". SpatialForward does not say chords are optically thin. The cross-stage collapse has no homogeneity caveat. | Use "if", "necessary for a dip" and "intensity bias". Retag stark_saha_lte_consistent PURE-MATH ("conditional bundling"). Rename lteValid to mcWhirterAdmissible with a deprecated alias (0 oracle references). Add optically-thin and homogeneity caveats. | S | REVISE (split) |
| RF-09 | P1, blocker | ScopeCheck resolves namespaces | tools/ScopeCheck.lean:28-32, 59-68, 82-90 | Checks 133 of 163 EXACT rows (binary re-run). Skips all 27 Alt and 3 Classic rows and their APPROXIMATION dependencies. The tag map is keyed by short name. Currently 0 violations, so the defect is latent. | Resolve by (module, short name) or by fully qualified Name. Hard-fail on unresolved or duplicate keys. Print resolved/total per tag. Add Alt and Classic regression rows. Land this before any retag in RF-11, RF-15 or RF-29. | S | REVISE (P0→P1) |
| RF-02 | P1 | OpticalDepth path-length coupling | OpticalDepth.lean:39-47, 118-138; ForwardMap.lean:20-22 | At fixed Fcal, S ∝ 1/ℓ and the thick intensity is strictly antitone in ℓ (EllAntitone.lean, rc=0). But Fcal lumps the plasma volume, which scales with ℓ, so this is an unstated coupling. The Wien T-shape holds; only the absolute normalization needs Einstein–Milne. | Add a scope sentence that Fcal carries volume ∝ ℓ. Qualify the Wien normalization. Land the faithful positive statement: Fcal := F'·ℓ makes S independent of ℓ and makes the thick intensity StrictMonoOn in ℓ. Kirchhoff consistency follows in FT-14. | S | REVISE (P0→P1) |
| RF-15b | P1 | Tag-only physics fixes (after RF-27 and RF-09) | Continuum.lean:121-124; EquivalentWidth.lean:215; SpatialForward.lean:167-176; VoigtWidth.lean:48-72; VoigtErrorEnclosure; PartialLTE.lean:36-64; SahaInverse.lean:17-19, 86-94; StarkBroadening.lean:15-35 | Tautologies are tagged EXACT. O–L fit lemmas say "A Voigt profile" although the module header says empirical fit. The Voigt enclosure is only the bracket width (about 61% allowed). PartialLTE conflates absolute energy E* with a gap. "Single straight line" should be two parallel lines. The Stark ion term (∝ n_e^{1/4}) is not excluded. | Retag according to the RF-27 outcome. Write "the Olivero–Longbothum FWHM". Reword the enclosure and fix the prose. Run scope-check after RF-09 before any APPROXIMATION retag. | S | REVISE (split) |
| RF-16 | P1 | Grouped fixed-effects design (C1g/C2g) | OLS.lean; Certificates.lean:74, 97, 125; new GroupedDesign.lean; companion certificates_wiring.py:19-27, iterative.py:1703-1820, 3940-3991 | The production fit is weighted within-element; the wiring pools lines. False positive executed and re-run: C1 = C3 = True at 4.0 with within-element SS = 0. C2 at rank 3 < 4 is PLAUSIBLE. C3 is C1 verbatim. | FT-04. Certificates C1g and C2g. Redefine C3 as a noise-gain σ²/SS_W under a new id. The companion evaluates on the kept mask and marks C1–C3 not applicable until mirrored. | L | KEEP |
| RF-17 | P1 | Certify the loop the pipeline runs | new SBOuterLoop.lean; Certificates (C11 slot); companion iterative.py:1561-1634, 2444-2551 | No spec theorem covers the 0.5-damped Gauss–Seidel with an IP-shifted SB graph and sb_offset. The gain closed form matched to 5 decimals (re-run). g = 1.158 drifts. The 100 K stop at g = 0.964 leaves about 5.6 kK linearized distance. | FT-01, as revised. | L | KEEP |
| RF-18 | P1 | Log-derivative Lipschitz constants | PartitionLipschitz.lean; SahaStability.lean:500-559; NoiseToComposition.lean:106; AtomicDataPerturbation.lean:474; DifferentialEstimator | The exp ≤ 1 constants overshoot. Re-run: the tight S bound is 2.76–4.34× the true value (max-E variant 5.8–9.8×); the Fe U channel is 83.1 against 0.0402. | FT-15. Add new `_tight` theorems and leave the old statements untouched, with no le_trans re-derivation. | L | REVISE |
| RF-19 | P1 | IPD and level-cutoff layer | new IonizationDepression.lean; Boltzmann.lean; AtomicDataPerturbation δ_U; spec 03 §1 S9/S10; companion partition.py, saha_boltzmann.py, pipeline.py:375 | IPD is modeled nowhere. Forward-on/inverse-off gives an n_e bias of exactly e^(−Δχ/kT); the 0.9358 figure is a consistency check. A sharp n_e-dependent cutoff makes U discontinuous (re-run: Ca I 178 crossings, 21.0%; Ti I 0; Fe I 3; single jumps ≤ 1.42%). | FT-02, FT-05 and FT-11 S10. Handle the jumps through δ_U (Lipschitz plus a bounded jump) rather than calling the hypotheses unsatisfiable. | L | KEEP |
| RF-20 | P1 | C8 on error bars, TS-01 refusal, numbering | StarkBroadening.lean:169-207; StarkOpacityGuard.lean:180-190; Certificates (C8 slot); spec 03:281-282; G2 TS-09 | C8's source theorem needs exact equality. C8 and C11 are absent. Numbering conflicts: spec 03 says "do not back-fill" while G2 says "fill C8/C11 first". The Saha consistency check is trivially satisfied on the sb_offset route. | FT-06 (revised) plus FT-03(e). The owner decides numbering in the spec D-table and in LEAN_CERTIFICATE_DEFS. `_resolve_ne` keeps both sources. | M | KEEP |
| RF-21 | P1 | Weighted (Aitken) BLUE | Alt/GaussMarkov.lean; Alt/OLSVariance.lean; FisherLineSelection.lean; new WeightedLeastSquares.lean | No WLS object exists. The pipeline's plane fit is inverse-variance weighted. OLS variance goes from 2 to 2500.25 when a σ = 100 line is added. | FT-10. | M | KEEP |
| RF-22 | P1 | C4 soundness against what the gate measures | Certificates.lean:151-165; Alt/StochasticBudget.lean:574-578; ErrorBudget; HeteroAtomicData; companion certificate_gate.py:81-83, 385-387; error_budget.py:127-172; strict.py:212-245 | ε = 1/min SNR is a 1σ scale. The exact-atomic-data premise is implicit, while the pipeline treats gA as variance. The span→SS_E conversion nR²/12 is not conservative for n > 6; the minimum is R²/2. | FT-12 C4σ; a noise-plus-atomic composite; ssE_ge_half_span_sq; a C4∧C5 composite. The companion gates on SS_E. | M | KEEP |
| RF-23 | P1 | Composition theorems in the scored geometry | Closure.lean; CompositionRobustness.lean; Aitchison*.lean; MatrixEffects.lean:25, 131; companion scoreboard.py, closure.py:898-960, strict.py:253-285 | Only absolute number-fraction bounds exist, while scoring is in wt% and Aitchison. The default oxide closure is off-simplex (sum 0.667, PLAUSIBLE). clr maps zeros silently via log 0 = 0. "Mass fraction" is used for number shares. | FT-07 plus FT-03 (a)–(d). A positivity warning on aitchisonDist. An oxide caveat. Mole wording. | M | KEEP |
| RF-25 | P1 | Oracle provenance and pipeline-executing tests | oracle/fixtures.json; companion tests/oracle/*, tests/data/*, test_forward_saha_conformance.py:34, 170-174; test_oracle_regression.py:89 | Three hand-copied vendored subsets with different hashes, one of them stale. The Saha check is inline and contains a tautology. The partition test uses ip_ev = 1e9. A11's IPD regression test does not exist. Coverage is 16/81 modules (PLAUSIBLE). | Stamp only the sha256 of Generate.lean; stamping the git commit would break the CI diff. Keep one vendored copy with a hash sync-check. Add a pure saha_factor pinned at non-unit constants, an IPD golden as xfail(strict=True), and a cutoff fixture. Drop the tautology. Consume the energy-ordinate scenario. Widen the must-pass set. | M | REVISE |
| RF-24 | P1, after RF-16/17/18 | Energy-affine gA gauge | HeteroAtomicData.lean:211, 251; OLS.lean | The W3-C gauges do not fix the E-linear gA direction, which is degenerate with 1/kT. Item (4) duplicates RF-14(d). | FT-09 (revised); drop (4). | M | REVISE |
| RF-15c | P2 | Prove the Gaussian quadrature rule | LineBroadening.lean:26-27, 93-98 | Called "exact … asserted", yet provable from gaussianReal_conv_gaussianReal. | Land gaussFWHM_conv and gaussianPDFReal_halfMax (axiom-clean in scratch). Change "asserted" to "proved". | S | REVISE (split) |
| RF-26 | P2 | Frontier dossiers and dev-spec fixes | ROADMAP.md:147, 187; 03:191; 11:476-490; 12; dossier headers; spec 02 §4, 03 §2-3 and §6, 06 Phases 0/3/6 | Refusals rest on false mathlib-absence claims: convexOn_zpow and iIndepFun.hasGaussianLaw exist. Stamps say v4.31.0, pin is v4.33.1. Frontier-12 wiring claims are stale. ROADMAP says not to use ContractingWith, but the code does. Phase 6 needs the K8 gain that Phase 3 refuses. Scenario 7(b) needs erf, which is absent. The Phase-0 table is stale. | Retract the refusals (FT-17, FT-12(b)). Restamp. Put the U-04 ledger into frontier 12. Add K8 Varah (FT-16) after citation-integrity. Use Lorentzian lines for 7(b) via Float.atan. Add voigtMeasure. Phase 0: F02 verified, F07 failed. | M | KEEP |
| RF-27 | P2 | ScopeCheck v2 and EXACT semantics | tools/ScopeCheck.lean; gen_docs.py; stats.sh:21; check-scope-consistency.sh; mutate-check.sh; conventions.md §7; CI | Tags attach to theorems while reductions live in defs: 45 EXACT over the REDUCED lineIntensity, 13 via boltzmann_plot_intensity, 18 over approximation models (counts PLAUSIBLE). "Sum to one" carries four tags. ScopeCheck has no REDUCED rank. stats.sh counts a docstring. Vacuity checking is absent. mutate, prereg and citation checks run outside CI. | The owner decides "EXACT relative to the model" versus "EXACT = faithful". Then: def rows; statement-level monotonicity with an allowlist; ALIAS/WITNESS tags; kernel-environment hygiene; CI gates. | L | KEEP |
| RF-28 | P2 | One multi-species model; SoundEstimator | Inverse; Joint/CompositionIdentifiability; SelfAbsorptionInverse; MultiSpecies; Classic; Alt/*; ForwardMapEnergy | Three data models. ForwardMapEnergy is imported by 0 modules. sound_agree is trivial. Sound is uninhabited. | A LineCatalog with per-line response; PlasmaParams as the constant-row case; SoundEstimator taking atomic data as a known input and quantifying over (T, N) only; energy-flux corollaries. Land in stages, keeping names. | L | KEEP |
| RF-29 | P2 | Deduplicate and fix layering | many; see ARCH-06…11, 15, 19 | Duplicate definitions (the classicDensity alias is admitted) and duplicate proofs. The core imports Alt (OpticalDepth:7, LineSelection:9). 192 inline SS_E expressions. Unused hypotheses. | As proposed, after RF-09, with aliases preserved. | L | KEEP |
| RF-30 | P3 | Polish | AGENTS.md:24; CONTEXT.md:213; EquivalentWidth.lean:40, 918; Alt/SelfAbsorbed.lean:112-118; GAPS:133 | Counts disagree (72/81/82). The damping wing is called "OUT OF SCOPE" in a file that proves it. A misnamed theorem. GAPS says "still open". | As proposed. GAPS item 6 should point to Lean names with the frozen-offset scope, not to audit ids. | S | KEEP |

---

## 4. Spec–pipeline contract

**Cross-cutting facts.**
- The only Lean citation on the live solver path is `SahaInverse.sahaBoltzmann_shift_eq_log_saha` (iterative.py:1217, 1582), and it is faithful. The other 36 cited names sit in modules that G2 found dormant or dead.
- A5 hands the trust stack (certificates.py, certificates_wiring.py, identifiability.py, conformal.py, coverage.py, reliability.py, error_budget.py, derived_thresholds.py) to W2-A.
- `cflibs/evolution/certificate_gate.py` appears in both F2's and W2-S2's Owns lists (workstreams.md:77, :389). Resolve that before either changes the HARD set.
- A11 says theorems transfer only if U(T) is the literal level sum. The exact provider's T clamp (partition.py:1513-1538) also breaks this condition.

**F1 (scoring truth: Aitchison primary loss on the cation panel, declared basis).**
- *Spec provides:* `Aitchison.clr`, `clr_sum_zero`, `AitchisonIsometry.aitchisonDist`, `ilr_isometry`, `Closure.composition_smul_invariant`, `MatrixEffects.recoveredComposition_ratio_matrix_invariant`, `Alt.NeutralityScale.closureEstimate_bias`. None of these is used by the scorer.
- *Pipeline must adopt:* strict positivity before clr (Lean uses log 0 = 0), with zero replacement declared. The oracle stays on the mole basis (A5). The oxide closure must return a simplex plus a reporting transform (BL-36; SPC-06 found sum 0.667, PLAUSIBLE). Do not cite the absolute composition bounds for trace elements.
- *Spec must add:* FT-07 (clr_mul, perturbation and scale invariance, aliasing = ‖clr ρ‖, relative closure bound, mass-fraction transfer) and RF-23.

**F7 (DED gate: noise attribution, CRLB, fixed-point gain).**
- *Spec provides:* `FisherLineSelection.crlb_slope` and `olsSlope_attains_crlb` (Fisher information defined, homoscedastic; not a Cramér–Rao theorem); `Alt.OLSVariance`; `Alt.StochasticBudget`; `DifferentialEstimator.differentialRatio_immune_to_atomicData`. All are dormant.
- *Pipeline must adopt:* do not cite the crlb_* names as Cramér–Rao. `scripts/diag/ded_fixed_point_gain.py` should compute the closed-form g of FT-01 on each median piece, treat g ≥ 1 as "no attracting fixed point", and use the residual enclosure as the stop criterion.
- *Spec must add:* FT-01; FT-10 (BLUE floor and intercept-difference variance); FT-12(b) (exact Gaussian law for known σ_k).

**F8 (answer contract: `answered = produced ∧ converged ∧ abstention_policy`).**
- *Spec provides:* soundness re-exports for C1–C7, C9, C10 and C12–C14; `EvaluatorSoundness.hardGateBundle_*` (vacuous at realistic parameters); ConformalCoverage (counting only).
- *Pipeline must adopt:* none of the following may drive `answered`: C1–C3 (wrong design, SPC-01/INV-04), C12 (vacuous), C4 fed ε = 1/min SNR (a 1σ scale), C7 (circular), C10 (wrong loop). Every `reasons` entry should name a theorem: the C8 refusal, or TS-01 non-informativeness.
- *Spec must add:* FT-03's three-branch policy with group weights matching PAS; the FT-06 refusal; FT-04's C1g/C2g; FT-12's C4σ.

**W2-A (line-based science; owns the trust stack; BL-25/32/33/34/35/36).**
- *Spec provides:*
  - `OLS.*`, `OLSIdentifiability`, `ErrorBudget`, and `OLS.jointDesign_det_pos_iff` (single-intercept only).
  - `SahaInverse.sahaBoltzmann_shift_eq_log_saha` (live and faithful).
  - `StarkBroadening.starkDensity_recovers`.
  - `OuterLoopModelB.outerLoop_contracts` and `SahaRangeEnclosure.outerLoop_contracts_apriori`, which are REDUCED with a frozen offset. Do not use these as convergence evidence.
- *Pipeline must adopt:*
  - Make the A5 reuse-or-supersede decision against this report.
  - Evaluate identifiability on the kept mask with the within-element design.
  - Stop on the residual enclosure, not on a 100 K step.
  - `_resolve_ne` keeps both Stark and Saha sources.
  - Gate on SS_E rather than span, converting span with R²/2.
  - FitPolicy may cite WLS optimality only for measured-noise weights, not for A_ki grade weights.
- *Spec must add:* FT-04, FT-01, FT-10, FT-12, FT-06, and FT-17 (forward closure only).

**W2-S2 (AtomicEvidence; also listed as owner of certificate_gate.py).**
- *Spec provides:* `HeteroAtomicData.olsSlope_aliasing_A`, `olsSlope_aliasing_A_hetero`, `temp_rel_error_atomicData_hetero`; `AtomicDataPerturbation.classicDensity_aliasing_error_channels`; `Alt.OLSAtomicDataPerturbation`; C14. There are 0 pipeline references to any of them.
- *Pipeline must adopt:* a gA grade becomes a δ_k bias bound, not variance (HeteroAtomicData:94-97). C12 leaves the HARD set. C4's ε is either labelled 1σ or replaced by C4σ. Level lists are delivered truncated at or below the χ_eff used in the exponent, since the raw DB violates hEχ for 202 of 324 species.
- *Spec must add:* the RF-22 noise-plus-atomic composite; FT-09; FT-15 (to feed δ_U); FT-07's relative aliasing bound.

**W2-S3 / W3-A (M4 PopulationContext; forward physics; BL-40…44).**
- *Spec provides:* the 41 Tier-1 rows (e.g. `Saha.saha_relation`, `SahaStability.sahaFactor_strictMonoOn_temp`, `SahaRangeEnclosure.electronDensityFromRatio_mem_Icc`, `PartitionLipschitz.partitionFunction_lipschitz_temp`), plus StarkShift, OpticalDepth, RadiativeTransferDepth and EquivalentWidth.
- *Pipeline must adopt:*
  - A per-stage (χ_eff, level list ⊆ {E ≤ χ_eff}) pair, identical in forward and inverse.
  - Remove the exact-provider T clamp before claiming Tier-1 transfer.
  - A 2Δχ edge for stage III (FT-11 S10).
  - For contraction theorems to apply, the cutoff policy must be one of: n_e-independent, frozen inside the inner loop, or continuous occupation weights. A sharp n_e-dependent cutoff is incompatible.
  - McWhirter inputs in cm⁻³, K and eV.
  - BL-44: a Kirchhoff-consistent opacity and transfer before the instrument.
- *Spec must add:* FT-02, FT-05, FT-11, FT-14, FT-15; the RF-10 doc fix.

**M5 (one PopulationContext plus one emission/profile kernel; A11 "Tier 1b after M5").**
- *Spec provides:* Tier 1b is flat-slab SA/OpticalDepth identities, which are tautologies of the model, plus `MatrixIonizationCoupling.envelope_ionization_matrix_shift`, whose clause (c) has free binders.
- *Pipeline must adopt:* treat Tier 1b as model identities, not acceptance criteria.
- *Spec must add:* profile-level acceptance criteria:
  - FT-13: escape factor ≥ slab factor, and ½-Lipschitz τ-error propagation.
  - FT-14: Kirchhoff source, monotonicity in ℓ and N, and a per-line τ ratio with the stimulated-emission factor.
  - FT-16: the K8 instrument gain.
  - Spec 03 §2 `voigtMeasure` (RF-26).

**M6 (W1-S6 split of iterative.py; A11 "Tier 2 for M6").**
- *Spec provides today:* no valid convergence theorem for `iterative.py`. `outerLoop_contracts` and `jointConvergence` model a frozen-offset map that becomes degenerate once made consistent (INV-01, INV-02). Tier 2 lists Alt.CSigma (not csigma.py's twin), `homologousPair_*` (shared U) and DifferentialEstimator (not opc.py).
- *Pipeline must adopt:* W1-S6's pure `step(block, state)` is the object FT-01 certifies. The iteration trace should record g, the residual and the exit reason.
- *Spec must add:* FT-01, FT-04, FT-08(a); a per-element-F OPC theorem before any DifferentialEstimator↔opc.py pairing.

**W3-B (self-absorption; owns csigma.py).**
- *Spec provides:* `CurveOfGrowth.cogRatio_injOn`, `DoubletChannel.doubletRatio_injOn`, `SelfAbsorptionInverse.*`, `OpticalDepthBridge.boundOpticalDepth_lumped_alias`, and C13. All of these assume the flat kernel.
- *Pipeline must adopt:*
  - csigma.py has no Lean twin.
  - C13's inputs are opacity coefficients.
  - The per-line τ ratio keeps both e^(−ΔE_l/kT) (R3-05) and the (1 − e^(−hν/kT)) factor (FT-14 revised).
  - For Stark-broadened lines (γ/σ ≳ 0.1) the pair ratio has a second branch within a band under 1%, so the W3-B gate needs a conditioning check or a third observable.
- *Spec must add:* FT-13, FT-20, FT-18, FT-14(iv).

**W3-C (calibration layer).**
- *Spec provides:* `HeteroAtomicData.olsSlope_aliasing_A` (EXACT), `Classic.classic_calibration_free`, the AtomicDataPerturbation aliasing results, InhomogeneityBias.
- *Pipeline must adopt:* add the E-linear gA direction to the gauge, or report its posterior correlation with T. Identifying that direction needs an independent n_e or known composition. Require b < min_i 1/(kB·T_i). A T-independent gA factor cannot absorb a cutoff-policy change (FT-05(iii)).
- *Spec must add:* FT-09 (revised), FT-05, FT-15.

**W3-E (DED ratio drift; the owner's Al/Ti and V/Ti metric).**
- *Spec provides:* the MatrixEffects homologous-pair results (shared U, Boltzmann only); DifferentialEstimator; `TemporalEvolution.temporal_temperature_insitu`; `Alt.NeutralityScale`. NeutralityScale addresses the absolute Fcal, is orthogonal to ratio mode, and its Abbass citation is off the whitelist.
- *Pipeline must adopt:* do not cite NeutralityScale or the shared-U invariance for BL-48. The rule of matching pairs on |ΔE_k − ΔIP| nulls first-order T-sensitivity only when both observed stages are minority stages and the ion-stage mean excitation energies match. Otherwise select pairs on the full first-order coefficient.
- *Spec must add:* FT-08, the FT-10(c) intercept-difference floor, and FT-07.

---

## 5. Frontier theorem slate

The slate is ranked as proposed. The verdicts changed statements, not the order. FT-04 must still land before FT-01's physics binding. "PROVED" means proved in scratch and checked axiom-clean ({propext, Classical.choice, Quot.sound}) during this run.

### FT-01: Stop and convergence certificate for the (T, n_e) loop the pipeline runs
*Verdict: REVISE. Grade B for the mathematics, C for the physics binding.*

**Statement.** With IPD off, the reduced map (SB graph on x* = E + IP(z−1) with element dummies; n_e from the sb_offset median element) is affine in u = 1/kT on each median piece, with gain g = (Σ b_e D_e)·D_m/Σ(W_e + b_e D_e²).
- The u-damped idealization converges exactly at rate 1−λ+λg, and converges from every start iff 1 − 2/λ < g < 1.
- The pipeline damps T, not u. For 0 < g < 1 the T-damped Möbius map converges monotonically from every T > 0, with local rate 1−λ+λg.
- For a nonlinear map, a derivative window inside (1−2/λ, 1) on an invariant box gives contraction. A fixed point with g′ > 1 repels for every λ > 0.
- A 2×2 Gauss–Seidel Jacobian applies when ∂n_e,new/∂n_e,prev = 0 (sb_offset tier, IPD off). Then ρ(J) < 1 iff g < 1 ∧ −5 < A < 3 ∧ 3A + BC > −9.
- A unit-invariant weighted gate exists iff a < 1 ∧ d < 1 ∧ bc < (1−a)(1−d).
- A-posteriori stop: |u − u*| ≤ |Φu − u|/(1−q). At g = 0.964 the 100 K step implies about 5.6 kK linearized distance.

```lean
def dampedMap (lam : ℝ) (g : ℝ → ℝ) (u : ℝ) : ℝ := (1 - lam) * u + lam * g u
theorem dampedAffine_iterate (lam g c u0 : ℝ) (hg : g ≠ 1) (n : ℕ) :
    (dampedMap lam (fun u => g * u + c))^[n] u0 - c / (1 - g)
      = (1 - lam + lam * g) ^ n * (u0 - c / (1 - g))                        -- PROVED; u-damped model
theorem dampedAffine_tendsto_iff (lam g c : ℝ) (hlam : 0 < lam) (hg : g ≠ 1) :
    (∀ u0, Tendsto (fun n => (dampedMap lam (fun u => g * u + c))^[n] u0) atTop (𝓝 (c / (1 - g))))
      ↔ (1 - 2 / lam < g ∧ g < 1)
-- what iterative.py does (damping in T):
theorem tDamped_mobius_converges {g c lam : ℝ} (hg0 : 0 < g) (hg1 : g < 1) (hc : 0 < c)
    (hl0 : 0 < lam) (hl1 : lam ≤ 1) (T0 : ℝ) (hT0 : 0 < T0) :
    Tendsto (fun n => (dampedMap lam (fun T => T / (g + c * T)))^[n] T0) atTop (𝓝 ((1 - g) / c))
theorem tDamped_local_rate {g c lam : ℝ} (hg1 : g < 1) (hc : 0 < c) :
    HasDerivAt (dampedMap lam (fun T => T / (g + c * T))) (1 - lam + lam * g) ((1 - g) / c)
theorem dampedMap_contracts {g g' : ℝ → ℝ} {a b m M lam : ℝ} (hlam0 : 0 < lam) (hab : a ≤ b)
    (hd : ∀ T ∈ Set.Icc a b, HasDerivAt g (g' T) T) (hmM : ∀ T ∈ Set.Icc a b, m ≤ g' T ∧ g' T ≤ M)
    (hlo : 1 - 2 / lam < m) (hhi : M < 1)
    (hmaps : Set.MapsTo (dampedMap lam g) (Set.Icc a b) (Set.Icc a b)) :
    ∃ Tstar ∈ Set.Icc a b, dampedMap lam g Tstar = Tstar ∧
      ∀ T0 ∈ Set.Icc a b, Tendsto (fun n => (dampedMap lam g)^[n] T0) atTop (𝓝 Tstar)
theorem dampedMap_repelling {g : ℝ → ℝ} {d Tstar lam : ℝ} (hfix : g Tstar = Tstar)
    (hd : HasDerivAt g d Tstar) (hd1 : 1 < d) (hlam : 0 < lam) :
    ∃ ε > 0, ∀ T, 0 < |T - Tstar| → |T - Tstar| < ε → |T - Tstar| < |dampedMap lam g T - Tstar|
theorem residual_stop {Φ : ℝ → ℝ} {s : Set ℝ} {q u ustar : ℝ} (hq : q < 1)
    (hLip : ∀ x ∈ s, ∀ y ∈ s, |Φ x - Φ y| ≤ q * |x - y|) (hu : u ∈ s) (hs : ustar ∈ s)
    (hfix : Φ ustar = ustar) : |u - ustar| ≤ |Φ u - u| / (1 - q)             -- PROVED
theorem jury_two (t d : ℝ) :
    (∀ z : ℂ, z ^ 2 - (t : ℂ) * z + (d : ℂ) = 0 → ‖z‖ < 1) ↔ (|d| < 1 ∧ |t| < 1 + d)
theorem gaussSeidel_det_trace (A B C : ℝ) :      -- valid only when ∂ne_new/∂ne_prev = 0
    let J : Matrix (Fin 2) (Fin 2) ℝ := !![1/2 + A/2, B/2; C/2 * (1/2 + A/2), 1/2 + B*C/4]
    J.det = (1 + A) / 4 ∧ 1 + J.det - J.trace = (1 - (A + B * C)) / 4   -- PROVED
theorem exists_weights_iff {a b c d : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c) :
    (∃ wT wn : ℝ, 0 < wT ∧ 0 < wn ∧ max (a + b * wn / wT) (c * wT / wn + d) < 1)
      ↔ (a < 1 ∧ d < 1 ∧ b * c < (1 - a) * (1 - d))                        -- ⇐ PROVED
theorem single_group_gain {b D W : ℝ} (hb : 0 < b) (hW : 0 < W) : b * D ^ 2 / (b * D ^ 2 + W) < 1
```

- **Scope.** PURE-MATH for the dynamics and linear algebra. REDUCED for the binding `reducedMap_affine_u`: IPD off, one median piece, unit SB weights, fixed-slope sb_offset leg, no holds.
- **Hypotheses.**
  - `hg ≠ 1`: the marginal case is exactly the one to refuse.
  - The derivative window replaces the product-of-Lipschitz gate, which is 10^3–10^5 too loose.
  - `hmaps` is checked a posteriori from the T window.
  - The Gauss–Seidel form needs the n_e leg to be independent of n_e. That fails on the Stark and pressure fallbacks and with IPD on, via effective_ips.
  - `0 < b` holds because b = n_I·n_II/n_e.
- **Prerequisites.** FT-04 (`feSlope_add_smul`) for the binding. mathlib: `ContractingWith.dist_fixedPoint_le`, `image_sub_le_mul_sub_of_deriv_le`, `tendsto_pow_atTop_nhds_zero_of_lt_one`, `Matrix.det_fin_two`.
- **Queue decomposition.**
  1. `dampedAffine_iterate`, `residual_stop`, `gaussSeidel_det_trace`, weights ⇐: done.
  2. `dampedAffine_tendsto_iff`.
  3. `gate_of_weights` (⇒).
  4. `jointOuterContraction_weighted`: rescale, and instantiate Gauss–Seidel as fNe∘fT.
  5. `jury_two`, as a real-roots target and a complex-roots target.
  6. `tDamped_mobius_converges` (monotone sign-preserving argument) and `tDamped_local_rate`.
  7. `dampedMap_contracts` (MVT plus the ContractingWith-on-Icc pattern from `outerContraction_box`).
  8. `dampedMap_repelling`.
  9. `single_group_gain`.
  10. Physics binding in three steps: SB slope affine in ln S; ln S affine in u via fixed-slope intercepts; composition. This step needs a Mode B statement audit first.
- **Consumers.** BL-25 and BL-06 (critical; exit reason and abstention), BL-35/R9-02, BL-49, F7 `ded_fixed_point_gain.py`, the G2 TS-09 C11 slot, and the W1-S6 `step()`.
- **Verifier revisions.**
  - The u-damped lemmas are relabelled as a model: the pipeline damps T.
  - The global window is false for T-damping (at g = −1 the iterate goes negative).
  - The Jacobian hypothesis is now explicit.
  - `single_group_gain` was false for B < −W, so `0 < b` was added.
  - `hlam1` and the unused `ha`/`hd` were dropped.
  - The binding is grade C because the map is piecewise.
- **Literature.** Aguilera & Aragón 2007 (SAB 62:378, whitelisted) and Yalcin 1999 (whitelisted) define the map. Everything else is PURE-MATH.

### FT-02: IPD gauge and the implicit IPD-aware Saha inverse
*Verdict: REVISE. Grade A.*

**Statement.**
- S(χ − d) = S(χ)·e^(d/kT). An IPD-off inverse applied to IPD-on data therefore reports n_e·e^(−Δχ/kT).
- With an element-independent d on the I→II edge, the sb_offset route recovers every species' Saha ratio exactly: S_s(χ_s)/n̂ = S_s(χ_s − d)/n_e. Two-stage totals, and hence composition, are therefore exact.
- Stark or injected n_e is biased by exactly e^(Δχ/kT).
- In ℓ = ln n_e, with Δχ = kT·b·√n_e, the IPD-aware inverse is the fixed point of F(ℓ) = ln a + b·e^(ℓ/2). There is at most one root with q = Δχ/(2kT) < 1. F contracts on invariant half-lines, and d ln n_e/d ln R lies in [1, 1/(1−q)] as a two-point bracket.
- Numbers at 1e17 cm⁻³ and 11 kK: Δχ = 0.0629 eV, q = 0.0332, q³ ≈ 3.7e-5 (jitpipe's three inner steps); the fold sits near 9.08e19 cm⁻³.
- The 0.9358 reproduction of R1-07 is a consistency check, because its Debye–Hückel anchor was fitted to R1-07.

```lean
theorem sahaFactor_ipd_gauge (kB T me h chi d : ℝ) (gZ EZ : ι → ℝ) (gZ1 EZ1 : κ → ℝ) :
    sahaFactor kB T me h (chi - d) gZ EZ gZ1 EZ1
      = sahaFactor kB T me h chi gZ EZ gZ1 EZ1 * Real.exp (d / (kB * T))            -- PROVED
theorem ne_ipd_mismatch {kB T me h chi d R ne : ℝ} (hR : R ≠ 0)
    (hfwd : R * ne = sahaFactor kB T me h (chi - d) gZ EZ gZ1 EZ1) :
    electronDensityFromRatio kB T me h chi gZ EZ gZ1 EZ1 R = ne * Real.exp (-(d / (kB * T)))  -- PROVED
theorem sahaRatio_ipd_gauge (hfwd : Rm * ne = sahaFactor kB T me h (chim - d) gm Em gm1 Em1) … :
    sahaFactor kB T me h chis gs Es gs1 Es1 / electronDensityFromRatio kB T me h chim gm Em gm1 Em1 Rm
      = sahaFactor kB T me h (chis - d) gs Es gs1 Es1 / ne                          -- PROVED
-- corollary: N_I,s·(1 + S_s/n̂) = N_I,s·(1 + S_s(χ−d)/n_e) ⇒ composition exact (I→II, element-independent d, U frozen)
noncomputable def ipdLogMap (a b ℓ : ℝ) : ℝ := Real.log a + b * Real.exp (ℓ / 2)
theorem ipdLogMap_root_subsingleton {a b : ℝ} (hb : 0 < b) :
    {ℓ | ipdLogMap a b ℓ = ℓ ∧ b * Real.exp (ℓ / 2) < 2}.Subsingleton
theorem ipdLogMap_contracts {a b ℓ1 q : ℝ} (hb : 0 ≤ b) (hq : b * Real.exp (ℓ1 / 2) / 2 ≤ q)
    (hq1 : q < 1) (hmaps : Set.MapsTo (ipdLogMap a b) (Set.Iic ℓ1) (Set.Iic ℓ1)) :
    ∃ ℓs ∈ Set.Iic ℓ1, ipdLogMap a b ℓs = ℓs ∧ (∀ ℓ ∈ Set.Iic ℓ1, ipdLogMap a b ℓ = ℓ → ℓ = ℓs) ∧
      ∀ ℓ0 ∈ Set.Iic ℓ1, Tendsto (fun n => (ipdLogMap a b)^[n] ℓ0) atTop (𝓝 ℓs)
theorem ipdInverse_twoPoint_sensitivity {a1 a2 b l1 l2 q : ℝ} (ha1 : 0 < a1) (hb : 0 ≤ b)
    (hq : q < 1) (h1 : ipdLogMap a1 b l1 = l1) (h2 : ipdLogMap a2 b l2 = l2) (ha : a1 ≤ a2)
    (hreg : b * Real.exp (max l1 l2 / 2) / 2 ≤ q) :
    Real.log a2 - Real.log a1 ≤ l2 - l1 ∧ l2 - l1 ≤ (Real.log a2 - Real.log a1) / (1 - q)
```

- **Scope.** EXACT for the gauge and mismatch identities. PURE-MATH for the fixed-point lemmas. REDUCED for the physical reading: Debye–Hückel √n_e form, one edge, element-independent d, level list frozen in the inner loop.
- **Hypotheses.**
  - `0 < a1` avoids Lean's junk log.
  - `0 ≤ b` because lowering is non-negative. The unguarded version has two Lean counterexamples.
  - q < 1 is sharp, since the roots fold at q = 1.
  - Because F is monotone, F(ℓ1) ≤ ℓ1 suffices for `hmaps`.
- **Prerequisites.** Saha.lean. mathlib: `Real.exp_add`, `ContractingWith.exists_fixedPoint'`, the MVT. FT-05 or a frozen cutoff inside the inner loop.
- **Queue decomposition.**
  1. The gauge, mismatch and ratio-gauge lemmas: done.
  2. The composition corollary.
  3. `ipdLogMap_hasDerivAt`.
  4. Lipschitz on `Iic`.
  5. Contraction.
  6. Root subsingleton, via strictMonoOn of ℓ − F.
  7. Two-point sensitivity.
  8. Physics binding with a = S(χ)/R.
- **Consumers.** BL-42 (bead 3n4a), R1-07, the A11 IPD regression test (RF-25), the m4 doc (RF-10), jitpipe/solve.py:842-866, BL-34.
- **Verifier revisions.**
  - The `composition_smul_invariant` mechanism was wrong and is replaced by `sahaRatio_ipd_gauge`.
  - The sensitivity lemma was false without `0 < a1` and `0 ≤ b`.
  - q³ is 3.7e-5.
  - The M4 sentence is incomplete, not false.
  - (a) holds when Δχ is unmodelled; with the DH model, (b) identifies n_e.
  - The M4 change is an addition, not a correction.
- **Literature.** Griem 1997 (whitelisted). Ristić et al. 2024, PPCF, DOI 10.1088/1361-6587/ad8b68, was retrieved by the literature auditor; it is off the whitelist and not re-opened. The Δχ model (electron-only vs electron+ion) is an owner decision, so b stays abstract.

### FT-03: Refuse-to-report policy on the Aitchison PAS loss
*Verdict: REVISE. Grade A.*

**Statement.** Take per-spectrum losses ℓ_i with certified bounds L_i ≤ ℓ_i ≤ U_i, group weights w_i > 0 (PAS is a grouped mean, objective-and-splits.md:11), and the ambiguous set A = {L_i ≤ λ < U_i}. The three-branch policy answers if U_i ≤ λ, refuses if L_i > λ, and makes an explicit choice on A.
- Off A, each item costs at most min(ℓ_i, λ), the oracle cost.
- Refusing on A gives PAS ≤ (Σw)·λ and regret ≤ Σ_A w_i (λ − L_i).
- Answering on A gives gate value G = PAS_forced − PAS_gated ≥ 0 (SC-04).
- The two guarantees conflict on A, so the policy must expose the choice.
- Loss certificate: d_A(Ĉ, C) ≤ ‖e − c·1‖₂ for every c, with e_s = ln(N̂_s/N_s).
- Refusal-reason soundness: on sb_offset, the Saha-consistency residual is identically 0.

```lean
noncomputable def pasPolicy {N : ℕ} (w l L U : Fin N → ℝ) (lam : ℝ) (ansA : Fin N → Prop)
    [DecidablePred ansA] : ℝ :=
  ∑ i, w i * (if U i ≤ lam then l i else if lam < L i then lam else if ansA i then l i else lam)
theorem pasPolicy_offAmbig_oracle (hL : L i ≤ l i) (hU : l i ≤ U i) (hi : ¬ (L i ≤ lam ∧ lam < U i)) :
    (if U i ≤ lam then l i else if lam < L i then lam else l i) ≤ min (l i) lam
theorem pasPolicy_refuseAmbig_le (hw : ∀ i, 0 < w i) (hU : ∀ i, l i ≤ U i) :
    pasPolicy w l L U lam (fun _ => False) ≤ (∑ i, w i) * lam      -- weighted form of pas_certified_le_lambda (PROVED unweighted)
theorem pasPolicy_refuseAmbig_regret (hw) (hL : ∀ i, L i ≤ l i) (hU : ∀ i, l i ≤ U i) :
    pasPolicy w l L U lam (fun _ => False) - ∑ i, w i * min (l i) lam
      ≤ ∑ i, w i * (if L i ≤ lam ∧ lam < U i then lam - L i else 0)
theorem pasPolicy_answerAmbig_gateValue (hw) (hL : ∀ i, L i ≤ l i) :
    pasPolicy w l L U lam (fun _ => True) ≤ ∑ i, w i * l i          -- G ≥ 0; weighted pas_gate_value_nonneg (PROVED unweighted)
theorem aitchisonDist_le_logErr [Nonempty ι] {x y : ι → ℝ} (hx : ∀ k, 0 < x k) (hy : ∀ k, 0 < y k)
    (c : ℝ) : aitchisonDist y x ≤ Real.sqrt (∑ s, (Real.log (y s / x s) - c) ^ 2)
theorem sahaConsistency_trivial_of_sbOffset {kB T me h chi Rhat : ℝ} (hR : Rhat ≠ 0) :
    Rhat * electronDensityFromRatio kB T me h chi gZ EZ gZ1 EZ1 Rhat
      = sahaFactor kB T me h chi gZ EZ gZ1 EZ1                    -- PROVED
theorem sahaTemperature_eq_fit (hinj : Set.InjOn (fun T => sahaFactor kB T me h chi gZ EZ gZ1 EZ1 / Rhat) box)
    (hTf : Tfit ∈ box) (hTs : Tsaha ∈ box)
    (hsol : sahaFactor kB Tsaha me h chi gZ EZ gZ1 EZ1 / Rhat
              = electronDensityFromRatio kB Tfit me h chi gZ EZ gZ1 EZ1 Rhat) : Tsaha = Tfit
```

- **Scope.** PURE-MATH throughout, including the refusal-reason lemmas. They state a property of the diagnostic, not of the plasma.
- **Hypotheses.**
  - The bounds are R1-epistemic, so the theorem is conditional.
  - λ_d is fixed before scoring, which makes these deterministic finite-sample statements.
  - Strict positivity is required (log 0 = 0); zero replacement comes first.
  - `hinj` comes from `electronDensityFromRatio_strictMonoOn_temp` under hEχ read as a cutoff obligation.
- **Prerequisites.** FT-07 and FT-15 make the U_i non-vacuous.
- **Queue decomposition.**
  1. Weighted generalizations of the three proved policy lemmas.
  2. `pasPolicy_offAmbig_oracle`.
  3. `clr_sub_eq_centered_log`.
  4. `norm_centered_le`, reusing `FisherLineSelection.sum_sq_sub_eq_spreadOn_add`.
  5. `aitchisonDist_le_logErr`.
  6. `sahaTemperature_eq_fit`.
  7. Bundled `answerPolicy` soundness.
- **Consumers.** BL-02 (critical), F8 `abstention_policy`, G1 SC-03/SC-04/SC-05, G2 TS-01 (critical) and TS-02, BL-01.
- **Verifier revisions.** A single policy with both guarantees is contradictory on A; Lean witnesses showed both failure directions. The fix is a three-branch policy with group weights. Part (e) is retagged PURE-MATH, and its docstring must name the mismatches it does not cover: weighted vs unweighted intercepts, raw vs IPD IP.
- **Literature.** Aitchison 1986 (whitelisted). PAS is the companion's own definition.

### FT-04: Fixed-effects (element-dummy) weighted Saha–Boltzmann design and C1g/C2g
*Verdict: KEEP. Grade A; `feJoint_identifiable_iff` is grade B.*

**Statement.** For y_k = a_{e(k)} + βx_k (+ νs_k) with weights w > 0:
- β is identifiable iff the weighted within-element sum of squares SS_W > 0.
- The within-centered slope, the production formula at iterative.py:1764-1806, minimizes the weighted RSS.
- The slope is linear in y, which gives FT-01 its offset-affinity lemma.
- (β, ν) are identifiable iff the within-element Gram determinant is positive.
- A pooled SS > 0 does not imply SS_W > 0. The executed false positive (re-run) had C1 = C3 = 4.0 with SS_W = 0.
- Under Var ε_k = σ²/w_k, Var β̂ = σ²/SS_W.

```lean
noncomputable def gMean (grp : ι → κ) (w f : ι → ℝ) (e : κ) : ℝ :=
  (∑ k ∈ univ.filter (fun k => grp k = e), w k * f k) / ∑ k ∈ univ.filter (fun k => grp k = e), w k
noncomputable def withinCross (grp : ι → κ) (w x y : ι → ℝ) : ℝ :=
  ∑ k, w k * (x k - gMean grp w x (grp k)) * (y k - gMean grp w y (grp k))
noncomputable def withinSS (grp : ι → κ) (w x : ι → ℝ) : ℝ := withinCross grp w x x
noncomputable def feSlope (grp : ι → κ) (w x y : ι → ℝ) : ℝ := withinCross grp w x y / withinSS grp w x
theorem fe_identifiable_iff (hw : ∀ k, 0 < w k) :
    (∀ (a a' : κ → ℝ) (β β' : ℝ), (∀ k, a (grp k) + β * x k = a' (grp k) + β' * x k) → β = β')
      ↔ 0 < withinSS grp w x
theorem feSlope_add_smul (c : ℝ) :
    feSlope grp w x (fun k => y k + c * s k) = feSlope grp w x y + c * feSlope grp w x s
theorem feSlope_isMin (hw : ∀ k, 0 < w k) (hSS : 0 < withinSS grp w x) (a : κ → ℝ) (β : ℝ) :
    ∑ k, w k * (y k - (gMean grp w y (grp k) - feSlope grp w x y * gMean grp w x (grp k))
                  - feSlope grp w x y * x k) ^ 2 ≤ ∑ k, w k * (y k - a (grp k) - β * x k) ^ 2
theorem feJoint_identifiable_iff (hw : ∀ k, 0 < w k) :
    (∀ (a a' : κ → ℝ) (β β' ν ν' : ℝ),
        (∀ k, a (grp k) + β * x k + ν * s k = a' (grp k) + β' * x k + ν' * s k) → β = β' ∧ ν = ν')
      ↔ 0 < withinSS grp w x * withinSS grp w s - withinCross grp w x s ^ 2
example : 0 < ∑ k : Fin 4, (![3, 3, 5, 5] k - mean ![(3 : ℝ), 3, 5, 5]) ^ 2 ∧
    withinSS (![0, 0, 1, 1] : Fin 4 → ℕ) (fun _ => 1) ![(3 : ℝ), 3, 5, 5] = 0
def groupedRankCert (grp : ι → κ) (w x : ι → ℝ) : Prop := 0 < withinSS grp w x
def groupedJointRankCert (grp : ι → κ) (w x s : ι → ℝ) : Prop :=
  0 < withinSS grp w x * withinSS grp w s - withinCross grp w x s ^ 2
```

- **Scope.** PURE-MATH. The physics binding (x = E + IP_e·s, ν = ln n_e) is REDUCED: LTE, one T, IPD off or frozen.
- **Hypotheses.** Weights w > 0 (the pipeline uses capped 1/σ_y²). Evaluate on the solver's kept set, since elements with fewer than 2 lines are dropped at iterative.py:1727. Empty groups give 0/0 = 0; document this in gMean.
- **Prerequisites.** mathlib `Finset.sum_fiberwise`, `Finset.sum_mul_sq_le_sq_mul_sq`, `Matrix.det_fin_two`.
- **Queue decomposition.**
  1. gMean linearity.
  2. `withinCross_add_right`.
  3. `feSlope_add_smul`.
  4. `withinCross_groupConst`, the fiberwise crux.
  5. `withinSS_eq_zero_iff`.
  6. `fe_identifiable_iff`.
  7. `feSlope_isMin`.
  8. Gram ≥ 0.
  9. `feJoint_identifiable_iff` (grade B).
  10. The counterexample.
  11. C1g/C2g soundness.
- **Consumers.** certificates_wiring C1/C2/C3, BL-35/R2-07, BL-36/R2-09, FT-01.
- **Verifier.** Refutation attempts failed and novelty is confirmed. The only notes: grade the joint theorem B, and require evaluation on the kept lines.
- **Literature.** Aguilera & Aragón 2007 and Aitken 1935 (both whitelisted).

### FT-05: Partition-function truncation and cutoff policy
*Verdict: REVISE. Grade A.*

**Statement.**
- (i) 0 ≤ U − U_cut ≤ (Σ_{E≥cut} g)·e^(−cut/kT).
- (ii) If some level is kept and some dropped, U/U_cut is strictly increasing in T. No extra hypothesis is needed, because every dropped level lies above every kept level.
- (iii) Hence U/U_cut is injective in T, so no T-independent gA factor can fit two distinct training temperatures.
- (iv) When numerator and U use mismatched lists, every kept level is biased by the species-common, T-dependent factor U_cut/U.
- (v) A sharp cutoff that moves with n_e cannot satisfy the Lipschitz-in-n_e hypotheses. Compatible policies are an n_e-independent cutoff, a cutoff frozen inside the inner loop, or continuous weights w_k(n_e).

```lean
noncomputable def partitionFunctionCut (kB T cut : ℝ) (g E : ι → ℝ) : ℝ :=
  ∑ k ∈ univ.filter (fun k => E k < cut), g k * boltzmannFactor kB T (E k)
theorem partitionFunction_sub_cut_bounds (hg : ∀ k, 0 ≤ g k) (hkT : 0 < kB * T) :
    0 ≤ partitionFunction kB T g E - partitionFunctionCut kB T cut g E ∧
    partitionFunction kB T g E - partitionFunctionCut kB T cut g E
      ≤ (∑ k ∈ univ.filter (fun k => cut ≤ E k), g k) * Real.exp (-cut / (kB * T))   -- PROVED
theorem cutRatio_strictMonoOn_temp (hkB : 0 < kB) (hg : ∀ k, 0 < g k)
    (hkeep : ∃ k, E k < cut) (hdrop : ∃ k, cut ≤ E k) :
    StrictMonoOn (fun T => partitionFunction kB T g E / partitionFunctionCut kB T cut g E) (Set.Ioi 0)
theorem cutRatio_injOn (hkB) (hg) (hkeep) (hdrop) :
    Set.InjOn (fun T => partitionFunction kB T g E / partitionFunctionCut kB T cut g E) (Set.Ioi 0)
theorem cutRatio_not_absorbable_two (…) (hT1 : 0 < T1) (hT2 : 0 < T2) (hne : T1 ≠ T2) (c : ℝ) :
    ¬ (partitionFunction kB T1 g E = c * partitionFunctionCut kB T1 cut g E ∧
       partitionFunction kB T2 g E = c * partitionFunctionCut kB T2 cut g E)
theorem population_cut_consistent :   -- keep := univ.filter (E · < cut); bf k := boltzmannFactor kB T (E k)
    (∑ k ∈ keep, N * g k * bf k / partitionFunctionCut kB T cut g E = N) ∧
    ∀ k ∈ keep, population kB T N g E k
      = (N * g k * bf k / partitionFunctionCut kB T cut g E)
          * (partitionFunctionCut kB T cut g E / partitionFunction kB T g E)
theorem sharpCutoff_discontinuous : ∃ (g E : Fin 2 → ℝ) (Δχ : ℝ → ℝ), Continuous Δχ ∧
    ¬ ContinuousOn (fun ne => partitionFunctionCut kB T (chi - Δχ ne) g E) (Set.Ioi 0)
```

- **Scope.** PURE-MATH for (i)–(iii) and (v). EXACT for (iv).
- **Hypotheses.** `hkeep` and `hdrop` are load-bearing: the ratio is 1 if nothing is dropped and U_cut = 0 if nothing is kept. Both hold for 202 of 324 DB species. hEχ is restated as a cutoff obligation.
- **Queue decomposition.**
  1. Bounds: done.
  2. `tailKeep_cross` double-sum sign (the crux).
  3. strictMono.
  4. injOn.
  5. Non-absorbable corollary.
  6. `population_cut_consistent`.
  7. Fin-2 witness.
  8. Doc rewording of hEχ (in RF-10).
- **Consumers.** BL-41 (critical), R1-02 (critical), R1-03, R1-10, BL-47, M4 LevelCutoffPolicy.
- **Verifier revisions.** (iii) as `¬∀T` was too weak and is now an injOn statement. (iv) as literally worded was false and is now precise. (v) as "only continuous policies" overclaimed.
- **Literature.** Griem 1997 (whitelisted). Hummer & Mihalas 1988 is cited only via R1-02 and is unverified. Mihalas 1978 is UNVERIFIED and must not be cited.

### FT-06: Missing runtime certificates: C8 on error bars, a sound refusal, C10 without an unknown fixed point
*Verdict: REVISE. Grade A.*

**Statement.** Given R1 brackets n_e ∈ [lS, uS] from Stark and [lR, uR] from Saha:
- If either lower end clears C√T·ΔE³, the true n_e passes McWhirter. Soundness needs only one diagnostic.
- The two-diagnostic content is the refusal: if min(uS, uR) < max(lS, lR), the two error models cannot both hold.
- The Stark bracket is [n_S/(kOpac·ρ_w), n_S·ρ_w]. With ρ_w = 1 it reduces to the existing `starkOpacityLteCert`, which is prior art.
- An IPD-off Saha inverse gives [n̂, n̂·e^(Δχmax/kT)].
- C10-closed is a re-export of the existing capstone.

```lean
def starkSahaCert (lS uS lR uR C T dE : ℝ) : Prop :=
  max lS lR ≤ min uS uR ∧ C * Real.sqrt T * dE ^ 3 ≤ max lS lR
theorem starkSaha_certificate_sound {lS uS lR uR C T dE ne : ℝ} (hS : lS ≤ ne ∧ ne ≤ uS)
    (hR : lR ≤ ne ∧ ne ≤ uR) (h : starkSahaCert lS uS lR uR C T dE) :
    mcWhirterCert C T dE ne                                   -- PROVED (uses lower ends only)
theorem starkSaha_refusal_sound {lS uS lR uR ne : ℝ} (hdis : min uS uR < max lS lR) :
    ¬ ((lS ≤ ne ∧ ne ≤ uS) ∧ (lR ≤ ne ∧ ne ≤ uR))              -- PROVED
theorem saha_ipd_bracket {kB T me h chi d dmax R ne : ℝ} (hkT : 0 < kB * T) (hR : 0 < R)
    (hne : 0 < ne) (hd : 0 ≤ d) (hdm : d ≤ dmax)
    (hfwd : R * ne = sahaFactor kB T me h (chi - d) gZ EZ gZ1 EZ1) :
    electronDensityFromRatio kB T me h chi gZ EZ gZ1 EZ1 R ≤ ne ∧
    ne ≤ electronDensityFromRatio kB T me h chi gZ EZ gZ1 EZ1 R * Real.exp (dmax / (kB * T)) -- PROVED
theorem stark_bracket_rho (hw : 0 < w) (hρ : 1 ≤ ρw) (hk : 0 < kOpac)
    (hwT : w / ρw ≤ wTrue ∧ wTrue ≤ w * ρw)
    (hopac : starkFWHM wTrue nRef neTrue ≤ widthMeas)
    (hbudget : widthMeas ≤ kOpac * starkFWHM wTrue nRef neTrue) :
    starkDensity w nRef widthMeas / (kOpac * ρw) ≤ neTrue ∧ neTrue ≤ starkDensity w nRef widthMeas * ρw
theorem dampedIter_certificate_sound_closed [Nonempty ι] (S Ntot : ι → ℝ) {x0 : ℝ}
    (hcert : dampedIterCert S Ntot) (hx0 : 0 ≤ x0) : … :=
  dampedMultiElementIter_converges_to_equilibrium S Ntot hcert.1 hcert.2 rfl hx0   -- re-export (RF-05)
```

- **Scope.** PURE-MATH for soundness and refusal. EXACT for `saha_ipd_bracket`. REDUCED for the Stark bracket (linear electron-impact width). Retag `stark_saha_lte_consistent` to PURE-MATH or REDUCED.
- **Hypotheses.** The R1 brackets are assumed inputs (kOpac from StarkOpacityGuard, ρ_w from the Stark-parameter grade, where 99.3% of pipeline widths are heuristic, and Δχmax), carrying a C14-style note. The predicate must carry units: n_e in cm⁻³, T in K, ΔE in eV.
- **Queue decomposition.**
  1. Soundness, refusal and Saha bracket: done.
  2. `stark_bracket_rho`.
  3. C8 composite.
  4. C10 re-export.
  5. Docstrings and tags.
  6. Float mirror with ≤-vs-< boundary fixtures.
- **Consumers.** G2 TS-09 (C8 slot), TS-01 and TS-02, BL-34, F8 reasons. `_resolve_ne` must keep both sources, since today it returns the first one.
- **Verifier revisions.**
  - "Two-diagnostic soundness" overclaimed; soundness uses one diagnostic.
  - `stark_bracket_rho` is now fully written out.
  - `starkOpacityLteCert` was not credited as prior art.
  - The C10 docstring should name its actual scope, not simply be called "false". It also does not model round_trip.py's isobaric three-stage loop.
  - The numbering is an owner decision.
- **Literature.** McWhirter 1965, Cristoforetti 2010 and Griem 1974 (all whitelisted).

### FT-07: Aitchison error transfer and abundance-scaled closure bounds
*Verdict: KEEP. Grade A.*

**Statement.**
- clr(a⊙x) = clr a + clr x. Hence d_A is perturbation-invariant (mole↔mass) and scale-invariant (oxide output).
- Aliasing: if N̂ = N⊙ρ, then d_A(N̂, N) = ‖clr ρ‖; a common factor is invisible.
- Relative closure: if |N̂_s − N_s| ≤ ηN_s with η < 1, then |Ĉ_s − C_s| ≤ 2η/(1−η)·C_s. For a 0.5% minor element with 5% error this gives 5.26e-4, against an actual worst case of 5.23e-4 and a current absolute bound of 0.0557.
- The same bound transfers to mass fractions.
- Additive errors do amplify on minor elements.

```lean
theorem clr_mul {x a : ι → ℝ} (hx : ∀ k, 0 < x k) (ha : ∀ k, 0 < a k) :
    clr (fun k => a k * x k) = fun k => clr a k + clr x k                         -- PROVED
theorem aitchisonDist_perturb [Nonempty ι] (hx : ∀ k, 0 < x k) (hy : ∀ k, 0 < y k)
    (ha : ∀ k, 0 < a k) : aitchisonDist (fun k => a k * x k) (fun k => a k * y k) = aitchisonDist x y
theorem aitchisonDist_smul [Nonempty ι] (hc : 0 < c) (hx : ∀ k, 0 < x k) :
    aitchisonDist (fun k => c * x k) y = aitchisonDist x y
theorem aitchisonDist_aliasing [Nonempty ι] (hN : ∀ s, 0 < N s) (hρ : ∀ s, 0 < ρ s) :
    aitchisonDist (fun s => N s * ρ s) N = ‖clrE ρ‖
theorem composition_rel_error_mul (hN : ∀ s, 0 < N s) (hη0 : 0 ≤ η) (hη1 : η < 1)
    (hmul : ∀ s, |Nhat s - N s| ≤ η * N s) (s : ι) :
    |composition Nhat s - composition N s| ≤ (2 * η / (1 - η)) * composition N s  -- PROVED
theorem classicComposition_atomicData_error_rel (hδ : δ < 1 / 2) … -- η := δ/(1-δ) < 1
theorem massFraction_rel_error (hM : ∀ s, 0 < M s) … -- composition (M ⊙ N̂) vs composition (M ⊙ N)
```

- **Scope.** PURE-MATH for the identities and bounds. REDUCED for the aliasing binding (classic reader at known T).
- **Hypotheses.** Strict positivity, because clr uses the total log. `hδ < 1/2` so that η < 1; the verifier added this.
- **Queue decomposition.**
  1. `clr_mul` and the relative bound: done.
  2. `clr_const`.
  3. Perturbation and scale invariance.
  4. Aliasing.
  5. `classicComposition_atomicData_error_rel`.
  6. Mass-fraction transfer.
  7. Additive-amplification witness.
- **Consumers.** BL-01 (critical), BL-05, A5, BL-36 oxide closure, a relative C6, M8 flags, the W3-C gauge, FT-03's U_i.
- **Verifier notes.** Basis invariance holds only for components that were not zero-replaced (δ_k = 0.65·DL_k replacement).
- **Literature.** Aitchison 1986 and Tognoni 2010 (whitelisted). Gornushkin & Völker 2022 (Sensors 22:7149) and Völker & Gornushkin 2024 (JAAS) were retrieved by the literature auditor; they are off the whitelist, to be cited only after whitelisting.

### FT-08: Closure-free ratio mode vs NeutralityScale, and the exact ΔIP stage-fraction sensitivity
*Verdict: KEEP. Grade A for (a), B for (b)–(c).*

**Statement.**
- (a) Ratio mode is invariant under any common normalization. Closure-normalized and neutrality-normalized readers return identical ratios, so NeutralityScale cannot improve a ratio.
- (b) For neutral lines with two-stage totals, the log-ratio at assumed β has exact derivative (E_a − ⟨E⟩_{I,A}) − (E_b − ⟨E⟩_{I,B}) − f_A κ_A + f_B κ_B. Here κ_X = χ_X + 3/(2β) + ⟨E⟩_{II,X} − ⟨E⟩_{I,X}. When both elements are mostly ionized (f → 1) this reduces to (E_a − E_b) − (χ_A − χ_B) − (⟨E⟩_{II,A} − ⟨E⟩_{II,B}). The |ΔE − ΔIP| rule is therefore exact only when the ion-stage mean excitation energies also match.
- (c) A two-point bound holds on a β-box.

```lean
theorem ratio_mode_normalization_invariant {N : κ → ℝ} {c : ℝ} (hc : c ≠ 0) (hsum : ∑ t, N t ≠ 0)
    (a b : κ) : composition (fun t => c * N t) a / composition (fun t => c * N t) b = N a / N b
theorem neutrality_closure_same_ratio_perU … -- stated on MultiSpecies.lineIntensityPerU (per-species U_s)
theorem ratioEstimate_hasDerivAt {lnUa lnUb lnSa lnSb : ℝ → ℝ} {Ea Eb β ne dUa dUb dSa dSb : ℝ}
    (hne : 0 < ne) (hUa : HasDerivAt lnUa dUa β) (hUb : HasDerivAt lnUb dUb β)
    (hSa : HasDerivAt lnSa dSa β) (hSb : HasDerivAt lnSb dSb β) :
    HasDerivAt (fun b => b * (Ea - Eb) + (lnUa b - lnUb b)
        + Real.log (1 + Real.exp (lnSa b) / ne) - Real.log (1 + Real.exp (lnSb b) / ne))
      ((Ea - Eb) + (dUa - dUb)
        + (Real.exp (lnSa β) / ne) / (1 + Real.exp (lnSa β) / ne) * dSa
        - (Real.exp (lnSb β) / ne) / (1 + Real.exp (lnSb β) / ne) * dSb) β
theorem log_partitionFunction_hasDerivAt_beta :
    HasDerivAt (fun β => Real.log (partitionFunction 1 (1 / β) g E)) (-(meanExcitation 1 (1 / β) g E)) β
theorem log_sahaFactor_hasDerivAt_beta : … -- derivative = -(chi + 3/(2β) + ⟨E⟩_II - ⟨E⟩_I)
theorem ratioEstimate_error_le (hbox : ∀ b ∈ Set.Icc β1 β2, |coef b| ≤ L) :
    |Δ βhat - Δ β| ≤ L * |βhat - β|
```

- **Scope.** PURE-MATH for (a); the verifier retagged it from EXACT. REDUCED for (b)–(c): LTE, one T, two stages, fixed n_e, literal-sum U.
- **Hypotheses.** Derivatives are taken at fixed n_e. On the sb_offset route n_e is coupled to T (about 9–10 per eV), so add a total-derivative variant with `HasDerivAt lnNe`. Ion-line branches flip ρ.
- **Queue decomposition.**
  1. (a) as a one-liner.
  2. Per-U neutrality/closure identity.
  3. Chain rule.
  4. d ln U/dβ, shared with FT-15.
  5. d ln S/dβ (rpow in β).
  6. Matched-ionized algebra.
  7. MVT bound.
  8. Total-derivative variant.
- **Consumers.** BL-48/W3-E, R2-08, R6-08, R11-05, bead 0i64.4.
- **Verifier notes.** (a) is PURE-MATH. It must use `lineIntensityPerU`, or drop the per-species claim. Do not cite NeutralityScale/Abbass until Abbass is whitelisted.
- **Literature.** Aguilera & Aragón 2007, Tognoni 2010 and Griem 1997 (whitelisted).

### FT-09: Energy-affine atomic-data gauge (calibration-layer non-identifiability)
*Verdict: REVISE. Grade A; the headline is nearly done.*

**Statement.** If ln(A_k/A′_k) = α + bE_k, the slope identity is already a corollary of `HeteroAtomicData.olsSlope_aliasing_A`. The genuinely new content is observational equivalence. When b·kB·T < 1, the A′-ordinates equal true ordinates at (T′, N′), with 1/kT′ = 1/kT − b and N′ = N·e^α·U(T′)/U(T). In grouped two-stage data every residual is unchanged, and ln n̂_e shifts by (3/2)ln(T′/T) + b·IP. Identifying b therefore needs an independent n_e or a known composition.

```lean
theorem affine_gA_gauge_of_aliasing … :
    olsSlope E (fun k => Real.log (lineIntensity kB T N Fcal g E A k / (g k * A' k)))
      = -(1 / (kB * T)) + b                                   -- PROVED (8 lines from olsSlope_aliasing_A)
theorem affine_gA_observational_equiv (hkB : 0 < kB) (hT : 0 < T) (hg : ∀ k, 0 < g k)
    (hA : ∀ k, 0 < A k) (hN : 0 < N) (hFcal : 0 < Fcal)
    (haff : ∀ k, A' k = A k * Real.exp (-(α + b * E k))) (hb : b * (kB * T) < 1) :
    ∃ T' N', 0 < T' ∧ 0 < N' ∧ 1 / (kB * T') = 1 / (kB * T) - b ∧
      ∀ k, Real.log (lineIntensity kB T N Fcal g E A k / (g k * A' k))
         = Real.log (lineIntensity kB T' N' Fcal g E A k / (g k * A k))
theorem affine_gA_gauge_grouped … -- feSlope version (FT-04); inter-stage offset invariant; ln n̂_e shift (3/2)·log(T'/T) + b·IP
theorem affine_gauge_composition_leak … -- via FT-15 at T' vs T
```

- **Scope.** EXACT for the single-stage slope and residual identity (`olsSlope_aliasing_A` is already EXACT, Tognoni 2010). REDUCED for the leakage bound.
- **Hypotheses.** `hb` keeps T′ > 0; without it the gauge orbit leaves the physical domain. Across training spectra, require b < min_i 1/(kB·T_i).
- **Queue decomposition.**
  1. Gauge corollary: done.
  2. Observational equivalence.
  3. Grouped/two-stage version.
  4. Leakage bound, after FT-15.
- **Consumers.** BL-47/W3-C, BL-26, C2 campaign, and the overhaul design risk that the layer absorbs misspecification.
- **Verifier revisions.** The slope lemma is not new. `hb` was missing. The multi-stage caveat was misdirected: on sb_offset the offset is gauge-invariant (PLAUSIBLE, derived by hand).
- **Literature.** Tognoni 2010 and Ciucci 1999 (whitelisted).

### FT-10: Information floor for the slope and the log-ratio (heteroscedastic Aitken BLUE)
*Verdict: KEEP. Grade A for the deterministic core, B for the probabilistic parts.*

**Statement.**
- WLS weights minimize Σa²/w over linear unbiased weights, with minimum 1/Σw(E − Ē_w)².
- Under uncorrelated noise with Var ε_k = 1/w_k, WLS is BLUE.
- Unweighted OLS can get worse when a line is added: 2 → 2500.25.
- The common-slope intercept difference d̂ has variance σ²(1/n_a + 1/n_b + (Ē_a − Ē_b)²/(SS_a + SS_b)) and is BLUE.
- This is a BLUE floor. The Cramér–Rao inequality is not proved.

```lean
noncomputable def wMean (w E : ι → ℝ) : ℝ := (∑ k, w k * E k) / ∑ k, w k
noncomputable def wSS (w E : ι → ℝ) : ℝ := ∑ k, w k * (E k - wMean w E) ^ 2
noncomputable def wlsWeight (w E : ι → ℝ) (k : ι) : ℝ := w k * (E k - wMean w E) / wSS w E
theorem wls_min_noiseGain {w E a : ι → ℝ} (hw : ∀ k, 0 < w k) (hSS : 0 < wSS w E)
    (ha0 : ∑ k, a k = 0) (ha1 : ∑ k, a k * E k = 1) :
    ∑ k, wlsWeight w E k ^ 2 / w k = 1 / wSS w E ∧ 1 / wSS w E ≤ ∑ k, a k ^ 2 / w k
theorem wls_is_blue_hetero (hL2 : ∀ k, MemLp (ε k) 2 μ)
    (huncorr : ∀ i j, i ≠ j → covariance (ε i) (ε j) μ = 0) (hvar : ∀ k, variance (ε k) μ = 1 / w k)
    (ha0) (ha1) : variance (fun ω => ∑ k, wlsWeight w E k * (α + β * E k + ε k ω)) μ
                    ≤ variance (Alt.linEstimator a E α β ε) μ
example : ∃ (E σ2 : Fin 3 → ℝ), (∑ k, olsWeight E k ^ 2 * σ2 k)
    > ∑ k : Fin 2, olsWeight (E ∘ Fin.castSucc) k ^ 2 * σ2 (Fin.castSucc k)
theorem interceptDiff_noiseGain … -- Σwa² + Σwb² = 1/na + 1/nb + (mean Ea − mean Eb)²/(SSa + SSb)
theorem interceptDiff_variance_eq … -- σ² · (1/na + 1/nb + (mean Ea − mean Eb)²/(SSa + SSb))
```

- **Scope.** PURE-MATH (statistics). The physics reading is REDUCED: uncorrelated log-intensity noise with known σ_k. d̂ estimates b_a − b_b, so ln(N_a/N_b) also carries a T-dependent ln(U_a/U_b) term.
- **Hypotheses.** w > 0. Uncorrelated noise suffices. A_ki grades stay out of σ, because they are bias.
- **Queue decomposition.**
  1. Weight sums.
  2. Equality part.
  3. Weighted Cauchy–Schwarz inequality.
  4. Fin-3 counterexample.
  5. Per-line-σ generalization of `variance_const_add_weightedNoise`, then heteroscedastic BLUE.
  6. Intercept-difference gain.
  7. Its variance over a Sum index.
  8. d̂ BLUE.
- **Consumers.** BL-33, BL-32, R2-02, R2-03, BL-07/F7 budget, BL-48, R6 pair selection.
- **Verifier notes.** FisherLineSelection already scopes "adding a line never hurts" to homoscedastic noise, so the example turns a documented limit into a theorem. Retag `ols_is_blue`. No new name may contain "crlb".
- **Literature.** Aitken 1935 and Tognoni 2010 (whitelisted). Cramér 1946 and Rao 1945 appear as prose lineage only.

### FT-11: SahaCascade (spec 03 §1) plus an IPD-aware S10
*Verdict: REVISE. Grade B.*

**Statement.**
- S1–S9 as specified in spec 03 §1: stage fractions; strict antitonicity of the liberated charge; a unique positive neutral n_e; Z = 1 reduction; residual enclosure; Saha binding.
- New S10: with IPD-lowered edges S_z(n) = S0_z·e^((z+1)φ(n)), strict antitonicity holds on a box IF (z+1)(φ(n2) − φ(n1)) < ln(n2/n1) for every edge. This is sufficient, not necessary. For Debye–Hückel it binds at the top edge as Z·Δχ/(2kT) < 1, which fixes the stage-III edge at 2Δχ.
- S9 is "EXACT for Saha–Eggert with n_e-independent χ". S10 suffices for its IPD extension; it is not needed.

```lean
noncomputable def sahaStageProduct (S : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1 | z + 1 => sahaStageProduct S z * S z
noncomputable def stageFraction (Z : ℕ) (S : ℕ → ℝ) (ne : ℝ) (z : ℕ) : ℝ :=
  (sahaStageProduct S z / ne ^ z) / ∑ k ∈ Finset.range (Z + 1), sahaStageProduct S k / ne ^ k
noncomputable def speciesCharge (Z : ℕ) (S : ℕ → ℝ) (Ntot ne : ℝ) : ℝ :=
  Ntot * ∑ z ∈ Finset.range (Z + 1), (z : ℝ) * stageFraction Z S ne z
noncomputable def totalIonizedCharge (Z : κ → ℕ) (S : κ → ℕ → ℝ) (Ntot : κ → ℝ) (ne : ℝ) : ℝ :=
  ∑ s, speciesCharge (Z s) (S s) (Ntot s) ne
theorem mean_strictAnti_of_ratio {Z : ℕ} {p q : ℕ → ℝ} (hZ : 1 ≤ Z) (hp : ∀ z ≤ Z, 0 < p z)
    (hq : ∀ z ≤ Z, 0 < q z) (hr : ∀ z < Z, q (z + 1) * p z < p (z + 1) * q z) :
    (∑ z ∈ range (Z + 1), (z : ℝ) * q z) / ∑ z ∈ range (Z + 1), q z
      < (∑ z ∈ range (Z + 1), (z : ℝ) * p z) / ∑ z ∈ range (Z + 1), p z   -- crux; S3 and S10 are instances
theorem speciesCharge_strictAntiOn (hZ : 1 ≤ Z) (hN : 0 < Ntot) (hS : ∀ z < Z, 0 < S z) :
    StrictAntiOn (speciesCharge Z S Ntot) (Set.Ioi 0)
theorem cascade_exists_unique [Nonempty κ] (hZ : ∀ s, 1 ≤ Z s) (hN : ∀ s, 0 < Ntot s)
    (hS : ∀ s, ∀ z < Z s, 0 < S s z) : ∃! ne, 0 < ne ∧ ne = totalIonizedCharge Z S Ntot ne
theorem totalIonizedCharge_Z_one (hne : ne ≠ 0) (hZ : ∀ s, Z s = 1) :
    totalIonizedCharge Z S Ntot ne = multiElementIonized (fun s => S s 0) Ntot ne   -- PROVED
theorem cascade_residual_enclosure [Nonempty κ] (hZ) (hN) (hS) {x nestar : ℝ} (hx : 0 < x)
    (hpos : 0 < nestar) (hstar : nestar = totalIonizedCharge Z S Ntot nestar) :
    |x - nestar| ≤ |x - totalIonizedCharge Z S Ntot x|          -- hpos is load-bearing (ne = 0 is a junk fixed point)
theorem speciesCharge_ipd_strictAntiOn (hZ : 1 ≤ Z) (hN : 0 < Ntot) (hS : ∀ z < Z, 0 < S0 z)
    (hlo : 0 < lo) (hMLR : ∀ n1 ∈ Set.Icc lo hi, ∀ n2 ∈ Set.Icc lo hi, n1 < n2 →
      ∀ z < Z, ((z : ℝ) + 1) * (φ n2 - φ n1) < Real.log (n2 / n1)) :
    StrictAntiOn (fun n => speciesCharge Z (fun z => S0 z * Real.exp (((z : ℝ) + 1) * φ n)) Ntot n)
      (Set.Icc lo hi)                                            -- sufficient, not necessary
```

- **Scope.** S1–S8 PURE-MATH. S9 EXACT for n_e-independent χ. S10 REDUCED: Debye–Hückel-type lowering, frozen level lists, ion-charge dependence of λ_D ignored.
- **Hypotheses.** `[Nonempty κ]` (for empty κ the map is 0). `hpos` for S8. S9 needs dependent level types ι : ℕ → Type, because padding with g = 0 breaks `partitionFunction_pos`. Fix that design choice in the pre-registration.
- **Queue decomposition.** S1, S2, S4, S7 (done), `mean_strictAnti_of_ratio` (split into a double-sum identity and a termwise sign), S3, S5 by the IVT, S6, S8, S9 binding, S10 via the generic lemma.
- **Consumers.** BL-42 (2Δχ stage-III edge), R1-07, R1-09, R1-03, BL-36 stage ≥ 3 guard, BL-44, spec Phase 1 (P0).
- **Verifier revisions.**
  - The S8 sketch was false without `hpos`; a Lean witness exists.
  - The S10 "iff" was false; there is a numeric counterexample.
  - "S9 needs S10" overclaimed.
  - Novelty is limited to S10 and the S9 retag. S1–S9 are already specified.
  - The slate's "elaborates" header was only partly true, since S8 was never type-checked.
- **Literature.** Griem 1997 (whitelisted). The (z+1) edge scaling is cited only via BL-42.

### FT-12: Statistical slope certificate C4σ, and the exact Gaussian law of β̂
*Verdict: REVISE. Grade A for (a), B for (b).*

**Statement.**
- (a) With independent sub-Gaussian log-ordinate noises and per-line proxies c_k: P(|β̂ − β| ≥ δ) ≤ 2exp(−δ²/(2Σ w_k² c_k)). `slopeTailCert` ≤ α then implies the slope is within τ with probability at least 1 − α.
- (b) With independent Gaussian noises N(0, σ_k²): μ.map β̂ = gaussianReal(β, Σ w_k² σ_k²). This is exact only for known σ_k; with an estimated σ, Student t applies.
- This reopens the frontier-11 refusal, which rested on a false absence claim.

```lean
def slopeTailCert (E : ι → ℝ) (c : ι → NNReal) (tauBeta alpha : ℝ) : Prop :=
  2 * Real.exp (-(tauBeta ^ 2) / (2 * ∑ k, olsWeight E k ^ 2 * (c k : ℝ))) ≤ alpha
theorem olsSlope_subGaussian_tail_hetero [Nonempty ι] (E : ι → ℝ) (α β : ℝ) (ε : ι → Ω → ℝ)
    {c : ι → NNReal} {δ : ℝ} (hvar : 0 < ∑ k, (E k - mean E) ^ 2) (hδ : 0 ≤ δ)
    (hindep : iIndepFun ε μ) (hsubG : ∀ k, HasSubgaussianMGF (ε k) (c k) μ) :
    μ.real {ω | δ ≤ |Alt.betaHat E α β ε ω - β|}
      ≤ 2 * Real.exp (-(δ ^ 2) / (2 * ∑ k, olsWeight E k ^ 2 * (c k : ℝ)))
theorem slopeTail_certificate_sound (hcert : slopeTailCert E c tauBeta alpha) … :
    μ.real {ω | tauBeta ≤ |Alt.betaHat E α β ε ω - β|} ≤ alpha
theorem weightedNoise_map_eq … -- PROVED (GLaw.lean)
theorem betaHat_map_eq_gaussianReal [Nonempty ι] (E) (α β) (ε) (σ : ι → NNReal)
    (hvar : 0 < ∑ k, (E k - mean E) ^ 2) (hlaw : ∀ k, HasLaw (ε k) (gaussianReal 0 (σ k ^ 2)) μ)
    (hind : iIndepFun ε μ) :
    μ.map (Alt.betaHat E α β ε) = gaussianReal β (∑ k, ⟨olsWeight E k ^ 2, sq_nonneg _⟩ * σ k ^ 2)
```

- **Scope.** PURE-MATH. The binding c_k ≈ 1/SNR_k² is APPROXIMATION (the delta method on log I), not REDUCED.
- **Hypotheses.** `iIndepFun` is required. The `hc` hypothesis was dropped: when the proxy sum is 0, Lean's −δ²/0 = 0 gives the trivial bound 2. The gate's α must include a union bound over certificates.
- **Queue decomposition.**
  1. Heteroscedastic tail: copy the existing proof with a per-summand c.
  2. Certificate soundness.
  3. Temperature corollary via `temp_slope_event_subset`.
  4. Weighted-noise law: done.
  5. Heteroscedastic β̂ law.
  6. Exact coverage.
  7. Float mirror.
- **Consumers.** certificate_gate C4 HARD, G2 TS-08, BL-35, BL-36 coverage.
- **Verifier revisions.** Drop `hc`. Make (b) heteroscedastic. Tag the binding APPROXIMATION. The interval is exact only for known σ_k. "Gauss–Markov suffices" needs joint Gaussianity.

### FT-13: Profile escape factor ≥ slab SA; ½-Lipschitz log escape; τ-error propagation
*Verdict: REVISE. Grade A.*

**Statement.**
- (a) For 0 ≤ ψ ≤ 1 with ∫ψ < ∞: equivWidth ψ τ0 ≥ SA(τ0)·τ0·∫ψ. Dividing by the slab SA over-corrects when τ0 is the physical line-centre depth. Gaussian values: 0.447 vs 0.317 at τ0 = 3, and 0.187 vs 0.100 at τ0 = 10 (reproduced).
- (b) ln SA is ½-Lipschitz on [0, ∞).
- (c) The profile-generic escape factor is also ½-Lipschitz in log. So |τ̂ − τ| ≤ Δ implies a log-intensity error ≤ Δ/2. Δ is an assumed input (C14-pattern REFUSAL), not a certificate.

```lean
lemma slab_chord_le (hτ : 0 ≤ τ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 - Real.exp (-τ)) * t ≤ 1 - Real.exp (-(τ * t))                    -- PROVED
theorem escape_ge_slab {ψ : ℝ → ℝ} {τ0 : ℝ} (hψ0 : 0 ≤ ψ) (hψ1 : ∀ x, ψ x ≤ 1) (hint : Integrable ψ)
    (hτ : 0 < τ0) : selfAbsorptionFactor τ0 * (τ0 * ∫ x, ψ x) ≤ equivWidth ψ τ0
theorem log_selfAbsorptionFactor_lipschitz {τ τ' : ℝ} (hτ : 0 ≤ τ) (hτ' : 0 ≤ τ') :
    |Real.log (selfAbsorptionFactor τ) - Real.log (selfAbsorptionFactor τ')| ≤ |τ - τ'| / 2
noncomputable def escapeFactor (ψ : ℝ → ℝ) (τ : ℝ) : ℝ := equivWidth ψ τ / (τ * ∫ x, ψ x)
theorem log_escapeFactor_lipschitz (hψ0 : 0 ≤ ψ) (hψ1 : ∀ x, ψ x ≤ 1) (hint : Integrable ψ)
    (hpos : 0 < ∫ x, ψ x) (hτ : 0 < τ) (hτ' : 0 < τ') :
    |Real.log (escapeFactor ψ τ) - Real.log (escapeFactor ψ τ')| ≤ |τ - τ'| / 2
theorem tauError_propagation (hI : 0 < Ithin) (hmeas : Imeas = Ithin * escapeFactor ψ τ)
    (hΔ : |τhat - τ| ≤ Δ) … : |Real.log (Imeas / escapeFactor ψ τhat) - Real.log Ithin| ≤ Δ / 2
    -- REFUSAL: Δ is assumed, not measured (C14 pattern)
```

- **Scope.** PURE-MATH for (a) and (b). REDUCED for (c): known profile shape, homogeneous slab. Retag `knownTau_certificate_sound` PURE-MATH.
- **Hypotheses.** ψ ≤ 1 fixes τ0 as the line-centre depth. The `hpos` condition excludes degenerate profiles.
- **Queue decomposition.**
  1. Chord lemma: done.
  2. `escape_ge_slab` via `integral_mono`.
  3. The real inequality 1/τ − 1/(e^τ − 1) ∈ (0, ½).
  4. HasDerivAt of ln SA.
  5. (b) by MVT plus continuity at 0.
  6. (c) pointwise ψ·SA(τψ) plus `integral_mono`.
  7. Propagation.
- **Consumers.** C12 replacement (RF-04), BL-44, BL-45, W3-B gate, R3-05, R1-04 NR-5.
- **Verifier revisions.** `robustTauCert` was as vacuous as C12 and is replaced by an error-propagation lemma with a REFUSAL note. (c) no longer puts the slab SA on the measured side.
- **Literature.** Gornushkin 1999 and Bulajic 2002 (whitelisted).

### FT-14: Physically scaled self-absorption
*Verdict: REVISE. Grade A for (i), B otherwise.*

**Statement.**
- (i) Kirchhoff: with the Boltzmann ratio and the Einstein relation, ε/κ = B0/(e^x − 1), independent of N, U, A and L.
- (ii) The emergent integrated intensity S·W_ψ(κL) is strictly increasing in L and N when ∫ψ > 0.
- (iii) The peak τ falls as the Stark width rises.
- (iv) The per-line τ ratio, with guards, keeps the stimulated-emission factor (1 − e^(−x_i)) per line. This is about 0.92 per line in the visible and about 0.79 at hν/kT ≈ 1.55.
- (v) Transfer before instrument: equivWidth φ τ ≤ equivWidth (R⋆φ) τ, by Jensen.

```lean
noncomputable def lineOpacity (κ0 nl x : ℝ) : ℝ := κ0 * nl * (1 - Real.exp (-x))
noncomputable def lineEmissivity (ε0 nu : ℝ) : ℝ := ε0 * nu
theorem source_eq_planck {κ0 ε0 B0 nl nu x gu gl : ℝ} (hx : 0 < x) (hκ : 0 < κ0) (hnl : 0 < nl)
    (hpop : nu / nl = gu / gl * Real.exp (-x)) (hein : ε0 * gu / gl = κ0 * B0) :
    lineEmissivity ε0 nu / lineOpacity κ0 nl x = B0 / (Real.exp x - 1)      -- PROVED
theorem slabIntegrated_strictMono_L (hS : 0 < S) (hκ : 0 < κ) (hψ0 : 0 ≤ ψ) (hint : Integrable ψ)
    (hpos : 0 < ∫ x, ψ x) : StrictMonoOn (fun L => S * equivWidth ψ (κ * L)) (Set.Ioi 0)
theorem perLine_tauRatio [Nonempty ι] (hN : N ≠ 0) (hell : ell ≠ 0) (hg : ∀ k, 0 < g k)
    (hσ2 : σ02 ≠ 0) :
    opticalDepth kB T N σ01 ell g E l1 / opticalDepth kB T N σ02 ell g E l2
      = σ01 * g l1 * boltzmannFactor kB T (E l1) / (σ02 * g l2 * boltzmannFactor kB T (E l2))
-- model identity: σ0i ∝ λi² · g_ui · A_i · φi(0) · (1 − e^{−x_i}) / g_li   (λ/ν convention pinned in pre-registration)
theorem equivWidth_le_conv {R φ : ℝ → ℝ} {τ : ℝ} (hR : ∀ x, 0 ≤ R x) (hR1 : ∫ x, R x = 1)
    (hRint : Integrable R) (hφ : 0 ≤ φ) (hint : Integrable φ) (hτ : 0 ≤ τ) :
    equivWidth φ τ ≤ equivWidth (fun x => ∫ y, R (x - y) * φ y) τ
```

- **Scope.** (i) EXACT given the hypotheses; the physics sits in `hein`. (ii) and (v) PURE-MATH, with a REDUCED physics reading. (iii) and (iv) REDUCED.
- **Hypotheses.** Keep κ0, ε0 and B0 abstract until the λ²/8π factor and the ν/λ convention are verified from Griem 1997, which was not opened this session.
- **Queue decomposition.**
  1. (i): done.
  2. ℓ-free source; fixes `lteSourceStrength` (RF-02).
  3. Strict monotonicity of equivWidth in τ.
  4. L- and N-monotonicity.
  5. Guarded τ ratio plus the model identity.
  6. Pointwise Jensen via `ConcaveOn.le_map_integral`.
  7. Fubini integration.
  8. Strict version.
- **Consumers.** BL-44, R1-04, R3-05, BL-45 acceptance identity, M5/Tier 1b replacement, the spec 03 §3 K-series deferral.
- **Verifier revisions.**
  - (i) is regraded to A.
  - (iv) omitted the stimulated factor and was internally inconsistent.
  - The unguarded `perLine_tauRatio` is false (N = 0 witness) and was never elaborated.
  - The Stark half credits existing N-monotonicity.
- **Literature.** Griem 1997, Gornushkin 1999 and Griem 1974 (whitelisted).

### FT-15: Log-derivative Lipschitz constants for U and S (mean excitation energy)
*Verdict: KEEP. Grade B.*

**Statement.**
- d ln U/dβ = −⟨E⟩_β, and d⟨E⟩/dT = Var(E)/(kT²) ≥ 0.
- On [Tmin, Tmax]: |ln U(T1) − ln U(T2)| ≤ ⟨E⟩_{Tmax}·|1/kT1 − 1/kT2|.
- Under hEχ: |ln S(T1) − ln S(T2)| ≤ (3/(2Tmin) + (χ + ⟨E⟩_II(Tmax))/(kTmin²))·|T1 − T2|.
- Measured: 2.76–4.34× the true sensitivity, against 7.7e5–9.7e7× today. The Fe U channel drops from 83.1 to 0.0402 (both re-run).

```lean
noncomputable def meanExcitation (kB T : ℝ) (g E : ι → ℝ) : ℝ :=
  (∑ k, g k * E k * boltzmannFactor kB T (E k)) / partitionFunction kB T g E
theorem meanExcitation_monotoneOn_temp [Nonempty ι] (hkB : 0 < kB) (hg : ∀ k, 0 < g k) :
    MonotoneOn (fun T => meanExcitation kB T g E) (Set.Ioi 0)
theorem log_partitionFunction_lipschitz [Nonempty ι] (hkB : 0 < kB) (hTmin : 0 < Tmin)
    (hT1 : Tmin ≤ T1) (hT1M : T1 ≤ Tmax) (hT2 : Tmin ≤ T2) (hT2M : T2 ≤ Tmax)
    (hg : ∀ k, 0 < g k) (hE : ∀ k, 0 ≤ E k) :
    |Real.log (partitionFunction kB T1 g E) - Real.log (partitionFunction kB T2 g E)|
      ≤ meanExcitation kB Tmax g E * |1 / (kB * T1) - 1 / (kB * T2)|
theorem log_sahaFactor_lipschitz … (hEχ : ∀ k, EZ k ≤ chi) :
    |Real.log (sahaFactor kB T1 me h chi gZ EZ gZ1 EZ1) - Real.log (sahaFactor kB T2 me h chi gZ EZ gZ1 EZ1)|
      ≤ (3 / (2 * Tmin) + (chi + meanExcitation kB Tmax gZ1 EZ1) / (kB * Tmin ^ 2)) * |T1 - T2|
theorem tempResponseErrorBoundOfGap_tight … -- NEW; existing theorems left untouched (RF-18)
```

- **Scope.** PURE-MATH. REDUCED when bound to data, which requires the literal-sum U over a truncated list (FT-05).
- **Hypotheses.** hEχ, read as a cutoff obligation, is sufficient but not necessary. It gives χ − ⟨E⟩_I ≥ 0.
- **Queue decomposition.** HasDerivAt of U in β; d ln U = −⟨E⟩; d⟨E⟩ = −Var; Var ≥ 0 by Cauchy–Schwarz; monotonicity; ln U Lipschitz; thermal-bracket derivative; ln S Lipschitz; `_tight` substitution. Steps 1–4 are the first batch. A max-E variant (derivative-free, 5.8–9.8× tight) is milestone 0.
- **Consumers.** EvaluatorSoundness envelope (RF-12), BL-07/F7, the certificate_gate HARD set, FT-08, FT-09, FT-01 physical gains.
- **Verifier.** Keep. Optionally evaluate ⟨E⟩ at max(T1, T2).

### FT-16: Extraction under profile misspecification, and the Varah ℓ∞ gain (spec K8)
*Verdict: KEEP. Grade A.*

**Statement.**
- Î − I = (KᵀK)⁻¹Kᵀ(K_true − K)I + (KᵀK)⁻¹Kᵀη exactly. The bias vanishes for the oracle extractor, which is built at the true state (R3-01).
- If KᵀK is strictly row-diagonally dominant with margin δ, then ‖Î − I‖∞ ≤ ‖Kᵀ((K_true − K)I + η)‖∞/δ.
- The numerator is an assumed input. Only the margin δ is runtime-checkable (C16′ ⇒ C16).

```lean
theorem extractor_bias_identity (K Kt : Matrix P L ℝ) (I : L → ℝ) (η : P → ℝ)
    (hdet : IsUnit (Kᵀ * K).det) :
    ((Kᵀ * K)⁻¹ * Kᵀ).mulVec (Kt.mulVec I + η) - I
      = ((Kᵀ * K)⁻¹ * Kᵀ).mulVec ((Kt - K).mulVec I) + ((Kᵀ * K)⁻¹ * Kᵀ).mulVec η   -- PROVED
theorem linfty_le_of_rowDiagDominant [Nonempty L] (M : Matrix L L ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hdom : ∀ k, δ + ∑ j ∈ univ.erase k, |M k j| ≤ |M k k|) (x : L → ℝ) (i : L) :
    |x i| ≤ (univ.sup' univ_nonempty fun k => |(M.mulVec x) k|) / δ            -- PROVED
theorem kernelLS_error_linfty (hdom : …)
    (hnormal : (Kᵀ * K).mulVec Ihat = Kᵀ.mulVec (Kt.mulVec I + η)) :
    ∀ l, |Ihat l - I l| ≤ (univ.sup' _ fun k => |(Kᵀ.mulVec ((Kt - K).mulVec I + η)) k|) / δ
def kernelMarginCert (K : Matrix P L ℝ) (δ : ℝ) : Prop :=
  0 < δ ∧ ∀ k, δ + ∑ j ∈ univ.erase k, |(Kᵀ * K) k j| ≤ |(Kᵀ * K) k k|
-- kernel_to_ordinate: corollary of Analysis.abs_log_ratio_le (no restatement)
```

- **Scope.** PURE-MATH. REDUCED physics: optically thin, additive lines, K fixed per step.
- **Queue decomposition.** Bias identity and Varah: done. Then the error bound, margin soundness (via `det_ne_zero_of_sum_row_lt_diag`), the ordinate corollary, and composition with `noise_to_composition` after FT-15.
- **Consumers.** BL-28, BL-27, BL-29, BL-31, R3-01, the spec Phase 6 entry (RF-26), BL-49.
- **Literature.** Varah, Linear Algebra Appl. 11 (1975) 3–5, retrieved by web search and not whitelisted; it goes through citation-integrity first. Cremers & Radziemski 2013 and Griem 1974 (whitelisted). The result depends on SpectrometerForward (spec 03 §3) landing.

### FT-17: Newton's method on multi-element charge neutrality (reopens Frontier 03 M8)
*Verdict: KEEP. Grade A.*

**Statement.**
- N x − r = −(x − r)²·Σ a_s/((x + S_s)²(r + S_s))/f′(x), with a_s = Ntot_s·S_s.
- Hence, from any x ≥ 0: N x ≤ r ≤ G(N x), a two-sided bracket after one step.
- |N x − r| ≤ (Σ Ntot_s/S_s²)(x − r)², and the iterates rise monotonically to r.
- The refusal claiming convexity infrastructure was absent is false (`convexOn_zpow` exists), and the identity route needs no convexity anyway.

```lean
noncomputable def neutralityNewton (S Ntot : ι → ℝ) (x : ℝ) : ℝ :=
  x - (x - multiElementIonized S Ntot x) / (1 + ∑ s, Ntot s * S s / (x + S s) ^ 2)
theorem neutralityNewton_error_eq … -- PROVED
theorem neutralityNewton_le_root … -- PROVED (needs only 0 ≤ Ntot)
theorem neutralityNewton_quadratic … : |neutralityNewton S Ntot x - r| ≤ (∑ s, Ntot s / S s ^ 2) * (x - r) ^ 2  -- PROVED
theorem neutralityNewton_enclosure [Nonempty ι] (hS : ∀ s, 0 < S s) (hN : ∀ s, 0 ≤ Ntot s) (hx : 0 ≤ x)
    (hr : 0 < r) (hfix : r = multiElementIonized S Ntot r) :
    neutralityNewton S Ntot x ≤ r ∧ r ≤ multiElementIonized S Ntot (neutralityNewton S Ntot x)
theorem neutralityNewton_tendsto [Nonempty ι] (hS) (hN) (hx0 : 0 ≤ x0) (hfix) :
    Tendsto (fun n => (neutralityNewton S Ntot)^[n] x0) atTop (𝓝 r)
```

- **Scope.** PURE-MATH numerics. REDUCED physics: single T, LTE, singly ionized. Z-stage cascades are not covered.
- **Queue decomposition.** Identity, ≤ root and quadratic bound: done. Then the closed form with N x > 0, r ≤ G(N x), x ≤ r ⇒ x ≤ N x, the linear rate, convergence, and a certificate wrapper that eliminates r.
- **Consumers.** The forward closure (anderson_solver.py, saha_boltzmann.py), BL-44, the spec S8/C15 template. This is not the inverse loop (PS-12).
- **Verifier.** Keep. Weaken `hN` to `0 ≤ Ntot` where only the identity is used. Tightness of the quadratic constant matters only near the root.

### FT-18: Sign of the self-absorption temperature bias
*Verdict: REVISE. Grade A.*

**Statement.** If τ is antitone in E over strictly increasing energy pairs, the OLS slope of the self-absorbed plot is at least the thin slope, so T is overestimated. A two-line witness shows the opposite ordering reverses the sign. Which sign occurs is fixed by the τ-vs-E_upper ordering. This does not settle the empirical literature dispute.

```lean
theorem olsSlope_selfAbsorbed_ge [Nonempty ι] {E y τ : ι → ℝ} (hτ : ∀ k, 0 < τ k)
    (hanti : ∀ i j, E i < E j → τ j ≤ τ i) :
    olsSlope E y ≤ olsSlope E (fun k => y k + Real.log (selfAbsorptionFactor (τ k)))
theorem apparentTemp_overestimate {kB T s : ℝ} (hkB : 0 < kB) (hT : 0 < T)
    (hthin : olsSlope E y = -(1 / (kB * T))) (hle : olsSlope E y ≤ s) (hneg : s < 0) :
    T ≤ -(1 / (kB * s))
example : ∃ (E y τ : Fin 2 → ℝ), (∀ k, 0 < τ k) ∧ StrictMono τ ∧ StrictMono E ∧
    olsSlope E (fun k => y k + Real.log (selfAbsorptionFactor (τ k))) < olsSlope E y
```

- **Scope.** REDUCED: flat-profile SA, unweighted OLS, single T. It generalizes to FT-13's escape factor.
- **Queue decomposition.** Make the private `olsSlope_add` public (Alt/OLSAtomicDataPerturbation.lean:109) rather than re-proving it; monovariance; centred covariance ≥ 0; the main theorem; the witness; the apparent-temperature lemma.
- **Consumers.** BL-45, R11-03, R3 resonance-line selection, NR-5.
- **Verifier revisions.**
  - `hanti` in its non-strict form was too strong for multiplets.
  - `apparentTemp_overestimate` was false without `hle`.
  - "Settles the literature" overclaimed.
  - `hvar` is removable.
- **Literature.** Gornushkin 1999 and Bulajic 2002 (whitelisted). John & Anoop 2023, Fayyaz 2024 and Safi 2019 were retrieved by the literature auditor and are off the whitelist. The John & Anoop abstract states no slope sign.

### FT-19: Ion apparent temperature ≥ neutral apparent temperature in line-of-sight mixtures
*Verdict: REVISE. Grade A−.*

**Statement.**
- With uniform n_e, the ion zone weight is the neutral zone weight times ionReweight(T) = 2θ(T)^{3/2}e^(−χ/kT)/n_e. The partition functions cancel.
- ionReweight is strictly increasing in T for χ ≥ 0, so no hEχ is needed.
- A reweighting antitone in b = 1/kT lowers the tilted mean, and the tilted mean is antitone in the anchor.
- Given the anchor condition, β_ion ≤ β_neutral. This is consistent with Aguilera & Aragón's measured 9890 K (Fe I) and 11400 K (Fe II). It does not prove them: their plasma has non-uniform n_e and they used multi-line plots.

```lean
noncomputable def ionReweight (kB me h chi ne T : ℝ) : ℝ :=
  2 * thermalBracket kB T me h ^ (3 / 2 : ℝ) * Real.exp (-chi / (kB * T)) / ne
theorem ion_zoneWeight_eq (hNII : …) :
    zoneWeight kB Fcal T NII gZ1 EZ1 z = zoneWeight kB Fcal T NI gZ EZ z * ionReweight kB me h chi ne (T z)  -- PROVED
theorem ionReweight_strictMonoOn (hkB : 0 < kB) (hme : 0 < me) (hh : 0 < h) (hchi : 0 ≤ chi)
    (hne : 0 < ne) : StrictMonoOn (ionReweight kB me h chi ne) (Set.Ioi 0)
theorem tiltMean_antitone_anchor (hw : ∀ z, 0 < w z) : … -- PROVED (from tiltMean_le_pairSlope, pairSlope_le_tiltMean)
theorem tiltMean_reweight_le [Nonempty ζ] {w b ρ : ζ → ℝ} (hw : ∀ z, 0 < w z) (hρ : ∀ z, 0 < ρ z)
    (hanti : ∀ i j, b i ≤ b j → ρ j ≤ ρ i) (a : ℝ) : tiltMean (fun z => w z * ρ z) b a ≤ tiltMean w b a
theorem mixed_ion_apparentBeta_le_neutral (hanchor : EupNeutral ≤ EloIon) : … -- ion two-line β ≤ neutral two-line β
```

- **Scope.** REDUCED: uniform n_e, two-line pairs, optically thin. The reweighting lemma is PURE-MATH.
- **Queue decomposition.** Weighted Chebyshev double sum; reweight lemma; anchor monotonicity (done); ionReweight monotonicity; assembly.
- **Consumers.** The pooled SB-graph slope (R9-02), G2 TS-01, M8 flags, the Cσ route.
- **Verifier revisions.** The ρ = S/n_e reweighting was mis-specified: it should cancel U_II/U_I. hEχ was unnecessary. The paper is "consistent with", not proved.
- **Literature.** Aguilera & Aragón 2007 SAB (whitelisted). The measurement itself is Aguilera & Aragón 2007, J. Phys.: Conf. Ser. 59:210 (OSTI 20916907), retrieved this session; it needs its own whitelist string.

### FT-20: Pair curve-of-growth identifiability boundary
*Verdict: REVISE. Grade B.*

**Statement.**
- (a) If the COG log-slope τW′/W is strictly decreasing, the pair ratio is strictly antitone for every r > 1. This is the sufficient direction only.
- (b) Explicit counterexample: the two-step profile 1_[0,1] + η·1_[0,M] with η = 1/100, M = 20, r = 2 gives R(1) = 1.5077, R(3) = 1.3905 and R(10) = 1.5826. Turning points sit at n ≈ 2.42 (1.382) and 20.18 (1.6345). The ratio is not injective.
- (c) Pre-registered, numerical only. For the Voigt ratio with r = 2 (σ the Gaussian standard deviation, γ the Lorentzian HWHM), the interior minimum lies inside smaller-line τ0 ∈ [0.1, 15] for γ/σ ≳ 0.03–0.1, with a second-branch band under 1%. At γ/σ = 0.01 the minimum sits at τ0 ≈ 35–37, outside the gate.

```lean
noncomputable def stepProfile (η M : ℝ) : ℝ → ℝ := fun x =>
  Set.indicator (Set.Icc 0 1) (fun _ => 1) x + η * Set.indicator (Set.Icc 0 M) (fun _ => 1) x
theorem equivWidth_stepProfile {η M τ : ℝ} (hη : 0 ≤ η) (hM : 1 ≤ M) :
    equivWidth (stepProfile η M) τ
      = (1 - Real.exp (-(τ * (1 + η)))) + (M - 1) * (1 - Real.exp (-(τ * η)))
theorem stepProfile_pairRatio_not_injOn :
    ¬ Set.InjOn (fun n => equivWidth (stepProfile (1 / 100) 20) (2 * n)
                          / equivWidth (stepProfile (1 / 100) 20) n) (Set.Ioi 0)
theorem pairRatio_strictAntiOn_of_logSlope … -- sufficient direction; grade C, later
```

- **Scope.** PURE-MATH counterexample. Retag only `cogRatio_injOn` and `saDistinct_certificate_sound` from EXACT to REDUCED. `doubletRatio_injOn` is already REDUCED.
- **Queue decomposition.** Closed form via `integral_indicator`; three enclosed values (12 exp enclosures); continuity; "continuous and injective ⇒ strictly monotone" contradiction; log-slope criterion later.
- **Consumers.** BL-45/W3-B gate, R3-05, R3-09 (Al doublet, r ≈ 1.97), C13.
- **Verifier revisions.** The Voigt claim was false at γ/σ = 0.01 inside the gate. The practical ambiguity is real but narrow. The retag list was partly stale.

---

## 6. Recommended sequencing

**Step 0: gates before anything else.**
1. **RF-07.** Until leanchecker replay and olean-based axiom and type probes exist, count no queue result as "verified". Re-verify F02 afterwards.
2. **RF-09.** ScopeCheck must resolve Alt and Classic before any retag in RF-11, RF-15 or RF-29.
3. **RF-08 and RF-25** as one cross-repo pair: regenerate the oracle at non-unit constants, stamp only the sha256 of Generate.lean, resync the single vendored companion copy, fix `test_forward_saha_conformance` (T_e_eV ≠ 1), and add the IPD golden as `xfail(strict=True)`.

**Step 1: P0 prose and tag batch.** These carry no proof risk. Run `gen-docs.sh` and scope-check at the end.
- RF-01, RF-03 (1)–(4), RF-04 (retag and pins; the lemma follows FT-13), RF-05 (re-export only), RF-06, RF-10, RF-11, RF-12, RF-13 (via citation-integrity, with the CI fatal-OFF-WHITELIST change in the same PR), RF-14, RF-15a.

**Owner decisions to record before the dependent work.**
- EXACT semantics (RF-27): relative to the stated model, or faithful to the physics.
- C8/C11 numbering (RF-20): back-fill or C15+.
- Debye–Hückel coefficient model (FT-02, FT-19).
- Level-cutoff policy for BL-41 (FT-05): n_e-independent, frozen inner loop, or continuous weights.
- λ/ν and λ²/8π conventions (FT-14), after opening Griem 1997.

**Queue now** (grade A, statements elaborate, several lemmas proved; only after RF-07):
- FT-04 items 1–8, 10, 11.
- FT-07 items 2–7.
- FT-02 items 2–7.
- FT-03 items 1–6.
- FT-06 items 2–4.
- FT-17 remaining steps.
- FT-16 items 3–5.
- FT-15 items 1–4 (first batch).
- FT-13 (a) and (b).
- FT-09 steps 2–3.
- FT-10 items 1–4 and 6.
- FT-12 items 1–3.
- FT-05 items 2–7.
- FT-18.
- FT-01 pure-mathematics items (tendsto_iff, `tDamped_mobius_converges`, weights ⇒, `jury_two` as two targets, contracts, repelling, `single_group_gain`).

Give dominated-convergence and measure targets (FT-13(a) integration step, FT-14(v), FT-20 closed form, FT-12(b)) one lemma per target. The F07 failure at 311k tokens is the relevant failure profile.

**Statement audit and pre-registration before queuing:**
- FT-01 step 10 (the physics binding; piecewise map, weights, damping in T).
- FT-11 (dependent level types for S9, `hpos`, S10 as sufficient).
- FT-14 (constants and conventions).
- FT-19 (ionReweight, anchor condition).
- FT-20 (c) (restated Voigt claim, σ and γ conventions).
- FT-12 (b) and the APPROXIMATION binding.
- FT-08 (b) (stage sign conventions, total derivative).
- FT-09 grouped two-stage version.
- FT-05 (iv) precise form.
- FT-03 group weighting matched to `objective-and-splits.md:11`.

**Refactor order.**
1. RF-09.
2. RF-16 with FT-04.
3. RF-17 with FT-01.
4. RF-18 and RF-19 (FT-15, FT-02, FT-05, FT-11 S10).
5. RF-20, RF-22, RF-23, RF-21.
6. RF-24 (after RF-16, RF-17 and RF-18).
7. P2: RF-15c, RF-26, RF-27 after the owner decision, RF-28 staged, RF-29 after RF-09.
8. RF-30.

**Hand to the companion, by owning workstream.**
- **W2-A (A5 trust stack).**
  - Evaluate C1–C3 as within-element designs on the kept mask, or mark them not applicable.
  - `_resolve_ne` keeps both n_e sources.
  - Convert span to SS_E with R²/2 (error_budget.py, strict.py).
  - Stop on the residual enclosure.
  - Mark `validity.py`'s Saha-consistency criterion `not_evaluated` on sb_offset, citing FT-03(e).
- **F2 / W2-S2 (certificate_gate.py; resolve the double ownership).**
  - Take C12 out of HARD.
  - Label C4's ε as 1σ, or replace it with C4σ.
  - Keep C1–C3 out of HARD until C1g/C2g are mirrored.
- **W2-S3 / W3-A.**
  - Adopt the A11 amendment (per-stage (χ_eff, level list) pair contract).
  - Remove the exact-provider T clamp.
  - Use the 2Δχ stage-III edge.
  - Keep IPD/cutoff forward and inverse on one PopulationContext.
- **W2-A / BL-36.** The oxide closure returns a simplex plus a reporting transform. Until then skip `require_simplex` in oxide mode.
- **Routing doc and M4 Tier 2.** csigma.py has no Lean twin. DifferentialEstimator is not opc.py's twin.
- **W3-B.** Rename the C13 inputs as opacities. The τ ratio keeps the exp(−ΔE_l/kT) and (1 − e^(−hν/kT)) factors.
- **F7.** Compute the closed-form g in `ded_fixed_point_gain.py`. Do not cite `crlb_*` as Cramér–Rao.

---

## 7. Appendix

**Killed proposals.** No proposal was killed outright: all 20 FT and 30 RF items survived, with 7 FT and 16 RF items kept as stated. The following sub-claims were refuted or narrowed by verifiers and are dropped:

| Item | Dropped sub-claim | Reason |
|---|---|---|
| FT-01 | (a) as a statement about `iterative.py`; the global window "all starts converge iff 1−2/λ<g<1" for T-damping | The pipeline damps T. At g = −1 the T-iterate goes negative. |
| FT-01 | The Jacobian as generally valid; `single_group_gain` without 0 < b | Valid only when ∂n_e,new/∂n_e,prev = 0; the gain lemma is false for B < −W. |
| FT-02 | `ipdOff_composition_invariant` via composition_smul_invariant | Wrong mechanism; replaced by `sahaRatio_ipd_gauge`. |
| FT-02 | `ipdInverse_twoPoint_sensitivity` as sketched; "M4 sentence is a live overclaim"; q³ ≈ 3e-5 | Two Lean counterexamples (a1 < 0; b < 0); the sentence is incomplete, not false; q³ = 3.7e-5. |
| FT-03 | One policy carrying both (a)/(b) and (c); (e) tagged EXACT | Contradictory on the ambiguous set (Lean witnesses); (e) is PURE-MATH. |
| FT-05 | (iii) as ¬∀T; (iv) literal wording; (v) "only continuous policies" | Too weak; literally false; overclaim. |
| FT-06 | "Soundness needs both diagnostics"; elided `stark_bracket_rho`; novelty of the Stark half | One lower bracket suffices; `starkOpacityLteCert` is prior art. |
| FT-09 | The slope identity as new; "weak Saha-T information" on sb_offset | Already `olsSlope_aliasing_A` plus `ols_recovers_line`; the offset is gauge-invariant (PLAUSIBLE). |
| FT-11 | S8 without `0 < nestar`; S10 "iff"; "S9 needs S10"; S1–S9 as novel | Junk fixed point at n_e = 0 (Lean witness); numeric counterexample; S10 only suffices; already in spec 03 §1. |
| FT-12 | `hc`; homoscedastic (b); REDUCED binding; "exact interval" with estimated σ | Unnecessary; the headline is per-line; delta-method APPROXIMATION; needs Student t. |
| FT-13 | `robustTauCert` as a certificate; slab SA on the measured side in (c) | As vacuous as C12; contradicts (a). |
| FT-14 | Unguarded `perLine_tauRatio`; (iv) without the stimulated factor; (i) grade B | False at N = 0 (Lean witness); internally inconsistent; (i) is grade A. |
| FT-18 | Non-strict `hanti`; `apparentTemp_overestimate` without `hle`; "settles the literature"; re-proving `olsSlope_add` | Too strong; false; overclaim; the lemma exists privately. |
| FT-19 | ρ = S/n_e; hEχ; "proves the measurement" | Must cancel U_II/U_I; unnecessary; the measured plasma has non-uniform n_e. |
| FT-20 | Voigt non-injectivity "inside the gate for γ/σ from 0.01"; retagging `doubletRatio_injOn` | Minimum at τ0 ≈ 36 at γ/σ = 0.01; `doubletRatio_injOn` is already REDUCED. |
| RF-01 | Deleting "thermometer" for all lines; "iff" | The ionic-line form holds at fixed n_e; only "if" is proved. |
| RF-02 | P0 priority; landing the antitone lemma as a headline witness | Fcal lumps volume ∝ ℓ, so this is an unstated coupling; the positive statement is preferred. |
| RF-03 | "Non-monotone for every γ/σ inside the gate"; follow-ups (5)/(6) as P0 fixes | Only for γ/σ ≳ 0.1, band under 1%; moved to FT-13, FT-18, FT-20. |
| RF-05 | (2) SahaContraction headline edit; (3) re-proving the closed corollary | Already scoped; `dampedMultiElementIter_converges_to_equilibrium` exists. |
| RF-06 | "Hidden" shared-U assumption; homologousPair_* in M4 Tier 1 | Disclosed, so the defect is the tag; they are Tier 2, and the envelope is Tier 1b. |
| RF-07 | Olean-only axiom reading as sufficient | Reports [] for doCheck:=false; leanchecker is mandatory. |
| RF-09 | P0 | Latent (0 violations); P1 blocker. |
| RF-10 | CGS wording located in StarkBroadening | It is at PartialLTE:61 and Dimensions:186-187. |
| RF-11 | APPROXIMATION retag option | Misuse of the tag; keep REDUCED and name the reduction. |
| RF-14 | (f) as a broad overclaim; (d) as CONFIRMED | The caveat exists at :88-97; (d) not re-run, so PLAUSIBLE. |
| RF-15 | Single-priority bundle | Split into P0, P1 and P2. |
| RF-18 | Re-deriving the old theorems as le_trans corollaries | An unproved extra obligation; add `_tight` theorems instead. |
| RF-24 | (4) uncentred aliasing bound | Duplicates RF-14(d). |
| RF-25 | Stamping the git commit into fixtures.json | Breaks CI's `diff -u` on every commit. |
| FM-04 | "Add outerLoop_contracts_apriori" | Already exists (SahaRangeEnclosure.lean:105). |
| LF-04 | "Non-monotone for every damping tested" as a gate-range claim | Narrowed as in RF-03 and FT-20. |
| LIT-02 | "The M4 IPD sentence is false" | Incomplete, not false; RF-10's addition stands. |

**Parked, not dropped.** These were confirmed by an auditor but not carried into any RF or FT item, so they were not verifier-checked. Treat them as open.
- **LIT-09.** OpacityBroadening refuses the El Sherbini width law. The auditor's grid shows an effective exponent in (0.5000, 0.5687]. The proposed idea is a proven band SA^(−1/2) ≤ R(τ) ≤ SA^(−0.57) (grade C).
- **LIT-10.** No conditioning modulus exists for doublet/COG τ recovery. Maali & Shabanov 2019 was retrieved.
- **LIT-18.** Tognoni 2007's ideal-plasma accuracy study (retrieved) is uncited.
- **LIT-19.** No duplicating-mirror self-absorption channel exists. Moon 2009 was retrieved.
- **Frontier ideas not advanced to the slate:**
  - LF FI-5, the exact centre-dip criterion (named as the RF-15 follow-up).
  - LF FI-6, a global-L composition alias.
  - U FI-6, measure-theoretic split-conformal coverage with an Aitchison score.
  - FM idea 4, the Doppler COG √ln τ sharp limit.
  - ARCH FI2, a TwoPt Lipschitz combinator library.
  - ARCH FI5, OLS as an orthogonal projection.
  - G ideas F-01 (certified exp/log enclosures for transcendental fixtures), F-02 (single-source Float/ℝ mirror) and F-05 (mutant-separation proofs). The G def-level lattice and witness linkage are folded into RF-27.

**Operational note.** One verifier re-ran a companion probe with `uv run`, which reinstalled 2 packages in the companion `.venv`. No tracked file changed; git status shows only pre-existing `.beads` changes.

**Auditors that failed or were thin:** none.