# Open items

> **AUTO-GENERATED** by `scripts/gen_cards.py`: every card's `open_items`, rolled up. cflibs-formal has no `.beads/`; this plus optional issue links is the tracker (IA-proposal §1.3 item 4).

## [`f02m6.saha-ne-monotone-temp`](f02m6.saha-ne-monotone-temp.md)

- **owner-decision**: Owner spot-check of the EXACT relation tag is still required before the card can be treated as done.
- **lean**: Independent statement review and gen_cards.py --stamp are still required; the current statement_hash is UNREVIEWED.

## [`ft01.damped-t-loop-convergence`](ft01.damped-t-loop-convergence.md)

- **lean**: the physics binding (the pipeline's reduced Saha-Boltzmann update is affine in 1/T on a median piece, IPD off, unit weights) is not stated or landed; it needs its own REDUCED statement and a Mode B statement audit before any C11 certificate could cite this family (FT-01)
- **lean**: the 2x2 Gauss-Seidel stability test is only half landed: gaussSeidel_det_trace (det J = (1 + A)/4, 1 + det J - trace J = (1 - g)/4) is proved in audit scratch (Slate.lean) and not landed; the Jury test itself, jury_two (with its scalar form jury_pair), landed in JointConvergence after this card, not a member of it
- **lean**: dampedMap_repelling (a fixed point with g' > 1 repels for every damping), tDamped_local_rate (the local rate at T-star), single_group_gain and jointOuterContraction_weighted are not staged
- **lean**: dampedMap_contracts states no rate at all (no a-priori bound q^n/(1-q)|H T0 - T0| is stated). The explicit constant q = max(|1-lam+lam*m|, |1-lam+lam*M|) is now exported by dampedMap_lipschitz_explicit, landed in JointConvergence after this card, not a member of it (dampedMap_lipschitz is now its existential corollary); with residual_stop it gives the a-posteriori stop bound
- **model-row**: once a physics-binding declaration lands it will need its own REDUCED docs/scope-tags.tsv row citing the Saha-Boltzmann source; none of the five PURE-MATH results here needs one
- **pipeline**: no C11 predicate or def/soundness theorem exists in Certificates.lean or in the companion's certificate_gate.py; the certificates.yaml C11 entry is status not-implemented

## [`ft02.ipd-saha-inverse-gauge`](ft02.ipd-saha-inverse-gauge.md)

- **lean**: The physics-binding step (item 8, `a = S(χ)/R`) is not landed under this or any other card. FT-02's gauge, mismatch and ratio-gauge identities (audit item 1) and the corrected composition corollary (item 2) are landed in `CflibsFormal/IpdGauge.lean` (`sahaFactor_ipd_gauge`, `ne_ipd_mismatch`, `sahaRatio_ipd_gauge`, `twoStageTotal_ipd_gauge`, `composition_ipd_gauge`), outside this card, which documents only the `ipdLogMap` fixed-point family (FT-02 items 3-7). The originally sketched composition-invariance corollary (`ipdOff_composition_invariant`) used the wrong mechanism and was not landed. (FT-02)
- **pipeline**: Whether CF-LIBS-improved's `_ne_for_T` three-step loop actually lies in an `hmaps`-invariant half-line with realized slope `q < 1` on any real spectrum is unverified — the loop carries no runtime check of either condition. See "Role in the composition-extraction pipeline" below for a proposed check and its falsification arm.
- **model-row**: `ipdLogMap` (the `def` itself) carries no `docs/scope-tags.tsv` row and inherits no relation tag: the lowering coefficient `b` stays abstract by owner decision D18, so no tag applies until the physics-binding step (FT-02 item 8) is written and reviewed. (D18)

## [`ft03.refuse-to-report-policy`](ft03.refuse-to-report-policy.md)

- **pipeline**: Non-vacuous pipeline use requires certified upper bounds U_i; the audit names FT-07 and FT-15 as prerequisite error-bound sources. (FT-03)
- **lean**: Per-item statement for an arbitrary ansA, including the answer-on-A regret bound ∑_{i ∈ A} w i (U i − lam), is a separate target that is not landed. (FT-03)
- **lean**: FT-03 part (e), refusal-reason soundness on the sb_offset route (sahaConsistency_trivial_of_sbOffset, sahaTemperature_eq_fit), is not landed. (FT-03)

## [`ft04.fixed-effects-design-identifiability`](ft04.fixed-effects-design-identifiability.md)

- **pipeline**: Define and wire a grouped design-rank certificate (working name C1g; a new id from C15 per D16) testing 0 < withinSS grp w x on the solver's kept lines, alongside or instead of the pooled C1/C3 checks (owner decision); a grouped joint certificate (C2g) would rest on the joint result fe_joint_identifiable_iff (FT-04 part (iv)), landed in FixedEffectsDesign after this card and not a member of it.
 (FT-04)

## [`ft05.partition-function-cutoff-ratio`](ft05.partition-function-cutoff-ratio.md)

- **lean**: FT-05 (iv) population_cut_consistent and (v) sharpCutoff_discontinuous are not stated (FT-05)
- **model-row**: partitionFunctionCut has no row in docs/scope-tags.tsv, and D17's weighted level sum (Hummer–Mihalas occupation probabilities, with the fixed cutoff as the 0/1-weight instance) is not formalized (D17)

## [`ft06.stark-bracket-premise`](ft06.stark-bracket-premise.md)

- **pipeline**: The C8 two-diagnostic certificate and its refusal are not landed; this theorem is only the Stark-side premise. (FT-06)
- **pipeline**: cflibs/inversion/physics/reliability.py#stark_saha_lte_gate is the current runtime C8 slot (relative-tolerance agreement, not bracket intersection); cflibs/evolution/certificate_gate.py#hard_certificate_gate is the separate evaluator-side HARD set. Neither wires this theorem's bracket in. (FT-06)
- **docstring**: StarkOpacityGuard's REFUSAL note says the tau-to-width link is not formalized anywhere in this repo; OpacityBroadening.kOpacOf now formalizes it for a slab-Lorentzian model, so the note is stale

## [`ft07.aitchison-atomic-data-error-transfer`](ft07.aitchison-atomic-data-error-transfer.md)

- **owner-decision**: The title in registry/cards.yaml for this card still reads 'Aitchison error transfer under classic-reader atomic-data error'; the lead should update it to match this card's retitled 'Abundance-scaled closure bound under classic-reader atomic-data error' (card authors may not edit registry/cards.yaml). (FT-07)

## [`ft08.neutrality-scale-same-ratio`](ft08.neutrality-scale-same-ratio.md)

- **owner-decision**: Owner spot-check required by D24 for this card's relation tag is pending.
- **citation**: Abbass 2016 (cited in the NeutralityScale module docstring as prior art for neutrality normalization) is UNVERIFIED in docs/citation-whitelist.tsv. Attach it here with role prior-art only after the primary source is opened and the row is VERIFIED or CORRECTED.

## [`ft08.ratio-mode-normalization-invariance`](ft08.ratio-mode-normalization-invariance.md)

- **lean**: Compose log_sahaFactor_hasDerivAt_beta and hasDerivAt_log_sum_exp (d ln U/dβ = −⟨E⟩; both landed in SahaStability, outside this card) with ratioEstimate_hasDerivAt to obtain the audited coefficient (E_a−⟨E⟩_{I,A})−(E_b−⟨E⟩_{I,B})−f_Aκ_A+f_Bκ_B.

## [`ft09.affine-atomic-data-gauge`](ft09.affine-atomic-data-gauge.md)

- **owner-decision**: Owner spot-check required by D24 for the card's relation tag. (FT-09)
- **lean**: Grouped two-stage gauge and composition-leakage bound remain deferred; this card documents only the single-stage observational equivalence. (FT-09)
- **pipeline**: Wiring to calibration-layer consumers beyond the named BoltzmannPlotFitter anchor is not done. (FT-09)
- **owner-decision**: The title in registry/cards.yaml for this card still reads 'Energy-affine atomic-data gauge is an exact temperature shift'; the lead should update it to match this card's retitled 'Energy-affine atomic-data gauge: an exact temperature shift plus density rescale' (card authors may not edit registry/cards.yaml). (FT-09)

## [`ft10.noise-gain-floor-blue`](ft10.noise-gain-floor-blue.md)

- **lean**: Land the probabilistic heteroscedastic BLUE variance statement under uncorrelated noise with variance one over the line weights; this card proves only the deterministic noise-gain floor. (FT-10)
- **docstring**: Rename existing `crlb_slope` and `olsSlope_attains_crlb` names in a separate change; no new name may contain `crlb`. (FT-10)
- **pipeline**: Decide whether the weight cap in `_fit_common_boltzmann_plane` should be reported as a precision cost against the $1/S_w$ floor. (FT-10)
- **lean**: Land the variance statement for the common-slope intercept difference (homoscedastic, over a Sum index). (FT-10)
- **lean**: Land optimality (BLUE) of the intercept difference; only its noise gain is proved here. (FT-10)

## [`ft12.stochastic-slope-tail-budget`](ft12.stochastic-slope-tail-budget.md)

- **lean**: The certificate soundness wrapper slopeTailCert and the temperature corollary via temp_slope_event_subset are follow-up FT-12 steps, not part of this card. (FT-12)
- **lean**: The heteroscedastic Gaussian law of betaHat and exact coverage are separate FT-12 steps and are not claimed here. (FT-12)
- **pipeline**: The C4-sigma statistical certificate is still a candidate under C15; no certificate id or gate wiring is landed.
- **lean**: Float mirror of the tail bound in the oracle. (FT-12)

## [`ft13.escape-factor-slab-bound`](ft13.escape-factor-slab-bound.md)

- **lean**: The profile-generic escapeFactor Lipschitz lemma proposed for FT-13 is not landed. The flat-slab tau-error propagation lemma (log_slabCorrected_error_le) is landed outside this card.
- **pipeline**: C12 remains the wired HARD known-tau identity in the certificate gate; this card does not retire or replace it.

## [`ft14i.kirchhoff-source-planck`](ft14i.kirchhoff-source-planck.md)

- **citation**: D19 requires constants checked against standard references before FT-14 is stated; no record shows Griem 1997 (or another source) was opened for B0 = 2hν³/c², and the D19 wavelength-form bridge lemma is not formalized. The landed statement sidesteps the first gap by keeping κ0, ε0, B0 abstract.
 (D19)
- **model-row**: lineOpacity carries no model row although its stimulated-emission factor already presupposes LTE populations; PR #8 recorded this as an open owner decision, still pending.

- **lean**: source_eq_planck/lineOpacity are not wired into OpticalDepth.opticalDepth, which remains Wien-limit; every result that instantiates τ with opticalDepth (e.g. opticalDepth_knownTauCert, the OpticalDepthBridge τ-ratio results, thickLineIntensity) inherits that gap. C12/C13 (knownTau_certificate_sound, saDistinct_certificate_sound / cogRatio_injOn) are stated over an abstract τ / opacity coefficient and do not, though a binding of their τ to opticalDepth would.

- **docstring**: KirchhoffSource.lean's docstring attributes the n_l = 0 vanishing to a/0 = 0; scratch evidence shows the right side actually vanishes because hpop/hein force B0 = 0. The guard-keeping conclusion is unaffected; the stated mechanism is imprecise.

- **pipeline**: No pipeline test checks the pipeline's coefficients against hpop/hein (round-trip test proposed in section 5, not implemented), and whether the NIST_PARITY instrument-width path is reachable in practice is untraced.

- **lean**: FT-14 part (v) (transfer before instrument) remains parked as FT14-conv-absorptance-le, Fubini step unstaged — a sibling result, not this card's declaration.
 (FT-14)
- **owner-decision**: Owner spot-check of this EXACT card (D24) pending; required before merge to main.

## [`ft14iv.perline-tauratio-bridge`](ft14iv.perline-tauratio-bridge.md)

- **model-row**: The model-level identity for sigma0_i in terms of lambda, g_u, A, and phi(0) is not formalized here; radiation constants remain abstract per D19.
- **pipeline**: Decide whether _tau_ratio should carry the per-line (1 - exp(-x_i)) and lower-level Boltzmann factors; a full comparison needs the D19 sigma0 model identity.
- **docstring**: OpticalDepthBridge module scope block says stimulated emission is not modelled; reconcile it with perLine_tauRatio, which carries (1 - exp(-x_i)) via its sigma0 argument.

## [`ft14v.equivwidth-strict-mono`](ft14v.equivwidth-strict-mono.md)

- **owner-decision**: Resolve cross-registry naming: the card plan groups this theorem under FT-14, but its docs/scope-tags.tsv row and PR credit are recorded under registry/frontier.yaml's FT-19 `landed` list, not FT-14's. (FT-14)
- **lean**: Re-review the LaTeX statement binder by binder and stamp the statement hash after independent review.
- **pipeline**: Record a CF-LIBS-improved path#symbol anchor when a pipeline consumer is identified; none is named in this draft.
- **citation**: The theorem docstring cites no source; the EquivalentWidth module's `## Literature` cites Mihalas 1978 (whitelist UNVERIFIED) for the equivalent-width definition and Gornushkin 1999 (AUDIT-VETTED) for the LIBS curve of growth. Decide whether to attach them as context only (no locator: neither row is VERIFIED/CORRECTED).

## [`ft15.mean-excitation-lipschitz`](ft15.mean-excitation-lipschitz.md)

- **lean**: Complete adversarial review and stamp lean.reviewed.statement_hash; the current value is UNREVIEWED.
- **lean**: FT-15's ln S (Saha-factor) Lipschitz leg is not landed. The [Tmin, Tmax] box form of the ln U bound is log_partitionFunction_lipschitz_box, landed in SahaStability after this card, not a member of it. (FT-15)

## [`ft16.kernel-extraction-varah-bound`](ft16.kernel-extraction-varah-bound.md)

- **citation**: The audit's candidate 1975 linear-algebra source is not attached; route it through citation-integrity before citing it.
- **lean**: The ordinate corollary should be derived from `CflibsFormal.abs_log_ratio_le` rather than restated; it is outside this headline statement.
- **lean**: Margin-certificate soundness (kernelMarginCert; nonsingularity of KᵀK via mathlib det_ne_zero_of_sum_row_lt_diag) is not landed. (FT-16)
- **lean**: Compose the bound with the ordinate corollary (`CflibsFormal.abs_log_ratio_le`) and `noise_to_composition` to reach a log-ordinate budget.
- **pipeline**: Wire the resulting bound into the composition-extraction error budget once the forward-model piece is available.

## [`ft17.neutrality-newton-bracket`](ft17.neutrality-newton-bracket.md)

- **lean**: The audit's queue decomposition also asked for a linear convergence rate and a certificate wrapper that eliminates r from the check; neither is claimed by any landed declaration. Strict positivity (N x > 0 for x >= 0 when some species is present) and the monotone-step fact (0 <= x <= r implies x <= N x) are neutralityNewton_pos_and_step_monotone, landed in SahaEquilibrium after this card, not a member of it. (FT-17)
- **model-row**: Applying the bracket to the pressure-balance fallback would need a fixed-pressure (isobaric) closure, a Z-stage ladder and n_e-dependent effective ionization potentials, not only a Z-stage generalization of multiElementIonized.
- **model-row**: multiElementIonized (def) encodes the REDUCED two-stage fixed-T closure but carries no MODEL row in docs/scope-tags.tsv (D15). (D15)

## [`ft18.self-absorption-slope-bias-sign`](ft18.self-absorption-slope-bias-sign.md)

- **model-row**: No claim is made that real CF-LIBS line sets satisfy H2; the tau-versus-E ordering is an empirical per-line-set check before applying the theorem. (FT-18)
- **pipeline**: No CF-LIBS-improved code references this theorem; the default Boltzmann fit is weighted and sigma-clipped, so applying FT-18 there needs a weighted fixed-line-set analogue or an unweighted diagnostic fit. (FT-18)

## [`ft19.ion-apparent-temperature`](ft19.ion-apparent-temperature.md)

- **lean**: A strict version for genuinely inhomogeneous zones (via pairSlope_lt_tiltMean-style steps) is not stated.
- **lean**: The n-line OLS analogue is not proved; InhomogeneityBias's own docstring calls it true but needing the endpoint-residual sign of a least-squares fit to convex data. A per-element diagnostic on more than two lines per stage would need it.
- **model-row**: Zone-dependent n_e is not covered: no antivariance condition on θ(T_z)^{3/2}·e^{-χ/(k_B T_z)}/n_{e,z} is stated or checked. (FT-19)
- **model-row**: ionReweight carries no ionization-potential depression (D18's Debye–Hückel form is not wired in); the card author's own unformalized algebra suggests monotonicity survives for Δχ below a fraction of χ or k_B T, not checked in Lean or in scratch.
- **pipeline**: two_zone.py's module docstring attributes its illustrative 9890 K / 11400 K figures to the Spectrochim. Acta B 62:378 paper; the whitelist row for that measurement (§7) locates the figures in the J. Phys.: Conf. Ser. 59:210 paper instead; the SAB 62:378 paper has not been opened, so the attribution is possibly, not certainly, wrong. A correction for that private repo, out of scope here.

## [`ft20.step-profile-pair-ratio-counterexample`](ft20.step-profile-pair-ratio-counterexample.md)

- **lean**: FT-20(c), non-injectivity for a Voigt (Gaussian+Lorentzian) profile, is numerics only and needs a pre-registered statement audit of the sigma/gamma conventions before it can be staged as a Lean target. (FT-20(c))
- **docstring**: The companion's C13 docstring (widths, relative composition) and its pointer to cogRatio_injOn's (stale) line in CurveOfGrowth.lean are stale; see the pipeline[] tension rows.
- **pipeline**: No root-count guard exists for any non-flat pair or doublet optical-depth solver; the flat-kernel solvers on the current pair/doublet paths are provably single-rooted, so none is needed there today.

