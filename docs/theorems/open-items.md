# Open items

> **AUTO-GENERATED** by `scripts/gen_cards.py`: every card's `open_items`, rolled up. cflibs-formal has no `.beads/`; this plus optional issue links is the tracker (IA-proposal §1.3 item 4).

## [`ft01.damped-t-loop-convergence`](ft01.damped-t-loop-convergence.md)

- **lean**: the physics binding (the pipeline's reduced Saha-Boltzmann update is affine in 1/T on a median piece, IPD off, unit weights) is not stated or landed; it needs its own REDUCED statement and a Mode B statement audit before any C11 certificate could cite this family (FT-01)
- **lean**: the 2x2 Gauss-Seidel stability test is not landed: gaussSeidel_det_trace is proved in audit scratch (Slate.lean); jury_two is only stated there (sorry)
- **lean**: residual_stop and dampedAffine_iterate are proved in audit scratch (Proofs.lean); dampedAffine_tendsto_iff is only stated (sorry, Slate.lean); none is landed (docs/research/audit-2026-09-24/evidence/frontier-proposer/Proofs.lean)
- **lean**: dampedMap_repelling (a fixed point with g' > 1 repels for every damping), tDamped_local_rate (the local rate at T-star), single_group_gain and jointOuterContraction_weighted are not staged
- **lean**: dampedMap_lipschitz asserts only that some q < 1 exists (its docstring names q = max(|1-lam+lam*m|, |1-lam+lam*M|) but the statement does not export it); dampedMap_contracts states no rate at all; a stop certificate needs q, or the residual bound, as an explicit theorem output
- **model-row**: once a physics-binding declaration lands it will need its own REDUCED docs/scope-tags.tsv row citing the Saha-Boltzmann source; none of the five PURE-MATH results here needs one
- **pipeline**: no C11 predicate or def/soundness theorem exists in Certificates.lean or in the companion's certificate_gate.py; the certificates.yaml C11 entry is status not-implemented

## [`ft02.ipd-saha-inverse-gauge`](ft02.ipd-saha-inverse-gauge.md)

- **lean**: FT-02's gauge, mismatch and ratio-gauge identities (audit item 1) and the composition corollary (item 2) were proved in the audit's scratch evidence (`docs/research/audit-2026-09-24/evidence/plasma-state/IPDGauge.lean`, `docs/research/audit-2026-09-24/evidence/frontier-verifier/Verify.lean`) but not landed in `CflibsFormal/`; the physics-binding step (item 8, `a = S(χ)/R`) is likewise not landed under this or any other card. `registry/frontier.yaml`'s own landing note records that the originally sketched composition-invariance corollary (`ipdOff_composition_invariant`) used the wrong mechanism, and its proposed replacement (`sahaRatio_ipd_gauge`) is not landed as a separate `docs/scope-tags.tsv` row either. This card documents only the `ipdLogMap` fixed-point family (FT-02 items 3-7). (FT-02)
- **pipeline**: Whether CF-LIBS-improved's `_ne_for_T` three-step loop actually lies in an `hmaps`-invariant half-line with realized slope `q < 1` on any real spectrum is unverified — the loop carries no runtime check of either condition. See "Role in the composition-extraction pipeline" below for a proposed check and its falsification arm.
- **model-row**: `ipdLogMap` (the `def` itself) carries no `docs/scope-tags.tsv` row and inherits no relation tag: the lowering coefficient `b` stays abstract by owner decision D18, so no tag applies until the physics-binding step (FT-02 item 8) is written and reviewed. (D18)

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

## [`ft17.neutrality-newton-bracket`](ft17.neutrality-newton-bracket.md)

- **lean**: Global convergence of the Newton iteration from an arbitrary x0 >= 0 (not just the one-step bracket) is parked, not landed. (FT17-neutralityNewton-tendsto)
- **lean**: The audit's queue decomposition also asked for strict positivity (N x > 0 for x >= 0), the companion monotone-step fact (0 <= x <= r implies x <= N x), a linear convergence rate, and a certificate wrapper that eliminates r from the check; none of these is claimed by any landed declaration in this family. (FT-17)
- **model-row**: Applying the bracket to the pressure-balance fallback would need a fixed-pressure (isobaric) closure, a Z-stage ladder and n_e-dependent effective ionization potentials, not only a Z-stage generalization of multiElementIonized.
- **model-row**: multiElementIonized (def) encodes the REDUCED two-stage fixed-T closure but carries no MODEL row in docs/scope-tags.tsv (D15). (D15)

## [`ft19.ion-apparent-temperature`](ft19.ion-apparent-temperature.md)

- **lean**: FT-19d, the weaker anchor E_j ≤ E'_{i'} + χ (drops hchi): audited correct, re-verified here in scratch (evidence/ft19d.lean, standard axioms), not landed; it would let the pipeline's own +χ ion-abscissa shift discharge the anchor instead of the strict hanchor above. (FT-19d)
- **lean**: Temperature form (0 < β_II, 0 < β_I, 1/(k_B β_I) ≤ 1/(k_B β_II)) re-verified in scratch (evidence/ft19_temperature.lean); not landed.
- **lean**: A strict version for genuinely inhomogeneous zones (via pairSlope_lt_tiltMean-style steps) is not stated.
- **lean**: The n-line OLS analogue is not proved; InhomogeneityBias's own docstring calls it true but needing the endpoint-residual sign of a least-squares fit to convex data. A per-element diagnostic on more than two lines per stage would need it.
- **model-row**: Zone-dependent n_e is not covered: no antivariance condition on θ(T_z)^{3/2}·e^{-χ/(k_B T_z)}/n_{e,z} is stated or checked. (FT-19)
- **model-row**: ionReweight carries no ionization-potential depression (D18's Debye–Hückel form is not wired in); the card author's own unformalized algebra suggests monotonicity survives for Δχ below a fraction of χ or k_B T, not checked in Lean or in scratch.
- **pipeline**: two_zone.py's module docstring attributes its illustrative 9890 K / 11400 K figures to the Spectrochim. Acta B 62:378 paper; the whitelist row for that measurement (§7) locates the figures in the J. Phys.: Conf. Ser. 59:210 paper instead; the SAB 62:378 paper has not been opened, so the attribution is possibly, not certainly, wrong. A correction for that private repo, out of scope here.
- **docstring**: mixed_ion_apparentBeta_le_neutral's docstring says the J. Phys.: Conf. Ser. 59:210 paper is not whitelisted and was not opened; it is now whitelisted VERIFIED — update the docstring.

## [`ft20.step-profile-pair-ratio-counterexample`](ft20.step-profile-pair-ratio-counterexample.md)

- **lean**: FT-20(a), the sufficient criterion (a strictly decreasing curve-of-growth log-slope implies a strictly antitone pair ratio for every r > 1), is not staged or landed. (FT-20(a))
- **lean**: FT-20(c), non-injectivity for a Voigt (Gaussian+Lorentzian) profile, is numerics only and needs a pre-registered statement audit of the sigma/gamma conventions before it can be staged as a Lean target. (FT-20(c))
- **docstring**: The companion's C13 docstring (widths, relative composition) and its pointer to cogRatio_injOn's (stale) line in CurveOfGrowth.lean are stale; see the pipeline[] tension rows.
- **pipeline**: No root-count guard exists for any non-flat pair or doublet optical-depth solver; the flat-kernel solvers on the current pair/doublet paths are provably single-rooted, so none is needed there today.

