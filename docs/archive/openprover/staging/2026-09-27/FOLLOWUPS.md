# Staged 2026-09-27: what is waiting on what

- FT19-mixed-ion-apparentBeta-le-neutral: enqueue after FT19-ionReweight-strictMonoOn and
  FT19-tiltMean-reweight-le verify; append their verified proofs to its dossier (as done for FT13-log).
  Scope at landing: PURE-MATH / PURE-MATH / REDUCED. Cite Aguilera-Aragon 2007 JPCS 59:210 only as
  "consistent with"; it needs its own whitelist row.
- FT-19d (follow-up, audited correct 2026-09-27): weaker anchor EZ j <= EZ1 i' + chi via the
  reweight 2*theta^{3/2}/n_e and tiltWeight (w*rho) b a = tiltWeight (w*rho') b (a + chi); drops hchi.
- FT20-equivWidth-stepProfile: proof in _hand-land/ (verify.py PASS 2026-09-27); hand-land.
- FT20-stepProfile-pairRatio-not-injOn: one-line bridge; hand-land after FT20-equivWidth-stepProfile
  and FT20-stepW-pairRatio-not-injOn exist. At landing, retag cogRatio_injOn and
  saDistinct_certificate_sound EXACT -> REDUCED (flat-kernel slab) with a pointer to the counterexample.
- FT-08 hand-land (verify.py PASS 2026-09-27): ratio_mode_normalization_invariant (PURE-MATH),
  neutrality_closure_same_ratio (audit: EXACT, not REDUCED: lineIntensityPerU is EXACT and the
  relation is exact algebra; cite Tognoni 2010), ratioEstimate_hasDerivAt (audit: PURE-MATH: Mathlib
  only, abstract functions). Do not cite Abbass/NeutralityScale as prior art.
- FT08-log-sahaFactor-hasDerivAt-beta (queued 2026-09-27): tag must equal Saha.log_sahaFactor's tag
  RESOLVED 2026-09-27 (PR #7, 9dbbc60): sahaFactor has model tag REDUCED, so log_sahaFactor publishes
  REDUCED (relation EXACT); tag this derivative relation EXACT, and it publishes REDUCED automatically.
- FT-14 hand-land (verify.py PASS 2026-09-27): source_eq_planck (EXACT given hpop/hein; keep hx, hnl
  as physical-regime guards: droppable only via junk values), perLine_tauRatio (REDUCED; at landing
  DROP [Nonempty ι] and add `haveI : Nonempty ι := ⟨l1⟩`; keep hσ2; use the audit's two-line witness
  ι = Fin 2, l1 = 0, l2 = 1, E = ![0,1], κ01 = 2, κ02 = 3, x1 = 0.5, x2 = 1.5 in the docstring).
  Closes OpticalDepthBridge's "per-line σ₀ᵢ is open work".
- FT-14 queued 2026-09-27: equivWidth_strictMonoOn (Ici 0 is right; keep hint for API parity with
  equivWidth_mono), conv_absorptance_le (the pointwise Jensen step; its dossier witness phi = 1 is the
  equality case; hRφ necessity argued, not executed; the integrated Fubini step (decomposition item 8)
  is not yet staged).
- PR #7 merged 2026-09-27 (9dbbc60): the hand-land batch (task #4 + _hand-land/) is now unblocked.
- 2026-09-27: PR #8 (feat/land-frontier-proofs) lands the 19 older hand-land proofs, 7 queue
  results and the 6 _hand-land/ proofs here. Its model-row questions for the owner:
  partitionFunctionCut, ipdLogMap, sahaEquilibriumNe, multiElementIonized, Alt.betaHat and
  lineOpacity. Later landings: the FT-20 counterexample and bridge (with the cogRatio_injOn /
  saDistinct_certificate_sound retag), the FT-19 lemmas and assembly, FT13-log, FT17-tendsto,
  the FT08 Saha derivative and the FT-14 queue targets.
- PR #8 merged 2026-09-27 (78c3daa). lean-main is still at fb1681d. BEFORE advancing it: the queued
  FT08-log-sahaFactor-hasDerivAt-beta statement defines a local `meanExcitation` and opens
  CflibsFormal, which now has `CflibsFormal.meanExcitation` (identical body). Either let that target
  finish first, or re-point its statement at the landed def, which needs a re-audit because the
  statement changes. Rebuild lean-main after advancing (`lake build`); advance only when the
  queue is idle.
- 2026-09-28: lean-main advanced to main 78c3daa and rebuilt (queue idle). FT08-log is parked, so the
  meanExcitation clash is moot until it is re-queued; if it is, point its statement at
  `CflibsFormal.meanExcitation` first. Verified overnight: FT19-tiltMean (attempt 3, 500k budget),
  FT14-equivWidth (attempt 3), and the FT19 assembly (attempt 2, with both lemmas in its dossier).
  Parked: FT13-log (5 runs), FT08-log, FT14-conv, FT17-tendsto, F07. Landing branch:
  feat/land-frontier-proofs-2 in ~/code/cflibs-formal-land2.
