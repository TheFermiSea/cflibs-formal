# Frontier 13 — Formalizing the sound algebraic core of 2DCOS-LIBS

*Planning dossier. No Lean edited; every mathlib claim grep-verified against `.lake/packages/mathlib` (v4.31.0, pinned), every in-repo claim anchored to a real declaration. Physics scope fixed by `docs/2dcos/monograph.corrected.md` + `docs/2dcos/ERRATA.md`: formalize only the correlation algebra + compositional identities that are TRUE; refuse the refuted "Model B" (§5). Full file: docs/frontiers/13-2dcos-formalization.md*

*Adversarial-review stamp (this pass): all 24 inventory entries and all in-repo anchors re-grepped and CONFIRMED present at the cited file:line in mathlib v4.31.0 and CflibsFormal/Closure.lean. All ten Milestone-A statements are expressible over mathlib `Matrix`/`Finset`/`Real` and the proof sketches close. Verdict PASS.*

## 1. The formal obstacle
No Lean formalization of 2DCOS exists (mathlib or repo: grep of CflibsFormal/ for noda|2dcos|asynchronous|hilbert-noda|softmax|clr returns nothing). The 2DCOS-LIBS framework mixes sound linear algebra with refuted physics: the audit graded the "Model B" standardless/n_e-free/temperature-free quantification FATAL on independent grounds (ERRATA C1, C2, C5); removed in the rebuild. What survives, audit-blessed: Noda's Hilbert–Noda matrix + sync/async maps are ordinary real-matrix constructions with clean symmetry; the zero-async-diagonal Ψ(ν,ν)=0 is a correct universal antisymmetry consequence (ERRATA C22 caveat: elementary, not a novel "law"; ERRATA C8: being universal it falsifies no model); the compositional layer's softmax(log x) is plain Aitchison closure not ILR (ERRATA C3). The obstacle is discipline: carve off exactly the true algebra, tag scope honestly, and refuse the rest by design. Value = rigor: a machine-checked CflibsFormal/TwoDCOS.lean where the true algebra is proven and refuted claims are conspicuously absent.

## 2. Mathematical landscape
Data object: Y : Matrix (Fin n) (Fin m) ℝ, row a = channel a's mean-centered time trace, Y a t = ỹ(ν_a,t). 1/(m−1) is the unbiased covariance scalar (nonzero; irrelevant to the symmetry theorems; m≥2 needed only where diagonal = variance).

2.1 Hilbert–Noda N j k = if j=k then 0 else 1/(π·((k:ℝ)−(j:ℝ))). THEOREM Nᵀ=−N: ext (j,k) via transpose_apply/neg_apply; j=k both 0 (eq_comm); j≠k goal 1/(π(j−k))=−(1/(π(k−j))) by neg_div/ring, no π≠0 needed. Only place the kernel value enters.

2.2 Φ Y = (1/((m:ℝ)−1))•(Y*Yᵀ). Symmetric via transpose_smul/transpose_mul/transpose_transpose. Diagonal Φ Y a a = (1/((m:ℝ)−1))·∑ₜ (Y a t)² (smul_apply/mul_apply/transpose_apply) = Var_t; ≥0 for m≥2 (sum_nonneg+sq_nonneg, 1/((m:ℝ)−1)≥0). REFUSED as identities: the Φ≈I_aI_b S_a S_b Var(T) factorization + energy-weighting (interpretive, sign-flipping; ERRATA C21).

2.3 Ψ Y = (1/((m:ℝ)−1))•(Y*N*Yᵀ). Antisymmetric Ψ Yᵀ=−Ψ Y (transpose_mul×2, transpose_transpose, Nᵀ=−N, mul_neg/neg_mul, transpose_smul/smul_neg) — the only consumer of Nᵀ=−N. HEADLINE zero-diagonal Ψ Y a a=0: evaluate (Ψ Y)ᵀ=−Ψ Y at (a,a): LHS=Ψ Y a a (transpose_apply), RHS=−(Ψ Y a a) (neg_apply) ⇒ x=−x ⇒ 0 (linarith; char ℝ ≠ 2). Standard universal property (Noda 1993); falsifies no self-absorption model (ERRATA C8/C22).

2.4 Single-driver / phase-diversity: if Y a t = s a·δ t then Ψ Y=0 entirely. Spine lemma skew_quadForm_zero: for Nᵀ=−N, ∑ⱼ∑ₖ v j·N j k·v k = 0 (Finset.sum_comm swap + N k j=−N j k ⇒ Q=−Q; diagonal terms map consistently, over ℝ forces Q=0). Then entrywise pull s a,s b out (mul_sum/sum_mul), apply to δ: δᵀNδ=0. Honest reading: single monotone cooling driver ⇒ zero asynchronicity; nonzero Ψ requires ≥2 independent temporal profiles.

2.5 Noda sequential-order: formalizable fragment is sign-consistency (Φ symmetric, Ψ antisym ⇒ Φ(a,b)·Ψ(a,b) antisymmetric, 0 on diagonal). Full physical lead/lag = HYPOTHESIS, not a pure-math theorem. Grade B.

2.6 Compositional: closure already exists as `composition` (Closure.lean:46) with composition_sum_one (:61) = closure_sum_one DONE (requires the existing hypothesis `0 < totalDensity n`, i.e. strict positivity of ∑x — slightly stronger than "∑x ≠ 0", but it is the shipped lemma, so A10 is a pure cite). New: softmax_log_eq_closure (the C3 identity: softmax(fun k=>log(x k))=composition x via exp_log; softmax∘log IS closure, not ILR); clr_sum_zero (∑ clr=0 via sum_sub_distrib/sum_const/card_univ, Nonempty; no positivity needed).

2.7 ILR: genuine ilr x=Vᵀclr x, VᵀV=I, 1ᵀV=0, isometry S^D→ℝ^(D−1). clr round-trip = B (exp_log/log_exp + clr_sum_zero). Full isometry = C (needs OrthonormalBasis/LinearIsometry on the hyperplane H + a constructed Helmert/SBP basis). Land the C3 core; mark full isometry B/C in open[].

## 3. mathlib inventory (all re-grep-verified v4.31.0 this pass)
No new infrastructure for Milestone A. Matrix: transpose_mul (Data/Matrix/Mul.lean:1150), transpose_transpose (LinearAlgebra/Matrix/Defs.lean:394), transpose_neg (:428), transpose_smul (:424), transpose_apply (:142), neg_apply (:274), smul_apply (:266), mul_apply (Data/Matrix/Mul.lean:298). BigOps: Finset.sum_comm (to_additive of prod_comm, Algebra/BigOperators/Group/Finset/Sigma.lean:121), mul_sum (Ring/Finset.lean:59), sum_mul (:56), sum_sub_distrib (to_additive-generated; real name confirmed via use site Probability/CentralLimitTheorem.lean:108), Finset.card_univ (Data/Fintype/Card.lean:104). Reals: exp_log (Log/Basic.lean:58), log_exp (:74), log_mul (:132), log_div (:137). Convex: stdSimplex (Analysis/Convex/StdSimplex.lean:35, already used by composition_mem_stdSimplex). InnerProduct: OrthonormalBasis (PiL2.lean, only for grade-C full ILR). In-repo: composition/totalDensity (Closure.lean:46,41), composition_sum_one (:61)=closure_sum_one DONE, composition_mem_stdSimplex (:87).

## 4. Milestone ladder
Milestone A (all Tier A, all realizability-confirmed): A1 hilbertNoda_transpose (Nᵀ=−N); A2 sync_transpose (Φ symm); A3 sync_diag + sync_diag_nonneg; A4 async_transpose (Ψ antisym, needs A1); A5 async_diag_zero (HEADLINE, needs A4); A6 skew_quadForm_zero (lemma); A7 async_single_driver_zero (needs A6); A8 softmax_log_eq_closure (C3, highest value); A9 clr_sum_zero; A10 closure_sum_one = existing composition_sum_one (cite). B/C: B1 sequentialOrder sign-consistency; B2 clr round-trip; C1 full ILR isometry (open[]).

## 5. Refusals
Model B (n_e elimination / standardless / temperature-free) — FATAL ERRATA C1,C2; Model A (dynamic-T-integration composition inversion) — ERRATA C21; async-as-Wronskian-flux identity — ERRATA C5 (Hilbert transform is not a derivative); energy-weighted-covariance quantification — ERRATA C21; softmax=ILR mislabel (formalize as closure via A8, refuse only the false ILR name); zero-diagonal⇒"Model C unphysical" non-sequitur — ERRATA C8; butterfly self-absorption signature = HYPOTHESIS not theorem.

## 6. Recommendation
Attack Milestone A now: settled elementary matrix + log/exp algebra, zero new mathlib, reuses existing composition. Best first target: A8 (softmax_log_eq_closure = audit C3). Then A1→A5 (Noda algebra to the headline zero-diagonal) and A6→A7 (single-driver). A9 trivial; A10 is a cite. Effort: S (one session). Real work is discipline: scope-tag every theorem, keep refused claims out.