# FT12-olsSlope-subGaussian-tail-hetero: planning dossier

*Source: deep audit 2026-09-24 (`docs/research/audit-2026-09-24/REPORT.md` §5 FT-12 (a), queue
decomposition item 1), with the verifier's revision: `hc` dropped (REVISE, grade A). One change from
the audit sketch: the section variable `[IsProbabilityMeasure μ]` is omitted, like the landed
homoscedastic twin (which uses `omit [IsProbabilityMeasure μ] in`); a proof compiled without it.
This does **not** generalise the statement: `hindep : iIndepFun ε μ` already implies
`IsProbabilityMeasure μ` (`iIndepFun.isProbabilityMeasure`), so the statement is equivalent to the
probability-space version (statement audit 2026-09-24, which corrected the docstring and predicted
the published tag). Group g3, priority 15.
Toolchain: Lean / mathlib v4.33.1 (the built `lean-main` checkout). Every Lean snippet below was
compiled against that checkout on 2026-09-24 under the statement's own imports.*

## 1. Goal

Statement file: `statement.lean`, namespace `Plan.FT12`, imports `Mathlib` and
`CflibsFormal.Alt.StochasticBudget`, `open Finset CflibsFormal MeasureTheory ProbabilityTheory`,
`variable {ι : Type*} [Fintype ι] {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}`.

```lean
theorem olsSlope_subGaussian_tail_hetero [Nonempty ι] (E : ι → ℝ) (α β : ℝ) (ε : ι → Ω → ℝ)
    {c : ι → NNReal} {δ : ℝ} (hvar : 0 < ∑ k, (E k - mean E) ^ 2) (hδ : 0 ≤ δ)
    (hindep : iIndepFun ε μ) (hsubG : ∀ k, HasSubgaussianMGF (ε k) (c k) μ) :
    μ.real {ω | δ ≤ |Alt.betaHat E α β ε ω - β|}
      ≤ 2 * Real.exp (-(δ ^ 2) / (2 * ∑ k, olsWeight E k ^ 2 * (c k : ℝ)))
```

## 2. Definitions (imported)

```lean
-- CflibsFormal/OLS.lean:40,58
noncomputable def mean (f : ι → ℝ) : ℝ := (∑ k, f k) / (Fintype.card ι)
noncomputable def olsWeight (E : ι → ℝ) (k : ι) : ℝ :=
  (E k - mean E) / (∑ j, (E j - mean E) ^ 2)
-- CflibsFormal/Alt/OLSVariance.lean:93 (namespace CflibsFormal.Alt)
noncomputable def betaHat (E : ι → ℝ) (α β : ℝ) (ε : ι → Ω → ℝ) (ω : Ω) : ℝ :=
  olsSlope E (fun k => α + β * E k + ε k ω)
```

Key repo lemma (`Alt/OLSVariance.lean:100`, public):
`Alt.olsSlope_estimator_eq [Nonempty ι] (E : ι → ℝ) (α β : ℝ) (ε : ι → Ω → ℝ)
(hvar : 0 < ∑ k, (E k - mean E) ^ 2) (ω : Ω) : betaHat E α β ε ω = β + ∑ k, olsWeight E k * ε k ω`.

## 3. Proof route: copy the landed homoscedastic proof, three edits

Template: `CflibsFormal/Alt/StochasticBudget.lean:574-627`, `olsSlope_subGaussian_tail` (single
proxy `c`, with `hc : 0 < c`). Edits: (1) use `c k` in the per-summand proxy; (2) delete the
closed-form steps (`hw2`, `hCcoe`, `hexp_eq`, which only convert `∑ w² c` into `c/SS_E`);
(3) rewrite the NNReal coercion per term. The result (compiled):

```lean
  have hindep' : iIndepFun (fun k => (fun x : ℝ => olsWeight E k * x) ∘ ε k) μ :=
    hindep.comp (fun k x => olsWeight E k * x) (fun k => measurable_id.const_mul (olsWeight E k))
  have hsum : HasSubgaussianMGF (fun ω => ∑ k, olsWeight E k * ε k ω)
      (∑ k, (⟨(olsWeight E k) ^ 2, sq_nonneg _⟩ * c k : NNReal)) μ :=
    HasSubgaussianMGF.sum_of_iIndepFun hindep'
      (fun k _ => (hsubG k).const_mul (olsWeight E k))
  have hterm : ∀ k, ((⟨(olsWeight E k) ^ 2, sq_nonneg _⟩ * c k : NNReal) : ℝ)
      = (olsWeight E k) ^ 2 * (c k : ℝ) := fun k => NNReal.coe_mul _ _
  have hpos := hsum.measure_ge_le hδ
  have hneg := hsum.neg.measure_ge_le hδ
  simp only [NNReal.coe_sum, Pi.neg_apply, hterm] at hpos hneg
  have hset : {ω | δ ≤ |Alt.betaHat E α β ε ω - β|}
      = {ω | δ ≤ ∑ k, olsWeight E k * ε k ω}
          ∪ {ω | δ ≤ -(∑ k, olsWeight E k * ε k ω)} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_union]
    rw [Alt.olsSlope_estimator_eq E α β ε hvar,
      show β + (∑ k, olsWeight E k * ε k ω) - β = ∑ k, olsWeight E k * ε k ω from by ring]
    exact le_abs
  rw [hset]
  calc μ.real ({ω | δ ≤ ∑ k, olsWeight E k * ε k ω}
          ∪ {ω | δ ≤ -(∑ k, olsWeight E k * ε k ω)})
      ≤ μ.real {ω | δ ≤ ∑ k, olsWeight E k * ε k ω}
          + μ.real {ω | δ ≤ -(∑ k, olsWeight E k * ε k ω)} := measureReal_union_le _ _
    _ ≤ _ := add_le_add hpos hneg
    _ = _ := by ring
```

**No case split on `∑ w²·c = 0` is needed.** `HasSubgaussianMGF.measure_ge_le` has no positivity
hypothesis on the proxy: at proxy `0`, Lean's `−δ²/(2·0) = 0` gives the bound `exp 0 = 1` per
tail, so the formula stays true. (The audit risk note suggested a case split through
`μ.real ≤ 1`. That route is available, because `hindep.isProbabilityMeasure` supplies the
probability measure, but it is unnecessary.)

## 4. Mathlib lemmas (all resolved in v4.33.1)

- `ProbabilityTheory.HasSubgaussianMGF.measure_ge_le (h : HasSubgaussianMGF X c μ) {ε : ℝ}
  (hε : 0 ≤ ε) : μ.real {ω | ε ≤ X ω} ≤ Real.exp (-ε ^ 2 / (2 * ↑c))`
- `ProbabilityTheory.HasSubgaussianMGF.sum_of_iIndepFun (h_indep : iIndepFun X μ)
  {c : ι → NNReal} {s : Finset ι} (h_subG : ∀ i ∈ s, HasSubgaussianMGF (X i) (c i) μ) :
  HasSubgaussianMGF (fun ω ↦ ∑ i ∈ s, X i ω) (∑ i ∈ s, c i) μ`
- `HasSubgaussianMGF.const_mul (h) (r : ℝ) : HasSubgaussianMGF (fun ω ↦ r * X ω) (⟨r ^ 2,
  sq_nonneg r⟩ * c) μ`; `HasSubgaussianMGF.neg`
- `ProbabilityTheory.iIndepFun.comp (h : iIndepFun f μ) (g) (hg : ∀ i, Measurable (g i)) :
  iIndepFun (fun i => g i ∘ f i) μ`
- `MeasureTheory.measureReal_union_le (s₁ s₂) : μ.real (s₁ ∪ s₂) ≤ μ.real s₁ + μ.real s₂`
- `le_abs : a ≤ |b| ↔ a ≤ b ∨ a ≤ -b`, `NNReal.coe_sum`, `NNReal.coe_mul`, `Set.mem_ofPred_eq`
  (`Set.mem_setOf_eq` still works but is deprecated: a warning only)

## 5. Pitfalls and verifier rules

- `-(δ ^ 2)` in the statement and `-δ ^ 2` in `measure_ge_le` are the same term (`-δ ^ 2` parses
  as `-(δ ^ 2)`), so after the `simp only … at hpos hneg` step the bounds match the goal.
- Do not `push_cast` the NNReal sum into a separate `have` stated with an outer coercion: the
  elaborator puts the coercion inside the sum and the later `rw` fails to find the pattern. The
  per-term `hterm` with `simp only [NNReal.coe_sum, …]` is the form that works.
- Do not add `[IsProbabilityMeasure μ]`: the `variable` line must stay verbatim, and the elaborated
  type is compared.
- Keep the statement header verbatim (two imports, `open`, `namespace`, `variable`) and the target
  signature text up to `:=`; state it with `theorem`; do not name a helper
  `olsSlope_subGaussian_tail_hetero'`. Forbidden: `sorry`, `admit`, `native_decide`, `axiom`,
  `macro`/`syntax`/`elab`, `#`-commands, `set_option` other than heartbeat/recursion limits.

## 6. Scope and consumers

Relation PURE-MATH. `Alt.betaHat` is the OLS slope of the additive-noise linear Boltzmann-plot
model `y k = α + β·E k + ε k` (`Alt/OLSVariance.lean:93`), and the landed homoscedastic twin's row
is `Alt/StochasticBudget.lean olsSlope_subGaussian_tail REDUCED Aitken 1935`; published = the
weaker axis, **REDUCED**, citation Aitken 1935 (whitelisted). Lead-level note, not a blocker: the
family's rows are inconsistent (`olsSlope_variance_noiseGain` EXACT, `olsSlope_unbiased`
REDUCED, same model).
The physics binding `c_k ≈ 1/SNR_k²` (delta method on `log I`) is APPROXIMATION and outside this
statement. Follow-ups (thin wrappers after landing): `slopeTailCert` soundness and the temperature
corollary via `temp_slope_event_subset`. Consumers: certificate_gate C4 (HARD), [backlog-id], [backlog-id],
[backlog-id]; reopens the frontier-11 refusal that rested on a false mathlib-absence claim.

Statement-audit evidence (`staging/2026-09-24/_statement-audit/ft12_prob.lean`, exit 0):
`hindep.isProbabilityMeasure` compiles; at `E = (0, 1, 2)`, `c = (1, 2, 3)`, `δ = 3` the proxy sum
`∑ w_k²·c_k = 1` and the right side `2·e^{−9/2} < 1` (an informative bound); `hsubG` is
satisfiable with a positive proxy (zero noise on `Measure.dirac ()`).
