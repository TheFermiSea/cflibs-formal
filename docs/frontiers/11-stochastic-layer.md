# Frontier 11 — The stochastic layer: from variance to concentration of recovered T and composition

*Planning dossier. No Lean edited; every current-state claim anchored to a real
declaration, every mathlib claim grepped against `.lake/packages/mathlib` (v4.31.0).
This frontier extends the probability layer (`Alt.OLSVariance`, `Alt.GaussMarkov`)
from second-moment (`Var`) statements to **distributional / concentration** (tail)
statements about the recovered slope, intercept, temperature, and composition.*

> **Reviewer note (scope tags corrected).** The Chebyshev / sub-Gaussian tail bounds
> (M2, M4, M7) were originally tagged `EXACT`; they are **slackened, non-attainable**
> bounds (Chebyshev and sub-Gaussian tails carry irreducible slack), so the faithful
> repo classification is **`REDUCED`** — matching `temp_rel_error_le` (REDUCED, a
> slackened bound), and distinct from the exact *identities* `olsSlope_variance_eq` /
> `alphaHat_variance_eq` (EXACT) and the *attainable* worst-case bound `relDensity_le`
> (EXACT). Only M3's variance identity remains EXACT. Grades (A/B/C, reachability) are
> unaffected by this documentation-axis correction.

---

## 1. The formal obstacle

The repo already carries a genuine measure-theoretic probability layer. In
`CflibsFormal/Alt/OLSVariance.lean` the Boltzmann-plot ordinates are a linear model
with random noise `yₖ(ω) = α + β·Eₖ + εₖ(ω)`, the OLS slope becomes a random variable
`betaHat E α β ε` (`OLSVariance.lean:93`), and the module proves the **exact
second-moment law**:

- `olsSlope_estimator_eq` (`OLSVariance.lean:100`) — the pointwise identity
  `β̂(ω) = β + ∑ₖ wₖ·εₖ(ω)`, `wₖ = olsWeight E k`.
- `olsSlope_unbiased` (`OLSVariance.lean:177`) — `𝔼[β̂] = β`.
- `olsSlope_variance_eq` (`OLSVariance.lean:203`) — **`Var(β̂) = σ²/SS_E`**
  (`SS_E = ∑ₖ (Eₖ − Ē)²`).
- `olsSlope_variance_antitone` (`OLSVariance.lean:219`) — more spread ⇒ less variance.

The two reusable kernels are `expectation_const_add_weightedNoise`
(`OLSVariance.lean:126`, `𝔼[c + ∑ wₖεₖ] = c`) and `variance_const_add_weightedNoise`
(`OLSVariance.lean:146`, `Var(c + ∑ wₖεₖ) = σ²·∑ wₖ²`), both weight-agnostic. The
measure is declared `[IsProbabilityMeasure μ]` (`OLSVariance.lean:120`), so it is finite.
The sibling `Alt/GaussMarkov.lean` adds the BLUE optimality ladder
(`linEstimator`, `linEstimator_variance` `:142`, `ols_is_blue` `:194`).

**What the repo cannot state today.** Every probabilistic result stops at the second
moment. There is *no* statement of the form

> `μ {ω | δ ≤ |betaHat E α β ε ω − β|} ≤ …`  (a **tail / deviation** bound)

and therefore no probabilistic statement about the *recovered temperature* or
*composition* — only the **deterministic** worst-case error budget
(`ErrorBudget.temp_rel_error_eq` `:199`, `relDensity_le` `:261`,
`composition_target_sufficient` `:325`) exists on the diagnostic side. The two layers
never meet: the exact identity `temp_rel_error_eq`
(`|T̂ − T|/T = k_B·T̂·|β̂ − β|`) is available deterministically, and `Var(β̂)` is
available probabilistically, but *no theorem converts the variance of the slope into a
probability that the recovered temperature misses by more than `ε`*. That bridge —
Chebyshev on `β̂`, then an exact event-inclusion transfer into a temperature/composition
tail — is the frontier.

The obstacle is *not* missing mathematics or missing mathlib (see §3): it is that the
existing `Var` results have never been fed into mathlib's Chebyshev inequality, and the
deterministic error-transfer identities have never been read as **event inclusions**.

---

## 2. Mathematical landscape

Notation throughout: `wₖ = olsWeight E k = (Eₖ − Ē)/SS_E`, `n = Fintype.card ι`,
`Ē = mean E`, `SS_E = ∑ₖ (Eₖ − Ē)²`, `σ²` the common noise variance. All routes reuse
`olsSlope_estimator_eq` / the two `*_weightedNoise` kernels verbatim.

### 2.1 Slope concentration — Chebyshev on `β̂` — CONFIRMED (grade A, immediate)

mathlib's Chebyshev inequality (`meas_ge_le_variance_div_sq`,
`Probability/Moments/Variance.lean:399`) reads

```
[IsFiniteMeasure μ] (hX : MemLp X 2 μ) (hc : 0 < c) :
  μ {ω | c ≤ |X ω − μ[X]|} ≤ ENNReal.ofReal (variance X μ / c ^ 2)
```

Instantiate `X = betaHat E α β ε`, `c = δ`. Two rewrites close it: `μ[betaHat] = β`
(`olsSlope_unbiased`) turns the centered set into `{ω | δ ≤ |β̂ ω − β|}`, and
`variance (betaHat …) μ = σ²/SS_E` (`olsSlope_variance_eq`) turns the RHS into
`σ²/(SS_E·δ²)`. Result:

```
μ {ω | δ ≤ |betaHat E α β ε ω − β|} ≤ ENNReal.ofReal (σ² / (SS_E · δ²)).
```

The one obligation is `MemLp (betaHat …) 2 μ`. By `olsSlope_estimator_eq`,
`betaHat = fun ω ↦ β + ∑ₖ wₖ εₖ ω` (a `funext`), and the RHS is `MemLp 2` because it is
a constant plus `memLp_finsetSum` (`.../TriangleInequality.lean:144`) of
`(hL2 k).const_mul (wₖ)` (`MemLp.const_mul`, `.../SMul.lean:50`) — **exactly the L²
bookkeeping already performed inside `variance_const_add_weightedNoise`
(`OLSVariance.lean:151-153`).** No new mathlib, no new idea. This is the concrete,
immediately-reachable core (M1–M2 below). The `[IsFiniteMeasure μ]` hypothesis is
discharged by the module's ambient `[IsProbabilityMeasure μ]`.

### 2.2 Temperature tail transfer — the crown — CONFIRMED (Chebyshev A; transfer B)

This is candidate (b). The recovered temperature is the physical inversion of the
Boltzmann-plot slope: with true slope `m = −1/(k_B T) < 0` and estimator `m̂ = betaHat`,
the temperature estimator is `T̂ = τ(m̂)`, `τ(x) := −1/(k_B·x)` (defined and *strictly
increasing* on `(−∞,0)`, `τ'(x) = 1/(k_B x²) > 0`). Because `|1/(k_B T̂) − 1/(k_B T)| =
|(−m̂) − (−m)| = |m̂ − m|`, the slope error is literally the inverse-temperature error;
the sign convention is absorbed by the absolute value.

**The transfer is a deterministic event inclusion — NO delta method, NO calculus.** Fix
`ε > 0` and set

```
δ(ε) := ε / (k_B · T · (T + ε)).
```

Claim: `{ω | ε ≤ |τ(betaHat ω) − T|} ⊆ {ω | δ(ε) ≤ |betaHat ω − m|}`. Proof of the
contrapositive (pointwise, elementary algebra): suppose `|m̂ − m| < δ(ε)`. Note
`δ(ε) = ε/(k_B T(T+ε)) < 1/(k_B T) = |m|` (ratio `ε/(T+ε) < 1`), so the whole interval
`(m − δ, m + δ)` lies in `(−∞, 0)` and `τ` is increasing there. Evaluate the endpoints
with `m = −1/(k_B T)`:

```
τ(m + δ) = T/(1 − k_B T δ),   τ(m − δ) = T/(1 + k_B T δ).
```

So `τ(m+δ) − T = k_B T² δ/(1 − k_B T δ)` and `T − τ(m−δ) = k_B T² δ/(1 + k_B T δ)`. At
`δ = δ(ε)` the first equals `ε` exactly (solve `k_B T² δ = ε(1 − k_B T δ)`), and the
second is strictly smaller. Hence `τ(m̂) ∈ (τ(m−δ), τ(m+δ)) ⊆ (T − ε, T + ε)`, i.e.
`|T̂ − T| < ε`. ∎ *(Reviewer-verified: the endpoint identities and the exact solve for
`δ(ε)` were re-derived independently and are correct.)* Chaining with §2.1:

```
μ {ω | ε ≤ |T̂ ω − T|} ≤ μ {ω | δ(ε) ≤ |betaHat ω − m|}
                       ≤ ENNReal.ofReal (σ² · k_B² T² (T+ε)² / (SS_E · ε²)).
```

Fully explicit `δ(ε)`, fully explicit final bound. The Lean cost above the grade-A
Chebyshev is: (i) a `tempOfSlope` definition and its measurability (`τ` is `Measurable`
via `measurable_inv`/`measurable_const_mul`, with a junk value at `0`), and (ii) the
interval-inclusion lemma (the elementary `calc` above, with the automatic branch fact
`δ(ε) < |m|`). Grade **B** — the algebra is settled on paper; the branch/positivity and
measurability bookkeeping put it above a one-liner. The slope Chebyshev (§2.1) is the
grade-A half that a dev should land first.

> **Framing note.** The realized M5 proof above is a *self-contained* interval inclusion
> on `τ`; it does **not** invoke `temp_rel_error_eq` (whose multiplicative form
> `|T̂−T|/T = k_B T̂ |β̂−β|` is a different route). `temp_rel_error_eq` is the conceptual
> bridge cited in §1, but the concrete M5 leg reaches the tail without it — so M5 does
> not depend on that identity being re-expressible.

### 2.3 Intercept estimator + its tail — CONFIRMED (grade A, full non-centered form)

Candidate (a). Define `alphaHat E α β ε ω := olsIntercept E (fun k ↦ α + β Eₖ + εₖ ω)`.
Because `olsIntercept = mean y − olsSlope·Ē` (`OLS.olsIntercept`, `:52`) and
`mean y = α + β Ē + mean ε` while `olsSlope = β + ∑ wₖ εₖ` (`olsSlope_estimator_eq`),

```
alphaHat = α + mean ε − (∑ₖ wₖ εₖ)·Ē
         = α + ∑ₖ aₖ·εₖ,     aₖ := 1/n − wₖ·Ē.
```

This is **exactly the `c + ∑ aₖ εₖ` shape of the two kernels**, so unbiasedness and
variance come for free:

- `𝔼[α̂] = α` via `expectation_const_add_weightedNoise (a) α` (`OLSVariance.lean:126`).
- `Var(α̂) = σ²·∑ₖ aₖ²` via `variance_const_add_weightedNoise (a) α σ`
  (`OLSVariance.lean:146`).

The closed form of `∑ aₖ²` is a three-line Finset computation using the two identities
already used by `weight_sq_ge_noiseGain` (`GaussMarkov.lean:156`):

```
∑ₖ aₖ² = ∑ₖ (1/n − wₖ Ē)² = 1/n − 2Ē/n·(∑ₖ wₖ) + Ē²·(∑ₖ wₖ²)
       = 1/n + Ē²/SS_E,
```

using `∑ₖ wₖ = 0` (`OLS.centered_sum_zero` `:64` scaled by `1/SS_E`) and
`∑ₖ wₖ² = 1/SS_E` (`OLS.olsSlope_noise_gain` `:128`). Hence the **classical, exact**

```
Var(α̂) = σ²·(1/n + Ē²/SS_E),
```

which collapses to `σ²/n` in the centered convention `Ē = 0` (the standard Boltzmann-plot
normalization used by `olsIntercept_stable_centered`, `ErrorBudget.lean:282`). Chebyshev
(§2.1, same lemma) then gives `μ {ω | δ ≤ |α̂ ω − α|} ≤ ofReal(σ²(1/n + Ē²/SS_E)/δ²)`.
The variance identity is grade **A / EXACT**; the tail from it (M4) is grade **A** but a
slackened bound (**REDUCED**, as M2). *(Reviewer-verified: `∑aₖ² = 1/n + Ē²/SS_E`
re-derived independently and correct; the only plumbing beyond the two cited kernels is
`mean`-additivity — `Finset.sum_add_distrib` — to split `mean ε` off the affine part.)*

### 2.4 Composition tail + union bound — CONFIRMED (grade B/C)

Candidate (c). The OLS density reader is `N = exp(b)·U/Fcal` with `b` the intercept
(`ErrorBudget.relDensity_le` `:261`), which proves the **exact deterministic** bound
`|b̂ − b| ≤ η ⟹ |N̂ − N| ≤ N·(exp η − 1)`. Read as an event inclusion via its
contrapositive with `η(τ) := log(1 + τ/N)` (so `N(exp η(τ) − 1) = τ`):

```
{ω | τ ≤ |N̂ ω − N|} ⊆ {ω | η(τ) ≤ |b̂ ω − b|},
```

and `b̂` is the intercept estimator `α̂` of §2.3, so Chebyshev gives a per-species density
tail `μ {τ ≤ |N̂ₛ − Nₛ|} ≤ ofReal(Var(α̂ₛ)/η(τ)²)`. The "any species off by ≥ τ" event
is closed by mathlib's finite union bound `measure_biUnion_finset_le`
(`OuterMeasure/Basic.lean:83`):

```
μ (⋃ₛ {ω | τ ≤ |N̂ₛ ω − Nₛ|}) ≤ ∑ₛ μ {ω | τ ≤ |N̂ₛ ω − Nₛ|}
                              ≤ ∑ₛ ofReal(Var(α̂ₛ)/η(τ)²).
```

Grade **B/C**: the union bound and the log-inversion are elementary, but it needs a
per-species probabilistic model (a family of intercept estimators over `σ : species`,
each with its own noise), which is new scaffolding rather than a reuse. The clean
downstream target composition tail (`|Cₛ|` via `composition_abs_sub_le_uniform` `:301`)
adds another inclusion layer; that final step is the C-grade part and should be deferred.

### 2.5 Sub-Gaussian upgrade — CONFIRMED-composable, stronger hypotheses — (grade B)

Candidate (d). The decisive inventory question — *does mathlib's sub-Gaussian API compose
with non-identically-weighted independent sums?* — is **YES** (grep-verified below). The
measure-level API (`Probability/Moments/SubGaussian.lean`) has all three pieces:

- **scaling:** `HasSubgaussianMGF.const_mul` (`:685`) — `X` sub-Gaussian `c` ⇒ `r·X`
  sub-Gaussian `r²·c`.
- **non-uniform independent sum:** `HasSubgaussianMGF.sum_of_iIndepFun` (`:768`) takes a
  *per-term* constant `c : ι → ℝ≥0` and yields sub-Gaussian constant `∑ᵢ cᵢ` — it does
  **not** require identical distribution. *(Reviewer-verified: signature at `:768` is
  `{X : ι → Ω → ℝ} (h_indep : iIndepFun X μ) {c : ι → ℝ≥0} …` — per-term `c`, confirmed.)*
- **tail:** `HasSubgaussianMGF.measure_ge_le` (`:704`),
  `μ.real {ω | ε ≤ X ω} ≤ exp(−ε²/(2c))`; and the packaged
  `measure_sum_ge_le_of_iIndepFun` (`:780`).

So if each `εₖ` is sub-Gaussian with constant `cₖ` (e.g. bounded noise via Hoeffding's
lemma `hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero` `:842`, constant
`((b−a)/2)²`), then `wₖ·εₖ` is sub-Gaussian `wₖ²cₖ` (`const_mul`), the family
`fun k ↦ wₖ·εₖ` is independent (`iIndepFun.comp` `Independence/Basic.lean:670` from
`iIndepFun ε`), and `∑ wₖ εₖ = β̂ − β` is sub-Gaussian `∑ wₖ²cₖ`. Homoscedastic
sub-Gaussian (`cₖ = c`) gives `∑ wₖ² c = c/SS_E`, hence the **exponential** one-sided
tail

```
μ.real {ω | δ ≤ betaHat ω − β} ≤ exp(−δ²·SS_E / (2c)),
```

an exponential upgrade of Chebyshev's polynomial `σ²/(SS_E δ²)`. Two-sided `|β̂ − β|`
needs the union of the two one-sided tails (apply also to `−(β̂ − β)` via
`HasSubgaussianMGF.neg` `:646`), doubling the RHS. Grade **B**, and it is a genuine
**hypothesis strengthening**: it requires `iIndepFun ε` (mutual independence) and
sub-Gaussianity (a distributional assumption), both strictly stronger than the
Gauss–Markov `L²` + pairwise-uncorrelated hypotheses of `OLSVariance`. It therefore lives
as a *separate* theorem, not a replacement — honest scope forbids advertising it under
the weaker model.

### 2.6 Markov / Chernoff-mgf direct route — EVALUATED-NOT-NEEDED

mathlib has raw Markov (`mul_meas_ge_le_lintegral₀`, `Integral/Lebesgue/Markov.lean:50`;
`meas_ge_le_lintegral_div` `:104`) and the mgf-Chernoff bound
`measure_ge_le_exp_mul_mgf` (`Moments/Basic.lean:429`). Neither is the right tool here:
the variance is already in hand as an *exact closed form* (`σ²/SS_E`), so Chebyshev
(`meas_ge_le_variance_div_sq`, which is itself the `p=2` Markov specialization) is the
direct, minimal route for the tail bounds; and the mgf-Chernoff bound needs an mgf
hypothesis we do not have without assuming sub-Gaussianity — at which point
`§2.5`'s packaged sub-Gaussian API is strictly more convenient. **Recommendation: use
`meas_ge_le_variance_div_sq` for M2/M4/M5/M6 and the `HasSubgaussianMGF` API for M7; do
not hand-roll Markov or `measure_ge_le_exp_mul_mgf`.**

### 2.7 CLT / delta-method / exact Gaussian law — REFUTED (see §5)

Asymptotic-normality confidence intervals, the delta-method variance of `T̂`, and the
exact (Gaussian) law of `β̂` are all evaluated and refused; the mathematics and the
mathlib status are in §5.

---

## 3. mathlib inventory

Everything the grade-A and grade-B milestones need is **present** (grep-verified against
`.lake/packages/mathlib`, v4.31.0). The one genuine absence is a finite-sample
CLT/Berry–Esseen, which only blocks the *refused* milestones.

| Needed | mathlib name + file (grep-verified) | Used by |
|---|---|---|
| Chebyshev (variance form) | `ProbabilityTheory.meas_ge_le_variance_div_sq` — `Probability/Moments/Variance.lean:399` | M2, M4, M5, M6 |
| Chebyshev (eVariance form) | `ProbabilityTheory.meas_ge_le_evariance_div_sq` — `…/Variance.lean:382` | fallback |
| `MemLp` of a finite sum | `MeasureTheory.memLp_finsetSum` — `…/LpSeminorm/TriangleInequality.lean:144` | M1 |
| `MemLp` under scaling | `MeasureTheory.MemLp.const_mul` — `…/LpSeminorm/SMul.lean:50` | M1 |
| `variance_nonneg` | `ProbabilityTheory.variance_nonneg` — `…/Variance.lean:202` | M2 (positivity) |
| Sub-Gaussian scaling | `…HasSubgaussianMGF.const_mul` — `Probability/Moments/SubGaussian.lean:685` | M7 |
| Sub-Gaussian non-uniform sum | `…HasSubgaussianMGF.sum_of_iIndepFun` — `…/SubGaussian.lean:768` (per-term `c:ι→ℝ≥0`) | M7 |
| Sub-Gaussian one-sided tail | `…HasSubgaussianMGF.measure_ge_le` — `…/SubGaussian.lean:704` | M7 |
| Sub-Gaussian packaged Hoeffding | `…measure_sum_ge_le_of_iIndepFun` — `…/SubGaussian.lean:780` | M7 |
| Sub-Gaussian negation (2-sided) | `…HasSubgaussianMGF.neg` — `…/SubGaussian.lean:646` | M7 |
| Hoeffding's lemma (bounded ⇒ subG) | `…hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero` — `…/SubGaussian.lean:842` | M7 |
| Independence of images | `ProbabilityTheory.iIndepFun.comp` — `Probability/Independence/Basic.lean:670` | M7 |
| Finite union bound | `MeasureTheory.measure_biUnion_finset_le` — `MeasureTheory/OuterMeasure/Basic.lean:83` | M6 |
| Markov (mgf-Chernoff) | `ProbabilityTheory.measure_ge_le_exp_mul_mgf` — `Probability/Moments/Basic.lean:429` | EVALUATED-NOT-NEEDED (§2.6) |
| Markov (raw) | `MeasureTheory.mul_meas_ge_le_lintegral₀` — `MeasureTheory/Integral/Lebesgue/Markov.lean:50` | EVALUATED-NOT-NEEDED |
| Measurable reciprocal | `measurable_inv`, `measurable_const_mul` | M5 (`tempOfSlope` meas.) |
| **Finite-sample CLT / Berry–Esseen** | **ABSENT.** Only `tendstoInDistribution_inv_sqrt_mul_sum_sub` — `Probability/CentralLimitTheorem.lean:123` (asymptotic, i.i.d., convergence-in-distribution). Searched: `Berry`, `Esseen` — absent. | blocks refused CI milestones (§5) |

Reusable **in-repo** lemmas (all build-verified; the whole ladder rests on these):

- `Alt.OLSVariance.olsSlope_estimator_eq` (`:100`) — `β̂ = β + ∑ wₖ εₖ`. **Central.**
- `Alt.OLSVariance.olsSlope_unbiased` (`:177`), `olsSlope_variance_eq` (`:203`).
- `Alt.OLSVariance.expectation_const_add_weightedNoise` (`:126`),
  `variance_const_add_weightedNoise` (`:146`) — the two weight-agnostic kernels reused
  for the intercept (§2.3).
- `OLS.centered_sum_zero` (`:64`), `OLS.olsSlope_noise_gain` (`:128`,
  `∑ wₖ² = 1/SS_E`) — the `∑ aₖ² = 1/n + Ē²/SS_E` computation.
- `OLS.olsIntercept` (`:52`), `OLS.mean` (`:40`), `OLS.olsWeight` (`:58`),
  `OLS.mean_affine` (`:75`).
- `ErrorBudget.temp_rel_error_eq` (`:199`, EXACT identity) — the temperature-channel spine.
- `ErrorBudget.relDensity_le` (`:261`, EXACT) — the M6 density-tail spine.
- `ErrorBudget.composition_abs_sub_le_uniform` (`:301`) — the M6 closure leg.
- Ambient `[IsProbabilityMeasure μ]` (`OLSVariance.lean:120`) — supplies `IsFiniteMeasure`
  for Chebyshev.

---

## 4. Milestone ladder

Ordered; grades A/B/C. Proposed home: a new `CflibsFormal/Alt/Concentration.lean`
(`namespace CflibsFormal.Alt`, `import CflibsFormal.Alt.OLSVariance` +
`CflibsFormal.ErrorBudget`), so it reuses the estimator, both kernels, and the
error-transfer identities without re-derivation. Every new result needs a
`docs/scope-tags.tsv` row (CI fails otherwise) and a non-vacuity witness in the
`OLSVariance`/`GaussMarkov` house style.

### M1 — `betaHat_memLp_two` (helper) · **A**
```
lemma betaHat_memLp_two [Nonempty ι] (E : ι → ℝ) (α β : ℝ) (ε : ι → Ω → ℝ)
    (hvar : 0 < ∑ k, (E k - mean E) ^ 2) (hL2 : ∀ k, MemLp (ε k) 2 μ) :
    MemLp (betaHat E α β ε) 2 μ
```
Scope: PURE-MATH · `—`. Rewrite by `funext (olsSlope_estimator_eq …)` to
`fun ω ↦ β + ∑ wₖ εₖ ω`, then `(memLp_const _).add (memLp_finsetSum …
(fun k _ ↦ (hL2 k).const_mul _))`. This is the L² obligation the Chebyshev lemma
demands; it is the same computation already inside
`variance_const_add_weightedNoise:151-153`. Prereq: none.

### M2 — `olsSlope_chebyshev` (the grade-A crown core) · **A**
```
theorem olsSlope_chebyshev [Nonempty ι] (E : ι → ℝ) (α β σ δ : ℝ) (ε : ι → Ω → ℝ)
    (hvar : 0 < ∑ k, (E k - mean E) ^ 2) (hδ : 0 < δ)
    (hL2 : ∀ k, MemLp (ε k) 2 μ)
    (huncorr : ∀ i j, i ≠ j → covariance (ε i) (ε j) μ = 0)
    (hhom : ∀ k, variance (ε k) μ = σ ^ 2) :
    μ {ω | δ ≤ |betaHat E α β ε ω - β|}
      ≤ ENNReal.ofReal (σ ^ 2 / ((∑ k, (E k - mean E) ^ 2) * δ ^ 2))
```
Scope: **REDUCED** · Aitken 1935. *(A Chebyshev tail bound carries irreducible slack — it
is not attainable — so it is classified like the other slackened bound `temp_rel_error_le`
(REDUCED), NOT like the exact identity `olsSlope_variance_eq` or the attainable
worst-case bound `relDensity_le` (both EXACT).)* Proof: `meas_ge_le_variance_div_sq
(betaHat_memLp_two …) hδ`, then rewrite `μ[betaHat] = β` (`olsSlope_unbiased`) inside the
set and `variance (betaHat …) = σ²/SS_E` (`olsSlope_variance_eq`) in the RHS
(`ENNReal.ofReal` congruence; `σ²/SS_E/δ² = σ²/(SS_E·δ²)` by `ring`/`div_div`). Prereq:
M1. Non-vacuity: reuse the `Fin 3`, `E = ![0,1,2]` witness family (cf.
`GaussMarkov.lean:213`) with a `Dirac`/uniform noise so the set is non-trivial and the
bound `< 1`.

### M3 — `alphaHat` + `alphaHat_variance_eq` (intercept estimator, candidate a) · **A**
```
noncomputable def alphaHat (E : ι → ℝ) (α β : ℝ) (ε : ι → Ω → ℝ) (ω : Ω) : ℝ :=
  olsIntercept E (fun k => α + β * E k + ε k ω)

theorem alphaHat_estimator_eq [Nonempty ι] … :
    alphaHat E α β ε ω = α + ∑ k, (1/(Fintype.card ι) - olsWeight E k * mean E) * ε k ω
theorem alphaHat_unbiased [Nonempty ι] … : μ[alphaHat E α β ε] = α
theorem alphaHat_variance_eq [Nonempty ι] … :
    variance (alphaHat E α β ε) μ
      = σ ^ 2 * (1/(Fintype.card ι) + (mean E) ^ 2 / (∑ k, (E k - mean E) ^ 2))
```
Scope: `alphaHat_estimator_eq` PURE-MATH `—`; `alphaHat_unbiased`/`alphaHat_variance_eq`
**EXACT** · Aitken 1935 (genuine identities, no slack). Proof: `alphaHat_estimator_eq` is
`olsIntercept` unfolded + `olsSlope_estimator_eq` + `mean_affine` (`OLS.lean:75`) +
`Finset.sum_add_distrib` (to split `mean ε`) + `ring`; then `alphaHat_unbiased` =
`expectation_const_add_weightedNoise (aₖ) α`, and `alphaHat_variance_eq` =
`variance_const_add_weightedNoise (aₖ) α σ` followed by the `∑ aₖ² = 1/n + Ē²/SS_E`
computation (`centered_sum_zero`, `olsSlope_noise_gain`; the Pythagorean-style algebra of
`weight_sq_ge_noiseGain`). Prereq: none (independent of M1/M2). **This is the
full classical form**; `Ē = 0` gives `σ²/n`.

### M4 — `alphaHat_chebyshev` (intercept tail) · **A**
```
theorem alphaHat_chebyshev [Nonempty ι] … (hδ : 0 < δ) … :
    μ {ω | δ ≤ |alphaHat E α β ε ω - α|}
      ≤ ENNReal.ofReal
          (σ ^ 2 * (1/(Fintype.card ι) + (mean E)^2 / (∑ k, (E k - mean E)^2)) / δ ^ 2)
```
Scope: **REDUCED** · Aitken 1935 (slackened Chebyshev tail, as M2). Proof: the `alphaHat`
analogue of M2 — an `alphaHat_memLp_two` helper (identical to M1 with weights `aₖ`) then
`meas_ge_le_variance_div_sq` + `alphaHat_unbiased` + `alphaHat_variance_eq`. Prereq: M3.

### M5 — `temp_tail_transfer` (crown completion, candidate b) · **B**
```
noncomputable def tempOfSlope (kB x : ℝ) : ℝ := -1 / (kB * x)   -- junk at x = 0
noncomputable def tempHat (kB E : ι → ℝ) … (ω) : ℝ := tempOfSlope kB (betaHat E α β ε ω)

theorem temp_tail_transfer [Nonempty ι] … {kB T ε : ℝ}
    (hkB : 0 < kB) (hT : 0 < T) (hε : 0 < ε)
    (hm : β = -1/(kB*T))                       -- Boltzmann-plot slope identification
    … :
    μ {ω | ε ≤ |tempHat … ω - T|}
      ≤ ENNReal.ofReal (σ^2 * kB^2 * T^2 * (T+ε)^2 / ((∑ k,(E k-mean E)^2) * ε^2))
```
Scope: **REDUCED** · Tognoni 2010 (the Chebyshev+inclusion bound carries slack, unlike
the EXACT identity `temp_rel_error_eq`). Two lemmas: (i) the deterministic interval
inclusion `{ε ≤ |τ(m̂)−T|} ⊆ {δ(ε) ≤ |m̂−m|}`, `δ(ε) = ε/(kB·T·(T+ε))` — the §2.2 `calc`,
closed by `nlinarith` given `δ(ε) < 1/(kB T)`; (ii) `measure_mono` of that inclusion,
then M2 at `δ = δ(ε)`. Needs `tempOfSlope` measurability
(`measurable_inv`/`const_mul`). Prereq: M1, M2. This is the theorem that closes the
"no probabilistic temperature statement" obstacle of §1.

### M6 — `composition_tail_union` (candidate c) · **B/C**
```
theorem density_tail_species …           -- per species, grade B
theorem composition_tail_union [Fintype κ] … {τ : ℝ} (hτ : 0 < τ) … :
    μ (⋃ s, {ω | τ ≤ |densityHat s ω - N s|})
      ≤ ∑ s, ENNReal.ofReal (Var(alphaHat_s) / (Real.log (1 + τ / N s))^2)
```
Scope: **REDUCED** · Tognoni 2010 / Ciucci 1999. Per-species leg (grade B): the
`relDensity_le` contrapositive `{τ ≤ |N̂ₛ−Nₛ|} ⊆ {η(τ) ≤ |α̂ₛ−α|}`,
`η(τ) = log(1+τ/Nₛ)`, then M4. Union (grade B): `measure_biUnion_finset_le`. Prereq: M3,
M4, plus a per-species random model (`σ : species → …`) — new scaffolding. The final
step to a *composition-fraction* tail via `composition_abs_sub_le_uniform` is the C-grade
tail; **defer it** until the density-tail union is green.

### M7 — `olsSlope_subGaussian_tail` (candidate d, stronger hypotheses) · **B**
```
theorem olsSlope_subGaussian_tail [Nonempty ι] … {c δ : ℝ≥0} (hδ : 0 ≤ (δ:ℝ))
    (hindep : iIndepFun ε μ) (hzero : ∀ k, μ[ε k] = 0)
    (hsubG : ∀ k, HasSubgaussianMGF (ε k) c μ) … :
    μ.real {ω | (δ:ℝ) ≤ |betaHat E α β ε ω - β|}
      ≤ 2 * Real.exp (-(δ:ℝ)^2 * (∑ k,(E k-mean E)^2) / (2 * c))
```
Scope: **REDUCED** · Aitken 1935 (a sub-Gaussian tail is a non-tight bound, like M2) —
with an **explicit honest note** that it assumes *mutual independence* `iIndepFun` and
*sub-Gaussian* noise, both strictly stronger than the Gauss–Markov (uncorrelated, `L²`)
model of M2. Proof: `hsubG k`→`const_mul` gives `wₖεₖ` sub-Gaussian `wₖ²c`;
`iIndepFun.comp` gives independence of `fun k ↦ wₖεₖ`; `sum_of_iIndepFun` gives `β̂−β`
sub-Gaussian `c·∑wₖ² = c/SS_E`; `measure_ge_le` (and its `neg` mirror, unioned) gives
the two-sided `2·exp(−δ²SS_E/(2c))`. Prereq: M1 (or independent). **Do not** present this
under M2's hypotheses (see §5).

**Immediate subset (a dev should attempt right after this dossier): M1, M2, M3, M4.**
All grade A, zero new mathlib, pure composition of the existing `OLSVariance` results
with `meas_ge_le_variance_div_sq`. M5–M7 are the grade-B follow-ups.

---

## 5. Refusals / traps

- **REFUSED — CLT-based / asymptotic confidence intervals for `β̂`, `T̂`, or `Cₛ`.**
  mathlib's only CLT is `tendstoInDistribution_inv_sqrt_mul_sum_sub`
  (`Probability/CentralLimitTheorem.lean:123`): convergence *in distribution* of the
  normalized sum of an **i.i.d.** sequence `X : ℕ → Ω → ℝ` to a Gaussian. Three
  independent blockers: (i) it is asymptotic (`Tendsto`), giving **no finite-`n`
  interval** — there is no Berry–Esseen/rate lemma (grep `Berry`, `Esseen`: absent);
  (ii) it needs **identically distributed** summands, but the OLS combination
  `∑ wₖ εₖ` has non-uniform weights `wₖ`, so it is not a normalized i.i.d. sum;
  (iii) it delivers a limit *law*, not a *tail bound* usable as `μ {…} ≤ …`. A
  "`P(|T̂−T| ≤ z_{α/2}·SE) ≈ 1−α`" statement is therefore unreachable and, worse,
  would be *unfaithful* (it is only approximate). **The exact `temp_rel_error_eq`
  identity + Chebyshev (M5) is the rigorous replacement** and should be the only
  temperature-uncertainty statement. Do not re-litigate.

- **REFUSED — delta-method variance of `T̂` (`Var(T̂) ≈ (dT/dβ)²·Var(β̂)`).** This is a
  first-order Taylor approximation; it needs `HasDerivAt` of the inversion and drops the
  higher-order remainder, so it is **not exact** and clashes with the honest-scope
  non-negotiable. It is also *unnecessary*: `temp_rel_error_eq` already gives the exact
  transfer with no linearization, and M5 turns it into an exact event inclusion. The
  repo's whole ErrorBudget philosophy (`temp_rel_error_eq` is EXACT, not a first-order
  estimate) forbids reintroducing the delta method.

- **REFUSED — the exact (Gaussian) law of `β̂`.** Even under Gaussian noise, stating
  "`β̂ ∼ Normal(β, σ²/SS_E)`" requires that a finite linear combination of independent
  Gaussians is Gaussian with the summed variance. mathlib's `gaussianReal`/`HasLaw`
  machinery exists but the "linear combination of independent Gaussians is Gaussian"
  closure lemma for a general finite weighted sum is not readily available
  (convolution-of-Gaussians is thin), so this is a large, separate infrastructure
  project — **out of scope for this frontier**. The sub-Gaussian tail (M7) captures the
  useful concentration content without the exact-law obligation.

- **TRAP — advertising the sub-Gaussian tail (M7) under the Gauss–Markov hypotheses.**
  `sum_of_iIndepFun` (`SubGaussian.lean:768`) *requires* `iIndepFun ε`; there is no
  sub-Gaussian/Bernstein sum lemma under mere pairwise uncorrelatedness. M2's headline
  strength is that it needs only `covariance = 0` (the classical Gauss–Markov
  hypothesis, per the `OLSVariance` docstring). M7 must state `iIndepFun` and
  sub-Gaussianity as explicit, prominent hypotheses and be annotated as a
  *strengthening* — never folded into or presented as improving M2.

- **TRAP — the `tempOfSlope` branch and measurability (M5).** `τ(x) = −1/(k_B x)` is only
  the physical temperature for `x < 0` (negative Boltzmann-plot slope); at `x = 0` it is
  junk. Two pitfalls: (i) prove `Measurable tempOfSlope` on all of `ℝ` (the junk value at
  `0` is fine — `inv` is measurable), do **not** try to restrict the domain inside the
  random variable; (ii) the interval-inclusion `calc` silently uses `δ(ε) < 1/(k_B T)`
  (so `m+δ < 0` and `τ` is increasing on the whole interval) — this is automatic
  (`ε/(T+ε) < 1`) but must be discharged explicitly or `nlinarith` will stall. Do not
  attempt a two-sided `|T̂−T|` bound by symmetry: the two temperature gaps
  `τ(m+δ)−T` and `T−τ(m−δ)` are **unequal** (denominators `1∓k_B Tδ`); `δ(ε)` is chosen
  from the *larger* (upper) gap, and the lower side then holds with strict slack.

- **TRAP — `ENNReal.ofReal` positivity side-conditions.** `meas_ge_le_variance_div_sq`
  returns an `ENNReal.ofReal` RHS; every rewrite of the real argument
  (`σ²/SS_E/δ² = σ²/(SS_E δ²)`, `∑aₖ² = 1/n + Ē²/SS_E`) must carry `0 < SS_E`,
  `0 < δ`, `0 < n` so `ENNReal.ofReal` congruence and `div_div` fire. `variance_nonneg`
  (`Variance.lean:202`) is needed for the non-negativity of the numerator. These are the
  only fiddly steps in the grade-A block.

- **NOT A DEAD END.** M1–M4 are settled: the mathematics is a direct composition, the
  mathlib is fully present and grepped (§3), and the reused kernels
  (`*_weightedNoise`, `olsSlope_variance_eq`, `olsSlope_noise_gain`) are already
  build-verified. The single best first milestone is **M2** (slope Chebyshev): once it
  lands, M4 (intercept tail) is its twin, M3 is the algebra that feeds it, and M5 is a
  deterministic event-inclusion on top. Prove M1→M2 first to de-risk the whole ladder.