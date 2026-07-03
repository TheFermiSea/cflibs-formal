# Frontier 01 — T-direction uniqueness of the nonlinear joint (T, N) fit

*Planning dossier. Not Lean code. Every current-state claim is anchored to a real declaration;
every mathlib claim is grepped and marked VERIFIED / ABSENT for mathlib v4.31.0.*

---

## 1. The formal obstacle

The joint nonlinear least-squares fit lives in `CflibsFormal/NonlinearLeastSquares.lean`. The
objective (line 82) is

```
nlObjective kB Fcal g E A obs (T, N) = ∑ k, (lineIntensity kB T N Fcal g E A k - obs k)^2
```

Current provable state, all anchored:

- **Existence** — `nlObjective_exists_min` (line 133): a minimizer exists on the compact box
  `Icc Tmin Tmax ×ˢ Icc Nmin Nmax` for **any** `obs`, by EVT (`IsCompact.exists_isMinOn`).
- **On-manifold value** — `nlObjective_onManifold_min` (line 153): if `obs` is the forward
  spectrum of `(T0, N0)`, the objective **value** at `(T0,N0)` is `0` and it is *a* minimizer.
  It does **not** claim `(T0,N0)` is the *unique* minimizer.
- **VARPRO N-collapse** — `lineIntensity_linear_in_N` (line 247), `profiledDensity` (line 258),
  `nlObjective_Nsection_decomposition` (line 291), `Nsection_minimizer_unique` (line 364): for
  each fixed `T`, the `N`-section is exactly quadratic and the profiled density
  `N̂(T) = (∑ c_k obs_k)/(∑ c_k²)` is its **unique** minimizer.

So the 2-D fit is provably 1-D: every joint minimizer's `N`-coordinate is pinned to `N̂(T̂)`. What
remains open is stated verbatim in the module's honest-scope note (lines 224–230):

> "The *`T`-direction* uniqueness remains genuinely open: `nlObjective` is non-convex in `T`
> through `exp(−E_k/(k_B T))` and the partition function `U(T)`, so the profiled-`T` objective
> `T ↦ nlObjective … (T, N̂(T))` may have multiple local minima."

**Precise obstacle.** There is currently *no* declaration asserting that the profiled objective
`Φ(T) := nlObjective kB Fcal g E A obs (T, N̂(T))` has a unique minimizer, nor even that the joint
minimizer is unique in the noise-free (on-manifold) case. `nlObjective_onManifold_min` pins the
minimum *value* but not the *argmin*. The frontier is: **make a true, provable uniqueness
statement about the `T`-coordinate of the joint minimizer.**

Adjacent exact-fit results we can lean on (all in `Identifiability.lean` / `ForwardMap.lean`):
`lineIntensity_ratio_closed_form` (line 86), `temperature_identifiability` (line 122),
`temperature_degeneracy` (line 156), `lineIntensity_pos` (`ForwardMap.lean:74`). These give
*injectivity* of the ratio observation under distinct energies, but say nothing about the argmin of
a *least-squares* residual off-manifold.

---

## 2. Mathematical landscape

### 2.1 The right normal form (a genuine refinement of the seeded framing)

Reparametrize `u := 1/(k_B T)` (seeded direction (a)). Unit-density intensities become
`c_k(T) = Fcal·A_k·g_k·exp(−E_k u)/U(T)`. Write `d_k(u) := w_k·exp(−E_k u)` with
`w_k := Fcal·A_k·g_k > 0`. Then `c(T) = (Fcal/U(T))·d(u)`, i.e. **`c(T)` and `d(u)` differ by the
common positive scalar `Fcal/U(T)`.**

The profiled residual is the projection residual of `obs` onto the ray through `c(T)`:

```
Φ(T) = ‖obs‖² − ⟨c(T), obs⟩² / ‖c(T)‖².
```

The Rayleigh quotient `⟨c,obs⟩²/‖c‖²` is **invariant under positive rescaling of `c`**, so the
factor `Fcal/U(T)` — including the whole partition function — **cancels exactly**:

```
Φ(T) = ‖obs‖² − ⟨d(u), obs⟩² / ‖d(u)‖²,   d_k(u) = w_k·exp(−E_k u).
```

This **refines the seeded problem statement**: the module's docstring names *both* `exp(−E_k/k_BT)`
*and* `U(T)` as sources of non-convexity, but `U(T)` provably drops out of the *profiled* objective.
The only surviving nonlinearity is the exponential-sum Rayleigh quotient — precisely the object of
the VARPRO / exponential-fitting literature. **This cancellation is itself a worthwhile first
lemma** (it removes the scariest-looking term from the open problem).

### 2.2 Seeded direction (b) — TWO LINES — CONFIRMED, and it collapses to a closed form

For `ι = Fin 2` with `c_0, c_1 > 0`, let `t := c_1/c_0`. Standard projection algebra (verified by
hand, `ring`-level):

```
Φ₂(T) = (obs_1 − obs_0·t)² / (1 + t²),        t = t(T) = (w_1/w_0)·exp((E_0 − E_1)·u).
```

Derivation: `‖obs‖²·(1+t²) − (obs_0 + t·obs_1)² = (obs_1 − obs_0·t)²` (an exact Lagrange-style
identity, pure `ring`). Two consequences:

1. **`t(T)` is strictly monotone in `T`** iff `E_0 ≠ E_1` (it is `exp` of a strictly monotone
   argument in `u = 1/(k_BT)`). Under `E_0 = E_1` it is constant — the analogue of
   `temperature_degeneracy`.
2. `Φ₂(T) = 0 ⟺ t(T) = obs_1/obs_0`, which (by strict monotonicity) has **at most one** solution
   in `T`. And `dΦ₂/dt ∝ −(obs_1 − obs_0 t)(obs_0 + obs_1 t)`, so on `t > 0` with `obs_0,obs_1 > 0`
   the residual is **unimodal** (strictly decreasing then increasing, single interior min at
   `t = obs_1/obs_0`). Hence over any interval the box-constrained minimizer is unique.

This is the tractable theorem and it **connects directly to `temperature_identifiability`**: on the
manifold `obs = (N0·c_0(T0), N0·c_1(T0))`, so `obs_1/obs_0 = t(T0)` and
`Φ₂(T) = obs_0²·(t(T0) − t(T))²/(1+t(T)²)`, which is `0` at `T0` and strictly positive elsewhere.
The exact-fit uniqueness of `temperature_identifiability` is thereby upgraded to a *least-squares*
uniqueness — with **no box-endpoint case analysis** needed on-manifold.

### 2.3 Seeded direction (d) — monotone ratio structure — CONFIRMED, subsumed

Direction (d) asks whether `T ↦` (ratio of two profiled residuals) is monotone under distinct
energies. The §2.2 closed form settles it: the two-line profiled residual is an *explicit* function
of the single strictly-monotone quantity `t(T)`, so any monotonicity/unimodality question reduces to
elementary calculus on `(obs_1 − obs_0 t)²/(1+t²)`. `lineIntensity_ratio_closed_form`
(`Identifiability.lean:86`) already supplies `t(T)` in closed form. Direction (d) is not a separate
milestone; it is the mechanism inside §2.2.

### 2.4 Seeded direction (c) — LOCAL / near-manifold uniqueness — REFINED to a *global* on-manifold result

The seeded hope was a local strong-convexity / implicit-function argument. There is a **stronger and
cleaner** fact available for *any* number of lines with at least one distinct-energy pair:

On-manifold `obs = N0·c(T0)`, so `obs ∝ d(u0)`. By Cauchy–Schwarz,
`⟨d(u),obs⟩² ≤ ‖d(u)‖²‖obs‖²` with **equality iff `d(u) ∥ obs ∥ d(u0)`**. Since all `d_k > 0`,
proportionality of `d(u)` and `d(u0)` forces, on any pair `(i,j)`,
`exp(−E_i u)·exp(−E_j u0) = exp(−E_j u)·exp(−E_i u0)`, i.e. `(E_i − E_j)(u − u0) = 0`. With one
distinct-energy pair this gives `u = u0`, hence `T = T0`. So **`T0` is the *unique global*
minimizer of the profiled residual on-manifold** (residual `0` only there) for `m ≥ 2` lines — not
merely a local minimum. This is a genuine strengthening of `nlObjective_onManifold_min`
(value → unique argmin). Local uniqueness is then a corollary, and the calculus second-derivative
machinery the seed proposed is unnecessary.

### 2.5 Seeded direction (a), continued — the m ≥ 3 OFF-manifold case is likely NON-unique (partial refutation)

For `m ≥ 3` lines and noisy off-manifold `obs`, global uniqueness of the `T`-argmin is
**expected false**, and a general uniqueness theorem should *not* be attempted:

- Fitting sums/ratios of exponentials by least squares is the textbook ill-posed, **multimodal**
  problem. Varah, *On fitting exponentials by nonlinear least squares* [VERIFIED: web —
  UBC TR-82-02, later SIAM J. Sci. Stat. Comput. 6 (1985) 30] documents "many low-lying local
  minima" and complicated level-set topology. General nonlinear-regression multimodality is
  surveyed in Golub & Pereyra, *Separable nonlinear least squares: the variable projection method
  and its applications* [VERIFIED: web — Inverse Problems 19 (2003) R1], building on Golub &
  Pereyra, *The differentiation of pseudoinverses and nonlinear least squares problems whose
  variables separate* [VERIFIED: web — SIAM J. Numer. Anal. 10 (1973) 413–432].
- **Caveat that keeps hope alive for structured cases:** the CF-LIBS profiled problem fits a
  **single** scalar `u` that scales *all* exponents by a common factor — it is *not* the classical
  Prony problem of fitting several *independent* unknown rates, where the worst multimodality
  lives. Here `d(u)` traces a 1-parameter curve (a scaled moment curve of a Chebyshev system). For
  `m = 2` the curve's direction is a monotone angle ⇒ unimodal (§2.2). For `m ≥ 3` the direction is
  a space curve and the Rayleigh quotient along it *can* have multiple local maxima depending on
  `obs`; total-positivity of the exponential system bounds sign changes but does **not** obviously
  bound the number of local minima of the projection. **Honest verdict:** treat `m ≥ 3`
  off-manifold global uniqueness as open/false; the provable wins are two-line (§2.2), on-manifold
  (§2.4), and near-manifold (§4, M4).

Physics-side, all forward identities are the repo's approved citations: the two-line Boltzmann ratio
is Ciucci et al. (1999) [VERIFIED: repo — `Identifiability.lean:79,368`] and the calibration-free
`(T,N)` inversion is Tognoni et al. (2010) [VERIFIED: repo — `NonlinearLeastSquares.lean`] — both
already cited in `NonlinearLeastSquares.lean` and `Identifiability.lean`. The VARPRO / exponential
references above are numerical-analysis sources *not* on the repo's approved list; they are
[VERIFIED: web] for use in *this dossier* but **must be re-checked before appearing in any Lean
docstring**.

---

## 3. mathlib inventory (v4.31.0)

Needed for the milestone ladder, each grepped:

- **Cauchy–Schwarz for `Finset` sums** — `sum_mul_sq_le_sq_mul_sq`.
  VERIFIED: `.lake/packages/mathlib/Mathlib/Algebra/Order/BigOperators/Ring/Finset.lean:159`
  (`(∑ i in s, f i * g i)^2 ≤ (∑ i in s, f i^2) * (∑ i in s, g i^2)`). Gives the *inequality*
  `Φ ≥ 0`.
- **Strict Cauchy–Schwarz / equality condition** — inner-product form
  `inner_lt_norm_mul_iff_real` VERIFIED:
  `.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Basic.lean:847`
  (`⟪x,y⟫_ℝ < ‖x‖*‖y‖ ↔ ‖y‖•x ≠ ‖x‖•y`); also `norm_inner_eq_norm_iff` (Basic.lean:731) and
  `inner_eq_norm_mul_iff_real` (Basic.lean:790). These are on `InnerProductSpace`; using them on the
  bare `Finset`-sum objective requires bridging to `EuclideanSpace ℝ (Fin m)`.
  NOTE: a *strict* equality condition packaged directly for `sum_mul_sq_le_sq_mul_sq` is
  **ABSENT** (searched: `sum_mul_sq_le_sq_mul_sq` + `eq`/`iff`/`lt` in
  `Algebra/Order/BigOperators`, `Analysis/MeanInequalities`). For `m = 2` this is not needed — the
  identity `‖obs‖²(1+t²) − ⟨·⟩² = (obs_1 − obs_0 t)²` is pure `ring`. For general `m` (M3) the
  cleanest route is the elementary Lagrange identity
  `‖d‖²‖obs‖² − ⟨d,obs⟩² = ∑_{i<j}(d_i obs_j − d_j obs_i)²` proved as a private lemma, avoiding the
  `EuclideanSpace` bridge entirely.
- **`exp` strict monotonicity / injectivity** — VERIFIED:
  `Real.exp_lt_exp` and `Real.exp_le_exp`
  (`.lake/packages/mathlib/Mathlib/Analysis/Complex/Exponential.lean:311,315`); `exp_strictMono`
  (`Analysis/Complex/Exponential.lean:298`); `Real.exp_eq_exp` already used in
  `Identifiability.lean:140`.
- **`StrictMono.injective`, `StrictMono.lt_iff_lt`** — VERIFIED:
  `.lake/packages/mathlib/Mathlib/Order/Monotone/Basic.lean:402,376`. For the `t(T)` monotone
  bijection.
- **Second-derivative / convexity tests** (only if a calculus route to M4 is taken) —
  `strictConvexOn_of_deriv2_pos` VERIFIED
  (`.lake/packages/mathlib/Mathlib/Analysis/Convex/Deriv.lean:266`); `convexOn_of_deriv2_nonneg`
  (Deriv.lean:214); `StrictConvexOn.eq_of_isMinOn` VERIFIED
  (`.lake/packages/mathlib/Mathlib/Analysis/Convex/Function.lean:1067`, "a strictly convex
  function has at most one minimizer"). **Caveat:** the profiled objective is *not* globally convex,
  so `StrictConvexOn.eq_of_isMinOn` is usable only on a sub-interval where `Φ'' > 0` is proven — and
  computing `Φ''` symbolically through the Rayleigh quotient is heavy. The algebraic (non-calculus)
  route of §2.2/§2.4 is strongly preferred and needs *none* of this.
- **Existing repo infrastructure reused**: `profiledDensity`, `nlObjective_Nsection_decomposition`,
  `Nsection_minimizer_unique` (`NonlinearLeastSquares.lean`); `lineIntensity_ratio_closed_form`,
  `temperature_identifiability` (`Identifiability.lean`); `lineIntensity_pos`,
  `lineIntensity_linear_in_N`.

**No missing mathlib infrastructure for M1–M3.** Bessel/special functions are *not* needed
(`U(T)` cancels). M4 optionally touches `Deriv`/`Convex` API, all present.

---

## 4. Milestone ladder

Scope tags follow the repo vocabulary (`docs/scope-tags.tsv`: PURE-MATH / EXACT / REDUCED /
APPROXIMATION). Every new theorem needs a `scope-tags.tsv` row (CI gate).

### M1 — Two-line profiled residual closed form + on-manifold uniqueness  *(tractability A)*
Prereqs: none beyond existing module.
Sketch:
```lean
-- partition-free ratio (reuse lineIntensity_ratio_closed_form)
theorem profiledResidual_two_closed_form (kB Fcal T : ℝ) (g E A obs : Fin 2 → ℝ)
    (hc : 0 < ∑ k, (lineIntensity kB T 1 Fcal g E A k)^2) :
    nlObjective kB Fcal g E A obs (T, profiledDensity kB Fcal g E A obs T)
      = (obs 1 - obs 0 * (lineIntensity kB T 1 Fcal g E A 1
                          / lineIntensity kB T 1 Fcal g E A 0))^2
        / (1 + (lineIntensity kB T 1 Fcal g E A 1 / lineIntensity kB T 1 Fcal g E A 0)^2)
-- on-manifold: unique global T-minimizer
theorem profiledT_two_onManifold_unique (hkB : 0 < kB) (hg : ∀ k, 0 < g k)
    (hFcal : 0 < Fcal) (hA : ∀ k, 0 < A k) (hN0 : 0 < N0) (hE : E 0 ≠ E 1)
    (hobs : ∀ k, obs k = lineIntensity kB T0 N0 Fcal g E A k) (hT0 : 0 < T0) (hT : 0 < T) :
    nlObjective … (T, N̂(T)) = 0 ↔ T = T0
```
Tag: PURE-MATH (closed form) + EXACT (on-manifold uniqueness). This is `Fin 2`, fully algebraic
(`ring` + `Real.exp_lt_exp` + `div` lemmas); no compactness, no calculus. **Best first milestone.**

### M2 — Full joint two-line on-manifold uniqueness `(T,N) = (T0,N0)`  *(tractability B)*
Prereqs: M1, `Nsection_minimizer_unique`.
Sketch: any joint minimizer has `N = N̂(T)` (existing), `Φ₂(T)=0 ⟺ T=T0` (M1), and
`N̂(T0) = N0` (profiled density of an exactly-parallel `obs`). Conclude the joint minimizer is
*exactly* `(T0,N0)` and unique.
```lean
theorem joint_two_onManifold_unique … :
    IsMinOn (nlObjective …) S p ∧ p ∈ S → p = (T0, N0)
```
Tag: EXACT. Upgrades `nlObjective_onManifold_min` from "value 0" to "unique argmin"; the direct
least-squares analogue of `temperature_identifiability` on two lines. Small assembly over M1.

### M3 — m-line on-manifold uniqueness of the profiled T  *(tractability B)*
Prereqs: private Lagrange identity `‖d‖²‖obs‖² − ⟨d,obs⟩² = ∑_{i<j}(d_i obs_j − d_j obs_i)²`.
Sketch: `Φ(T) = ‖obs‖² − ⟨c(T),obs⟩²/‖c(T)‖² ≥ 0`, `= 0 ⟺` proportional `⟺ T = T0` given one
distinct-energy pair (`Real.exp` injectivity). Works for any `[Fintype ι]` with `∃ i j, E i ≠ E j`.
```lean
theorem profiledT_onManifold_unique [Nonempty ι] (i j : ι) (hE : E i ≠ E j) … :
    nlObjective … (T, N̂(T)) = 0 ↔ T = T0
```
Tag: EXACT. The general-m strengthening of `nlObjective_onManifold_min`. Hardest sub-step is the
Lagrange identity over `Finset` pairs (elementary but fiddly); alternatively bridge to
`EuclideanSpace` and use `inner_lt_norm_mul_iff_real` (both viable).

### M4 — Near-manifold local uniqueness (small noise)  *(tractability B/C)*
Prereqs: M3.
Sketch: for `obs = forward(T0,N0) + η` with `‖η‖` small, `Φ` has a strict local min near `T0` that
is the unique minimizer in a neighborhood. Cleanest via continuity/perturbation of M3's strict
inequality (the `∑_{i<j}(·)²` gap is bounded below by a positive constant off a neighborhood of
`T0`, and `‖η‖` small keeps `T0`-region the winner) rather than a second-derivative test. If a
`Φ'' > 0` route is taken instead, needs `strictConvexOn_of_deriv2_pos` (VERIFIED) + a symbolic
Hessian through the Rayleigh quotient — heavier. Grade B if perturbation route, C if calculus route.
Tag: REDUCED (holds in a data-dependent neighborhood, not globally).

### M5 — Two-line box-constrained off-manifold uniqueness  *(tractability B)*
Prereqs: M1.
Sketch: off-manifold, `Φ₂(t) = (obs_1 − obs_0 t)²/(1+t²)` is unimodal in `t` (single interior min
at `t = obs_1/obs_0` when `obs_0,obs_1 > 0`; monotone otherwise), and `t(T)` is a strict-mono
bijection onto `[t(Tmax), t(Tmin)]`. So the box-constrained minimizer is unique (interior or a
single endpoint). Needs a short case split on whether `obs_1/obs_0` lands in the achievable `t`-range
and the sign of `obs`. Tag: REDUCED (`Fin 2`, box). This is the first genuinely *off-manifold*
`T`-uniqueness result — the real content of the frontier at the two-line level.

### M6 — (Investigate, likely negative) m ≥ 3 off-manifold non-uniqueness witness  *(tractability B for the counterexample; the positive theorem is C/open)*
Sketch: construct explicit `m = 3` energies + `obs` with two distinct profiled-`T` local minima
(mirroring `temperature_not_identifiable_of_degenerate`'s style of an exhibited counterexample),
formally documenting that global `T`-uniqueness is **false** in general and that the strict-mode
solver's multi-start / refusal logic is justified. Tag: EXACT (a counterexample is exact). This
closes the frontier *honestly* rather than leaving a false impression that uniqueness generalizes.

---

## 5. Risks & dead ends

- **Do not attempt global m ≥ 3 off-manifold uniqueness** (§2.5). It is the classic multimodal
  exponential-fitting problem; a general theorem is very likely false and would burn a session.
  M6's counterexample is the correct disposition.
- **Calculus route to unimodality is a trap.** Differentiating `Φ(T)` through
  `exp(−E_k/(k_BT))/U(T)` and the Rayleigh quotient produces a large symbolic derivative; proving
  its sign in Lean is far harder than the algebraic `(obs_1 − obs_0 t)²/(1+t²)` closed form. Prefer
  the algebra. `strictConvexOn_of_deriv2_pos` exists but `Φ` is not globally convex, so it only
  applies on a sub-interval you must first cut out — more work, not less.
- **`profiledDensity` denominator.** Every profiled statement needs
  `0 < ∑ c_k²` — already supplied by `profiledDensity_denom_pos`
  (`NonlinearLeastSquares.lean:320`, needs `0 < g, Fcal, A`). Not a blocker, but every milestone
  must thread it.
- **Sign of `obs`.** Real spectra have `obs_k ≥ 0`, but the *theorems* should either assume
  `obs_k > 0` (physical) or handle the general-sign unimodality case split (M5). Overclaiming
  uniqueness for arbitrary-sign `obs` in `Fin 2` is a subtle dead end (the interior min at
  `t = obs_1/obs_0` requires `obs_1/obs_0 > 0`).
- **EuclideanSpace bridging (M3).** If the Lagrange-identity route stalls, the
  `inner_lt_norm_mul_iff_real` route requires translating the bare `Finset` sum into
  `EuclideanSpace ℝ (Fin m)` norms/inner products (`‖·‖ = sqrt(∑ ·²)`), which adds `Real.sqrt`
  bookkeeping. Keep the elementary Lagrange identity as the primary plan.
- **Not worth it?** No — M1–M3 are cheap, directly strengthen an existing headline
  (`nlObjective_onManifold_min`), and land the frontier's honest core. Only M4+ carry real cost.

---

## 6. Recommendation

**Attack now, starting with M1.** The partition function `U(T)` — the intimidating half of the
stated non-convexity — provably cancels from the profiled objective (§2.1), and the two-line profiled
residual has the fully explicit closed form `Φ₂ = (obs_1 − obs_0·t)²/(1+t²)` with `t(T)` strictly
monotone under distinct energies (§2.2). This is elementary Lean (`ring` + `Real.exp_lt_exp`),
needs no new mathlib, reuses `profiledDensity` / `lineIntensity_ratio_closed_form`, and immediately
yields on-manifold `T`-uniqueness — upgrading the exact-fit `temperature_identifiability` to a
least-squares statement.

**Single best first milestone (M1):** prove the two-line profiled-residual closed form
`Φ₂(T) = (obs_1 − obs_0·t(T))²/(1 + t(T)²)` and, on-manifold, that `Φ₂(T) = 0 ⟺ T = T0` (unique
global `T`-minimizer). Tractability **A**.

Then M2 (joint two-line on-manifold, B) and M3 (general-m on-manifold, B) in the same push, M5 for
the first off-manifold uniqueness (B), and M6 to honestly fence off the m ≥ 3 off-manifold case.
Defer M4 (near-manifold local) unless the perturbation route proves cheap; avoid the calculus route
entirely.
