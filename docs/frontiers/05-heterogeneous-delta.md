# Per-line heterogeneous δ in the aliasing channel — the multi-line OLS density reader under per-line atomic-data error

Frontier: bound the **intercept-based multi-line OLS density reader** `Alt.olsDensity`
(and its composition `Alt.leastSquaresComposition`) under **per-line atomic-data errors**
`δ_k` on `(g_k, A_k, E_k)`, mirroring what `AtomicDataPerturbation.lean` already did for the
single-line `Classic.classicDensity` reader.

---

## 1. The formal obstacle

Two families exist; the multi-line-reader × atomic-data-error cell between them is empty.

**Single-line reader under atomic-data error — CLOSED.**
`CflibsFormal/AtomicDataPerturbation.lean` fully covers `Classic.classicDensity`:
- `classicDensity_aliasing` (line 190, EXACT): `N̂ = N · responseFactor(g,E,A) / responseFactor(g',E',A')`.
- `classicDensity_aliasing_error` (line 212, REDUCED): lumped `|ρ' − ρ| ≤ δ·ρ` ⇒ `|N̂ − N| ≤ N·δ/(1−δ)`.
- `classicDensity_aliasing_error_channels` (line 235), `classicComposition_atomicData_error` (line 294).

**Multi-line reader under NOISE — CLOSED (slope leg only).**
`CflibsFormal/ErrorBudget.lean` handles the OLS *slope* under per-line noise:
- `olsSlope_stable_hetero` (line 365): `|Δβ| ≤ (∑_k |E_k − Ē|·ε_k)/SS_E` for a per-line budget `ε : ι → ℝ`.
- `temp_rel_error_hetero` (line 401): composes that into the temperature leg.
- `relDensity_le` (line 276): `|b̂ − b| ≤ η ⇒ |N̂ − N| ≤ N·(exp η − 1)` for `N = exp(b)·U/Fcal`.
- `composition_abs_sub_le_uniform` (line 316) / `composition_target_sufficient` (line 340): per-species δ ⇒ ΔC.

**The empty cell.** The multi-line *density* reader is
```
Alt.olsDensity kB T Fcal g E A I
  = Real.exp (olsIntercept E (fun k => Real.log (I k / (g k * A k)))) * partitionFunction kB T g E / Fcal
```
(`CflibsFormal/Alt/LeastSquares.lean:107`). Its only correctness lemma is on the *true* spectrum:
`olsDensity_recovers` (line 139) — `olsDensity … (lineIntensity … g E A) = N`. There is **no**
theorem of the shape "analyst inverts with wrong `(g',E',A')` ⇒ bounded `|N̂ − N|`". Concretely,
grepping the repo:
- `olsIntercept_stable` matches exactly one declaration — `olsIntercept_stable_centered`
  (`ErrorBudget.lean:297`), which handles only a **global** scalar `ε` (`hδ : ∀ k, |ŷ_k − y_k| ≤ eps`,
  a single `eps : ℝ`) in the **centered** convention `mean E = 0`. There is **no**
  `olsIntercept_stable_hetero` (per-line `ε_k`), the intercept mirror of `olsSlope_stable_hetero`.
- No declaration mentions `olsDensity` and any of {`aliasing`, atomic-data `δ`, `g'`, `A'`}.

So the precise unproved statement (A-value channel, the physically dominant one):
> Emit `I_k = lineIntensity kB T N Fcal g E A k` with TRUE data; let the analyst read `olsDensity`
> with a WRONG transition-probability vector `A'` (correct `g, E`). Then `|N̂ − N| ≤ (bound in the δ_k)`.

Nothing anchors this today.

---

## 2. Mathematical landscape

### The ordinate-error observation (seeded direction (a)) — CONFIRMED, and sharper than seeded.

The Boltzmann-plot ordinate the reader fits is `ŷ_k = log(I_k/(g_k A'_k))`. With the true
spectrum `I_k = Fcal·N·g_k A_k·exp(−E_k/k_BT)/U`, and using `log_div`/`log_mul`,
```
ŷ_k = [log(Fcal·N/U) − E_k/(k_BT)]  +  log((g_k A_k)/(g'_k A'_k))
    =  y_k^true                     +  δ_k,       δ_k := log((g_k A_k)/(g'_k A'_k)).
```
So a per-line atomic-data error is **exactly an additive per-line ordinate error** `δ_k` — the same
object `ε_k` that `olsSlope_stable_hetero` / a hetero intercept bound consume. Seeded direction (a) is
confirmed.

**Refinement (stronger than the seed).** The seed proposes routing `δ_k` through a hetero intercept
bound and `abs_exp_sub_one_le`. But `Alt.olsDensity` is *affine-linear in the ordinate*, so the
intercept shift is an **exact identity**, no centering and no bound needed at the identity stage.
Since `olsIntercept E (y + δ) = olsIntercept E y + olsIntercept E δ` (linearity of `mean` and, via
`olsSlope_eq_centered`, of `olsSlope`), and `olsIntercept E y^true = log(Fcal·N/U)`
(`olsIntercept_of_forward`, `Alt/LeastSquares.lean:128`):
```
N̂ = exp(olsIntercept E ŷ)·U/Fcal
   = exp(olsIntercept E y^true)·exp(olsIntercept E δ)·U/Fcal
   = N · exp(olsIntercept E δ).                       [U' = U, i.e. A-only errors]
```
This is the **OLS mirror of `classicDensity_aliasing`**. In the centered convention (`mean E = 0`,
the repo's standard Boltzmann-plot normalization) `olsIntercept E δ = mean δ = (1/n)∑_k log((g_k A_k)/(g'_k A'_k))`,
so the multiplicative bias is the **geometric mean** of the per-line data ratios. This is a genuinely
new, physically meaningful statement: the single-line reader carries the *raw* ratio `ρ_true/ρ_wrong`
(`classicDensity_aliasing`), whereas OLS carries its **log-domain average** — the formal reason the
multi-line reader is more robust to a bad line (a single outlier `δ_k` is divided by `n`). Note this
is still a **bias**, not variance (see §5): if the `δ_k` are systematically one-signed, the geometric
mean does not shrink.

### The partition-function subtlety — CONFIRMED and scoped.

`olsDensity` uses the analyst's `g, E` in **two** further places: the abscissa `E` of the fit and the
factor `U = partitionFunction kB T g E`. Three sub-channels result:
1. **A-channel** (`g,E` correct, `A'` wrong): only the ordinate shifts; `U' = U` since `U` is
   `A`-independent. ⇒ the clean EXACT identity above. *Physically the dominant CF-LIBS atomic-data
   error is transition-probability (`A`) error — Tognoni 2010 [VERIFIED: repo verified-citation list].*
2. **g-channel** (`g'≠g`, `E`=E): ordinate shifts **and** `U(T;g',E) ≠ U(T;g,E)` — a second
   multiplicative factor `U'/U`, exactly as in `classicDensity_aliasing_error_channels`.
3. **E-channel** (`E'≠E`): the analyst fits `ŷ_k` (affine in the *true* `E`) against the *wrong*
   abscissa `E'`. The fit is no longer exact (nonzero residual), the design/weights change, and the
   intercept couples to the slope shift. Hardest; likely deferred.

### Literature (verification marks)

- Tognoni, Cristoforetti, Legnaioli, Palleschi, "Calibration-Free LIBS: State of the art,"
  *Spectrochim. Acta B* **65** (2010) 1–14 — atomic-parameter (chiefly transition-probability)
  uncertainty is the dominant accuracy contributor once the plasma is characterized.
  [VERIFIED: repo verified-citation list; already cited across `AtomicDataPerturbation.lean`.]
- Ciucci et al., *Appl. Spectrosc.* **53** (1999) 960 — intercept-borne concentration; the substrate
  of `olsDensity`. [VERIFIED: repo verified-citation list.]
- The "OLS averages atomic-data errors in the log domain (geometric mean)" reading is a *derived*
  observation from the affine structure, not a literature claim; docstring it as such, not as cited.
  [UNVERIFIED as a literature statement — present as an algebraic consequence, not a citation.]

---

## 3. mathlib inventory (mathlib v4.31.0, `.lake/packages/mathlib/Mathlib`)

Everything the A-channel / g-channel chain needs is present; the two genuinely-missing pieces are
**repo lemmas**, not mathlib gaps.

VERIFIED (mathlib):
- `Real.log_le_sub_one_of_pos : 0 < x → log x ≤ x − 1` — `Analysis/SpecialFunctions/Log/Basic.lean:306`.
  (The kernel of the log-transfer bound `|log r| ≤ δ/(1−δ)`.)
- `Real.log_div` (Basic.lean:137), `Real.log_mul` (132), `Real.log_inv` (142) — the ordinate split.
- `Real.exp_log : 0 < x → exp (log x) = x` (Basic.lean:58); `Real.exp_add` (used in-repo by
  `relDensity_le`); `Real.add_one_le_exp` (`Analysis/SpecialFunctions/Exp.lean`, used in-repo).
- `Real.log_one` (106), `Real.log_nonneg` (212), `Real.log_nonpos` (221),
  `Real.log_le_log_iff` (146), `Real.log_lt_log` (154) — monotonicity plumbing.
- `Finset.abs_sum_le_sum_abs` — `Algebra/Order/BigOperators/Group/Finset.lean:287`.

VERIFIED (repo, reuse verbatim):
- `abs_exp_sub_one_le {x eta} (|x| ≤ eta) : |exp x − 1| ≤ exp eta − 1` — **`ErrorBudget.lean:259`**
  (public). NOTE: the task brief said "now public in `Analysis.lean`" — that is inaccurate;
  `Analysis.lean` has only `strictAntiOn_div_of_deriv_num_neg`. The usable public form lives in
  `ErrorBudget.lean` (a second, private `abs_exp_sub_one_le (x) : … ≤ exp|x| − 1` sits in
  `AtomicDataPerturbation.lean:374`). Plan against the `ErrorBudget` one.
- `relDensity_le` (ErrorBudget.lean:276), `composition_abs_sub_le_uniform` (316),
  `composition_target_sufficient` (340), `olsSlope_sub_eq` (OLS.lean:102),
  `olsSlope_eq_centered` (OLS.lean:87), `mean`/`olsSlope`/`olsIntercept` (OLS.lean:40/46/52),
  `Alt.olsDensity_recovers` (Alt/LeastSquares.lean:139), `Alt.olsIntercept_of_forward` (128).

ABSENT — must be built in-repo (not mathlib deficiencies):
- A ready `|log r| ≤ δ/(1−δ)` for `|r − 1| ≤ δ, δ < 1`. Searched: `log_le`, `abs_log`,
  `one_sub_inv_le_log`, `log_le_sub_one`. Only the one-sided `log_le_sub_one_of_pos` exists; the
  two-sided `|·|` bound is a 4-line derivation from it (`log r ≤ r−1 ≤ δ`; `−log r = log r⁻¹ ≤ r⁻¹−1 ≤ δ/(1−δ)`).
- A per-line **heteroscedastic intercept-stability** lemma (`olsIntercept_stable_hetero`). Only the
  global-`ε` centered `olsIntercept_stable_centered` exists (ErrorBudget.lean:297).

No exotic infrastructure (no Bessel, no special functions beyond `log`/`exp`) is required.

### Where the theorem lives (import discipline)

`Alt.olsDensity` is in namespace `CflibsFormal.Alt` (`Alt/LeastSquares.lean`), so a **core** module
cannot import it. `ErrorBudget.lean` imports only `CompositionRobustness` + `OLS` (no `Alt`), so a
**new Alt module** can import BOTH `CflibsFormal.Alt.LeastSquares` and `CflibsFormal.ErrorBudget`
with no cycle. Plan:
- Pure-algebra helpers (`olsIntercept_stable_hetero`, `log`-transfer) → add to **core** `ErrorBudget.lean`
  (next to `olsSlope_stable_hetero`, `olsIntercept_stable_centered`) — keeps them reusable and
  `Mathlib`+OLS-only.
- Physics aliasing theorems (`olsDensity_aliasing_*`, composition corollary) → new module
  **`CflibsFormal/Alt/OLSAtomicDataPerturbation.lean`** importing `Alt.LeastSquares` + `ErrorBudget`,
  then registered in `CflibsFormal.lean` and (per AGENTS.md §"A new theorem is done only when")
  each result gets a `docs/scope-tags.tsv` row or the docs-sync CI gate fails.

---

## 4. Milestone ladder

Convention throughout: `δ_k` denotes the per-line atomic-data relative error; `ε_k` the induced
additive ordinate error `|log((g_k A_k)/(g'_k A'_k))|`.

**M0 — `olsIntercept_stable_hetero` (PURE-MATH; core `ErrorBudget.lean`). Grade A.**
Sketch (centered convention, the repo standard):
```
theorem olsIntercept_stable_hetero [Nonempty ι] {E y yHat eps : ι → ℝ}
    (hcent : mean E = 0) (hδ : ∀ k, |yHat k - y k| ≤ eps k) :
    |olsIntercept E yHat - olsIntercept E y| ≤ (∑ k, eps k) / (Fintype.card ι)
```
Proof: verbatim mirror of `olsIntercept_stable_centered` (ErrorBudget.lean:297) with per-line `eps k`
in the final `Finset.sum_le_sum`. Prereqs: none. *This is the missing intercept twin of
`olsSlope_stable_hetero`.*

**M1 — log-ratio transfer lemma (PURE-MATH; core, `ErrorBudget.lean` or `Analysis.lean`). Grade A.**
```
lemma abs_log_ratio_le {a a' δ : ℝ} (ha : 0 < a) (ha' : 0 < a')
    (hδ1 : δ < 1) (hpert : |a' - a| ≤ δ * a) : |Real.log (a / a')| ≤ δ / (1 - δ)
```
Proof: `r := a/a' ∈ [1/(1+δ), 1/(1−δ)]`; `log r ≤ r − 1 ≤ δ/(1−δ)` and `−log r = log r⁻¹ ≤ r⁻¹ − 1 ≤ δ`
via `Real.log_le_sub_one_of_pos` (twice) + `Real.log_inv`. Prereqs: none.

**M2 — `olsDensity_aliasing_A` (EXACT; new `Alt/OLSAtomicDataPerturbation.lean`). Grade B.**
The conceptual anchor — OLS mirror of `classicDensity_aliasing`.
```
theorem olsDensity_aliasing_A [Nonempty ι] {kB T N Fcal : ℝ} {g E A A' : ι → ℝ}
    (hg : ∀ k, 0 < g k) (hN : 0 < N) (hFcal : 0 < Fcal)
    (hA : ∀ k, 0 < A k) (hA' : ∀ k, 0 < A' k)
    (hvar : 0 < ∑ k, (E k - mean E) ^ 2) :
    Alt.olsDensity kB T Fcal g E A' (fun k => lineIntensity kB T N Fcal g E A k)
      = N * Real.exp (olsIntercept E (fun k => Real.log (A k / A' k)))
```
Proof: (i) pointwise `ŷ_k = y_k^true + log(A_k/A'_k)` via `log_div`/`log_mul` (all args > 0);
(ii) `olsIntercept E (y+δ) = olsIntercept E y + olsIntercept E δ` from linearity (`mean` + `olsSlope_eq_centered`);
(iii) `exp(olsIntercept E y^true)·U/Fcal = N` (repackage `olsDensity_recovers`/`olsIntercept_of_forward`);
(iv) `Real.exp_add`. Scope EXACT: no approximation, `U`-independent-of-`A` is genuine. Prereqs: none
(does not need M0/M1). Grade B only for assembly length — no hard step.
*Corollary worth stating (EXACT):* centered `mean E = 0` ⇒ bias `= exp(mean_k log(A_k/A'_k))` (geometric mean).

**M3 — `olsDensity_aliasing_A_error` (REDUCED; same module). Grade B.**
```
theorem olsDensity_aliasing_A_error [Nonempty ι] {kB T N Fcal : ℝ} {g E A A' : ι → ℝ} {δ : ι → ℝ}
    (…positivity…) (hcent : mean E = 0)
    (hδ1 : ∀ k, δ k < 1) (hpert : ∀ k, |A' k - A k| ≤ δ k * A k) :
    |Alt.olsDensity … A' (forward) - N| ≤ N * (Real.exp ((∑ k, δ k / (1 - δ k)) / Fintype.card ι) - 1)
```
Proof: M2 ⇒ `N̂ − N = N·(exp(olsIntercept E δ) − 1)`; centered ⇒ `olsIntercept E δ = mean δ`;
`|mean δ| ≤ (∑ ε_k)/n` (M0) with `ε_k ≤ δ_k/(1−δ_k)` (M1); then `abs_exp_sub_one_le`
(ErrorBudget.lean:259). Scope REDUCED (per-line `δ_k` lumped into a mean; `U'=U`, `E'=E`). Prereqs: M0, M1, M2.
*Alternatively route through `relDensity_le` directly for the `exp(b)·U/Fcal` shape.*

**M4 — `olsComposition_atomicData_error` (REDUCED; same module). Grade B.**
Feed the per-species M3 density bound (uniform envelope `Φ`, cap `N s ≤ Nmax`) into
`composition_abs_sub_le_uniform` (ErrorBudget.lean:316), exactly as
`classicComposition_atomicData_error` (AtomicDataPerturbation.lean:294) feeds
`composition_abs_sub_le_bound`. Yields `|Ĉ_s − C_s| ≤ (card κ + 1)·(Nmax·Φ)/Ŝ`. Prereqs: M3.
Grade B (positivity of the recovered densities + assembly).

**M5 — `olsDensity_aliasing_error_channels` (REDUCED; g+U two-channel, `E'=E`). Grade B.**
`g'≠g` adds the factor `U(T;g',E)/U(T;g,E)`; mirror `classicDensity_aliasing_error_channels`
(AtomicDataPerturbation.lean:235) by combining the exp-of-intercept channel with the `U'/U` channel
via the existing two-factor pattern (`abs_two_ratio_sub_le` is private to `AtomicDataPerturbation.lean`;
either re-expose it or re-derive the 6-line ratio bound). Prereqs: M2/M3 shape + a `U`-mismatch bound.

**M6 — E-channel, `E'≠E` (REDUCED/APPROXIMATION; hard). Grade C.**
Wrong abscissa ⇒ nonzero fit residual, design/weight change, slope↔intercept coupling. Needs a new
"intercept sensitivity to abscissa perturbation" analysis with no current repo analogue. Likely a
separate frontier; **defer**.

---

## 5. Risks & dead ends

- **Bias vs variance (seeded direction (b)) — must be stated, or the result is misleading.**
  `olsSlope_stable_hetero` and the `Alt.OLSVariance`/`GaussMarkov` layer treat `ε_k` as zero-mean
  **noise** (variance). Atomic-data errors are **systematic**: `δ_k = log((g_k A_k)/(g'_k A'_k))` is a
  fixed, correlated offset, not a random draw. The M2–M4 bounds are **worst-case bias** bounds. The
  "more lines ⇒ better" intuition (the module already flags it as *statistical*, ErrorBudget.lean
  docstring lines 44–55) does **not** transfer: the geometric mean divides an outlier by `n`, but a
  uniformly-signed systematic error is not averaged away (`exp(mean δ) ≠ 1` even as `n → ∞`). Docstring
  language plan: "REDUCED, systematic (bias) not statistical (variance); the deterministic worst case
  over the fixed per-line data errors; no variance-reduction / min-line-count claim." This exactly
  parallels the honest-scope note already in `ErrorBudget.lean`.
- **Centered-convention hypothesis.** M3/M4 use `mean E = 0`. This is WLOG on the energy origin (a
  shift is absorbed into `U`/intercept) and is the repo's stated Boltzmann-plot normalization
  (`olsIntercept_stable_centered`), but the docstring must say so rather than silently assume it. The
  EXACT M2 needs **no** centering (`olsIntercept E δ` is exact); only the closed-form *bound* does.
- **M6 could be genuinely awkward, not just hard.** With `E'≠E` the recovered "density" is no longer a
  clean multiplicative bias — the residual makes it a projection artifact. Bounding it may require an
  approximation (APPROXIMATION scope), and may not be worth it if `E` is the best-known atomic datum
  in practice. Not a soundness risk to stop at M5.
- **No mathematical falsity risk** in M0–M5: every step is an equality or a monotone bound over
  positive quantities; the EXACT identity is a cancellation, verifiable by a `norm_num` non-vacuity
  witness (mirror the `nvAdp*`/`nvHet*` witnesses already in both source files).

---

## 6. Recommendation

**Attack now.** The A-channel chain (M0→M1→M2→M3→M4) is high-value, low-risk, and reuses the existing
`relDensity_le` / `abs_exp_sub_one_le` / `composition_abs_sub_le_uniform` machinery verbatim — it is
the exact multi-line twin of the already-closed single-line `classicDensity_aliasing*` family, and it
finally populates the empty (multi-line reader × atomic-data error) cell. M5 (g+U) is a natural
follow-up in the same module; M6 (E-channel) should be spun out as its own frontier or deferred.

**Single best first milestone: M2 `olsDensity_aliasing_A` (EXACT).** It is the conceptual anchor
(mirrors `classicDensity_aliasing`), is self-contained (needs neither M0 nor M1), and delivers the
genuinely new physics content — OLS carries the *geometric-mean* (log-domain average) of the per-line
atomic-data ratios, the formal statement of why the multi-line reader tolerates a bad line that the
single-line reader cannot. Land M2 with a `norm_num` non-vacuity witness, then M0+M1 immediately unlock
the REDUCED bound M3 and the composition corollary M4.
