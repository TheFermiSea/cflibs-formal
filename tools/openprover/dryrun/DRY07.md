# Frontier 07 — The Ladenburg–Reiche sharp constant for the Lorentzian curve of growth

**Goal.** Upgrade the existing two-sided `√τ` *envelope* on the Lorentzian equivalent width to the
**sharp asymptotic equality** `W(τ) / √τ → 2` (the slope-½ damping-wing constant), i.e. prove

```
Filter.Tendsto (fun τ => equivWidth lorentzian τ / Real.sqrt τ) Filter.atTop (nhds 2).
```

The number `2` is the exact Ladenburg–Reiche wing constant in this module's units. This dossier
confirms the seeded bessel-free DCT route, evaluates the limit integral by hand to `2√π` (⇒ `C = 2`),
and shows **every** mathlib lemma the route needs already exists in v4.31.0 — no Bessel functions
required.

---

## 1. The formal obstacle

`CflibsFormal/EquivalentWidth.lean` defines (line 75)

```
noncomputable def equivWidth (φ : ℝ → ℝ) (τ : ℝ) : ℝ := ∫ x, (1 - Real.exp (-(τ * φ x)))
```

and the normalized Lorentzian profile (line 337)

```
noncomputable def lorentzian (x : ℝ) : ℝ := (1 / Real.pi) * (1 / (1 + x ^ 2))
```

with `lorentzian_integral : ∫ x, lorentzian x = 1` (line 355). The current thick-regime results are a
**non-sharp two-sided envelope**, for `τ ≥ 8π`:

- `equivWidth_lorentzian_sqrt_lower` (line 404):
  `(1 - Real.exp (-1)) / (2 * Real.sqrt (2 * Real.pi)) * Real.sqrt τ ≤ equivWidth lorentzian τ`
  — lower constant `c₋ = (1-e⁻¹)/(2√(2π)) ≈ 0.1261`, proved by dropping the integrand to the
  constant `1 - e⁻¹` on the core plateau `[1, √(τ/2π)]` (`lorentzian_tau_ge_one`, line 364).
- `equivWidth_lorentzian_sqrt_upper` (line 487):
  `equivWidth lorentzian τ ≤ 4 / Real.sqrt Real.pi * Real.sqrt τ`
  — upper constant `c₊ = 4/√π ≈ 2.257`, proved by splitting `ℝ = [-a,a] ∪ [-a,a]ᶜ` at `a = √(τ/π)`,
  bounding the core by `vol = 2a` and the tails by `τ·(tail mass) ≤ 2a`.
- `equivWidth_lorentzian_sqrt_two_sided` (line 565): the conjunction.

**The obstacle.** These are inequalities with a factor-`≈18` gap (`c₋ ≈ 0.126` vs `c₊ ≈ 2.257`); the
docstrings explicitly defer "the sharp Ladenburg–Reiche asymptotic *equality* (the exact slope-½
constant)". What is missing is (i) the *existence* of the limit `W(τ)/√τ`, and (ii) its *exact value*.
Neither the plateau lower bound nor the crude split upper bound can be sharpened to an equality — the
integrand must be resolved on the *whole* line simultaneously via a `τ`-dependent rescaling, which is
a different proof technique (dominated convergence after change of variables) than anything in the
file today. The nearest existing template is `equivWidth_weakLine` (line 149), which is DCT at *fixed*
integration variable; the sharp constant needs DCT on a *rescaled* variable.

---

## 2. Mathematical landscape

### The classical result
For a Lorentz (pressure-broadened) absorption line the curve of growth is the **Ladenburg–Reiche
function** `L(x) = x·e^{-x}·(I₀(x) + I₁(x))` (Ladenburg & Reiche 1913; standard in Mihalas,
*Stellar Atmospheres* 2nd ed. 1978, and the LIBS curve-of-growth treatment of Gornushkin 1999
[VERIFIED: repo's approved citation list]). Its **strong-line asymptotic** is `L(x) → √(2x/π)`, giving
the equivalent width `W ~ 2√(γ·S·u)` (HWHM `γ`, line strength `S`, column `u`). This is the slope-½
"square-root wing" branch. [UNVERIFIED — the exact `L(x)` form and its `√(2x/π)` tail should be
re-checked against a primary source before quoting in a Lean docstring; the *value* of the constant is
independently re-derived below and does not depend on trusting this formula.]

### Direction (a) — the bessel-free DCT route [CONFIRMED by hand]
In this module's units `L(x) = (1/π)/(1+x²)` (⇒ HWHM `γ = 1`, unit area) and `τ` plays the role of the
strong-line parameter `S·u`, so the classical asymptotic predicts `W ~ 2√(1·τ) = 2√τ`, i.e. `C = 2`.
The seeded substitution reproduces this without Bessel functions. Put `x = √(τ/π)·u` and `β := τ/π`:

```
τ·L(x) = τ·(1/π)/(1 + (τ/π)u²) = β/(1 + β u²) = 1/(1/β + u²)  --->  1/u²   as τ→∞.
```

Change of variables (Jacobian `√(τ/π)`):

```
W(τ) = √(τ/π) · ∫_ℝ (1 - exp(-β/(1+βu²))) du,     so   W(τ)/√τ = (1/√π) · ∫_ℝ g_β(u) du,
```

with `g_β(u) = 1 - exp(-1/(1/β + u²))`. Pointwise `g_β(u) → g_∞(u) := 1 - exp(-1/u²)` (a.e., all
`u ≠ 0`). Dominated convergence (domination below) gives

```
lim_{τ→∞} W(τ)/√τ = (1/√π) · ∫_ℝ (1 - exp(-1/u²)) du = (1/√π) · I.
```

**Evaluating `I = ∫_ℝ (1 - exp(-1/u²)) du = 2√π` [CONFIRMED, two independent ways].**

*Route A (IBP + inverse substitution).* By evenness `I = 2J`, `J = ∫_{0}^{∞}(1 - e^{-1/u²}) du`. Let
`f(u) = u·(1 - e^{-1/u²})` (with `f(0)=0` by continuity). Then

```
f'(u) = (1 - e^{-1/u²}) - 2·e^{-1/u²}/u²,   so   (1 - e^{-1/u²}) = f'(u) + 2·e^{-1/u²}/u².
```

Integrate over `(0,∞)`. The `f'` part telescopes: `∫_{Ioi 0} f' = lim_{u→∞} f - f(0) = 0 - 0 = 0`,
because `0 ≤ f(u) = u(1-e^{-1/u²}) ≤ u·(1/u²) = 1/u → 0` (squeeze, using `1 - e^{-y} ≤ y`) and
`f(0)=0`. The remaining part, by the substitution `w = 1/u`, is `∫_{Ioi 0} e^{-1/u²}/u² du =
∫_{Ioi 0} e^{-w²} dw = √π/2`. Hence `J = 0 + 2·(√π/2) = √π`, and `I = 2J = 2√π`.

*Route B (Tonelli + Gaussian scaling), as a cross-check.* Write `1 - e^{-1/u²} = ∫_0^1 (1/u²)
e^{-s/u²} ds`; swap (nonneg integrand); the inner integral `∫_ℝ (1/u²)e^{-s/u²} du = √(π/s)`; then
`I = ∫_0^1 √(π/s) ds = 2√π`. ✓ Same value.

Therefore `lim W(τ)/√τ = (1/√π)·2√π = 2`. **The sharp constant is `C = 2`.** Sanity: `2` lies strictly
inside the proven envelope `[c₋, c₊] = [0.126, 2.257]`, as required. **Direction (a) is CONFIRMED**;
the seeded candidate `I = 2√π ⇒ limit 2` is exactly right.

### Direction (b) — mathlib inventory for route (a) [CONFIRMED: all present, see §3]
Every step above maps to a lemma already in mathlib v4.31.0: the DCT-over-`atTop`, the full-line
change of variables, the improper FTC-2 (`∫_{Ioi} f' = m - f(a)`), the `x ↦ 1/x` substitution
(`integral_comp_rpow_Ioi`, `p = -1`), and the half-line Gaussian `∫_{Ioi 0} e^{-x²} = √π/2`. Route (a)
needs **no new mathlib**.

### Direction (c) — the FULL Ladenburg–Reiche function [REFUTED as a near-term target]
Formalizing `L(x) = x·e^{-x}(I₀(x)+I₁(x))` exactly requires modified Bessel functions `I₀, I₁`, which
are **ABSENT from mathlib v4.31.0** (§3). Building `besselI` with its integral representation,
recurrences, and large-argument asymptotics is an **XL upstream project** on its own. The key insight:
**the sharp *constant* does not need the full function.** Route (a) extracts the `τ→∞` limit directly
from the integral, bypassing Bessel entirely. So (c) is correctly deferred; only the asymptotic
constant (via (a)) is in reach.

---

## 3. mathlib inventory

Every claim grepped under `.lake/packages/mathlib/Mathlib`. The file already `import Mathlib`, so all
of these are in scope.

| Need | Status |
|------|--------|
| DCT along a filter | **VERIFIED** `tendsto_integral_filter_of_dominated_convergence` `[l.IsCountablyGenerated]` (`MeasureTheory/Integral/DominatedConvergence.lean:68`) — **already used** by `equivWidth_weakLine`. |
| `atTop` on `ℝ` is countably generated (the DCT typeclass arg) | **VERIFIED** `atTop_isCountablyGenerated_of_archimedean` (`Order/Filter/AtTopBot/Archimedean.lean:147`); `ℝ` is `Archimedean`. |
| Full-line linear change of variables | **VERIFIED** `MeasureTheory.integral_comp_mul_left g a : ∫ x, g (a*x) = |a⁻¹| • ∫ y, g y` and `integral_comp_div g a : ∫ x, g (x/a) = |a| • ∫ y, g y` (`MeasureTheory/Measure/Haar/NormedSpace.lean:151,167`). |
| Half-line Gaussian | **VERIFIED** `integral_gaussian_Ioi (b) : ∫ x in Ioi 0, exp (-b*x^2) = √(π/b)/2` (`.../Gaussian/GaussianIntegral.lean:318`); `b=1 ⇒ √π/2`. Full-line `integral_gaussian (b) : ∫ x, exp(-b*x^2) = √(π/b)` (:228). |
| `Γ(1/2) = √π` (seed asked) | **VERIFIED** `Real.Gamma_one_half_eq : Real.Gamma (1/2) = √π` (`.../GaussianIntegral.lean:335`) — present, but **not on the critical path**; `integral_gaussian_Ioi` supplies `√π/2` directly without going through `Γ`. |
| Improper FTC-2 (evaluate `∫_{Ioi} f'`) | **VERIFIED** `integral_Ioi_of_hasDerivAt_of_tendsto (hcont : ContinuousWithinAt f (Ici a) a) (hderiv : ∀ x ∈ Ioi a, HasDerivAt f (f' x) x) (f'int : IntegrableOn f' (Ioi a)) (hf : Tendsto f atTop (𝓝 m)) : ∫ x in Ioi a, f' x = m - f a` (`.../IntegralEqImproper.lean:789`). Crucially `hderiv` is required only on the **open** `Ioi a`, and the left endpoint needs only `ContinuousWithinAt` — this absorbs the removable singularity of `e^{-1/u²}` at `u=0`. |
| `x ↦ 1/x` substitution on `Ioi 0` | **VERIFIED** `integral_comp_rpow_Ioi g (hp : p ≠ 0) : ∫ x in Ioi 0, (|p|·x^(p-1)) • g (x^p) = ∫ y in Ioi 0, g y` (`.../IntegralEqImproper.lean:1133`). With `p = -1`: `∫ x in Ioi 0, x^(-2) • g(x⁻¹) = ∫ y in Ioi 0, g y`; take `g = fun y => exp(-y²)` ⇒ `∫_{Ioi 0} e^{-1/x²}/x² = √π/2` in essentially one line (modulo `rpow`↔`pow` bridging for `x>0`). |
| Dominating function `2/(1+u²)` integrable | **VERIFIED** `integrable_inv_one_add_sq : Integrable fun x ↦ (1+x²)⁻¹` (`.../ImproperIntegrals.lean:269`) — **already used** in the file; `.const_mul 2` gives `2/(1+u²)`. Full-line value `integral_univ_inv_one_add_sq = π` (:287) if needed. |
| `1 - e^{-y} ≤ y`, `exp` monotone, `√` algebra | **VERIFIED** `Real.one_sub_le_exp_neg`, `Real.exp_le_exp`, `Real.sqrt_div'`, `Real.sq_sqrt` — all **already used** in this file. |
| Modified Bessel `I₀, I₁` (for the FULL L–R function) | **ABSENT from mathlib v4.31.0** (searched: `besselI`, `BesselI`, `bessel_I`, `Bessel`). Only "Bessel's *inequality*" appears (`InnerProductSpace/Orthonormal.lean`), which is unrelated. ⇒ the full curve is upstream-XL; route (a) avoids it. |

**The clean domination bound.** For every `β > 0` and all `u`:
`g_β(u) = 1 - exp(-1/(1/β+u²)) ≤ 2/(1+u²)`.
Proof (two cases): `|u| ≤ 1`: `g_β ≤ 1 ≤ 2/(1+u²)` since `1+u² ≤ 2`. `|u| > 1`: `g_β ≤ 1/(1/β+u²) ≤
1/u² ≤ 2/(1+u²)` since `1+u² ≤ 2u²`. This is a strict improvement over the seeded `min(1, 1/u²)` — it
reuses the file's existing `integrable_inv_one_add_sq` witness and needs no `min`-integrability lemma.

---

## 4. Milestone ladder

Proposed scope tag for all new declarations: **EXACT** (within the model), citation *Gornushkin 1999 /
Ladenburg–Reiche* — matching the existing `equivWidth_lorentzian_*` rows in `docs/scope-tags.tsv`. Each
new theorem needs a `docs/scope-tags.tsv` row or CI fails (per repo memory).

**M1 — Scaling identity (grade A).**
```
theorem equivWidth_lorentzian_scaled (τ : ℝ) (hτ : 0 < τ) :
    equivWidth lorentzian τ
      = Real.sqrt (τ / Real.pi) * ∫ u, (1 - Real.exp (-((τ/Real.pi) / (1 + (τ/Real.pi) * u^2))))
```
Prereq: none. Uses `integral_comp_mul_left` with `a = √(τ/π)` and the algebraic rewrite
`τ·lorentzian(√(τ/π)·u) = β/(1+βu²)`. Self-contained, low-risk; unblocks everything. *(Grade A.)*

**M2 — The limit integral `I = 2√π` (grade B, the analytic crux).**
```
theorem integral_one_sub_exp_neg_inv_sq :
    (∫ u, (1 - Real.exp (-(1 / u^2)))) = 2 * Real.sqrt Real.pi
```
Prereq: none (independent; can be proved first as a de-risking spike). Sub-steps, all from §3:
(i) evenness ⇒ `= 2 · ∫_{Ioi 0}`; (ii) set `f u = u·(1 - e^{-1/u²})`, show `HasDerivAt` on `Ioi 0`
and `ContinuousWithinAt` at `0`; (iii) `Tendsto f atTop (𝓝 0)` by squeeze `0 ≤ f u ≤ 1/u`;
(iv) `integral_Ioi_of_hasDerivAt_of_tendsto ⇒ ∫_{Ioi 0} f' = 0`; (v) `integral_comp_rpow_Ioi (p=-1)`
+ `integral_gaussian_Ioi (b=1) ⇒ ∫_{Ioi 0} e^{-1/u²}/u² = √π/2`; (vi) assemble `J = √π`, `I = 2√π`.
Friction: the chain-rule `HasDerivAt` of `e^{-1/u²}` and `IntegrableOn f' (Ioi 0)` (difference of two
integrable pieces). No missing API — grade B, ~1–2 sessions. *(Grade B.)*

**M3 — DCT convergence of the rescaled integral (grade B).**
```
theorem tendsto_integral_g_beta :
    Filter.Tendsto (fun τ => ∫ u, (1 - Real.exp (-((τ/Real.pi)/(1+(τ/Real.pi)*u^2)))))
      Filter.atTop (nhds (∫ u, (1 - Real.exp (-(1/u^2)))))
```
Prereq: M2 supplies the integrability/value of the limit integrand (or prove integrability standalone
via the same `2/(1+u²)` bound). Uses `tendsto_integral_filter_of_dominated_convergence` with
`bound = fun u => 2/(1+u²)`, the `atTop` countable-generation instance, the domination bound of §3,
and the pointwise limit (arithmetic of `Tendsto` + continuity of `exp`). This mirrors the *structure*
of `equivWidth_weakLine` but over `atTop` with a rescaled family. *(Grade B — mechanical but long.)*

**M4 — The sharp asymptotic (grade A, given M1–M3).**
```
theorem equivWidth_lorentzian_sqrt_sharp :
    Filter.Tendsto (fun τ => equivWidth lorentzian τ / Real.sqrt τ) Filter.atTop (nhds 2)
```
Prereq: M1, M2, M3. Combine: `W/√τ = (1/√π)·(rescaled integral)` (M1 + `√(τ/π)/√τ = 1/√π`), which by
M3 tends to `(1/√π)·I`, and by M2 `I = 2√π`, so the limit is `(1/√π)·2√π = 2`. Just continuity of
multiplication and `Filter.Tendsto.const_mul`. *(Grade A.)*

**M5 (optional) — Sharpen the envelope docstrings / add an `IsEquivalent` form (grade A).**
Restate as `W(τ) ~[atTop] fun τ => 2 * Real.sqrt τ` via `Asymptotics.IsEquivalent` (mathlib has
`Asymptotics.isEquivalent_iff_tendsto_one` and friends), and update the `equivWidth_lorentzian_sqrt_*`
docstrings to reference the now-proven sharp constant. Cosmetic but closes the honest-scope note.

---

## 5. Risks & dead ends

- **`IntegrableOn f' (Ioi 0)` in M2** is the most fiddly obligation: `f'(u) = (1-e^{-1/u²}) -
  2e^{-1/u²}/u²`. Both summands are integrable on `Ioi 0` (the first is dominated by `2/(1+u²)`; the
  second is the `√π/2` substitution integrand), but assembling `Integrable.sub` with the right
  `IntegrableOn` restrictions is where a session can be spent. Not a blocker — no missing lemma.
- **`HasDerivAt` of `u ↦ e^{-1/u²}` on `Ioi 0`**: chain rule through `u ↦ -(u²)⁻¹` (deriv `2/u³`) then
  `Real.exp`. Standard `HasDerivAt.exp` / `HasDerivAt.inv`; watch the `u ≠ 0` side conditions (we are
  on the open `Ioi 0`, so `u > 0` is available). Grade-A-to-B friction, not a dead end.
- **`rpow` vs `pow` bookkeeping** in `integral_comp_rpow_Ioi` (`x^(-2)` as `rpow` vs `/u²` as `pow`):
  a `Real.rpow_natCast` / `Real.rpow_neg` rewrite on `x > 0`. Purely mechanical.
- **Wrong-constant risk**: mitigated — `C = 2` is derived twice (IBP route + Tonelli route) and must
  land inside the *already-proven* interval `[0.126, 2.257]`; it does. A slip would be caught by that
  bracket and by the non-vacuity `example`s the repo style demands.
- **Dead end to avoid**: do **not** attempt the full `L(x) = x e^{-x}(I₀+I₁)` — Bessel functions are
  ABSENT (§3) and are an XL upstream build. The frontier is the *constant*, not the *function*; route
  (a) is the whole point of staying bessel-free.
- **Worth-it check**: HIGH value. This turns the module's flagship thick-regime result from a factor-18
  envelope into an exact slope-½ law `W ~ 2√τ`, the textbook Ladenburg–Reiche wing constant, with zero
  new axioms and no upstream dependency. It is the natural capstone of the `equivWidth_lorentzian_*`
  development.

---

## 6. Recommendation

**Attack now.** Route (a) is fully supported by mathlib v4.31.0 — the DCT, the change of variables, the
improper FTC-2, the `x↦1/x` substitution, and the half-line Gaussian are all present and (for DCT and
`integrable_inv_one_add_sq`) already exercised in this very file. There is **no upstream blocker**.

**Single best first milestone: M1, the scaling identity** `equivWidth_lorentzian_scaled` (grade A). It
is self-contained, reuses `integral_comp_mul_left`, carries the entire proof's algebraic core
(`τ·L(√(τ/π)·u) = β/(1+βu²)`), and de-risks the ladder before the two grade-B integrals. Immediately
after, run M2 (`I = 2√π`) as an **independent spike** — it is the only genuinely hard piece, so proving
it early collapses the frontier's remaining risk; M3 and M4 are then mechanical.

**Effort tier: L.** One deep theorem resting on three substantial lemmas (two grade-B integrals + a
DCT), ~3–4 focused sessions, but no new mathlib infrastructure. (The *full* Ladenburg–Reiche function
would be XL — it needs Bessel functions upstream — and is explicitly out of scope here.)
