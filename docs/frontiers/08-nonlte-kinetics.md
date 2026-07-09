# Frontier 08 — Non-LTE / collisional-radiative kinetics

*Planning dossier. No Lean edited; every current-state claim anchored to a real
declaration, every mathlib claim grepped against `.lake/packages/mathlib`
(v4.31.0). Value = RIGOR: the physics is grounded in McWhirter 1965 /
Cristoforetti 2010 / Griem 1997 and the CF-LIBS corpus; the tractability grades
are backed by the inventory in §3.*

*Reviewer note (adversarial pass): inventory spot-checks all pass for every
A-milestone-load-bearing lemma; M1/M2/M4/M5 algebra re-derived by hand and the
named ErrorBudget/Boltzmann signatures re-read. Two corrections applied — (a) M3's
optional Tendsto plumbing names are UNVERIFIED (`Tendsto.const_sub` not found by
that name); (b) M4's framing was softened: it is standalone algebra on the abstract
rate ratio, NOT a formal bridge to the repo's numeric `mcWhirterBound` (that bridge
is atomic-physics-dependent and forbidden by §5). See flagged spots below.*

---

## 1. The formal obstacle

The repo formalizes the **algebra** of the McWhirter LTE criterion but explicitly
disclaims the **mechanism** behind it and the **departure** from it.

- `StarkBroadening.mcWhirterBound` (`StarkBroadening.lean:103`) —
  `n_e ≥ 1.6·10¹²·√T·(ΔE)³`, with `lteValid` (`:109`) the admissibility predicate.
- `PartialLTE.thermalizationLimit` (`PartialLTE.lean:65`) and
  `mcwhirter_iff_thermalizationLimit` (`PartialLTE.lean:87`) — the criterion
  inverted into an energy-gap threshold `E*`, proven the *same criterion two ways*.
- `PartialLTE`'s own scope note (`PartialLTE.lean:41-42`) states the obstacle
  verbatim: **"Out of scope: the full collisional–radiative model, Cristoforetti
  et al.'s relaxation-time / diffusion-length refinements, and level departure
  coefficients."**

So the repo can say *"McWhirter holds / fails"* as a bare inequality, but it
**cannot state**:

1. the two-level collisional-radiative rate balance whose solution `b₂` is the
   physical content of McWhirter (the corpus derivation
   `b₂ = R₂₁/(R₂₁+A₂₁) = 1/(1 + A₂₁/(n_e C₂₁))` — the mechanism the bound
   *proxies*);
2. any **departure coefficient** `b_i = n_i / n_iᴸᵀᴱ` as a first-class object,
   its LTE limit `b→1`, or its dependence on `n_e`;
3. a **non-LTE error budget** — how a bounded departure `|b_i − 1| ≤ δ_b`
   propagates into the recovered temperature / composition. This is the glaring
   asymmetry with `ErrorBudget.lean`, which already carries *ordinate*-error
   budgets (`olsSlope_stable_hetero` `:350`, `olsIntercept_stable_hetero` `:440`,
   `temp_rel_error_hetero` `:386`, `relDensity_le` `:261`) through the exact same
   Boltzmann-plot machinery — but with the perturbation source left as an abstract
   `ε_k`, never physically identified with a departure coefficient.

The target objects the repo cannot yet write:

```
def departureCoeff (R21 A21 : ℝ) : ℝ := R21 / (R21 + A21)          -- two-level b₂
theorem two_level_balance … : n2 / n2LTE = departureCoeff R21 A21   -- the fixed point
theorem departureCoeffNe_tendsto_one : Tendsto (departureCoeffNe C21 A21) atTop (𝓝 1)
theorem nonlte_temp_error … : |THat − T| / T ≤ kB·THat·(∑ |Eₖ−Ē|·|log bₖ|)/SS_E
```

None exist (grep: no `departure`, `collisionalRate`, `radiativeDecay`,
`bCoeff` token anywhere under `CflibsFormal/`; the only `*LTE*` module is
`PartialLTE.lean`). *(Reviewer confirmed: grep for those tokens returns nothing;
`PartialLTE.lean` is the only LTE module.)*

---

## 2. Mathematical landscape

The decisive observation — mirroring how Frontier 02 found a *derivative-free*
route — is that the entire physically-meaningful content here is **algebraic and
static**: the two-level "steady state" is an *algebraic balance equation*, not an
ODE, and the departure coefficient enters the Boltzmann plot as a *pure additive
log shift*. No kinetics ODE, no rate-matrix inversion, no time integration is
needed for any A/B milestone. That is what makes this frontier tractable.

### 2.1 The two-level rate balance is an algebraic fixed point — CONFIRMED

*(Grounded: CF-LIBS corpus query, sources `35951c4e…` (CR/LTE diagnostics),
`58a4ca4f…`; matches Griem 1997 §6 and Cristoforetti 2010.)*

For a two-level atom (lower 1, upper 2) in steady state, balance collisional
excitation against collisional de-excitation + radiative decay:

```
n₁ R₁₂ = n₂ (R₂₁ + A₂₁)                                   (BAL)
```

with `R₁₂` the collisional excitation rate (`∝ n_e`), `R₂₁ = n_e C₂₁` the
collisional de-excitation rate (`C₂₁` = electron-impact rate coefficient), `A₂₁`
the Einstein spontaneous-decay coefficient. Under **strict LTE** collisions
dominate (`A₂₁ ≪ R₂₁`) and detailed balance gives `n₁ R₁₂ = n₂ᴸᵀᴱ R₂₁` (LTE).

*(Physics caveat — reviewer: (LTE) as written uses the **actual** `n₁`, not
`n₁ᴸᵀᴱ`, i.e. it presumes the lower level is itself thermalized, `b₁ ≈ 1`. This is
the standard two-level assumption (lower/ground level in LTE) and must be stated in
the M1 docstring; the Lean theorem takes both (BAL) and (LTE) as hypotheses, so it
is mathematically valid as an idealized REDUCED reduction.)*

Dividing (BAL) by (LTE) and cancelling `n₁ R₁₂`:

```
b₂ ≔ n₂ / n₂ᴸᵀᴱ = R₂₁ / (R₂₁ + A₂₁) = 1 / (1 + A₂₁/(n_e C₂₁)).      (★)
```

This is **not** an ODE steady state we must solve — it is the *quotient of two
algebraic balance identities*. In Lean it is one `field_simp`/`div` manipulation:
hypotheses `(BAL)` and `(LTE)` with `n₂ᴸᵀᴱ ≠ 0`, `n₁·R₁₂ ≠ 0`, conclusion
`n₂/n₂ᴸᵀᴱ = R₂₁/(R₂₁+A₂₁)`. **CONFIRMED, grade A.** *(Reviewer re-derived: from
(BAL) `n₂ = n₁R₁₂/(R₂₁+A₂₁)`, from (LTE) `n₂ᴸᵀᴱ = n₁R₁₂/R₂₁`; the quotient is
`R₂₁/(R₂₁+A₂₁)`. `n₁·R₁₂ ≠ 0` is derivable from `n₂ᴸᵀᴱ ≠ 0 ∧ R₂₁ ≠ 0` via (LTE).)*

### 2.2 The departure sandwich `0 < b₂ ≤ 1` and the `1 − b` closed form — CONFIRMED

From (★), with `R₂₁ = n_e C₂₁ ≥ 0`, `A₂₁ > 0`:

```
1 − b₂ = A₂₁ / (R₂₁ + A₂₁) ∈ (0, 1],   hence   0 < b₂ ≤ 1.            (SAND)
```

The upper bound `b₂ ≤ 1` is the physical statement *"radiative leakage can only
underpopulate the upper level"* (sub-LTE). The `1 − b` closed form is the workhorse
for everything downstream: it converts "closeness to LTE" into a single positive
fraction. From it, the **explicit density bound**

```
|b₂ − 1| = A₂₁ / (n_e C₂₁ + A₂₁) ≤ A₂₁ / (n_e C₂₁)                    (DEP-BOUND)
```

(drop the `+A₂₁` in the denominator; `n_e C₂₁ > 0`). This is the clean, `nlinarith`-/
`gcongr`-closable inequality that a Lean dev needs — no transcendental content.
**CONFIRMED, grade A.**

### 2.3 Monotonicity + LTE / corona limits — CONFIRMED (mono A, limits B)

`b₂(n_e) = n_e C₂₁/(n_e C₂₁ + A₂₁)` is **strictly increasing in `n_e`** on
`(0,∞)` (denser plasma ⇒ closer to LTE): write `b₂ = 1 − A₂₁/(n_e C₂₁ + A₂₁)`;
the subtracted term is strictly decreasing (numerator fixed `> 0`, denominator
strictly increasing), so `b₂` strictly increases. `gcongr` +
`one_div_lt_one_div_of_lt` (§3). **grade A.**

Two limits (Cristoforetti 2010 boundary regimes):

- **LTE limit** `n_e → ∞ ⇒ b₂ → 1`: `1 − b₂ = A₂₁/(n_e C₂₁ + A₂₁) → 0` because the
  denominator `→ +∞`. Route: `A₂₁/(n_e C₂₁ + A₂₁) = A₂₁·(n_e C₂₁ + A₂₁)⁻¹`, and
  `(n_e C₂₁ + A₂₁)⁻¹ → 0` at `atTop` (`tendsto_inv_atTop_zero` composed with the
  affine `n_e ↦ n_e C₂₁ + A₂₁ → atTop`), then a `const_mul` step, then
  `1 − (…) → 1` via a `const_sub`/`const_add`-of-negation step. **grade B** (limit
  plumbing; the *core* lemma `tendsto_inv_atTop_zero` is grep-verified present, but
  the exact `Tendsto.const_sub` / generic `Tendsto.const_mul` names are UNVERIFIED —
  see §3 caveat — expect to adjust them at proof time).
- **Corona limit** `n_e → 0⁺ ⇒ b₂ → 0`: direct substitution `b₂(0) = 0` plus
  continuity (`b₂` is continuous, ratio of continuous with nonzero denominator).
  Optional; **grade B**.

### 2.4 McWhirter ⇒ a departure threshold (standalone algebra) — CONFIRMED, but NOT a formal bridge to the repo's numeric `mcWhirterBound`

The corpus makes the *physical* bridge exact: the McWhirter "collisional rate ≥ 10×
radiative" condition `n_e C₂₁ ≥ 10 A₂₁` substituted into (★) forces
`b₂ ≥ 10/(10+1) = 10/11 ≈ 0.909`. More usefully, the general **threshold
equivalence** (the departure analogue of `mcwhirter_iff_thermalizationLimit` **in
proof style only**): for `0 < δ < 1`, `A₂₁ > 0`, `C₂₁ > 0`, `n_e ≥ 0`,

```
b₂(n_e) ≥ 1 − δ   ⟺   n_e ≥ A₂₁·(1 − δ) / (C₂₁·δ).                    (THRESH)
```

Proof: `b₂ ≥ 1−δ ⟺ A₂₁/(n_eC₂₁+A₂₁) ≤ δ ⟺ A₂₁ ≤ δ(n_eC₂₁+A₂₁) ⟺
A₂₁(1−δ) ≤ δ C₂₁ n_e ⟺ n_e ≥ A₂₁(1−δ)/(C₂₁δ)` — all `div`/`le_div_iff₀`
rearrangements over positive denominators, in the same style as
`mcwhirter_iff_thermalizationLimit` (`PartialLTE.lean:87-95`). **CONFIRMED,
grade A.**

**Reviewer caveat (load-bearing framing correction).** These statements are over
the *abstract rate ratio* `n_e C₂₁` vs `A₂₁`. They are **NOT** formally connected to
the repo's `StarkBroadening.mcWhirterBound = 1.6·10¹²·√T·(ΔE)³ ≤ n_e` /
`lteValid` / `thermalizationLimit`. A genuine bridge would require identifying the
numeric prefactor/scaling `1.6·10¹²·√T·(ΔE)³` with `10·A₂₁/C₂₁` — an
atomic-physics-input identity (`A₂₁`, `C₂₁` are cross-section-derived data) that
§5 **explicitly forbids as non-derivable**. Therefore: (THRESH) and
`mcwhirter_forces_departure` motivate McWhirter and reproduce its `10/11` content,
but must **not** be docstringed as proven-equivalent to the repo's `mcWhirterBound`,
and the `import CflibsFormal.PartialLTE` (§4) is narrative/co-location for M4, not a
proof dependency — no M4 statement uses a `PartialLTE` declaration.

### 2.5 The crown jewel — departure coefficient IS an additive Boltzmann-plot ordinate error — CONFIRMED

This is the beautiful reuse the seed hoped for, and it is **exact**. The
Boltzmann-plot ordinate is `y_k = log(n_k / g_k)` (`Boltzmann.boltzmann_plot`,
`Boltzmann.lean:68`). Under non-LTE, `n_k^{NLTE} = b_k · n_k^{LTE}`, so with
`b_k > 0`:

```
y_k^{NLTE} = log(n_k^{NLTE}/g_k) = log(n_k^{LTE}/g_k) + log b_k
           = y_k^{LTE} + log b_k.                                    (SHIFT, EXACT)
```

So **a per-line departure coefficient is precisely a per-line additive ordinate
perturbation `δ_k = log b_k`** — exactly the `ε_k` slot of the heteroscedastic
machinery in `ErrorBudget.lean`. Two clean facts finish the budget:

- **(SHIFT)** is one `Real.log_mul` (needs `n_k^{LTE}/g_k > 0`, `b_k > 0`). EXACT
  identity.
- **The departure bound → ordinate bound.** If `|b_k − 1| ≤ δ_b` with `0 ≤ δ_b < 1`
  then

  ```
  |log b_k| = |log b_k − log 1| ≤ |b_k − 1| / (1 − δ_b) ≤ δ_b / (1 − δ_b).   (LOG-BND)
  ```

  This is **already in the repo**: `log_lip_floor` (`ErrorBudget.lean:532`,
  currently `private`) states `|log a − log b| ≤ |a − b|/c` for `0 < c ≤ a, b`.
  Apply with `a = b_k`, `b = 1`, `c = 1 − δ_b` (`1−δ_b ≤ b_k` since `b_k ≥ 1−δ_b`;
  `1−δ_b ≤ 1`; `1−δ_b > 0`). **grade A, given the helper is promoted.** *(Reviewer
  re-read `log_lip_floor` and re-derived (LOG-BND): the floor conditions hold, and
  `log 1 = 0` gives `|log b_k| ≤ |b_k−1|/(1−δ_b) ≤ δ_b/(1−δ_b)`. Confirmed.)*

With `δ_k ≔ log b_k` and the uniform bound `|δ_k| ≤ δ_b/(1−δ_b)`, the *entire
existing chain fires verbatim*:

```
olsSlope_stable_hetero  ⇒  |Δβ| ≤ (∑ₖ |Eₖ−Ē|·|log bₖ|)/SS_E
        └─ temp_rel_error_le ⇒ |ΔT|/T ≤ kB·T̂·(∑ₖ |Eₖ−Ē|·|log bₖ|)/SS_E   (temperature leg)
olsIntercept_stable_hetero + relDensity_le  ⇒  non-LTE density/composition error   (density leg)
```

This is **the exact composition already performed for abstract `ε_k` in
`temp_rel_error_hetero` (`ErrorBudget.lean:386`)** — the only new content is
identifying `ε_k = log b_k` via (SHIFT) and bounding it via (LOG-BND). It is a
*formalizable non-LTE error budget*, REDUCED (worst-case, uniform-`δ_b` or
per-line), and it is the answer to the seed's "what does a formalizable non-LTE
error budget look like?" **CONFIRMED, grade A** for the composition once (SHIFT),
(LOG-BND) and the helper promotion are in place. *(Reviewer verified the exact
signature of `temp_rel_error_hetero`: it takes `eps : ι → ℝ` and
`hδ : ∀ k, |yHat k − y k| ≤ eps k` plus `olsSlope E y = 1/(kB·T)`,
`olsSlope E yHat = 1/(kB·THat)` — instantiating `eps := fun k => |log (b k)|` with
`hδ` closed by (SHIFT) + `le_of_eq` is a near-trivial application. Confirmed A.
NOTE for the **density leg**: `olsIntercept_stable_hetero` carries a load-bearing
`hcent : mean E = 0` hypothesis — the standard centered Boltzmann-plot convention —
which `nonlte_density_error` must carry explicitly.)*

### 2.6 Full CR ladder / ODE kinetics — REFUTED as a target

The general CR system `dn_k/dt = Σ_j[n_j R_{jk} − n_k R_{kj}] + Σ_j n_j A_{jk} = 0`
(corpus source `58a4ca4f…`) is an `N`-level linear steady-state = a rank-`N`
matrix kernel problem, and its *time-dependent* form is an ODE system. mathlib has
`Matrix` kernels but the repo has **no** steady-state-of-rate-matrix infrastructure,
no ODE layer, and — decisively — the rate coefficients `C_{jk}` themselves are
cross-section integrals over the electron energy distribution (effective collision
strengths), i.e. **atomic-physics input data**, not derivable quantities. Any
milestone that computes `C₂₁`, inverts an `N×N` rate matrix, or evolves `n_k(t)` is
**out of scope** (see §5). The two-level *algebraic* balance (§2.1) is the correct,
and sufficient, formalizable kernel — it is exactly the reduction the corpus uses to
"mathematically isolate the departure coefficient."

---

## 3. mathlib inventory

Everything the A/B milestones need is present; **no new mathlib infrastructure**.
The heavy lifting is *in-repo reuse* (the `ErrorBudget` heteroscedastic chain),
which is the whole point. *(Reviewer: all A-milestone-load-bearing rows
grep-verified at the stated locations; the two UNVERIFIED rows are flagged and both
sit only in the optional grade-B M3.)*

| needed lemma | status |
|---|---|
| `Real.log_mul (hx : x≠0) (hy : y≠0) : log (x*y) = log x + log y` | VERIFIED `Analysis/SpecialFunctions/Log/Basic.lean:132` (already used by `boltzmann_plot`) — (SHIFT) step |
| `Real.log_le_sub_one_of_pos (hx : 0<x) : log x ≤ x−1` | VERIFIED `…/Log/Basic.lean:306` — underlies `log_lip_floor` |
| `one_div_lt_one_div_of_lt (ha : 0<a) (h : a<b) : 1/b < 1/a` | VERIFIED `Algebra/Order/Field/Basic.lean:72` — strict-mono of `b₂(n_e)` |
| `one_div_le_one_div_of_le (ha : 0<a) (h : a≤b) : 1/b ≤ 1/a` | VERIFIED `Algebra/Order/Field/Basic.lean:69` — mono variant |
| `tendsto_inv_atTop_zero : Tendsto (·⁻¹) atTop (𝓝 0)` | VERIFIED `Topology/Algebra/Order/Field.lean:74` — LTE limit (M3) |
| `Real.log_le_log (hx : 0<x) (hxy : x≤y) : log x ≤ log y` | VERIFIED as a **`lemma`** at `…/Log/Basic.lean:150` (used in-repo by `log_lip_floor`); `log_lt_log` `:154`, `log_lt_log_iff` `:157` — only if a strict departure-monotone corollary is wanted |
| `Filter.Tendsto.const_mul` (generic topological-ring form) | ⚠ UNVERIFIED name — grep found `Tendsto.const_mul` only for `ℝ≥0∞`/`EReal`, and `Tendsto.const_mul_atTop`/`atTop_mul_const` in `Order/Filter/AtTopBot/Field.lean:72/79`. The generic real form exists but under a name to be resolved at proof time — **M3 (grade B) only** |
| `Filter.Tendsto.const_sub` (→ `1 − …`) | ⚠ UNVERIFIED — grep for `theorem Tendsto.const_sub` returns **nothing**; likely achieved via `Tendsto.const_add` of a negated limit or `Continuous.tendsto` of `(1 − ·)`. Adjust at proof time — **M3 (grade B) only, does not affect any A milestone** |
| `tendsto_atTop_add_const_right` / `Tendsto.atTop_mul_const` (affine `n_e ↦ n_eC₂₁+A₂₁ → atTop`) | VERIFIED present: `tendsto_atTop_add_const_right` (e.g. `Order/Filter/AtTopBot` usages), `Tendsto.atTop_mul_const` `Order/Filter/AtTopBot/Field.lean:79` — M3 |
| `le_div_iff₀` / `div_le_iff₀` (positive-denominator rearrangement) | VERIFIED present in mathlib (`Algebra/Order/Field/Basic.lean` uses `le_div_iff₀ hb` at `:41`) and used in-repo (`PartialLTE.lean:95`, `ErrorBudget.lean:236`) — (THRESH), (SAND) |
| Chebyshev / FKG correlation machinery | NOT NEEDED (no mean-energy covariance appears; the two-level route is termwise) |

Reusable **in-repo** lemmas (all build-verified; reviewer re-read every signature
below), the spine of the frontier:

- `olsSlope_stable_hetero` (`ErrorBudget.lean:350`) — per-line ordinate → slope
  bound. **Central to §2.5 temperature leg.**
- `olsIntercept_stable_hetero` (`ErrorBudget.lean:440`) — per-line ordinate →
  intercept bound. **Central to §2.5 density leg. Carries `hcent : mean E = 0`.**
- `temp_rel_error_le` (`ErrorBudget.lean:215`) / `temp_rel_error_hetero`
  (`ErrorBudget.lean:386`) — slope error → relative temperature error (the exact
  template to instantiate with `ε_k = |log b_k|`; signature reviewer-verified).
- `relDensity_le` (`ErrorBudget.lean:261`) — intercept error → relative density
  error (`|N̂−N| ≤ N·(exp η − 1)`; density-leg closure).
- `log_lip_floor` (`ErrorBudget.lean:532`, **`private`**) — the (LOG-BND) step.
  **Must be promoted to public or restated** in the new module (one-line
  transplant). This is the only "plumbing debt." *(Reviewer confirmed it is
  declared `private theorem log_lip_floor`.)*
- `boltzmann_plot` (`Boltzmann.lean:68`), `population` (`Boltzmann.lean:51`),
  `partitionFunction_pos` (`Boltzmann.lean:45`) — supply `n_k^{LTE}/g_k > 0` for
  (SHIFT).
- `mcWhirterBound` (`StarkBroadening.lean:103`), `mcwhirter_iff_thermalizationLimit`
  (`PartialLTE.lean:87`) — the McWhirter side, cited for **proof-style analogy and
  motivation only** (see §2.4 caveat; no formal bridge to M4).

---

## 4. Milestone ladder

Proposed new module **`CflibsFormal/NonLTEKinetics.lean`**, importing
`CflibsFormal.ErrorBudget` (the heteroscedastic chain + `log_lip_floor`) and,
optionally, `CflibsFormal.PartialLTE` (for narrative co-location / docstring
cross-reference only — **not** a proof dependency, see §2.4). Namespace
`CflibsFormal`. The module fills exactly the `PartialLTE.lean:41-42` "out of scope:
departure coefficients" gap.

### M1 — `departureCoeff` + two-level balance fixed point · **A**
```
def departureCoeff (R21 A21 : ℝ) : ℝ := R21 / (R21 + A21)

theorem two_level_balance {n1 n2 n2LTE R12 R21 A21 : ℝ}
    (hbal : n1 * R12 = n2 * (R21 + A21))        -- (BAL)
    (hlte : n1 * R12 = n2LTE * R21)             -- (LTE) detailed balance, lower level in LTE (b₁≈1)
    (hn2LTE : n2LTE ≠ 0) (hden : R21 + A21 ≠ 0) (hR21 : R21 ≠ 0) :
    n2 / n2LTE = departureCoeff R21 A21
```
Scope: **REDUCED** (McWhirter 1965 / Griem 1997 / Cristoforetti 2010 — the
two-level reduction of the CR system; faithful but a reduction, and (LTE) presumes
the lower level is thermalized `b₁≈1` — docstring this). Proof: from `hbal`,
`n2 = n1·R12/(R21+A21)`; from `hlte`, `n2LTE = n1·R12/R21`; divide, `field_simp`;
`= R21/(R21+A21)`. Add positivity lemmas `departureCoeff_pos`,
`departureCoeff_le_one` (from (SAND), `R21≥0`, `A21>0`). Non-vacuity witness in repo
style (`R21=A21=1 ⇒ b=1/2`).

### M2 — `departureCoeffNe` (density form) + sandwich + strict-mono · **A**
```
noncomputable def departureCoeffNe (C21 A21 ne : ℝ) : ℝ :=
  ne * C21 / (ne * C21 + A21)                    -- = departureCoeff (ne*C21) A21

theorem departureCoeffNe_le_one … : departureCoeffNe C21 A21 ne ≤ 1
theorem one_sub_departureCoeffNe … :               -- (DEP-BOUND) crux
    (hC : 0 < C21) (hA : 0 < A21) (hne : 0 < ne) :
    |departureCoeffNe C21 A21 ne − 1| ≤ A21 / (ne * C21)
theorem departureCoeffNe_strictMonoOn_ne … :
    StrictMonoOn (fun ne => departureCoeffNe C21 A21 ne) (Set.Ioi 0)
```
Scope: **PURE-MATH** (the `def` is `C`-parametric real algebra; physics enters at
M4/M5). Proof: `1 − b = A21/(ne·C21+A21)`, `≤ A21/(ne·C21)` by dropping `+A21`
(`gcongr`/`div_le_div_of_nonneg_left`); strict-mono via
`one_div_lt_one_div_of_lt` on the `1 − A/(neC+A)` form. All grade A.

### M3 — LTE / corona limits · **B**
```
theorem departureCoeffNe_tendsto_one (hC : 0 < C21) (hA : 0 < A21) :
    Filter.Tendsto (fun ne => departureCoeffNe C21 A21 ne) Filter.atTop (nhds 1)
theorem departureCoeffNe_tendsto_zero_corona … :    -- optional, ne → 0⁺
    Filter.Tendsto (fun ne => departureCoeffNe C21 A21 ne) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)
```
Scope: **REDUCED** (Cristoforetti 2010 boundary regimes). Prereq: M2. Proof of
LTE limit: `1 − b₂ = A21·(ne·C21+A21)⁻¹`; `ne·C21+A21 → atTop`
(`Tendsto.atTop_mul_const`/`tendsto_atTop_add_const_right`); `tendsto_inv_atTop_zero`;
a `const_mul` → `0`; a `const_sub`/`const_add`-of-negation → `1`. Corona: substitute
`b₂(0)=0` + continuity. **B** — *the core `tendsto_inv_atTop_zero` is present, but
the `Tendsto.const_sub` / generic `Tendsto.const_mul` names are UNVERIFIED (§3) and
must be resolved at proof time; if they prove awkward, get `(1 − ·)` and `(A21 · ·)`
continuity via `Continuous.tendsto` instead.* Optional colour; no A milestone
depends on it.

### M4 — McWhirter ⇒ departure threshold (standalone algebra) · **A**
```
theorem mcwhirter_forces_departure (hC : 0 < C21) (hA : 0 < A21) (hne : 0 ≤ ne)
    (h10 : 10 * A21 ≤ ne * C21) : (10 : ℝ) / 11 ≤ departureCoeffNe C21 A21 ne
theorem departure_threshold_iff (hC : 0 < C21) (hA : 0 < A21) (hne : 0 ≤ ne)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    (1 − δ ≤ departureCoeffNe C21 A21 ne) ↔ (A21 * (1 − δ) / (C21 * δ) ≤ ne)   -- (THRESH)
```
Scope: **EXACT** for `mcwhirter_forces_departure` (the corpus-exact `10× ⇒ 10/11`
fact of McWhirter 1965 as recalled in Cristoforetti 2010, stated over the abstract
rate ratio `10·A21 ≤ ne·C21`); **REDUCED** for the general `(THRESH)` (two-level
model). Prereq: M2. Proof: `le_div_iff₀` rearrangements over positive denominators,
in the same style as `mcwhirter_iff_thermalizationLimit` (`PartialLTE.lean:87`).
**Framing (reviewer-corrected):** this is a *standalone* statement about the rate
ratio; it is **NOT** a formal bridge to the repo's numeric
`mcWhirterBound = 1.6·10¹²·√T·(ΔE)³` — connecting them needs the atomic-physics
identity `1.6·10¹²·√T·(ΔE)³ ↔ 10·A21/C21`, which §5 forbids as non-derivable.
Docstring it as "the departure content of the McWhirter *factor-of-10 rate ratio*,"
not as an equivalence to `lteValid`/`thermalizationLimit`.

### M5 — non-LTE Boltzmann-plot ordinate shift + error budget (CROWN JEWEL) · **A**
Three sub-results; the first is EXACT, the rest are the existing chain instantiated.
```
-- (SHIFT), EXACT identity
theorem nonlte_ordinate_shift {g nLTE : ℝ} (b : ℝ) (hnLTE : 0 < nLTE) (hg : 0 < g) (hb : 0 < b) :
    Real.log (b * nLTE / g) = Real.log (nLTE / g) + Real.log b
-- (LOG-BND), grade A given log_lip_floor promoted
theorem abs_log_departure_le {b δb : ℝ} (hδ0 : 0 ≤ δb) (hδ1 : δb < 1) (hb : |b − 1| ≤ δb) :
    |Real.log b| ≤ δb / (1 − δb)
-- temperature leg: instantiate temp_rel_error_hetero with εₖ = |log bₖ|
theorem nonlte_temp_error [Nonempty ι] {E yLTE yNLTE : ι → ℝ} {b : ι → ℝ} {kB T THat : ℝ}
    (hkB : 0 < kB) (hT : 0 < T) (hTHat : 0 < THat)
    (hshift : ∀ k, yNLTE k = yLTE k + Real.log (b k))   -- from nonlte_ordinate_shift
    (hvar : 0 < ∑ k, (E k − mean E)^2)
    (hβ : olsSlope E yLTE = 1/(kB*T)) (hβHat : olsSlope E yNLTE = 1/(kB*THat)) :
    |THat − T| / T ≤ kB * THat * ((∑ k, |E k − mean E| * |Real.log (b k)|)
                                    / (∑ k, (E k − mean E)^2))
-- density leg: olsIntercept_stable_hetero + relDensity_le, εₖ = |log bₖ|  (carries hcent : mean E = 0)
theorem nonlte_density_error … (hcent : mean E = 0) … :
    |NHat − N| ≤ N * (Real.exp ((∑ k, |Real.log (b k)|)/Fintype.card ι) − 1)
```
Scope: **EXACT** for `nonlte_ordinate_shift` (a definitional log identity, faithful
to `boltzmann_plot`); **REDUCED** for `nonlte_temp_error` / `nonlte_density_error`
(worst-case, deterministic — same tag as `temp_rel_error_hetero`,
`ErrorBudget.lean:386`). Prereq: `log_lip_floor` promoted to public (§3),
M2 for the optional uniform bound `|log bₖ| ≤ δ_b/(1−δ_b)`. Proof of the temperature
leg: `nonlte_temp_error` is *literally* `temp_rel_error_hetero` with `y := yLTE`,
`yHat := yNLTE`, `eps := fun k => |Real.log (b k)|`, and
`hδ : ∀ k, |yNLTE k − yLTE k| ≤ |log b_k|` closed by `hshift` + `le_of_eq`
(`|yNLTE k − yLTE k| = |log b_k|`). Density leg: `olsIntercept_stable_hetero`
(**requires `hcent : mean E = 0`**) → `relDensity_le` with `η = (∑|log b_k|)/card`.
Non-vacuity witness: two lines, `b = (1, e^{0.1})`, check the bound is a real
(non-⊤) number. **This is the deliverable** the seed asked for: "bounds on
composition error as a function of departure-coefficient bounds `|b_i − 1| ≤ δ_b`,
mirroring how `ErrorBudget.lean` treats ordinate errors."

### M6 (optional) — uniform-`δ_b` corollary + pLTE statement · **A/B**
```
theorem nonlte_temp_error_uniform … (hδb : ∀ k, |b k − 1| ≤ δb) (hδ1 : δb < 1) :
    |THat − T|/T ≤ kB*THat*(δb/(1−δb))*(∑ k, |E k − mean E|)/(∑ k, (E k − mean E)^2)
```
Scope: REDUCED. Prereq: M5 + `abs_log_departure_le`. Pure specialization
(`εₖ ≡ δ_b/(1−δ_b)`), factoring the constant out of the sum exactly as
`olsSlope_stable_l1_of_hetero` (`ErrorBudget.lean:370`) does. A **partial-LTE
(pLTE) validity statement** can be packaged here: "if only levels above `E*`
(`PartialLTE.thermalizationLimit`) are thermalized, restrict the budget to the
thermalized sub-family" — grade B, needs an index-subset predicate, optional.

---

## 5. Refusals / traps

- **Do NOT attempt the full CR rate-matrix / ODE steady state.** The `N`-level
  `dn_k/dt = 0` kernel and time-dependent kinetics are out of scope: no ODE layer,
  no rate-matrix-kernel infra in the repo, and the rate coefficients `C_{jk}` are
  atomic-physics *input data* (cross-section integrals / effective collision
  strengths), not derivable. §2.6 refutes this as a target. Stay two-level and
  **algebraic** — the corpus itself reduces to two levels "to mathematically
  isolate the departure coefficient." Re-litigating this wastes a session.
- **Do NOT compute or claim numerical `b_i`, `C₂₁`, or `A₂₁` values.** The value of
  this frontier is the *structural* map (departure ⇒ ordinate shift ⇒ error
  budget), not any specific number. `A₂₁`, `C₂₁` are parameters, kept explicit and
  `C`-parametric (mirror `PartialLTE`'s `C`-parametric `thermalizationLimit`).
- **Do NOT formally bridge M4 to the repo's numeric `mcWhirterBound`.** Identifying
  `1.6·10¹²·√T·(ΔE)³` with `10·A₂₁/C₂₁` is exactly the non-derivable atomic-physics
  identity this section forbids. M4 is standalone algebra on the *rate ratio*; keep
  the McWhirter connection at the docstring/motivation level (see §2.4). Do not
  docstring `mcwhirter_forces_departure` as equivalent to `lteValid`.
- **Do NOT over-claim that `b₂ ≈ 1` establishes LTE.** McWhirter is *necessary, not
  sufficient* (the `PartialLTE.lean:35-42` honest-scope caveat, verbatim from
  Cristoforetti 2010). `two_level_balance` proves a *two-level* departure (and
  presumes the lower level is itself in LTE, `b₁≈1`); it must not be docstringed as
  "LTE holds." State the conditional. This is the `StarkShift`/`PartialLTE` house
  lesson.
- **`log_lip_floor` is `private`.** M5 depends on it. Either promote it to a public
  lemma in `ErrorBudget.lean` (cleanest — it is genuinely reusable, PURE-MATH) or
  restate a one-line copy in `NonLTEKinetics.lean`. Do not import a `private` symbol
  — it will not resolve. Budget this explicitly (it is the only plumbing debt).
- **Sign/direction trap in (SAND) and (THRESH).** `1 − b = A/(neC+A)` (not
  `A/(neC)`) is the *equality*; `A/(neC)` is only the *upper bound* (DEP-BOUND).
  Keep them distinct: the limit (M3) uses the exact form, the McWhirter bound (M4)
  and error budget (M5 uniform) use the inequality. `δ` in (THRESH) must satisfy
  `0 < δ < 1` (else `1−δ ≤ 0` trivializes / `1−δ_b` denominator vanishes) — carry
  it as a load-bearing hypothesis, like `hne : 0 ≤ ne` in
  `mcwhirter_iff_thermalizationLimit`.
- **Do NOT feed `δ_b ≥ 1` into (LOG-BND).** `log_lip_floor` needs the positive floor
  `1 − δ_b > 0`; a departure so large it admits `b_k = 0` has unbounded `|log b_k|`
  (corona limit, §2.3). The budget is a *near-LTE* (small-δ_b) statement by
  construction — state it, do not paper over it.
- **M3 Tendsto plumbing is UNVERIFIED (grade B, optional).** `Tendsto.const_sub`
  does not exist by that name; the generic real `Tendsto.const_mul` name is
  unresolved (§3). Only `tendsto_inv_atTop_zero` and the affine-`atTop` lemmas are
  grep-confirmed. Expect to adjust the final two limit steps (or route through
  `Continuous.tendsto` of `A21··` and `1−·`). No A milestone depends on M3.
- **`nonlte_density_error` must carry `hcent : mean E = 0`.** `olsIntercept_stable_hetero`
  (the density-leg engine) is stated in the centered convention; the intercept =
  `mean y` reduction fails without it. Carry it as a hypothesis (the standard
  Boltzmann-plot normalization), like `hcent` in the source lemma.
- **Scope-tag audit.** Each new result needs a `docs/scope-tags.tsv` row or CI
  fails (413 rows currently; format `module⟶name⟶scope⟶citation`). The one
  judgement call: M4's `mcwhirter_forces_departure` is EXACT (corpus-exact `10/11`
  over the rate ratio), but the general `(THRESH)` and M1/M5 legs are REDUCED
  (two-level / worst-case). Tag honestly — a green proof of an over-claimed scope is
  worthless here.

**Recommendation: attack, starting with M5's `nonlte_ordinate_shift` + the
`temp_rel_error_hetero` instantiation.** The crown jewel (§2.5) is the highest-value,
lowest-risk milestone: it is EXACT at its core, reuses the *entire* proven
`ErrorBudget` heteroscedastic chain unchanged, and delivers precisely the
"formalizable non-LTE error budget" the topic asks for. M1–M4 are self-contained
algebra (grade A) that can land in the same session; M3's limits are the only
grade-B pieces and are optional colour (with the plumbing-name caveat above). Zero
new mathlib; one `private`→public promotion is the entire infrastructure cost.

---

*PROPOSED ADDITIONS — none required.* The dossier is fully grounded in the existing
citation set (McWhirter 1965; Cristoforetti 2010; Griem 1997; Aragón & Aguilera
2008 for the LTE-diagnostic framing). The corpus source
`35951c4e-59ee-4d42-b14a-0b42103d08c1` ("Collisional-Radiative Models and LTE
Diagnostics for LIBS") and `58a4ca4f-…` are internal NotebookLM synthesis notes,
not standalone peer-reviewed citations — cite the primary literature
(Cristoforetti 2010, Griem 1997) in module docstrings, not these notes.
