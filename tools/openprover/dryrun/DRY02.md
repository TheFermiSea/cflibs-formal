# Frontier 02 — Saha-factor monotonicity in temperature

*Planning dossier. No Lean edited; every current-state claim anchored to a real
declaration, every mathlib claim grepped against `.lake/packages/mathlib` (v4.31.0).*

---

## 1. The formal obstacle

The Saha factor is defined (`CflibsFormal/Saha.lean:68`) as

```
sahaFactor kB T me h chi gZ EZ gZ1 EZ1
  = 2 * (partitionFunction kB T gZ1 EZ1 / partitionFunction kB T gZ EZ)
      * (thermalBracket kB T me h) ^ (3/2 : ℝ)
      * Real.exp (-chi / (kB * T))
```

with `thermalBracket kB T me h = (2·π·me·kB·T)/h^2` (`Saha.lean:45`) and
`partitionFunction kB T g E = ∑ k, g k * boltzmannFactor kB T (E k)`
(`Boltzmann.lean:42`), `boltzmannFactor kB T E = Real.exp (-E/(kB T))`
(`Boltzmann.lean:37`).

What is **proven** about `S(T)`:

- `sahaFactor_pos` (`Saha.lean:91`) — `0 < S(T)`.
- `log_sahaFactor` (`Saha.lean:136`) — the closed additive form
  `log S = log 2 + (log U₁ − log U₀) + (3/2)·log(bracket) − χ/(kB T)`.
- `sahaFactor_lipschitz_temp` (`SahaStability.lean:570`) — the **sign-free**
  two-point bound `|S(T₁) − S(T₂)| ≤ sahaFactorLipConst · |T₁ − T₂|` on a box.

What is **open** — the obstacle — is any *signed* statement:

> There is no theorem `sahaFactor …_mono_temp` / `…_strictMono_temp`; the file's
> own scope note (`SahaStability.lean:48-54`) records monotonicity as
> "STILL OPEN … `dS/dT` … is *not* definite … monotonicity remains SKIPPED
> rather than proven under a hidden reduction", and the gap ledger
> (`docs/SOLVER_FORMALIZATION_GAPS.md:70-71`) says "MONOTONICITY stays honestly
> open (`dS/dT` sign-indefinite through `U_{z+1}/U_z`)".

The stated reason: the partition ratio `U₁(T)/U₀(T)` in `S` has a
sign-indefinite temperature derivative, so no factorwise sign argument closes it.
The target theorem we cannot yet state:

```
theorem sahaFactor_strictMonoOn_temp … :
    StrictMonoOn (fun T => sahaFactor kB T me h chi gZ EZ gZ1 EZ1) (Set.Ioi 0)
```

(matching the repo's `StrictMonoOn`/`StrictAntiOn … (Set.Ioi 0)` idiom used by
`electronDensity_antitone` (`StrictAntiOn`, `Saha.lean:120`) and
`sahaEquilibriumNe_strictMono_S` (`StrictMonoOn`, `SahaEquilibrium.lean:219`)).

---

## 2. Mathematical landscape

### 2.1 The seeded logarithmic-derivative identity — CONFIRMED as motivation

With `β = 1/(kB T)`, `U_i(β) = ∑ g_k exp(−β E_k)`, one has
`d(log U_i)/dβ = −⟨E⟩_i` (the Boltzmann-weighted mean level energy), hence
`d(log U_i)/dT = ⟨E⟩_i /(kB T²)`. Combined with `d/dT[(3/2)log(cT)] = 3/(2T)`
and `d/dT[−χ/(kB T)] = χ/(kB T²)`:

```
kB T² · d(log S)/dT = (3/2)·kB T + χ + (⟨E⟩₁ − ⟨E⟩₀).
```

This is exactly the seeded formula. Since `⟨E⟩₁ ≥ 0` and `⟨E⟩₀ ≤ Emax₀`, a
sufficient condition for `dS/dT > 0` is `χ + (3/2)kB T ≥ Emax₀`; and because every
bound neutral-stage level sits below the ionization limit (`E₀ₖ ≤ χ`, hence
`Emax₀ ≤ χ`), the plain hypothesis `∀ k, E₀ k ≤ χ` already forces the bracket
positive. The seeded physics is correct.

**But** this derivation needs `d(log U)/dT = ⟨E⟩/(kB T²)`, i.e. `HasDerivAt` of a
finite exponential sum plus a monotone-derivative-sign integration — machinery the
repo deliberately avoids (every existing `S`/`U` sensitivity result is a *two-point*
or *termwise* estimate: `partitionFunction_two_point_bound`,
`sahaFactor_lipschitz_temp`, the `PartitionLipschitz` legs). So we use the
derivative only as a compass and prove the sign **without derivatives**.

### 2.2 The derivative-free route — CONFIRMED, and it cracks the frontier

Everything reduces to two elementary partition facts and the already-proven
`log_sahaFactor`. Fix `0 < T₁ < T₂`, write `β_i = 1/(kB T_i)` so `β₁ > β₂ > 0`.
By `log_sahaFactor` (applied at `T₂` and `T₁` and subtracted):

```
log S(T₂) − log S(T₁)
  =  [log U₁(T₂) − log U₁(T₁)]                                (P₁)
   − [log U₀(T₂) − log U₀(T₁)]                                (P₀)
   + (3/2)·[log B(T₂) − log B(T₁)]                            (Bt)
   + χ·(β₁ − β₂).                                             (Ct)
```

Three sign facts, each **termwise / two-point**, no calculus:

- **(P₁) ≥ 0** — `U₁` is increasing in `T` (each `exp(−E₁ₖ/(kB T))` increases in
  `T` for `E₁ₖ ≥ 0`), so `U₁(T₁) ≤ U₁(T₂)` and `log` is monotone. This is exactly
  `partitionFunction_ge_floor` (`SahaStability.lean:391`, private) applied with
  floor `T₁`.

- **(Ct − P₀) ≥ 0** — the crux, and it is a *clean termwise comparison*. Claim
  `U₀(T₂) ≤ exp(χ(β₁ − β₂))·U₀(T₁)`. Termwise, dividing by `gₖ > 0` and using
  `exp` monotonicity, this is
  `−E₀ₖ β₂ ≤ χ(β₁ − β₂) − E₀ₖ β₁`, i.e.
  `(E₀ₖ − χ)(β₁ − β₂) ≤ 0`, which holds because `β₁ − β₂ > 0` and
  **`E₀ₖ − χ ≤ 0` is the hypothesis `∀ k, E₀ k ≤ χ`.** Taking `log`:
  `log U₀(T₂) − log U₀(T₁) ≤ χ(β₁ − β₂) = Ct`.

- **(Bt) > 0 (strict)** — `B(T) = (2π me kB/h²)·T` is *strictly* increasing, so
  `B(T₁) < B(T₂)`, both positive, and `Real.log_lt_log` gives strict `>`. This
  single term supplies strictness; it is independent of `χ`.

Hence `log S(T₂) − log S(T₁) = P₁ + (Ct − P₀) + Bt ≥ 0 + 0 + (>0) > 0`, and since
`S > 0` (`sahaFactor_pos`), `Real.log_lt_log_iff` returns `S(T₁) < S(T₂)`. ∎

The termwise inequality `(E₀ₖ − χ)(β₁ − β₂) ≤ 0` is the whole physics: **the
sign-indefinite partition ratio is tamed by pairing `U₀`'s growth against the
`exp(−χ/kB T)` factor** — the two "problematic" factors of `S` are bounded
*together*, not separately, which is precisely what `sahaFactor_lipschitz_temp`
could not do (it bounded each channel in isolation, losing the sign).

### 2.3 Physical hypothesis is universal, not a reduction

`E₀ₖ ≤ χ` says every bound level of the lower (neutral) stage lies below its
ionization limit — true for every atom (excitation energies measured from the
ground state are bounded by the ionization energy; equality only in the Rydberg
limit). The upper stage needs only `E₁ₖ ≥ 0` (already a standing hypothesis,
`hEZ1`). So the result is *unconditional in practice*.
[VERIFIED: standard atomic structure; consistent with the repo's verified list —
Griem / Saha–Eggert convention that `partitionFunction` sums bound levels up to
the ionization limit.]

### 2.4 Chebyshev / FKG / MonovaryOn direction — EVALUATED, NOT NEEDED

The seed suggested a correlation-inequality route (Chebyshev sum inequality /
`MonovaryOn.sum_mul_sum_le`) to compare `U₁/U₀` ratios. That machinery targets
`⟨E⟩₀ ≤ ⟨E⟩₁`-style covariance facts at a *single* temperature — useful if one
insisted on the derivative form `⟨E⟩₁ − ⟨E⟩₀`. The termwise route in §2.2
sidesteps it entirely: we never compare mean energies, we bound each `U` across
two temperatures directly. **Recommendation: do not use Chebyshev/Monovary.** It
is available (see §3) but adds a correlation lemma dependency for no gain.

### 2.5 Downstream payoff

`sahaEquilibriumNe_strictMono_S` (`SahaEquilibrium.lean:219`) already proves the
self-consistent equilibrium `n_e` is strictly increasing in `S`. Composing with a
proven `S` strict-mono-in-`T` yields "hotter plasma ⇒ more strongly ionized `n_e`"
as a *signed* physical law — a corollary the two-sided Lipschitz bound cannot give.
Likewise the diagnostic `n_e = S(T)/R` at fixed `R > 0` becomes strictly increasing
in `T`.

---

## 3. mathlib inventory

Everything the proof needs is present; **no new mathlib infrastructure** (this is
the decisive contrast with, e.g., a Bessel-function frontier).

- `Real.log_lt_log (hx : 0 < x) (h : x < y) : log x < log y`
  — VERIFIED: `Analysis/SpecialFunctions/Log/Basic.lean:154`. (strict Bt step)
- `Real.log_le_log (hx : 0 < x) (hxy : x ≤ y) : log x ≤ log y`
  — VERIFIED: `Analysis/SpecialFunctions/Log/Basic.lean:150`. (P₁ step)
- `Real.log_lt_log_iff (hx : 0 < x) (hy : 0 < y) : log x < log y ↔ x < y`
  — VERIFIED: `Analysis/SpecialFunctions/Log/Basic.lean:157`. (final log→value)
- `Real.log_le_log_iff` — VERIFIED: `…/Log/Basic.lean:146`.
- `Real.exp_le_exp : exp x ≤ exp y ↔ x ≤ y`
  — VERIFIED: `Analysis/Complex/Exponential.lean:315`. (termwise U₀ bound)
- `Real.exp_lt_exp : exp x < exp y ↔ x < y`
  — VERIFIED: `Analysis/Complex/Exponential.lean:311`.
- `Real.log_rpow (hx : 0 < x) (y) : log (x^y) = y*log x`
  — VERIFIED: `Analysis/SpecialFunctions/Pow/Real.lean:490` (already used by
  `log_sahaFactor`).
- `Finset.sum_le_sum` — VERIFIED:
  `Algebra/Order/BigOperators/Group/Finset.lean:108` (`@[to_additive … sum_le_sum]`;
  already used by `partitionFunction_ge_floor`).
- `StrictMonoOn` — VERIFIED: `Order/Monotone/Defs.lean:99`.
- Chebyshev sum inequality `MonovaryOn.sum_mul_sum_le_card_mul_sum`
  — VERIFIED present: `Algebra/Order/Chebyshev.lean:106` — but **not needed** (§2.4).

Reusable **in-repo** lemmas (all build-verified):

- `log_sahaFactor` (`Saha.lean:136`) — the additive decomposition. **Central.**
- `sahaFactor_pos` (`Saha.lean:91`) — closes the final `log→value` step.
- `partitionFunction_ge_floor` (`SahaStability.lean:391`, *private*) — gives P₁ and
  is the template for the U₀ upper-growth lemma. NOTE: private to `SahaStability`;
  reusable only if the new theorem lives in that file, else restate a public
  `partitionFunction_mono_temp`.
- `thermalBracket_mono` (`SahaStability.lean:341`, *private*) — `B` monotone; needs a
  strict sibling `thermalBracket_strictMono` (one-line: `B(T₂)−B(T₁)=coef·(T₂−T₁)>0`).
- `partitionFunction_pos` (`Boltzmann.lean:45`), `thermalBracket_pos` (`Saha.lean:50`).

---

## 4. Milestone ladder

Ordered; each step is small and self-contained. Proposed to live in
`SahaStability.lean` (reuses the private helpers) or a sibling `SahaMonotone.lean`
that first promotes the two needed helpers to public.

### M1 — `thermalBracket_strictMono` (helper)  · tractability **A**
```
private lemma thermalBracket_strictMono {kB me h Ta Tb : ℝ}
    (hkB : 0 < kB) (hme : 0 < me) (hh : 0 < h) (hab : Ta < Tb) :
    thermalBracket kB Ta me h < thermalBracket kB Tb me h
```
Scope: PURE-MATH. Prereq: none. Strict version of `thermalBracket_mono`; proof is
`B(Tb)−B(Ta) = (2π me kB/h²)(Tb−Ta) > 0` (`nlinarith`), copying `thermalBracket_mono`
with `<`.

### M2 — `partitionFunction_upper_growth` (the crux termwise lemma) · **A**
```
lemma partitionFunction_upper_growth {kB T1 T2 chi : ℝ} {g E : ι → ℝ}
    (hkB : 0 < kB) (hT1 : 0 < T1) (hT12 : T1 ≤ T2)
    (hg : ∀ k, 0 < g k) (hEχ : ∀ k, E k ≤ chi) :
    partitionFunction kB T2 g E
      ≤ Real.exp (chi * (1/(kB*T1) - 1/(kB*T2))) * partitionFunction kB T1 g E
```
Scope: PURE-MATH (it is real analysis; the *use* of `chi` as the level ceiling is
where physics enters at M4). Prereq: none. Proof: `Finset.mul_sum` on the RHS, then
`Finset.sum_le_sum`; termwise divide by `g k`, `Real.exp_le_exp.mpr`, and the
scalar inequality `(E k − chi)·(1/(kB T1) − 1/(kB T2)) ≤ 0` closed by `nlinarith`
from `E k ≤ chi` and `1/(kB T1) ≥ 1/(kB T2)` (`inv_kT` monotonicity, cf.
`inv_kT_sub_le`, `SahaStability.lean:290`). *Does not even need `E k ≥ 0`.*

### M3 — `partitionFunction_mono_temp` (promote P₁) · **A**
```
lemma partitionFunction_mono_temp {kB T1 T2 : ℝ} {g E : ι → ℝ}
    (hkB : 0 < kB) (hT1 : 0 < T1) (hT12 : T1 ≤ T2)
    (hg : ∀ k, 0 < g k) (hE : ∀ k, 0 ≤ E k) :
    partitionFunction kB T1 g E ≤ partitionFunction kB T2 g E
```
Scope: PURE-MATH. Prereq: none. This is `partitionFunction_ge_floor` re-exposed
publicly with the floor equal to the lower temperature (its proof transplants
verbatim). Needed because the private version is not reachable from a new module.

### M4 — `sahaFactor_strictMonoOn_temp` (headline) · **B**
```
theorem sahaFactor_strictMonoOn_temp [Nonempty ι] [Nonempty κ]
    {kB me h chi : ℝ} {gZ EZ : ι → ℝ} {gZ1 EZ1 : κ → ℝ}
    (hkB : 0 < kB) (hme : 0 < me) (hh : 0 < h) (hchi : 0 ≤ chi)
    (hgZ : ∀ k, 0 < gZ k) (hEZ : ∀ k, 0 ≤ EZ k)
    (hgZ1 : ∀ k, 0 < gZ1 k) (hEZ1 : ∀ k, 0 ≤ EZ1 k)
    (hEχ : ∀ k, EZ k ≤ chi) :                    -- the ionization-limit hypothesis
    StrictMonoOn (fun T => sahaFactor kB T me h chi gZ EZ gZ1 EZ1) (Set.Ioi 0)
```
Scope: **EXACT** (Saha–Eggert / Griem) — the forward model `sahaFactor` is used
verbatim; the only side hypothesis, `EZ k ≤ chi`, is a physically universal fact,
not a modelling over-estimate (contrast the REDUCED Lipschitz constant). *Flag for
review: if the auditor prefers to read `EZ k ≤ chi` as a restriction rather than a
universal truth, downgrade to REDUCED — but EXACT matches how `log_sahaFactor` and
`electronDensity_relativeError` are tagged.* Prereq: M1, M2, M3.
Proof sketch: `intro T1 hT1 T2 hT2 hlt`; establish `log S(T1) < log S(T2)` by
rewriting both sides with `log_sahaFactor` and `linarith` on
`P₁ ≥ 0` (M3 + `Real.log_le_log`), `Ct − P₀ ≥ 0`
(M2 → `Real.log_le_log` → `Real.log_mul`/`Real.log_exp`), `Bt > 0`
(M1 + `Real.log_lt_log`); discharge with
`(Real.log_lt_log_iff (sahaFactor_pos …) (sahaFactor_pos …)).mp`.
Add a non-vacuity witness in the file's existing `nvStc*` style
(`SahaStability.lean:692`), e.g. `ι = κ = Fin 1`, `g = 1`, `E = 0`, `chi = 1`,
`T ∈ {1,2}`, checking `S(1) < S(2)`.

### M5 — `electronDensityFromRatio_strictMonoOn_temp` (corollary) · **A**
```
theorem electronDensityFromRatio_strictMonoOn_temp … {R : ℝ} (hR : 0 < R)
    (hEχ : ∀ k, EZ k ≤ chi) :
    StrictMonoOn (fun T => electronDensityFromRatio kB T me h chi gZ EZ gZ1 EZ1 R)
      (Set.Ioi 0)
```
Scope: EXACT. Prereq: M4. `electronDensityFromRatio = S/R`; dividing a strict-mono
positive function by fixed `R > 0` preserves strict monotonicity
(`div_lt_div_of_pos_left`-type step or `StrictMonoOn.div_const`). This is the
signed T-channel companion to `electronDensity_lipschitz`, and closes the
"MONOTONICITY stays honestly open" residual in ledger item 3.

### M6 (optional) — `sahaEquilibriumNe_strictMono_temp` · **B**
Compose M4 with `sahaEquilibriumNe_strictMono_S` (`SahaEquilibrium.lean:219`) to get
the equilibrium ionization strictly increasing in `T`. Prereq: M4. Minor plumbing:
`StrictMonoOn.comp` with the codomain of `S(·)` landing in `Set.Ioi 0`
(from `sahaFactor_pos`).

### M7 (optional, harder) — relaxed hypothesis · tractability **B/C**
Replace `∀ k, EZ k ≤ χ` by the weaker `χ + (3/2)kB·Tmin ≥ Emax₀` (the seeded
sufficient condition, which admits levels *above* `χ` if `T` is warm enough). This
needs a *quantitative* lower bound on `Bt` in terms of `(T₂ − T₁)` (a log-of-linear
gap bound), replacing the qualitative `Bt > 0`. Grade B if a clean
`log B(T₂) − log B(T₁) ≥ c·(T₂ − T₁)/Tmax` bound is used; **C** if one insists on
sharpness. **Not recommended** — M4's hypothesis already holds for every real atom,
so M7 buys physical generality that never binds.

---

## 5. Risks & dead ends

- **Private-helper reachability.** `partitionFunction_ge_floor` and
  `thermalBracket_mono` are `private` to `SahaStability.lean`. If M1–M5 go in a new
  file they must be re-derived/promoted (M3, M1 already budget for this). Cheapest:
  put the new theorems *in* `SahaStability.lean`. Low risk, just a placement choice.
- **Scope-tag audit.** The repo's memory discipline requires a
  `docs/scope-tags.tsv` row per new theorem or CI fails. M1–M6 each need a row
  (`SahaStability.lean  sahaFactor_strictMonoOn_temp  EXACT  Saha–Eggert (Griem)`
  etc.). Non-blocking but mandatory. The EXACT-vs-REDUCED call on M4 (see M4 note)
  is the one judgement to get right.
- **Over-claiming.** Do **not** state unconditional `StrictMono` — the hypothesis
  `∀ k, EZ k ≤ χ` is load-bearing (a pathological table with a level above the
  ionization limit could non-monotone `S`), exactly the StarkShift-module lesson
  (`StarkShift.lean:18-21`: state the conditional, don't over-claim). Keep the
  hypothesis explicit.
- **Direction/sign slips.** The one place to be careful is the termwise
  `(E₀ₖ − χ)(β₁ − β₂) ≤ 0` and the `−P₀ + Ct ≥ 0` grouping; both were checked by
  hand above. `nlinarith`/`linarith` should discharge them once the pieces are in
  scope.
- **Not a dead end mathematically.** The direction is *true* and the proof is
  complete on paper (§2.2). There is no hidden appeal to unproven analysis.

---

## 6. Recommendation

**Attack now.** This frontier is unusually favourable: the mathematics is settled
(a derivative-free, termwise proof that matches the repo's house style), it needs
**zero new mathlib** (all lemmas grepped and present, §3), it *reuses the
already-proven* `log_sahaFactor` as its spine, and it converts a standing "honestly
open" ledger item into a signed physical law with a genuinely universal hypothesis.

**Single best first milestone: M2 (`partitionFunction_upper_growth`).** It is the
crux — the one new idea (pairing `U₀`'s growth against `exp(−χ/kB T)` termwise) —
is Tier-A, self-contained (no prerequisites, no even `E ≥ 0`), and once it lands the
headline M4 is bookkeeping over `log_sahaFactor`. Prove M2 first to de-risk the
whole ladder in one session; M1 and M3 are trivial siblings; M4 then assembles.

**Key dependency:** none upstream — the only dependency is the in-repo
`log_sahaFactor` decomposition, which is already proven. Effort for the whole
frontier (M1–M5): **S–M** (one focused session for M1–M4, a short follow-up for
M5/M6).
