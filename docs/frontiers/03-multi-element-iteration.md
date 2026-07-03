# Multi-Element Iteration Convergence

Planning dossier for closing the last open leg of gap #6: convergence of the
*multi-element* coupled Saha–charge-neutrality iteration. Anchored to
`CflibsFormal/SahaEquilibrium.lean` (655 lines, all green, no `sorry`).

---

## 1. The formal obstacle

The multi-element closure map is defined at
`SahaEquilibrium.lean:286-288`:

```
noncomputable def multiElementIonized {ι} [Fintype ι] (S Ntot : ι → ℝ) (x : ℝ) : ℝ :=
  ∑ s, Ntot s * S s / (x + S s)
```

Abbreviate `G := multiElementIonized S Ntot` and `a s := Ntot s * S s > 0`.
The repo already proves, for `[Nonempty ι]`, `hS : ∀ s, 0 < S s`, `hN : ∀ s, 0 < Ntot s`:

- `multiElementIonized_strictAntiOn` (`:295`) — `G` is `StrictAntiOn (Set.Ici 0)`.
- `multiElement_exists_pos_fixedPoint` (`:314`) — `∃ x, 0 < x ∧ x = G x` (IVT on `[0, M]`, `M := ∑ Ntot`).
- `multiElement_pos_fixedPoint_unique` (`:363`) — the positive fixed point is unique.
- `multiElement_single_eq_sahaEquilibriumNe` (`:387`) — single species reduces to `sahaEquilibriumNe`.

**What is open:** the *iteration* `x_{n+1} = G(x_n)` (or any variant) is never shown
to converge to the fixed point. Contrast the **scalar** leg, which *is* closed
(`:438-614`): `sahaIter S Ntot x := Real.sqrt (S*(Ntot-x))` (`:450`) is shown to be a
geometric contraction (`sahaIter_contraction :485`), interval-invariant
(`sahaIter_mapsTo :542`), with geometric error decay (`sahaIter_geometric_error :558`)
and `Filter.Tendsto` to the root (`sahaIter_tendsto :593`).

The obstacle is not cosmetic. The scalar ladder uses the **√-reformulation**
`x = √(S(Ntot−x))`, whose one-step Lipschitz factor `√S/(2√(Ntot−b))` can be forced
below 1 by choosing the interval. **There is no √-reformulation of the multi-element
sum** `x = ∑ a_s/(x+S_s)`, so the scalar proof does not transcribe. The only natural
iterations are the *direct substitution* map `G` itself, or a *damped* variant — and
`G` is **antitone**, so `x_{n+1}=G(x_n)` generically **oscillates** (period-2) rather
than converging. The precise open statement:

```
theorem multiElement_iter_tendsto (…hyps…) (x0 : ℝ) (hx0 : x0 ∈ Set.Icc 0 M) :
    Filter.Tendsto (fun n => Φ^[n] x0) Filter.atTop (nhds x*)   -- x* the fixed point
```

for some explicit iteration map `Φ` (either `G`, or a damped `H`) — currently absent.

---

## 2. Mathematical landscape

### Two exact structural identities (the whole game)

Both are elementary algebra on the finite sum; no calculus, no MVT. Write
`D_s(x,y) := (x+S_s)(y+S_s) > 0` for `x,y ≥ 0`.

**(I) Two-point / discrete-slope identity.**
```
G(x) − G(y) = ∑ a_s [1/(x+S_s) − 1/(y+S_s)] = (y − x) · ∑ a_s / D_s(x,y).
```
So `G` is Lipschitz with an *exact* local factor `c(x,y) := ∑ a_s/D_s(x,y) ∈ (0, ∞)`,
and `G(x)−G(y) = −(x−y)·c(x,y)` (antitone, as already known). For `x,y ≥ a`,
`D_s ≥ (a+S_s)²`, hence
```
c(x,y) ≤ L(a) := ∑ a_s/(a+S_s)² = ∑ Ntot_s S_s/(a+S_s)²   (the seeded L(a)),
```
and the global bound on `[0,∞)` is `c ≤ M_L := ∑ Ntot_s/S_s` (take `a=0`,
`a_s/S_s² = Ntot_s/S_s`). `L` is decreasing, `L(0)=M_L`.

**(II) Fixed-point self-slope < 1 (unconditional local attraction).**
At the fixed point `r = G(r) = ∑ a_s/(r+S_s)` (so `∑ w_s = r` with `w_s := a_s/(r+S_s) ≥ 0`):
```
L(r) = ∑ a_s/(r+S_s)² = ∑ w_s/(r+S_s) < ∑ w_s/r = r/r = 1,
```
the strict inequality because `r + S_s > r` (each `S_s > 0`). **So `L(r) < 1`
always** — the iteration is locally attracting at the fixed point *unconditionally*.
This is the mathematical reason a convergence theorem must exist; the difficulty is
turning local attraction into a *global*, formalizable statement.

### Evaluation of the four seeded directions

**(a) Direct contraction when `L(a) < 1`. CONFIRMED but CONDITIONAL (a REDUCED result).**
On `[a,b] ⊆ [0,∞)`, identity (I) gives `|G(x)−G(y)| ≤ L(a)|x−y|`, and `L(a)` is the
*sharp* interval constant (attained as `x,y ↓ a`). When `L(a) < 1`, `G` is a genuine
contraction and the scalar ladder transcribes verbatim (contraction → mapsTo →
geometric_error → tendsto). **When does `L(a)<1` hold?** Since `L` decreases and
`L(r)<1` (identity II), `L(a)<1` on *some* `[a,b]` around `r` — but the invariant
interval must contain `r`, forcing `a ≤ r`, and then `L(a) ≥ L(r)` may exceed 1. The
clean sufficient condition `L(0) = ∑ Ntot_s/S_s < 1` is **physically restrictive**
(weakly-populated / strongly-ionized: total densities small relative to Saha factors).
Verdict: a valid grade-A milestone, but it does **not** cover the common `M_L ≥ 1`
regime. It is a REDUCED conditional theorem, *not* the unconditional answer.

**(b) Damped (Krasnoselskii–Mann) iteration. CONFIRMED — the robust, unconditional fix.**
Set `H(x) := (1−λ)x + λG(x) = x + λ(G(x)−x)`. By identity (I) this is **exact**
(no MVT): for `x,y ∈ [0,b]`,
```
H(x) − H(y) = (1 − λ(1 + c(x,y)))·(x − y),   c(x,y) ∈ (0, L(a)].
```
Choose `λ = 1/(1+M_L)` with `M_L = ∑ Ntot_s/S_s`. Then
`1 − λ(1+c) = (M_L − c)/(1+M_L) ∈ [0, M_L/(1+M_L)]`, so **`H` is monotone increasing
AND a contraction** with factor `κ := M_L/(1+M_L) < 1`, on all of `[0,∞)` —
*unconditionally*, no smallness hypothesis. `H` fixes `r` (`H(r)=(1−λ)r+λG(r)=r`) and,
being a κ-contraction toward `r`, keeps `[0,M]` invariant (`M := ∑ Ntot`, with
`M ≥ r`). This is the winner for a clean *unconditional* `Tendsto`, and its Lean
ladder is structurally identical to the existing scalar one. Cost: it proves
convergence of the *damped* scheme, not literal direct substitution — an honest
REDUCED scope (mirrors the scalar file's choice to iterate the √-form, not the
direct `Ntot·S/(x+S)`).

**(c) `G∘G` monotone + cycle exclusion ⇒ direct iteration converges. CONFIRMED — the crown result.**
`G∘G` is monotone increasing (`Antitone.comp`, verified below). The decisive new lemma
is **no 2-cycle**: suppose `G(p)=q, G(q)=p, p≠q`. Subtracting and dividing by `q−p`
gives `∑ a_s/D_s(p,q) = 1`. Substituting `1/(p+S_s) = (q+S_s)/D_s` into `q = G(p)`:
```
q = ∑ a_s(q+S_s)/D_s = q·(∑ a_s/D_s) + ∑ a_s S_s/D_s = q·1 + ∑ a_s S_s/D_s
  ⇒ ∑ a_s S_s/D_s = 0,   impossible (every term > 0, ι nonempty).
```
Hence `Fix(G∘G) ∩ [0,M] = Fix(G) ∩ [0,M] = {r}` (using existing uniqueness; `0∉Fix`
since `G(0)=M>0`). Because `[0,M]` is `G`-invariant (`G([0,M])=[G(M),M]⊆[0,M]`), the
even orbit `(G∘G)^[k] x0` and odd orbit `(G∘G)^[k](G x0)` are each **monotone**
(`monotone_iterate_of_id_le` / `antitone_iterate_of_le_id`, branching on the first
step) and bounded, so converge (`tendsto_atTop_ciSup`/`ciInf`) to fixed points of
`G∘G` (`isFixedPt_of_tendsto_iterate`), i.e. both to `r`. Interleaving even+odd gives
`(G)^[n] x0 → r` for **any** `x0 ∈ [0,M]`, **unconditionally**, for the **literal
direct-substitution** iteration. This is the strongest and most physically faithful
result. `G∘G`-contraction, by contrast, is *not* globally available in the
multi-element case (the single-species cancellation `|(G∘G)'| = N²/(N+x+S)² < 1`
does not generalize), which is exactly why the monotone-subsequence route, not a
direct 2-step contraction, is required.

**(d) Newton on `f(x)=x−G(x)`. CONFIRMED math, but heavy — defer.**
`f' = 1 + ∑ a_s/(x+S_s)² ≥ 1 > 0` (strictly increasing) and
`f'' = −∑ 2 a_s/(x+S_s)³ < 0`, so **`f` is concave** (the seeded "check sign": each
`a_s/(x+S_s)` is *convex*, `G` convex, `f = id − G` concave). Concave-increasing `f`
with a simple root gives globally monotone, quadratically convergent Newton from a
suitable side. But formalizing needs `deriv`/`ConcaveOn`, tangent-line inequalities,
and quadratic-rate bookkeeping — far more analysis machinery than (a)–(c) and no
reuse of the existing ladder. Grade C; defer. (Newton buys a *rate*, not existence —
(b)/(c) already deliver convergence.)

### Literature

- Saha–Eggert ionization balance and the LTE closure/charge-neutrality coupling that
  produces `x = ∑ a_s/(x+S_s)`: Griem, *Principles of Plasma Spectroscopy*
  [VERIFIED: repo-approved, `reviews/literature-validity-audit.md:53`]; standard
  LIBS treatment in **Yalcin 1999** [VERIFIED: on the repo's approved-citation list].
  The self-consistent `n_e` loop is the CF-LIBS working method (**Ciucci 1999**,
  **Tognoni 2010**) [VERIFIED: approved list].
- Krasnoselskii–Mann / averaged-iteration convergence for nonexpansive maps is
  classical fixed-point theory (Krasnoselskii 1955; Mann 1953)
  [UNVERIFIED — must check before citing in a Lean docstring]. **Not needed as a
  citation**: our damped map is an honest *contraction* (κ<1), so Banach suffices and
  no nonexpansive-averaging theorem is invoked.
- The monotone-even/odd-subsequence argument for antitone fixed-point iterations is
  textbook real analysis (monotone convergence); no special citation required
  (`PURE-MATH`).

---

## 3. mathlib inventory (v4.31.0, grepped under `.lake/packages/mathlib/Mathlib`)

Needed vs available:

- **`Antitone.comp : Antitone g → Antitone f → Monotone (g ∘ f)`** —
  VERIFIED: `Order/Monotone/Defs.lean:375`. Gives `Monotone (G∘G)`.
- **`monotone_iterate_of_id_le : id ≤ f → Monotone (fun m => f^[m])`** and dual
  **`antitone_iterate_of_le_id : f ≤ id → Antitone (fun m => f^[m])`** —
  VERIFIED: `Order/Iterate.lean:128,133`. Monotonicity of the even/odd orbits.
- **`tendsto_atTop_ciSup (Monotone f) (BddAbove (range f))`** /
  **`tendsto_atTop_ciInf (Antitone f) (BddBelow (range f))`** —
  VERIFIED: `Topology/Order/MonotoneConvergence.lean:116,136`. Bounded-monotone limits.
- **`isFixedPt_of_tendsto_iterate : Tendsto (f^[·] x) atTop (𝓝 y) → ContinuousAt f y → IsFixedPt f y`** —
  VERIFIED: `Dynamics/FixedPoints/Topology.lean:35`. Limit of an orbit is a fixed point.
- **`squeeze_zero`** and **`tendsto_pow_atTop_nhds_zero_of_lt_one`** —
  VERIFIED: already imported and used at `SahaEquilibrium.lean:611,606`.
- **`ContractingWith` / `efixedPoint' (IsComplete s) (MapsTo f s s) …` / `ContractingWith.restrict` /
  `tendsto_iterate_efixedPoint`** — VERIFIED: `Topology/MetricSpace/Contracting.lean:40,170,81,118`.
  Optional Banach shortcut for the damped map on the complete set `Set.Icc 0 M`
  (`IsClosed.isComplete`, VERIFIED `Topology/UniformSpace/Cauchy.lean:447`;
  `isCompact_Icc`, VERIFIED `…/Bounded.lean`). Not required — the hand-rolled ladder
  (mirroring the scalar one) avoids subtype-metric plumbing.
- **`LipschitzOnWith.of_dist_le_mul`** — VERIFIED: `Topology/MetricSpace/Lipschitz.lean:58`
  (only if a `LipschitzOnWith` phrasing is wanted; the repo prefers explicit
  `|G x − G y| ≤ … `, cf. `saha_inv_lipschitz`).
- **Even/odd → full `Tendsto` interleave**: ABSENT as a single lemma
  (searched: `tendsto_atTop.*two_mul`, `even.*odd.*tendsto`, `Nat.tendsto_of`,
  `IsCompl.*tendsto`). Must be hand-rolled via `Metric.tendsto_atTop` + `Nat.even_or_odd`
  (~10–15 lines). Small, standard.
- **Convexity of `x ↦ (x+S)⁻¹` (for Newton, direction d)**: ABSENT as a ready lemma —
  `convexOn_rpow` requires `p ≥ 1` (`Analysis/Convex/SpecificFunctions/Basic.lean:207`),
  not `p=−1`. `hasDerivAt_inv`/`deriv_inv` exist (`Analysis/Calculus/Deriv/Inv.lean:55,66`)
  but assembling concave-Newton global convergence is bespoke. Confirms (d) = grade C.

Reuse precedent already in the repo (same two-point-Lipschitz idiom the milestones
need): `saha_inv_lipschitz` (`SahaStability.lean:115`), `div_two_point_bound` (`:425`),
`rpow_three_halves_two_point` (`:237`), and the scalar ladder `sahaIter_*`
(`SahaEquilibrium.lean:485-614`).

---

## 4. Milestone ladder

Naming/`ι`/hypothesis conventions follow the existing multi-element block
(`[Fintype ι] [Nonempty ι]`, `hS : ∀ s, 0 < S s`, `hN : ∀ s, 0 < Ntot s`).
Add one `docs/scope-tags.tsv` row per new theorem (CI gate).

**M1 — Two-point identity + Lipschitz constant.** *(grade A; PURE-MATH; prereq: none)*
```
theorem multiElementIonized_two_point (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    multiElementIonized S Ntot x - multiElementIonized S Ntot y
      = (y - x) * ∑ s, Ntot s * S s / ((x + S s) * (y + S s))
theorem multiElementIonized_lipschitz (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |multiElementIonized S Ntot x - multiElementIonized S Ntot y|
      ≤ (∑ s, Ntot s / S s) * |x - y|
```
`Finset.sum_sub_distrib` + per-term `div_sub_div` + `Finset.sum_le_sum` with
`(x+S_s)(y+S_s) ≥ S_s²`. The workhorse for M3/M5. Also state the sharper on-interval
form with `L(a) = ∑ Ntot_s S_s/(a+S_s)²`.

**M2 — Fixed-point self-slope < 1.** *(grade A; PURE-MATH; prereq: existence lemma)*
```
theorem multiElement_selfSlope_lt_one (hr : 0 < r) (hfix : r = multiElementIonized S Ntot r) :
    (∑ s, Ntot s * S s / (r + S s) ^ 2) < 1
```
Identity (II): `∑ w_s/(r+S_s) < ∑ w_s/r = 1`, `w_s = a_s/(r+S_s)`, via
`Finset.sum_lt_sum` and `r + S_s > r`. Certifies unconditional local attraction; not a
prerequisite downstream but the conceptual keystone.

**M3 — Damped map: interval invariance + one-step contraction.** *(grade A/B; REDUCED; prereq: M1)*
Define `dampedIter S Ntot lam x := x + lam * (multiElementIonized S Ntot x - x)`.
With `Mlip := ∑ Ntot_s/S_s`, `lam := 1/(1+Mlip)`, `kappa := Mlip/(1+Mlip)`:
```
theorem dampedIter_mapsTo … : x ∈ Set.Icc 0 M → dampedIter … x ∈ Set.Icc 0 M
theorem dampedIter_contraction … (hx : x ∈ Set.Icc 0 M) :
    |dampedIter S Ntot lam x - r| ≤ kappa * |x - r|
```
`r = fixed point`; use `H(x)-r = H(x)-H(r) = (1-lam(1+c))(x-r)` from M1's exact
identity, `0 ≤ 1-lam(1+c) ≤ kappa < 1`.

**M4 — Geometric error decay (induction).** *(grade A; REDUCED; prereq: M3)*
```
theorem dampedIter_geometric_error … (n : ℕ) :
    |(dampedIter S Ntot lam)^[n] x0 - r| ≤ kappa ^ n * |x0 - r|
```
Verbatim structure of `sahaIter_geometric_error` (`:558`): invariance keeps iterates
in `[0,M]`, induct with M3.

**M5 — Damped convergence (headline).** *(grade A/B; REDUCED; prereq: M4)*
```
theorem dampedIter_tendsto … (hx0 : x0 ∈ Set.Icc 0 M) :
    Filter.Tendsto (fun n => (dampedIter S Ntot lam)^[n] x0) atTop (nhds r)
```
`squeeze_zero` + `tendsto_pow_atTop_nhds_zero_of_lt_one` (κ<1 unconditionally) — exact
analogue of `sahaIter_tendsto` (`:593`), but with **no `q<1` side hypothesis**: the
multi-element damped iteration converges for every admissible parameter set. Wire a
`![1,1]/![1,1]` non-vacuity witness (as at `:401-436`).

**M6 — No 2-cycle for `G`.** *(grade A/B; PURE-MATH; prereq: existence/uniqueness)*
```
theorem multiElementIonized_no_two_cycle (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hpq : multiElementIonized S Ntot p = q) (hqp : multiElementIonized S Ntot q = p) : p = q
```
The `∑ a_s S_s/D_s = 0` contradiction of §2(c). Self-contained finite-sum algebra;
the crisp new mathematical content. High insight-per-line; also usable standalone.

**M7 — Direct-iteration convergence (crown).** *(grade B; REDUCED; prereq: M6)*
```
theorem multiElementIonized_iter_tendsto … (hx0 : x0 ∈ Set.Icc 0 M) :
    Filter.Tendsto (fun n => (multiElementIonized S Ntot)^[n] x0) atTop (nhds r)
```
`Antitone.comp` (⇒ `Monotone (G∘G)`), `G`-invariance of `[0,M]`,
`monotone_iterate_of_id_le`/`antitone_iterate_of_le_id` for even/odd orbits,
`tendsto_atTop_ciSup`/`ciInf`, `isFixedPt_of_tendsto_iterate`, M6 to pin both limits to
`r`, plus a hand-rolled even/odd interleave. Proves the **literal** direct-substitution
iteration converges unconditionally. Heaviest bookkeeping; highest payoff.

**M8 — Newton rate.** *(grade C; prereq: new convexity/deriv lemmas — defer)*
Optional quadratic-rate refinement of §2(d); needs concave-Newton infrastructure not in
mathlib. Out of scope for the first pass.

---

## 5. Risks & dead ends

- **Plain direct contraction (a) is not the answer alone.** `L(0)=∑Ntot_s/S_s<1` is
  physically narrow; presenting (a) as "multi-element convergence" would overstate
  scope. It must be labelled a REDUCED *conditional* result, subordinate to M5/M7.
- **Which iteration is "the" solver loop?** Damping (M5) changes the map; a reviewer may
  object that the real CF-LIBS code substitutes directly. Mitigation: M7 covers the
  literal direct map; and the scalar leg already set the precedent of iterating a
  reformulated map (√-form) — document the scope tag honestly (REDUCED: "damped/direct
  scheme; outer T-loop still open").
- **M7 interleave friction.** No mathlib even/odd→full lemma; the monotone-orbit branch
  (increasing vs decreasing depending on `x0 ⋛ G(G x0)`) doubles the case work. Real but
  bounded (~40–70 lines total). If it stalls, M5 already delivers a publishable
  unconditional convergence theorem — M7 is upside, not a blocker.
- **`G∘G` is not a global 2-step contraction** in the multi-element case (single-species
  cancellation fails). Do **not** attempt a direct `|G(G x)−r| ≤ κ|x−r|` route; it is
  likely false globally. The monotone-subsequence argument is the correct instrument.
- **Newton (M8)** risks sinking a session into convexity/deriv plumbing for only a rate
  improvement. Defer unless a quadratic-rate claim is specifically wanted.
- **Not false anywhere:** identities (I),(II) and the no-2-cycle contradiction are
  exact; existence/uniqueness are already theorems. No direction here is mathematically
  doomed — the risk is purely formalization effort, concentrated in M7.

---

## 6. Recommendation

**Attack now.** The frontier is tractable with current mathlib and heavily reuses the
existing scalar ladder and the repo's two-point-Lipschitz idiom. No upstream mathlib
dependency is required for M1–M7 (only M8/Newton would need new convexity
infrastructure).

**Single best first milestone: M1** (`multiElementIonized_two_point` +
`multiElementIonized_lipschitz`), grade A, PURE-MATH, no prerequisites. It is the exact
algebraic core every downstream milestone consumes, it mirrors `saha_inv_lipschitz`
(`SahaStability.lean:115`) so the proof idiom is already in-repo, and it converts the
abstract "iteration converges" goal into concrete, verified inequalities.

**Then** proceed M3→M4→M5 to land the **unconditional damped-convergence headline**
(`dampedIter_tendsto`) — the cleanest strong result, structurally identical to
`sahaIter_tendsto`. **In parallel** M6 (no-2-cycle) is independent and self-contained;
land it next as the standalone insight, then M7 for the crown (literal direct iteration,
unconditional). Defer M8 (Newton) indefinitely.

Whole-frontier effort: **L** (M1–M7; M1–M2 are a single short session, M3–M5 one
session, M6 one session, M7 the long pole).
