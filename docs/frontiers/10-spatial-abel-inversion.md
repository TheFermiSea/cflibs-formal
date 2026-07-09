# Frontier 10 — Spatial inversion depth: Abel transform & onion peeling

*Planning dossier. No Lean edited; every current-state claim anchored to a real
declaration, every mathlib claim grepped against `.lake/packages/mathlib`
(v4.31.0). The value is RIGOR: the discrete inversion's **well-posedness** is
already proven in the repo, so this dossier goes one layer deeper — the explicit
recovery map and the *noise-amplification* (condition) bound that the existing
module deliberately disclaims — and honestly refuses the continuous Abel pair.*

---

## 1. The formal obstacle

`SpatialForward.lean` already relaxes single-zone homogeneity and proves the
discrete onion-peeling inversion is **well-posed**:

- `chordIntensity L ε := L.mulVec ε` (`SpatialForward.lean:111`) — the discrete
  Abel forward map `I = L·ε`.
- `ChordGeometry N` (`:125`) — packages `L` with `upper : L.BlockTriangular id`
  (`j < i → L i j = 0`) and `diag_pos : ∀ i, 0 < L i i`.
- `chordGeometry_det_ne_zero` (`:139`) — `det L = ∏ Lᵢᵢ ≠ 0`
  (via `Matrix.det_of_upperTriangular`).
- `chordGeometry_isUnit` (`:148`) — `L` invertible.
- `chord_profile_identifiable` (`:167`) — **the identifiability theorem**: equal
  chord data force equal radial profiles, via `Matrix.mulVec_injective_of_isUnit`.
- `singleZone_identifiable` (`:178`) — the `N = 1` specialization.

So "finite `N`-shell peeling is triangular ⇒ invertible ⇒ EXACT recovery" is
**already a theorem**. What the module cannot state today — the obstacle — is
everything *quantitative and constructive* about that recovery. Three concrete
gaps, in increasing difficulty:

1. **No explicit recovery map.** Identifiability is proven *abstractly*
   (`mulVec_injective_of_isUnit`): from `L·ε = L·ε'` deduce `ε = ε'`. The module
   never exhibits the actual **back-substitution / peeling recursion**
   `ε_i = (I_i − Σ_{j>i} L_ij ε_j) / L_ii` — the algorithm practitioners run — as
   a theorem, nor a named left inverse `peel` with `peel ∘ chordIntensity = id`.
   Injectivity says the answer is unique; it does not name the answer.

2. **No noise-amplification / condition bound** — the real hole. The module's own
   scope note (`SpatialForward.lean:63-79`) restricts itself to *invertibility*
   and states it "has no CF-LIBS code dependency beyond mathlib's linear
   algebra." There is **no** theorem of the `ErrorBudget` shape
   `‖Δε‖ ≤ κ·‖ΔI‖` telling you how a chord-intensity error `ΔI` is amplified into
   a radial-profile error `Δε`. This is exactly the physically dominant issue: the
   inward recursion subtracts previously-recovered outer shells, so errors
   **compound geometrically toward the core** (grounding: the onion-peeling
   variance "sums and geometrically amplifies … at the plasma axis `r→0` the
   discrete transform approaches a singularity," and Aguilera & Aragón's
   radially-resolved CF-LIBS must aggressively pre-smooth for exactly this reason
   — see §2.5 / citation set). The repo has the error-budget machinery
   (`ErrorBudget.lean`, deterministic worst-case bounds) but has never pointed it
   at the spatial inversion.

3. **The continuous Abel pair is unformalized** and, per the module's honest
   "Scope / not covered" note (`:63-73`), deliberately so:
   `ε(r) = −(1/π) ∫_r^R I′(y)/√(y²−r²) dy`. No injectivity/uniqueness theorem for
   the continuous transform exists. This is a refusal (§5), not a milestone.

Target objects we cannot yet state:

```
def onionPeel (G : ChordGeometry N) (I : Fin N → ℝ) : Fin N → ℝ      -- explicit inverse
theorem onionPeel_chordIntensity (G) (ε) : onionPeel G (chordIntensity G.L ε) = ε
theorem peeling_amplification (G) (ε ε') :                            -- ErrorBudget-style
    ‖ε − ε'‖∞ ≤ (peelingCondFactor G) · ‖chordIntensity G.L ε − chordIntensity G.L ε'‖∞
```

---

## 2. Mathematical landscape

Notation throughout: `N` shells, index `i : Fin N`; the **outermost** shell is the
largest index (`i = N−1`, a chord whose turning radius is largest crosses only its
own shell). `L.upper` gives `L i j = 0` for `j < i`, so row `i` of `I = L·ε` reads
```
I_i = Σ_j L_ij ε_j = L_ii · ε_i  +  Σ_{j>i} L_ij ε_j        (⋆)
```
(the `j < i` terms vanish; the `j > i` terms are the outer shells already peeled).

### 2.1 The peeling identity — CONFIRMED (grade A)

Solving (⋆) for `ε_i` (legal because `L_ii > 0`):
```
ε_i = (I_i − Σ_{j>i} L_ij ε_j) / L_ii .                     (P)
```
This is the onion-peeling recursion **as an exact identity about the true
profile** — no well-founded recursion is needed to *state* it, because it is a
pointwise equation that the genuine `ε` satisfies for every `i`. Proof is pure
algebra: expand `chordIntensity G.L ε i = Σ_j L i j * ε j`
(`Matrix.mulVec` / `Matrix.mulVec_eq_sum`), split the sum at `j = i` and drop the
`j < i` block using `G.upper`, then `field_simp`/`div` with `(G.diag_pos i).ne'`.
This exposes the algorithm the module currently hides behind `mulVec_injective`.

### 2.2 The explicit recovery map — CONFIRMED (grade A/B)

Two equivalent constructions of a named inverse:

- **(a) via the matrix inverse.** `L` is a unit (`chordGeometry_isUnit`); take
  `onionPeel G I := G.L⁻¹.mulVec I`. Then
  `onionPeel G (chordIntensity G.L ε) = L⁻¹ (L ε) = ε` by
  `Matrix.inv_mulVec_eq_vec` (after promoting `IsUnit` to `Invertible` via
  `(chordGeometry_isUnit G).invertible` / `Matrix.invertibleOfIsUnitDet`). Grade
  A. Bonus structural fact: `L⁻¹` is itself **upper-triangular**
  (`Matrix.blockTriangular_inv_of_blockTriangular`, Block.lean:406) — the peeling
  really is inside-out; the recovered `ε_i` depends only on `I_j` for `j ≥ i`.

- **(b) via primitive recursion** matching (P). Define `onionPeel` by downward
  recursion on `Fin N` (`Fin.reverseInduction`) implementing (P) literally, and
  prove it agrees with (a). Grade B — only because `Fin.reverseInduction`
  bookkeeping is fiddly; the mathematics is trivial. Route (a) is the cheap win;
  (b) is the "practitioner's algorithm verbatim" luxury.

### 2.3 The single-shell perturbation step — CONFIRMED (grade A)

Fix two profiles `ε, ε'`; write `Δε = ε − ε'`, `ΔI = chordIntensity G.L ε −
chordIntensity G.L ε'`. The forward map is **linear**, so `ΔI = L·Δε` and (P)
applies verbatim to the differences:
```
Δε_i = (ΔI_i − Σ_{j>i} L_ij Δε_j) / L_ii .
```
Taking absolute values and the triangle inequality (`Finset.abs_sum_le_sum_abs`,
Group/Finset.lean:287) with `L_ii > 0`:
```
|Δε_i| · L_ii  ≤  |ΔI_i|  +  Σ_{j>i} |L_ij| · |Δε_j| .      (S)
```
This is the one-step amplification: the error at shell `i` is its own measurement
error `|ΔI_i|` plus the leakage of every already-recovered **outer** shell's
error through the geometric coupling `|L_ij|`, all divided by the self-path
`L_ii`. Grade A — direct from 2.1 by linearity.

### 2.4 The geometric amplification bound — CONFIRMED (grade B), the headline

Assemble (S) by downward induction. Introduce two geometry constants:
```
ℓ  := min_i L_ii              ( > 0 by diag_pos )               — smallest self-path
ρ  := max_i ( Σ_{j>i} |L_ij| ) / L_ii    ( ≥ 0 )               — off-diagonal-to-diagonal ratio
```
and let `m := ‖ΔI‖∞ = max_i |ΔI_i|`. From (S), `|Δε_i| ≤ m/ℓ + ρ · max_{j>i}
|Δε_j|`. Downward induction (base `i = N−1`: no outer shells, `|Δε_{N−1}| ≤ m/ℓ`)
gives the **closed geometric bound**
```
|Δε_i|  ≤  (m/ℓ) · Σ_{k=0}^{N−1−i} ρ^k ,      hence
‖Δε‖∞   ≤  (m/ℓ) · Σ_{k=0}^{N−1} ρ^k
        =  (m/ℓ) · (ρ^N − 1)/(ρ − 1)          if ρ ≠ 1        (geom_sum_eq)
        ≤  (m/ℓ) · N                          if ρ ≤ 1 .
```
Induction step: `|Δε_i| ≤ m/ℓ + ρ·(m/ℓ)·Σ_{k=0}^{N−2−i} ρ^k =
(m/ℓ)·Σ_{k=0}^{N−1−i} ρ^k`. The finite geometric sum is `geom_sum_eq`
(Field/GeomSum.lean:43: `Σ_{i<n} x^i = (x^n−1)/(x−1)`). The sup-collapse step
`⨆_i (m/ℓ)·Σ_{k≤N−1−i} ρ^k ≤ (m/ℓ)·Σ_{k<N} ρ^k` uses `ρ ≥ 0` (every dropped tail
term is nonnegative), which holds since `ρ` is a sup of `(Σ|L_ij|)/L_ii ≥ 0`.

**This is the honest amplification statement the ledger-style error budget wants.**
Its content: the condition factor grows like `ρ^N` — **geometric in the shell
count** — when off-diagonal coupling rivals the diagonal (`ρ ≳ 1`), which is
precisely the inward "core singularity" blow-up the grounding describes. When the
geometry is diagonally dominant per-row-normalized (`ρ < 1`) the factor saturates
at `(m/ℓ)·1/(1−ρ)`; the plausibly-realistic `ρ ≈ 1` regime gives the linear-in-`N`
floor `(m/ℓ)·N`. This mirrors `ErrorBudget.lean`'s deterministic worst-case
philosophy (adversarial errors, no statistical averaging — cf. its scope note
`ErrorBudget.lean:44-56`). Grade B: the only non-trivial Lean step is the downward
`Fin.reverseInduction`; every inequality is elementary and every lemma is present.

### 2.5 The abstract ℓ∞ condition bound — EVALUATED, complementary (grade B)

mathlib carries the ℓ∞ (max-abs-row-sum) induced matrix norm and its submultiplicative
`mulVec` bound:
```
‖A‖ = sup_i Σ_j ‖A i j‖        (Matrix.linfty_opNorm_def, Normed.lean:284)
‖A *ᵥ v‖ ≤ ‖A‖ · ‖v‖           (Matrix.linfty_opNorm_mulVec, Normed.lean:353)
```
Under `open scoped`/local `Matrix.linftyOpNormedAddCommGroup` (Normed.lean:247),
`Δε = L⁻¹ *ᵥ ΔI` gives immediately
```
‖Δε‖∞ ≤ ‖L⁻¹‖∞ · ‖ΔI‖∞ ,     with  ‖L⁻¹‖∞ = max_i Σ_j |L⁻¹_ij|
```
i.e. a *named condition factor* `peelingCondFactor G := ‖G.L⁻¹‖∞`. Grade B (only
cost: instantiating the scoped normed-matrix instance in an otherwise elementary
file — lighter than the C\*-algebra `l2_opNorm` / spectral stack that Frontier 06
§3 judged too heavy and deliberately unused, but still an instance-plumbing step).
NOTE this is the **ℓ∞ induced norm** (`linfty_opNorm_mulVec`, elementary max-abs-
row-sum) — *not* the L²/spectral operator norm Frontier 06 refused; those are
distinct objects and only the L² one is on the recorded refusal list.
**Verdict: EVALUATED, keep as a one-line companion, but §2.4 is the headline** —
`‖L⁻¹‖∞` is a black box, whereas the geometric `(m/ℓ)·Σρ^k` bound makes the
physics (self-path `ℓ`, coupling `ρ`, shell count `N`) *legible*, which is the
repo's whole value proposition. The two are consistent: `‖L⁻¹‖∞` is exactly what
the recursion (S) bounds by `Σρ^k/ℓ`.

### 2.6 The continuous Abel transform — REFUTED as a milestone (see §5)

The forward `I(y) = 2∫_y^R ε(r) r/√(r²−y²) dr` and inverse
`ε(r) = −(1/π)∫_r^R I′(y)/√(y²−r²) dy` are a singular integral-transform pair.
Grep confirms **no Abel transform, no inverse-Abel, no such singular-kernel
Volterra-operator injectivity exists in mathlib** (searched `abelTransform`,
`abel_transform`, `inverseAbel` across all of `Mathlib/` — zero hits). Formalizing
injectivity/uniqueness of the continuous transform needs improper/singular
integrals (Cauchy principal value at `r = y`), differentiation under the integral
sign, and a Volterra-uniqueness argument — a large analysis build with no CF-LIBS
payoff the discrete method does not already deliver. Refusal, not milestone.

---

## 3. mathlib inventory  (toolchain: Lean 4.31.0 + pinned mathlib)

Everything the discrete milestones (M1–M5) need is present; the continuous side
(M6) is genuinely ABSENT.

| Needed lemma / object | mathlib name + file (grep-verified) or ABSENT |
|---|---|
| Determinant of upper-triangular = ∏ diag | `Matrix.det_of_upperTriangular` — VERIFIED `LinearAlgebra/Matrix/Block.lean:324` (already used, `SpatialForward.lean:141`) |
| Injectivity of `mulVec` for a unit | `Matrix.mulVec_injective_of_isUnit` — VERIFIED, **defined** `Data/Matrix/Mul.lean:1105` (a use-site is `LinearAlgebra/Matrix/ToLin.lean:353`); already used, `SpatialForward.lean:171` |
| `IsUnit L ↔ IsUnit det` | `Matrix.isUnit_iff_isUnit_det` — VERIFIED (already used, `SpatialForward.lean:150`) |
| Left-inverse cancellation `L⁻¹(L v)=v` | `Matrix.inv_mulVec_eq_vec` — VERIFIED `LinearAlgebra/Matrix/NonsingularInverse.lean:279` (needs `[Invertible L]`, from `IsUnit.invertible`) |
| Inverse of triangular is triangular | `Matrix.blockTriangular_inv_of_blockTriangular` — VERIFIED `LinearAlgebra/Matrix/Block.lean:406` |
| Downward recursion on `Fin N` | `Fin.reverseInduction` — VERIFIED present in **Lean core** `Init/Data/Fin/Lemmas.lean` (available without import; used e.g. `Mathlib/Data/Fin/Tuple/Take.lean:79`) |
| Triangle inequality for finite sums | `Finset.abs_sum_le_sum_abs` — VERIFIED `Algebra/Order/BigOperators/Group/Finset.lean:287` |
| Finite geometric sum closed form | `geom_sum_eq : Σ_{i<n} x^i = (xⁿ−1)/(x−1)` — VERIFIED `Algebra/Field/GeomSum.lean:43` |
| ℓ∞ induced matrix norm (max abs row sum) | `Matrix.linfty_opNorm_def` — VERIFIED `Analysis/Matrix/Normed.lean:284`; instance `Matrix.linftyOpNormedAddCommGroup` `:247` |
| ℓ∞ `mulVec` submultiplicativity | `Matrix.linfty_opNorm_mulVec` — VERIFIED `Analysis/Matrix/Normed.lean:353` |
| `min`/`max` order API (for `ℓ`, `ρ`) | `min_le_max`, `le_max_left`, `Finset.min'`/`sup` — VERIFIED (standard; cf. Frontier 06 §3) |
| Continuous Abel transform / inverse | **ABSENT** (searched: `abelTransform`, `abel_transform`, `inverseAbel` — 0 hits in `Mathlib/`) |
| Triangular back-substitution *solver* as a def | **ABSENT** (searched: `backsub`, `back_sub`, `forward_sub`, `triangularSolve` — 0 hits; must construct, see M2b) |
| Improper/singular (principal-value) integral for the Abel kernel | **ABSENT for this kernel** — `intervalIntegral` exists but the `1/√(y²−r²)` endpoint singularity + differentiation-under-integral is not packaged; not attempted |

Reusable **in-repo** anchors (all build-verified):
- `chordIntensity`, `ChordGeometry`, `chordGeometry_isUnit`,
  `chord_profile_identifiable` (`SpatialForward.lean:111,125,148,167`) — the spine.
- `ErrorBudget.lean` — the deterministic worst-case bound *style* (`olsSlope_stable_l2`
  `:~137`, the `abs_le_of_sq_le_sq` / triangle-inequality patterns) that M4 mirrors.
- `OLS.lean` — `Matrix`-API usage patterns (`Fin.sum_univ_two`, `Matrix.cons_val_*`)
  for expanding small `mulVec`s in witnesses.

Net: **zero new mathlib infrastructure** for M1–M5 (the discrete story); the heavy
analysis stack the continuous M6 would need is genuinely absent and deliberately
unused.

---

## 4. Milestone ladder

All proposed to live in `SpatialForward.lean` (reuses `ChordGeometry` and the
`isUnit` lemma directly; keeps the import surface at just `Mathlib`). Each new
result needs a `docs/scope-tags.tsv` row or CI fails.

### M1 — `peeling_identity` (the recursion as an exact identity) · grade **A**
```lean
theorem peeling_identity {N : ℕ} (G : ChordGeometry N) (eps : Fin N → ℝ) (i : Fin N) :
    eps i = (chordIntensity G.L eps i - ∑ j ∈ Finset.univ.filter (i < ·), G.L i j * eps j)
              / G.L i i
```
Scope: **PURE-MATH** — Parigger 2016 (onion-peeling back-substitution). Prereq:
none. Proof: unfold `chordIntensity`/`mulVec` to `Σ_j L i j * eps j`; split off
`j = i`; kill `j < i` via `G.upper` (`BlockTriangular id`); `field_simp` with
`(G.diag_pos i).ne'`. This is the "hidden algorithm" made explicit — the single
highest-value cheap win, and the base for M3/M4.

### M2 — `onionPeel` + `onionPeel_chordIntensity` (explicit recovery map) · grade **A** (route a)
```lean
noncomputable def onionPeel {N : ℕ} (G : ChordGeometry N) (I : Fin N → ℝ) : Fin N → ℝ :=
  G.L⁻¹.mulVec I
theorem onionPeel_chordIntensity {N : ℕ} (G : ChordGeometry N) (eps : Fin N → ℝ) :
    onionPeel G (chordIntensity G.L eps) = eps
theorem onionPeel_blockTriangular {N : ℕ} (G : ChordGeometry N) :
    (G.L⁻¹).BlockTriangular id          -- recovery is genuinely inside-out
```
Scope: **PURE-MATH** — Parigger 2016. Prereq: none (uses
`chordGeometry_isUnit`). Proof: `IsUnit.invertible`/`Matrix.invertibleOfIsUnitDet`
then `Matrix.inv_mulVec_eq_vec`; the triangularity from
`Matrix.blockTriangular_inv_of_blockTriangular`. Names the answer that
`chord_profile_identifiable` only proved unique. *(Optional M2b, grade B: a
primitive-recursive `onionPeel'` via `Fin.reverseInduction` implementing (P)
literally, proven equal to `onionPeel` — the practitioner's algorithm verbatim.)*

### M3 — `peeling_single_step` (one-shell perturbation) · grade **A**
```lean
theorem peeling_single_step {N : ℕ} (G : ChordGeometry N) (eps eps' : Fin N → ℝ) (i : Fin N) :
    |eps i - eps' i| * G.L i i
      ≤ |chordIntensity G.L eps i - chordIntensity G.L eps' i|
          + ∑ j ∈ Finset.univ.filter (i < ·), |G.L i j| * |eps j - eps' j|
```
Scope: **PURE-MATH**. Prereq: M1 (apply to `eps` and `eps'`, subtract — or use
linearity `ΔI = L·Δε` directly). Proof: `peeling_identity` twice, subtract, clear
`L i i > 0`, then `Finset.abs_sum_le_sum_abs` + `abs_mul`. Inequality (S) of §2.3.

### M4 — `peeling_amplification` (geometric-in-`N` condition bound) · grade **B**, HEADLINE
```lean
noncomputable def peelDiagFloor {N} (G : ChordGeometry N) : ℝ := ⨅ i, G.L i i      -- ℓ > 0
noncomputable def peelCouplingRatio {N} (G : ChordGeometry N) : ℝ :=               -- ρ ≥ 0
  ⨆ i, (∑ j ∈ Finset.univ.filter (i < ·), |G.L i j|) / G.L i i
theorem peeling_amplification {N : ℕ} (G : ChordGeometry N) (eps eps' : Fin N → ℝ) :
    (⨆ i, |eps i - eps' i|)
      ≤ (⨆ i, |chordIntensity G.L eps i - chordIntensity G.L eps' i|) / peelDiagFloor G
          * (∑ k ∈ Finset.range N, peelCouplingRatio G ^ k)
```
Scope: **REDUCED** (deterministic adversarial worst-case; the realized
amplification for benign geometries/errors is smaller) — Aguilera & Aragón 2007
(radially-resolved CF-LIBS, noise amplification toward the core) + Parigger 2016.
Prereq: M3. Proof: downward `Fin.reverseInduction`; base `i = N−1` (empty outer
set); step assembles M3 with `ρ·(previous bound)`; the range-sum is `geom_sum_eq`
(state the closed `(ρ^N−1)/(ρ−1)` form as a `have` when `ρ ≠ 1`, and the `≤ N/ℓ`
corollary when `ρ ≤ 1`). Non-vacuity witness in the module's `example` style: the
2-shell `L = !![1,1;0,1]` (already at `SpatialForward.lean:186`) has `ℓ = 1`,
`ρ = 1`, and `|Δε|∞ ≤ 2·|ΔI|∞` — checkable by hand. *This converts the module's
"no error analysis" disclaimer into the honest `ErrorBudget`-style bound, and is
the one milestone that adds genuinely new content over identifiability.*

### M5 — `peeling_condition_linfty` (abstract named condition factor) · grade **B**, optional
```lean
open scoped Matrix in
theorem peeling_condition_linfty {N : ℕ} (G : ChordGeometry N) (eps eps' : Fin N → ℝ) :
    ‖eps - eps'‖ ≤ ‖G.L⁻¹‖ * ‖chordIntensity G.L eps - chordIntensity G.L eps'‖
```
Scope: **PURE-MATH**. Prereq: M2. Proof: `Δε = L⁻¹ *ᵥ ΔI` (from
`inv_mulVec_eq_vec` + linearity), then `Matrix.linfty_opNorm_mulVec` under
`attribute [local instance] Matrix.linftyOpNormedAddCommGroup`. Delivers the
textbook `‖Δε‖ ≤ ‖L⁻¹‖·‖ΔI‖`; the `‖·‖` here is the **ℓ∞ induced norm** (max-abs-
row-sum), an elementary object distinct from the L²/spectral operator norm
Frontier 06 refused. `‖L⁻¹‖∞` is the named condition number but opaque — M4 is
what makes it legible, so ship M5 only as a cross-check.

### M6 — continuous Abel uniqueness · **REFUSAL** (see §5)
Not a milestone. Recorded so future sessions do not re-open it.

---

## 5. Refusals / traps

- **Do NOT attempt the continuous Abel transform or its inversion.** No Abel
  transform exists in mathlib (§3, grep-confirmed); its inverse is a singular
  (principal-value) integral requiring differentiation under the integral sign and
  Volterra-uniqueness for a `1/√(y²−r²)`-kernel operator. This is a large analysis
  project with **zero** CF-LIBS payoff beyond the discrete method already
  formalized, and the module's own scope note (`SpatialForward.lean:63-73`)
  already declares it out of scope. Keep it as cited background only. Re-litigating
  this is the trap; it is a deliberate, documented refusal.

- **Do NOT state a statistical / covariance amplification.** The natural-sounding
  `Σ_ε = L⁻¹ Σ_I (L⁻¹)ᵀ` (Gaussian noise pushforward) is *not* the repo's idiom:
  `ErrorBudget.lean` is deterministic worst-case, and the only probability layer
  (`Alt/OLSVariance.lean`) is scalar (`Var(β̂)=σ²/SS_E`). A multivariate-Gaussian
  pushforward through `L⁻¹` is a separate, heavier frontier (mathlib's
  `Matrix`-valued covariance / `MvGaussian` plumbing). M4's deterministic
  `‖Δε‖∞ ≤ κ·‖ΔI‖∞` is the honest, in-idiom statement.

- **Do NOT reach for the L²/spectral matrix operator norm.** M5 uses the
  *ℓ∞ induced* norm (`Matrix.linfty_opNorm_mulVec`, elementary, present). The
  L²/spectral operator-norm stack (`Matrix.l2_opNorm`, spectral theorem, Rayleigh
  quotients) is on the recorded refusal list and was judged too heavy and left
  deliberately unused by Frontier 06 §3 — do not substitute it for the ℓ∞ route.

- **Do NOT over-claim stability — the whole point is that it amplifies.** Never
  state an `N`-independent or `ρ`-independent bound: the inward recursion genuinely
  blows up geometrically as `ρ^N` (core singularity — grounded in the corpus). Any
  "the inversion is stable" phrasing without the explicit `(1/ℓ)·Σρ^k` factor is a
  rigor breach. Keep `peelDiagFloor` (`ℓ`) and `peelCouplingRatio` (`ρ`) explicit
  and visible in the statement; they *are* the physics.

- **Do NOT re-prove identifiability.** `chord_profile_identifiable`
  (`SpatialForward.lean:167`) already closes uniqueness; M1–M2 must *build on* it
  (name the recovered value), not restate it. The value added here is
  constructive + quantitative, not another injectivity proof.

- **Scope-tag / EXACT-vs-REDUCED judgement (the one call to get right).** M4 is
  **REDUCED**, not EXACT: it is an adversarial worst-case upper bound (like
  `ErrorBudget`'s `_l2` bounds), tight only for perfectly-correlated errors and
  the extremal-row geometry. Tagging it EXACT would over-claim. M1–M3, M5 are
  PURE-MATH (algebra / linear algebra). Add one `docs/scope-tags.tsv` row per
  result or the docs-sync CI gate fails. Use the repo's canonical citation string
  **"Aguilera & Aragón 2007"** (as in scope-tags.tsv rows 58, 180, 283–286) — not
  a "2009" variant, which is not on the approved citation list.

- **`Fin.reverseInduction` bookkeeping is the only real Lean risk** (M4, M2b).
  The mathematics is elementary; budget the effort for index-arithmetic on the
  `filter (i < ·)` outer-shell set and the base case `i = N−1` (empty set). If it
  fights back, prove M4 first via M5 (`‖L⁻¹‖∞` bound, no induction) to de-risk the
  ledger, then return for the legible geometric form.

---

## 6. Recommendation

**Attack M1–M4; ship M5 as a cross-check; refuse M6.** The identifiability gate is
already closed, so this frontier deepens it exactly where the module disclaims
depth: (M1) the peeling algorithm as a theorem, (M2) a named recovery map, and —
the real prize — (M4) the geometric-in-shell-count noise-amplification bound that
turns "we proved invertibility, we say nothing about error" into an
`ErrorBudget`-style honest condition statement grounded in the corpus's core-
singularity physics. It needs **zero new mathlib** (§3, all grep-verified) and
reuses `chordGeometry_isUnit` as its spine.

**Single best first milestone: M1 (`peeling_identity`)** — grade A, no
prerequisites, and it is the algebraic base that M3 and the M4 induction both
consume. Prove it and M2 in one session to de-risk the constructive layer; M4 is
then a bounded induction over the already-established single-step inequality.

**Defer/refuse:** the continuous Abel pair (M6) — genuinely absent from mathlib,
heavy analysis, no marginal payoff — and the statistical-covariance variant (own
frontier). The deterministic, legible `(1/ℓ)·Σρ^k` bound is the rigorous,
in-house-style deliverable.