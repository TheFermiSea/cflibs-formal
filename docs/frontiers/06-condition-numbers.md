# Frontier 06 — Quantitative condition numbers (beyond the rank gate)

*Planning dossier. Not code. No `.lean` was edited to produce it. Every current-state claim is
anchored to a real declaration; every mathlib claim is grepped and marked VERIFIED / ABSENT
against the pinned toolchain (Lean 4.31.0, the mathlib revision in `lake-manifest.json`).*

---

## 1. The formal obstacle

The repo has closed the **rank** gate for the Boltzmann-plot fit but not the **conditioning**
gate. The exact current state:

- `CflibsFormal/OLS.lean:185` — `designNormalMatrix (E : ι → ℝ) : Matrix (Fin 2) (Fin 2) ℝ`,
  the normal matrix `XᵀX` of the two-column design `[E | 1]`:
  `![![∑ Eₖ², ∑ Eₖ], ![∑ Eₖ, n]]` with `n = Fintype.card ι`.
- `CflibsFormal/OLS.lean:194` — `det_designNormalMatrix`:
  `(designNormalMatrix E).det = (Fintype.card ι) * ∑ k, (E k - mean E) ^ 2`, i.e. `det = n·SS_E`.
- `CflibsFormal/OLS.lean:220` — `designNormalMatrix_det_ne_zero_iff`:
  `det ≠ 0 ↔ 0 < ∑ k, (E k - mean E) ^ 2`. So the standing nondegeneracy hypothesis
  `hvar : 0 < SS_E` used everywhere (`olsSlope_noise_gain`, `ols_recovers_line`,
  `ols_minimizes_rss`, the whole `ErrorBudget` chain) **is** design-matrix nonsingularity.

The ledger records the residual precisely — `docs/SOLVER_FORMALIZATION_GAPS.md:76`:

> The design-matrix leg is ✅ closed … Still open: a quantitative condition-number (not just
> rank) analysis.

The obstacle is that `det ≠ 0` is a **binary** gate: it certifies invertibility but says nothing
about **how much a perturbation of the right-hand side is amplified** by the solve. `det = n·SS_E`
can be tiny (near-degenerate energies) while still nonzero; the rank gate passes but the fit is
numerically worthless. We currently have **no** theorem of the shape

```
‖Δ(solution)‖  ≤  κ · ‖Δ(rhs)‖              -- absolute amplification
‖Δ(solution)‖ / ‖solution‖  ≤  κ · ‖Δrhs‖ / ‖rhs‖   -- relative amplification
```

for the normal-equation solve, nor a definition of `κ` (the condition number) of
`designNormalMatrix`. The scalar sensitivity constants that *do* exist —
`olsSlope_noise_gain` (`OLS.lean:128`, `∑ wₖ² = 1/SS_E`) and `olsIntercept_stable_centered`
(`ErrorBudget.lean:297`, intercept gain on the centered design) — are the **per-channel**
amplifications but have never been assembled into a matrix condition number or shown to *be* the
eigenvalue ratio of the normal matrix.

---

## 2. Mathematical landscape

### The standard object

For a linear system `M x = c` with `M` symmetric positive-definite, the 2-norm condition number
is `κ₂(M) = λ_max(M) / λ_min(M)`, and the textbook perturbation theorem is
`‖Δx‖/‖x‖ ≤ κ₂(M)·‖Δc‖/‖c‖` (Golub & Van Loan, *Matrix Computations*, §2.6 — standard NLA, not a
LIBS citation; cite as textbook, [VERIFIED: universally standard]). This is the object the ledger
is asking for.

### Why the 2×2 case is closed-form (and why that matters)

`designNormalMatrix` is `2×2` and symmetric. Its eigenvalues are
`λ± = (tr ± √(tr² − 4·det))/2` with `tr = ∑Eₖ² + n`, `det = n·SS_E`. Everything is elementary
algebra of two reals — **no spectral theory is required in principle**. The seeded direction (a)
proposes exactly this: define `κ` via the explicit formula and prove the perturbation bound from
the explicit `2×2` inverse (adjugate / det). Evaluated below.

### The decisive observation — centering diagonalizes, scaling orthonormalizes

The physically standard Boltzmann-plot normalization references energies to their mean
(`mean E = 0`; this convention is already load-bearing in `olsIntercept_stable_centered`,
`ErrorBudget.lean:297`). Under centering, the two design columns — centered energy `(Eₖ − Ē)` and
the constant `1` — become **orthogonal**, because
`∑ₖ (Eₖ − Ē)·1 = ∑ₖ (Eₖ − Ē) = 0` (`centered_sum_zero`, `OLS.lean:64`). Hence the *centered*
normal matrix is **diagonal**:

```
Bᵀ B = ![![SS_E, 0], ![0, n]]        where B = [ (E − Ē) | 1 ]
```

For a diagonal PD matrix the eigenvalues are literally the diagonal entries, so

```
κ₂(centered normal matrix) = max(SS_E, n) / min(SS_E, n).
```

This is trivial to prove **and** interpretable — it is exactly seeded direction (b)'s
"centered-design theorem." It needs **zero** mathlib spectral machinery.

One layer deeper: if we additionally **scale** each column to unit norm (the *correlation* matrix,
the dimensionless conditioning object), the centered design has orthonormal columns and the
condition number collapses to **`κ = 1`**. In other words, the apparent conditioning "problem" of
the two-column design is entirely an artifact of the two columns having different scales
(`SS_E` [energy²] vs `n` [dimensionless] — note the mixed units, itself a warning that the raw
`max/min` ratio is **not** scale-invariant). The genuine, scale-free content is: the slope channel
has noise gain `1/SS_E` and the intercept channel has noise gain `1/n`, and *these are already
theorems* (`olsSlope_noise_gain`, `olsIntercept_stable_centered`).

### Evaluation of the seeded directions

- **(a) Spectral κ of the RAW matrix via the explicit `2×2` eigenvalue formula / adjugate inverse.**
  REFINE → partially REFUTE as the *primary* deliverable. It is provable (grade B, closed-form,
  no heavy API), but the raw condition number is **not shift-invariant**: replacing `E ↦ E + c`
  changes `∑Eₖ²` and `tr` while leaving the fit's physics identical. So `κ_raw` reports a units
  artifact, not a property of the data. The adjugate/`det` inverse is the right *tool* for the
  perturbation bound, but it should act on the **centered** matrix. Keep the explicit-inverse
  technique; drop the raw-matrix κ as the headline.

- **(b) Centered-design theorem: normal matrix = diag(SS_E, n), κ = max/min.** CONFIRM — this is
  the highest-value formulation. Trivial, interpretable, shift-invariant in the sense that matters
  (it is stated in the centered frame the solver already uses), and it plugs straight into the two
  existing per-channel noise gains. This is the recommended spine.

- **(c) Condition number of the Saha–Boltzmann JOINT (multi-element, ionization-shifted) design.**
  CONFIRM this is the **actual missing object**, and confirm it is genuinely absent. Grep result:
  the *only* real design/normal matrices in the repo are `designNormalMatrix` (`OLS.lean:185`) and
  the unrelated `chordIntensity` absorption matrix (`SpatialForward.lean:111`). `Alt/CSigma.lean`,
  `MultiSpecies.lean`, and `JointIdentifiability.lean` contain **no `Matrix` object at all** —
  the C-sigma / Saha–Boltzmann joint (`csigmaSahaOrdinate`, `CSigma.lean:324`;
  `csigma_saha_master_line`, `:339`) collapses multiple stages onto a *single* slope `1/(k_B T)`
  via a scalar ordinate shift, never forming a multi-column design. So the ≥3-column joint design
  matrix, its Gram/normal matrix, and its (non-closed-form) condition number are genuinely
  unformalized. This is where κ analysis stops being a repackaging and starts adding new content —
  but it needs new infrastructure (grade C, see §4/§5).

### Literature anchors (verified-list; free to cite)

- Boltzmann-plot multi-line OLS fit: Tognoni et al. 2010; two-line origin Ciucci et al. 1999
  [VERIFIED: on the repo's approved citation list].
- C-sigma / Saha–Boltzmann joint graph (the multi-element design that motivates (c)): Aguilera &
  Aragón 2007/2014 [VERIFIED: on the approved list; used already in `Alt/CSigma.lean` docstrings].
- Condition-number / perturbation theory itself is standard numerical linear algebra
  (Golub–Van Loan; Higham, *Accuracy and Stability of Numerical Algorithms*)
  [UNVERIFIED — must check exact edition/section before quoting in a Lean docstring; the *content*
  is textbook-standard and safe, only page-level citations need checking].

---

## 3. mathlib inventory  (toolchain: Lean 4.31.0 + pinned mathlib)

API needed for the recommended (centered-diagonal) path — all present:

- `Matrix.det_fin_two`, `Matrix.det_fin_two_of` — VERIFIED
  (`LinearAlgebra/Matrix/Determinant/Basic.lean:805,812`). Already used at `OLS.lean:206`.
- `Matrix.trace_fin_two`, `Matrix.trace_fin_two_of` — VERIFIED
  (`LinearAlgebra/Matrix/Trace.lean:220,232`). Needed only if the explicit-eigenvalue (direction a)
  route is taken.
- `Matrix.adjugate_fin_two`, `Matrix.adjugate_fin_two_of` — VERIFIED
  (`LinearAlgebra/Matrix/Adjugate.lean:373,380`). `adjugate_fin_two_of a b c d = !![d,-b;-c,a]` —
  the explicit `2×2` inverse numerator.
- `Matrix.inv_def` (`A⁻¹ = det⁻¹ • adjugate`), `Matrix.nonsing_inv_apply` — VERIFIED
  (`LinearAlgebra/Matrix/NonsingularInverse.lean:172,178`).
- `Matrix.diagonal`, `Matrix.diagonal_apply_eq/_ne`, `Matrix.det_diagonal` (`= ∏ dᵢ`) — VERIFIED
  (`Data/Matrix/Diagonal.lean:50,58,62`; `Determinant/Basic.lean:77`). Lets us state the centered
  matrix as `diagonal ![SS_E, n]` and re-derive `det = n·SS_E` as a consistency check.
- `Matrix.mulVec_smul`, `Matrix.smul_mulVec` — VERIFIED (`Data/Matrix/Mul.lean:800,806`).
- `abs_le_of_sq_le_sq` — VERIFIED (`Algebra/Order/Ring/Abs.lean:131`). Already used at
  `ErrorBudget.lean:237` — the sq→abs step for the perturbation bound.
- `Finset.sum_mul_sq_le_sq_mul_sq` (Cauchy–Schwarz) — VERIFIED
  (`Algebra/Order/BigOperators/Ring/Finset.lean:159`). Already used at `ErrorBudget.lean:115`.
- `min_le_max`, min/max order API — VERIFIED (`Order/MinMax.lean:87`).

API that is ABSENT or too heavy (drives the design toward the elementary route):

- A closed-form 2×2 eigenvalue lemma (`eigenvalues_fin_two` or similar) — **ABSENT from mathlib**
  (searched: `eigenvalues.*Fin 2`, `fin_two.*eigen`, `eigenvalue.*two` across
  `LinearAlgebra/Matrix/` and `Analysis/Matrix/`). Eigenvalues only exist via
  `Matrix.IsHermitian.eigenvalues`, defined in `Analysis/Matrix/Spectrum.lean` on top of the
  spectral theorem for inner-product spaces (`RCLike`, diagonalization). Usable but **disproportionately
  heavy** for a 2×2, and it would force `RCLike`/`ℂ`-flavored plumbing into an otherwise
  `ℝ`-elementary file. VERDICT: avoid — get eigenvalues from the *diagonal* form for free instead.
- A `Matrix.conditionNumber` / `condNumber` — **ABSENT from mathlib** (searched
  `conditionNumber`, `condition_number`, `condNumber` over all of `Mathlib/`). We define our own.
- `Matrix.PosDef.eigenvalues_pos` / `PosDef ↔ ∀ i, 0 < eigenvalues i` — present but in the heavy
  `Analysis/Matrix/PosDef.lean:72`; only needed if we go the spectral route. Skip.
- L² operator / spectral matrix norm (`Matrix.l2_opNorm`, `instNormedRingL2Op`) — present but in
  `Analysis/CStarAlgebra/Matrix.lean:184` (C*-algebra stack). VERIFIED to exist, judged **too heavy**;
  the recommended bounds are stated with explicit `∑`/`Real.sqrt` (the `ErrorBudget` house style),
  not an abstract operator norm.
- `Matrix.mulVec_fin_two` — **ABSENT** (no `mulVec_fin_two` anywhere in mathlib). But
  `Matrix.cons_mulVec` / `Matrix.mulVec_cons` **DO exist** (VERIFIED,
  `LinearAlgebra/Matrix/Notation.lean:350,356`; both `@[simp]`) — the earlier `Data/Matrix/`-scoped
  grep missed them. So the 2-vector solve can be expanded either with those `cons` lemmas or unfolded
  manually via `Fin.sum_univ_two` + `Matrix.cons_val_*` — routine, and the repo already does the
  manual pattern (e.g. `OLS.lean:248`). Their existence only makes M4/M5 easier, never harder.

Net: the recommended path uses **only** `Fin 2` determinant/adjugate/diagonal lemmas plus
elementary real algebra already exercised in `OLS.lean`/`ErrorBudget.lean`. No new mathlib
infrastructure. The heavy spectral/operator-norm stack is available but deliberately unused.

---

## 4. Milestone ladder

Notation: `SS_E := ∑ k, (E k - mean E)^2`, `n := Fintype.card ι`, `hvar : 0 < SS_E`.
Scope tags follow `docs/scope-tags.tsv` conventions (each new theorem needs a row or CI fails).

**M1 — Centered normal matrix is diagonal.** *(prereq: none; grade A; scope PURE-MATH)*
```lean
noncomputable def centeredDesignNormalMatrix (E : ι → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  ![![∑ k, (E k - mean E)^2, ∑ k, (E k - mean E)],
    ![∑ k, (E k - mean E),   (Fintype.card ι : ℝ)]]

theorem centeredDesignNormalMatrix_eq_diagonal [Nonempty ι] (E : ι → ℝ) :
    centeredDesignNormalMatrix E
      = Matrix.diagonal ![∑ k, (E k - mean E)^2, (Fintype.card ι : ℝ)]
```
Proof: off-diagonal entries are `centered_sum_zero E` (`OLS.lean:64`); `ext` + `Fin.cases`. The
keystone — makes M2–M6 near-trivial.

**M2 — Determinant consistency (centering is unimodular).** *(prereq M1; grade A; PURE-MATH)*
```lean
theorem det_centeredDesignNormalMatrix [Nonempty ι] (E : ι → ℝ) :
    (centeredDesignNormalMatrix E).det = (Fintype.card ι : ℝ) * ∑ k, (E k - mean E)^2
```
Via M1 + `Matrix.det_diagonal` (`= ∏ dᵢ = SS_E·n`). Cross-checks against the *raw*
`det_designNormalMatrix` (`OLS.lean:194`): both give `n·SS_E`, confirming centering preserves the
determinant. Low-cost, high-confidence anchor.

**M3 — Condition number definition + eigenvalue-ratio identity.** *(prereq M1; grade A; PURE-MATH)*
```lean
noncomputable def boltzmannConditionNumber (E : ι → ℝ) : ℝ :=
  max (∑ k, (E k - mean E)^2) (Fintype.card ι)
    / min (∑ k, (E k - mean E)^2) (Fintype.card ι)

theorem boltzmannConditionNumber_ge_one [Nonempty ι] (E : ι → ℝ) (hvar : 0 < SS_E) :
    1 ≤ boltzmannConditionNumber E
```
Because M1 exhibits the matrix as diagonal, its eigenvalues **are** `{SS_E, n}` by definition of
`diagonal` — no spectral API. `κ ≥ 1` from `min ≤ max` (`min_le_max`) + `min > 0` (needs
`hvar` and `n > 0`). Optionally add `boltzmannConditionNumber_eq_one_iff : κ = 1 ↔ SS_E = n`.

**M4 — Per-channel perturbation bound (the payoff, ties to existing gains).**
*(prereq M1; grade A/B; scope PURE-MATH, or REDUCED if stated on the physical solve)*
The diagonal solve `diag(SS_E, n) · x = c` is `x = (c₀/SS_E, c₁/n)`, so a perturbation `Δc`
propagates as `Δx = (Δc₀/SS_E, Δc₁/n)`:
```lean
theorem centeredSolve_perturbation [Nonempty ι] (E : ι → ℝ) (hvar : 0 < SS_E)
    (Δc : Fin 2 → ℝ) :
    (Δc 0 / (∑ k, (E k - mean E)^2))^2 + (Δc 1 / (Fintype.card ι : ℝ))^2
      ≤ (Δc 0 ^2 + Δc 1 ^2) / (min (∑ k, (E k - mean E)^2) (Fintype.card ι))^2
```
Pure algebra on two reals (`min_le` on each denominator + `div_le_div`). The slope channel gain
`1/SS_E` is *literally* `olsSlope_noise_gain` (`OLS.lean:128`) and the intercept channel gain
`1/n` is *literally* `olsIntercept_stable_centered` (`ErrorBudget.lean:297`); M4 is the theorem
that these two are the diagonal entries of one condition-number bound. Highest interpretive value.

**M5 — Relative 2-norm condition bound (the textbook statement).** *(prereq M1,M3,M4; grade B; PURE-MATH)*
```lean
theorem centeredSolve_relative_condition [Nonempty ι] (E : ι → ℝ) (hvar : 0 < SS_E)
    (c Δc : Fin 2 → ℝ) (hc : c 0 ^2 + c 1 ^2 ≠ 0) :
    Real.sqrt ((Δc 0/SS_E)^2 + (Δc 1/n)^2) / Real.sqrt ((c 0/SS_E)^2 + (c 1/n)^2)
      ≤ boltzmannConditionNumber E
          * Real.sqrt (Δc 0 ^2 + Δc 1 ^2) / Real.sqrt (c 0 ^2 + c 1 ^2)
```
Assembles `‖Δx‖ ≤ (1/λ_min)‖Δc‖` and `‖c‖ ≤ λ_max‖x‖` (both elementary component bounds on the
diagonal matrix, `λ_min = min(SS_E,n)`, `λ_max = max(SS_E,n)`), then divides. Uses `Real.sqrt`
monotonicity in the `ErrorBudget` style (cf. `olsSlope_stable_l2`, `ErrorBudget.lean:137`).
Grade B only for the `sqrt`/division bookkeeping; no new math.

**M6 — The honest interpretive theorem: scaled design is orthonormal ⇒ κ_scaled = 1.**
*(prereq M1; grade A; scope PURE-MATH)*
State that the correlation matrix of the centered design (each column scaled to unit norm) is the
`2×2` identity, hence perfectly conditioned; conclude that the *only* conditioning lever is `SS_E`
(entering exclusively through the slope channel's `1/SS_E` gain).
```lean
theorem centeredScaledDesign_orthonormal [Nonempty ι] (E : ι → ℝ) (hvar : 0 < SS_E) :
    -- normalized columns u = (E−Ē)/√SS_E and v = 1/√n satisfy ⟨u,u⟩=⟨v,v⟩=1, ⟨u,v⟩=0
    (∑ k, ((E k - mean E)/Real.sqrt SS_E)^2 = 1)
      ∧ (∑ k, (1/Real.sqrt (n:ℝ))^2 = 1)
      ∧ (∑ k, ((E k - mean E)/Real.sqrt SS_E) * (1/Real.sqrt (n:ℝ)) = 0)
```
This is the theorem that *de-mystifies the ledger ask*: it proves κ for the two-column design adds
no new scale-free content beyond the noise gains already in the repo. Do this one even if M5 is
skipped — it is the most defensible "we understood the question" deliverable.

**M7 — (DEFERRED) Multi-element Saha–Boltzmann joint design + its condition number.**
*(prereq: a general k-column design object that does not yet exist; grade C; scope REDUCED)*
Define the ≥3-column joint design (energy column, per-stage constants, ionization-energy shift
column — Aguilera & Aragón 2014), form its Gram/normal matrix, and bound its condition number.
Unlike the 2-column case this does **not** diagonalize under centering (the ionization-shift column
is not orthogonal to energy), so there is **no** closed-form eigenvalue ratio; it needs either the
heavy `Matrix.IsHermitian.eigenvalues` spectral stack or a bespoke block-structure argument. This
is the genuine open object; see §5. Recommend as a separate follow-on frontier, not this session.

---

## 5. Risks & dead ends

- **"κ adds nothing new" is a real risk to the whole frontier.** My analysis (§2) shows that for
  the 2-column design, the condition number is a repackaging of `1/SS_E` and `1/n`, and vanishes
  (κ=1) after column scaling. If the deliverable is *only* M1–M5, a fair critique is "you renamed
  two existing constants." MITIGATION: lead with M6 (the orthonormality/only-`SS_E` result) and
  frame M1–M5 as connecting the repo's bespoke sensitivity constants to the standard NLA object the
  runtime solver's numerics live in — plus the M2 determinant cross-check. Do **not** oversell a
  matrix κ as new physics.

- **Units / scale-dependence.** `max(SS_E, n)/min(SS_E, n)` mixes energy² with a pure count, so the
  raw ratio is not dimensionless and is not invariant under rescaling energy units. This is why M6
  (the *scaled* / correlation-matrix statement) is the mathematically honest headline and the raw κ
  (M3) must be documented as convention-dependent. Failing to flag this would be a rigor breach.

- **Direction (a) dead end.** Defining κ from the *raw* `designNormalMatrix` eigenvalues invites a
  shift-non-invariant, physically meaningless number (a mere `E ↦ E+c` changes it). Provable but not
  worth it; centered form only.

- **Spectral-API temptation.** Reaching for `Matrix.IsHermitian.eigenvalues`
  (`Analysis/Matrix/Spectrum.lean`) to "properly" get eigenvalues would drag `RCLike`/spectral-
  theorem imports into an `ℝ`-elementary module for zero gain over the diagonal form. Dead end for
  the 2×2; only unavoidable for M7 (k ≥ 3).

- **M7 is genuinely hard and may not be worth it soon.** The joint design object does not exist and
  its condition number has no closed form. It needs new infrastructure (a general design/Gram-matrix
  layer) that nothing else in the repo currently requires. Scoping it into this frontier would
  balloon the effort; better as its own dossier once a multi-element design object is motivated by a
  different need.

- **Mathematically-false traps: none identified.** M1–M6 are all true and elementary; the diagonal
  form and κ=1-after-scaling are standard facts. The only "false direction" is treating raw-matrix κ
  as meaningful.

---

## 6. Recommendation

**Attack now — the 2-column centered story (M1 → M2 → M3 → M4 → M6), defer M5 polish and M7.**

This closes the ledger's `SOLVER_FORMALIZATION_GAPS.md:76` "quantitative condition-number" residual
*honestly*: it delivers a named condition number (M3), the perturbation bound the rank gate lacks
(M4), a determinant cross-check (M2), and — crucially — the interpretive theorem (M6) that states
plainly what κ does and does not add over the existing `olsSlope_noise_gain` /
`olsIntercept_stable_centered` constants. It uses only `Fin 2` det/adjugate/diagonal lemmas and
real algebra already exercised in `OLS.lean`/`ErrorBudget.lean` — no new mathlib infrastructure,
no spectral or operator-norm stack.

**Single best first milestone: M1 — `centeredDesignNormalMatrix_eq_diagonal`** (grade A). It is the
keystone: once the centered normal matrix is exhibited as `diagonal ![SS_E, n]`, the eigenvalues
(M3), determinant (M2), perturbation bound (M4), and orthonormality (M6) all fall out with
elementary proofs, and it is provable in one session from `centered_sum_zero` alone.

**Defer** M7 (the multi-element Saha–Boltzmann joint design matrix) to a dedicated follow-on: it is
the one place where condition-number analysis becomes genuinely new content, but it requires a
multi-column design object the repo does not yet have and a non-closed-form (spectral) κ — grade C,
a separate frontier.
