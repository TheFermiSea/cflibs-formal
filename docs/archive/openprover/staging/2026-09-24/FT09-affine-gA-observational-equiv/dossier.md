# FT09-affine-gA-observational-equiv: planning dossier

*Source: deep audit 2026-09-24 (`docs/research/audit-2026-09-24/REPORT.md` §5 FT-09, queue
decomposition step 2), the verifier's headline with `hb : b·kB·T < 1` (REVISE, grade A). One change
from the audit sketch: the unused hypothesis `hFcal : 0 < Fcal` is dropped (the calibration cancels
identically; a proof compiled without it). Statement audit (2026-09-24): docstring only (the
signature is unchanged): `hA` is disclosed as a physical domain guard rather than a necessity,
the `Fcal = 0` junk point is disclosed, and the identification remark is narrowed to what this
single-stage statement supports. Group g3, priority 14. Toolchain: Lean / mathlib v4.33.1 (the
built `lean-main` checkout). Every Lean snippet below was compiled against that checkout on
2026-09-24 under the statement's own imports.*

## 1. Goal

Statement file: `statement.lean`, namespace `Plan.FT09`, imports `Mathlib` and
`CflibsFormal.ForwardMap`, `open Finset CflibsFormal`, `variable {ι : Type*} [Fintype ι]`.

```lean
theorem affine_gA_observational_equiv [Nonempty ι]
    {kB T N Fcal α b : ℝ} {g E A A' : ι → ℝ}
    (hkB : 0 < kB) (hT : 0 < T) (hg : ∀ k, 0 < g k) (hA : ∀ k, 0 < A k) (hN : 0 < N)
    (haff : ∀ k, A' k = A k * Real.exp (-(α + b * E k)))
    (hb : b * (kB * T) < 1) :
    ∃ T' N' : ℝ, 0 < T' ∧ 0 < N' ∧ 1 / (kB * T') = 1 / (kB * T) - b ∧
      ∀ k, Real.log (lineIntensity kB T N Fcal g E A k / (g k * A' k))
        = Real.log (lineIntensity kB T' N' Fcal g E A k / (g k * A k))
```

Physics: Boltzmann-plot ordinates computed with energy-affinely wrong `A'` equal the correct
ordinates of a plasma at a shifted temperature and rescaled density.

## 2. Definitions (imported)

```lean
-- CflibsFormal/Boltzmann.lean:36,41,50
noncomputable def boltzmannFactor (kB T E : ℝ) : ℝ := Real.exp (-E / (kB * T))
noncomputable def partitionFunction (kB T : ℝ) (g E : ι → ℝ) : ℝ :=
  ∑ k, g k * boltzmannFactor kB T (E k)
noncomputable def population (kB T N : ℝ) (g E : ι → ℝ) (k : ι) : ℝ :=
  N * g k * boltzmannFactor kB T (E k) / partitionFunction kB T g E
-- CflibsFormal/ForwardMap.lean:68
noncomputable def lineIntensity (kB T N Fcal : ℝ) (g E A : ι → ℝ) (k : ι) : ℝ :=
  Fcal * A k * population kB T N g E k
```

Repo lemma (usable): `partitionFunction_pos [Nonempty ι] {kB T : ℝ} {g E : ι → ℝ}
(hg : ∀ k, 0 < g k) : 0 < partitionFunction kB T g E` (`Boltzmann.lean:45`).

## 3. The math

Witnesses: `T' := 1/(kB·(1/(kB T) − b))`, `N' := N·e^α·U(T')/U(T)` with `U(·) =
partitionFunction kB · g E`. Then `−E/(kB T') = −E/(kB T) + b·E`, and
`I(T,N)/(g·A') = Fcal·N·e^{−E/kT}·e^{α+bE}/U(T) = Fcal·N'·e^{−E/kT'}/U(T') = I(T',N')/(g·A)`.
**The log arguments are equal**, so `congr 1`/`rw` suffices; no log algebra is needed.

## 4. Proof route (compiled as a whole)

Helpers (paste inside `namespace Plan.FT09`, after the `variable` line, before the target):

```lean
theorem exp_shift {kB T T' b e : ℝ} (hT' : 1 / (kB * T') = 1 / (kB * T) - b) :
    -e / (kB * T') = -e / (kB * T) + b * e := by
  rw [div_eq_mul_one_div, hT', div_eq_mul_one_div (-e) (kB * T)]
  ring

theorem ordinate_arg_eq [Nonempty ι] {kB T T' N Fcal α b : ℝ} {g E A A' : ι → ℝ}
    (hg : ∀ k, 0 < g k) (hA : ∀ k, 0 < A k)
    (haff : ∀ k, A' k = A k * Real.exp (-(α + b * E k)))
    (hT' : 1 / (kB * T') = 1 / (kB * T) - b) (k : ι) :
    lineIntensity kB T N Fcal g E A k / (g k * A' k)
      = lineIntensity kB T' (N * Real.exp α * partitionFunction kB T' g E
          / partitionFunction kB T g E) Fcal g E A k / (g k * A k) := by
  have hU : 0 < partitionFunction kB T g E := partitionFunction_pos hg
  have hU' : 0 < partitionFunction kB T' g E := partitionFunction_pos hg
  have hgk := (hg k).ne'
  have hAk := (hA k).ne'
  rw [haff k]
  unfold lineIntensity population boltzmannFactor
  rw [exp_shift hT', Real.exp_add, Real.exp_neg, Real.exp_add]
  field_simp
```

Target body:

```lean
  have hkT : 0 < kB * T := mul_pos hkB hT
  have hβ : 0 < 1 / (kB * T) - b := by
    rw [sub_pos, lt_div_iff₀ hkT]; linarith
  refine ⟨1 / (kB * (1 / (kB * T) - b)),
    N * Real.exp α * partitionFunction kB (1 / (kB * (1 / (kB * T) - b))) g E
      / partitionFunction kB T g E, by positivity, ?_, ?_, fun k => ?_⟩
  · have h1 := partitionFunction_pos (kB := kB) (T := 1 / (kB * (1 / (kB * T) - b))) (E := E) hg
    have h2 := partitionFunction_pos (kB := kB) (T := T) (E := E) hg
    positivity
  · field_simp
  · have hT'eq : 1 / (kB * (1 / (kB * (1 / (kB * T) - b)))) = 1 / (kB * T) - b := by
      field_simp
    rw [ordinate_arg_eq hg hA haff hT'eq k]
```

## 5. Mathlib lemmas (all resolved in v4.33.1)

`Real.exp_add : exp (x + y) = exp x * exp y`, `Real.exp_neg : exp (-x) = (exp x)⁻¹`,
`div_eq_mul_one_div`, `sub_pos`, `lt_div_iff₀`, `mul_pos`; tactics `field_simp`, `positivity`,
`linarith`, `ring`. Not needed but related: `Real.log_exp`, `Real.log_injOn_pos`.

## 6. Pitfalls and verifier rules

- `hb` is the whole existence condition: `0 < 1/(kB T) − b` ⇔ `b·kB·T < 1` (given `kB·T > 0`).
- `field_simp` needs `g k ≠ 0`, `A k ≠ 0`, `U(T) ≠ 0`, `U(T') ≠ 0` in context (the `have`s above);
  `exp` terms are nonzero automatically.
- `partitionFunction_pos` has implicit `kB T E`; pin them with named arguments as above when
  `positivity` needs the fact for a specific `T`.
- Keep the statement header verbatim (two imports, `open`, `namespace`, `variable`) and the target
  signature text up to `:=` (note: **no** `hFcal`); state it with `theorem`; do not name a helper
  `affine_gA_observational_equiv'`. Forbidden: `sorry`, `admit`, `native_decide`, `axiom`,
  `macro`/`syntax`/`elab`, `#`-commands, `set_option` other than heartbeat/recursion limits.

## 7. Scope, related results, consumers

Scope (two-axis): relation EXACT (identity of the ordinates within the model); `lineIntensity`
REDUCED (optically thin LTE, single stage); published REDUCED. Citation: Tognoni 2010, Ciucci 1999
(whitelisted). Related, already proved: `HeteroAtomicData.olsSlope_aliasing_A` (`:211`, EXACT) and
the audit's 8-line corollary `affine_gA_gauge_of_aliasing` (`frontier-verifier/Verify.lean:13`):
the OLS slope of the `A'`-ordinates is `−1/(kB T) + b`, the slope shadow of this statement.
Deferred (pre-registration): the grouped two-stage version (`ln n̂_e` shift
`(3/2)·ln(T'/T) + b·IP`) and the leakage bound after FT-15. Consumers: [backlog-id] / [backlog-id] (the
calibration layer can absorb this misspecification), [backlog-id], the C2 campaign.

Statement-audit notes (evidence `staging/2026-09-24/_statement-audit/ft09_probe.lean`, exit 0):

- `hA` is not load-bearing. `ordinate_arg_eq_noA` proves the ordinate-argument identity without
  it: at `A k = 0` both arguments are `0` (`x/0 = 0`) and both logs are `0`. The route in §4 uses
  `A k ≠ 0` for `field_simp`, so keep `hA` in the helper as written. `hA` stays in the target as a
  physical guard against that junk point. Dropping it would give a strictly stronger statement;
  that is a lead-level choice, not taken here.
- At `Fcal = 0` both ordinates are `log 0 = 0` for every `N'`, so the statement carries content
  about `N'` only for `Fcal > 0`; `T'` is pinned by its equation in all cases.
- What identifies `b` for this single-stage statement is an independent temperature
  (`b = 1/(kB T) − 1/(kB T')`). The roles of an independent `n_e` or a known composition belong
  to the deferred two-stage statement and are not proved here.
- Lead note (not a finding against this target): under the weaker-axis rule the existing
  `olsSlope_aliasing_A` EXACT row in `docs/scope-tags.tsv` would be retagged; flag at landing.
