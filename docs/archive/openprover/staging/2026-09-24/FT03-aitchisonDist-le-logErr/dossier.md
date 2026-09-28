# FT03-aitchisonDist-le-logErr: planning dossier

*Source: deep audit 2026-09-24 (`docs/research/audit-2026-09-24/REPORT.md` §5 FT-03, queue
decomposition items 3-5: `clr_sub_eq_centered_log`, `norm_centered_le`,
`aitchisonDist_le_logErr`; REVISE, grade A). Group g3, priority 13. Toolchain: Lean / mathlib
v4.33.1 (the built `lean-main` checkout). Every Lean snippet below was compiled against that
checkout on 2026-09-24 under the statement's own imports.*

## 1. Goal

Statement file: `statement.lean`, namespace `Plan.FT03`, imports `Mathlib` and
`CflibsFormal.AitchisonIsometry`, `open Finset CflibsFormal`, `variable {ι : Type*} [Fintype ι]`.

```lean
theorem aitchisonDist_le_logErr [Nonempty ι] {x y : ι → ℝ} (hx : ∀ k, 0 < x k)
    (hy : ∀ k, 0 < y k) (c : ℝ) :
    aitchisonDist y x ≤ Real.sqrt (∑ s, (Real.log (y s / x s) - c) ^ 2)
```

Meaning: a per-species log-ratio error bound, after removing any common shift `c`, bounds the
Aitchison distance between estimate `y` and truth `x`. Sharp at `c = mean of the log-ratios`.

## 2. Definitions (imported)

```lean
-- CflibsFormal/Aitchison.lean:69
noncomputable def clr (x : ι → ℝ) (k : ι) : ℝ :=
  Real.log (x k) - (∑ j, Real.log (x j)) / (Fintype.card ι)

-- CflibsFormal/AitchisonIsometry.lean:65 and :93 (that module has `variable [Nonempty ι]`)
noncomputable def clrE (x : ι → ℝ) : EuclideanSpace ℝ ι :=
  (WithLp.linearEquiv 2 ℝ (ι → ℝ)).symm (clr x)
noncomputable def aitchisonDist (x y : ι → ℝ) : ℝ :=
  ‖clrE x - clrE y‖
```

## 3. Proof route (three helpers, each compiled; then three lines)

With `e s = log (y s / x s)` and `D = card ι`:

1. `aitchisonDist y x = √(∑ s, (clr y s − clr x s)²)` (the flagged snag: unfolding the
   `EuclideanSpace` / `WithLp` norm).
2. `clr y s − clr x s = e s − (∑ j, e j)/D` (positivity, `Real.log_div`).
3. `∑ (e s − ē)² ≤ ∑ (e s − c)²` (parallel-axis: `∑(e−c)² = ∑(e−ē)² + 2(ē−c)·∑(e−ē) + D(ē−c)²`,
   and `∑(e − ē) = 0`).

Then (compiled, with the helpers below placed before the target):

```lean
  rw [aitchisonDist_eq_sqrt]
  apply Real.sqrt_le_sqrt
  rw [Finset.sum_congr rfl fun s _ => by rw [clr_sub_eq_centered_log hx hy s]]
  exact sum_sq_centered_le (fun s => Real.log (y s / x s)) c
```

Helpers (paste inside `namespace Plan.FT03`, after the `variable` line, before the target):

```lean
theorem aitchisonDist_eq_sqrt [Nonempty ι] (x y : ι → ℝ) :
    aitchisonDist y x = Real.sqrt (∑ s, (clr y s - clr x s) ^ 2) := by
  rw [aitchisonDist, EuclideanSpace.norm_eq]
  congr 1
  refine Finset.sum_congr rfl fun s _ => ?_
  simp [clrE, Real.norm_eq_abs, sq_abs]

theorem clr_sub_eq_centered_log [Nonempty ι] {x y : ι → ℝ} (hx : ∀ k, 0 < x k)
    (hy : ∀ k, 0 < y k) (s : ι) :
    clr y s - clr x s
      = Real.log (y s / x s) - (∑ j, Real.log (y j / x j)) / (Fintype.card ι : ℝ) := by
  simp only [clr, Real.log_div (hy _).ne' (hx _).ne', Finset.sum_sub_distrib]
  ring

theorem sum_sq_centered_le [Nonempty ι] (e : ι → ℝ) (c : ℝ) :
    ∑ s, (e s - (∑ j, e j) / (Fintype.card ι : ℝ)) ^ 2 ≤ ∑ s, (e s - c) ^ 2 := by
  have hD : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  set m := (∑ j, e j) / (Fintype.card ι : ℝ) with hm
  have h0 : ∑ s, (e s - m) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hm]
    field_simp
    ring
  have hsplit : ∑ s, (e s - c) ^ 2
      = ∑ s, (e s - m) ^ 2 + 2 * (m - c) * ∑ s, (e s - m)
        + (Fintype.card ι : ℝ) * (m - c) ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    rw [show (Fintype.card ι : ℝ) * (m - c) ^ 2 = ∑ _s : ι, (m - c) ^ 2 by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun s _ => by ring
  rw [hsplit, h0, mul_zero, add_zero]
  have : 0 ≤ (Fintype.card ι : ℝ) * (m - c) ^ 2 := by positivity
  linarith
```

Repo pattern for helper 3 (not importable here; `CflibsFormal/FisherLineSelection.lean:200`):
`sum_sq_sub_eq_spreadOn_add (E : ι → ℝ) (S : Finset ι) (hS : S.Nonempty) (c : ℝ) :
∑ j ∈ S, (E j - c) ^ 2 = spreadOn E S + (S.card : ℝ) * ((∑ i ∈ S, E i) / (S.card : ℝ) - c) ^ 2`.

## 4. Mathlib lemmas (all resolved in v4.33.1)

`EuclideanSpace.norm_eq : ‖x‖ = √(∑ i, ‖x.ofLp i‖ ^ 2)`, `Real.norm_eq_abs`, `sq_abs`,
`Real.sqrt_le_sqrt : x ≤ y → √x ≤ √y`, `Real.log_div : x ≠ 0 → y ≠ 0 → log (x / y) = log x − log y`,
`Finset.sum_congr`, `Finset.sum_sub_distrib`, `Finset.sum_add_distrib`, `Finset.mul_sum`,
`Finset.sum_const`, `Finset.card_univ`, `nsmul_eq_mul`, `Nat.cast_ne_zero`, `Fintype.card_ne_zero`.

## 5. Pitfalls and verifier rules

- `aitchisonDist` takes `[Nonempty ι]` (a section variable of `AitchisonIsometry`); every helper
  that mentions it needs `[Nonempty ι]`.
- The argument order is `aitchisonDist y x = ‖clrE y − clrE x‖`; helper 1 is stated in that order.
- The `simp [clrE, …]` in helper 1 unfolds `WithLp.linearEquiv`'s `symm` application to the
  coordinates; if it stalls after a mathlib change, `simp [clrE, WithLp.linearEquiv_symm_apply]`
  or `rfl`-based `show` on the coordinate is the place to look.
- Positivity is needed only through `Real.log_div`, which needs nonzero entries.
- Keep the statement header verbatim (two imports, `open`, `namespace`, `variable`) and the target
  signature text up to `:=`; state it with `theorem`; do not name a helper
  `aitchisonDist_le_logErr'`. Forbidden: `sorry`, `admit`, `native_decide`, `axiom`,
  `macro`/`syntax`/`elab`, `#`-commands, `set_option` other than heartbeat/recursion limits.

## 6. Scope and consumers

PURE-MATH (relation and definitions); published PURE-MATH; clr after Aitchison 1986
(whitelisted). Zero replacement must precede use (log 0 = 0). Consumer: the `U_i` of the
refuse-to-report policy (`FT03-pasPolicy-guarantees`), BL-02, G1 SC-03..05.
