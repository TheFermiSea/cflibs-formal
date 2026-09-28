# FT05: the truncation ratio `U/U_cut` is strictly increasing in temperature

Source: 2026-09-24 deep audit, frontier FT-05 items 2-3 (`tailKeep_cross` double-sum sign crux,
then strict monotonicity); verdict REVISE, grade A. Priority 5, group g2.

Statement audit (2026-09-24, M6 round): FIX, docstring only; queue-ready. The signature and the
`partitionFunctionCut` definition are unchanged. The theorem docstring no longer claims that
`D/U_cut` is "a positive combination of `exp(−(E_d − E_k)/(k_B T))`" (false: with kept levels at
`0`, `0.5` and a dropped level at `1`, `D/U_cut = e^{−β}/(1 + e^{−β/2})`); it now states the
cross-multiplied double-sum reduction of section 3. The genuinely new work is the crux in 4c.

## 1. Goal

Statement file: namespace `Plan.FT05`; imports `Mathlib`, `CflibsFormal.Boltzmann` only;
`open Finset CflibsFormal`; `variable {ι : Type*} [Fintype ι]`.

```lean
noncomputable def partitionFunctionCut (kB T cut : ℝ) (g E : ι → ℝ) : ℝ :=
  ∑ k ∈ univ.filter (fun k => E k < cut), g k * boltzmannFactor kB T (E k)

theorem cutRatio_strictMonoOn_temp {kB cut : ℝ} {g E : ι → ℝ} (hkB : 0 < kB)
    (hg : ∀ k, 0 < g k) (hkeep : ∃ k, E k < cut) (hdrop : ∃ k, cut ≤ E k) :
    StrictMonoOn (fun T => partitionFunction kB T g E / partitionFunctionCut kB T cut g E)
      (Set.Ioi 0)
```

Physics: truncating the partition-function sum at an energy `cut` (keep `E < cut`, drop
`cut ≤ E`) changes `U` by a factor `U/U_cut` that grows strictly with temperature whenever the
cutoff actually removes something and keeps something. So no temperature-independent factor can
absorb a cutoff change. The statement is generic; it asserts no cutoff policy.

## 2. Definitions

From `CflibsFormal/Boltzmann.lean` (the only repo module imported):

```lean
noncomputable def boltzmannFactor (kB T E : ℝ) : ℝ := Real.exp (-E / (kB * T))   -- line 37
lemma boltzmannFactor_pos (kB T E : ℝ) : 0 < boltzmannFactor kB T E                -- line 39
noncomputable def partitionFunction (kB T : ℝ) (g E : ι → ℝ) : ℝ :=                -- line 42
  ∑ k, g k * boltzmannFactor kB T (E k)
lemma partitionFunction_pos [Nonempty ι] {kB T : ℝ} {g E : ι → ℝ}                   -- line 45
    (hg : ∀ k, 0 < g k) : 0 < partitionFunction kB T g E
```

`partitionFunctionCut` is new (above). In goals, `univ.filter (fun k => E k < cut)` is displayed
as `∑ x ∈ univ with E x < cut, …` (same term). No module on main defines a truncated partition
function (`rg -i 'trunc|cutoff|partitionFunctionCut' CflibsFormal`: 0 hits).

## 3. Mathematical proof

Fix `0 < T1 < T2`, `β_i = 1/(k_B T_i)`, so `β1 > β2 > 0`. Let `K(T) = U_cut(T)` (kept sum) and
`D(T) = ∑_{cut ≤ E_d} g_d e^{−β E_d}` (dropped sum), so `U = K + D`.
1. `K(T) > 0` (a kept level exists, weights positive).
2. **Crux (`tailKeep_cross`)**: `D(T1)·K(T2) < D(T2)·K(T1)`. Expand both products as double sums
   over (dropped `d`, kept `k`):
   `D(T1)K(T2) = ∑_d ∑_k g_d g_k e^{−β1 E_d − β2 E_k}` and
   `D(T2)K(T1) = ∑_d ∑_k g_d g_k e^{−β2 E_d − β1 E_k}`.
   Termwise, the second exponent minus the first is `(β1 − β2)(E_d − E_k) > 0`, because
   `E_d ≥ cut > E_k`. Both index sets are nonempty (`hdrop`, `hkeep`), so the strict inequality
   survives summation.
3. `U/K` at `T1` < `U/K` at `T2` ⟺ `(K1 + D1)·K2 < (K2 + D2)·K1` (cross-multiply, `K1, K2 > 0`)
   ⟺ `D1·K2 < D2·K1`, which is step 2.

Numerics (audit, `_plan/numcheck.py`): 0 violations over 20000 random level sets.

## 4. Lean route

### 4a. Verified helpers (compiled in exactly this import/namespace context)

Place these after the definition (keep a blank line after the definition) and before the target.

```lean
/-- `U = U_cut + D`, `D` the sum over dropped levels (`cut ≤ E k`). -/
lemma partitionFunction_eq_cut_add_tail (kB T cut : ℝ) (g E : ι → ℝ) :
    partitionFunction kB T g E = partitionFunctionCut kB T cut g E
      + ∑ k ∈ univ.filter (fun k => cut ≤ E k), g k * boltzmannFactor kB T (E k) := by
  unfold partitionFunction partitionFunctionCut
  rw [← Finset.sum_filter_add_sum_filter_not univ (fun k => E k < cut)]
  simp only [not_lt]

/-- `U_cut > 0` once one level is kept. -/
lemma partitionFunctionCut_pos {kB T cut : ℝ} {g E : ι → ℝ} (hg : ∀ k, 0 < g k)
    (hkeep : ∃ k, E k < cut) : 0 < partitionFunctionCut kB T cut g E := by
  obtain ⟨k0, hk0⟩ := hkeep
  exact Finset.sum_pos (fun k _ => mul_pos (hg k) (boltzmannFactor_pos _ _ _))
    ⟨k0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk0⟩⟩

/-- Termwise sign crux: for a kept level `Ek < cut` and a dropped level `cut ≤ Ed`,
`bf(T1, Ed)·bf(T2, Ek) < bf(T2, Ed)·bf(T1, Ek)` when `0 < T1 < T2`. -/
lemma bf_cross_lt {kB T1 T2 cut Ed Ek : ℝ} (hkB : 0 < kB) (hT1 : 0 < T1) (hT12 : T1 < T2)
    (hk : Ek < cut) (hd : cut ≤ Ed) :
    boltzmannFactor kB T1 Ed * boltzmannFactor kB T2 Ek
      < boltzmannFactor kB T2 Ed * boltzmannFactor kB T1 Ek := by
  unfold boltzmannFactor
  rw [← Real.exp_add, ← Real.exp_add, Real.exp_lt_exp]
  have hkT1 : 0 < kB * T1 := mul_pos hkB hT1
  have hβ : 1 / (kB * T2) < 1 / (kB * T1) :=
    one_div_lt_one_div_of_lt hkT1 (mul_lt_mul_of_pos_left hT12 hkB)
  have e1 : -Ed / (kB * T1) + -Ek / (kB * T2)
      = -(Ed * (1 / (kB * T1))) - Ek * (1 / (kB * T2)) := by ring
  have e2 : -Ed / (kB * T2) + -Ek / (kB * T1)
      = -(Ed * (1 / (kB * T2))) - Ek * (1 / (kB * T1)) := by ring
  rw [e1, e2]
  nlinarith [mul_pos (sub_pos.mpr (lt_of_lt_of_le hk hd)) (sub_pos.mpr hβ)]
```

### 4b. Verified outer assembly (compiles with only `hcross` open)

```lean
  intro T1 hT1 T2 hT2 hlt
  simp only [Set.mem_Ioi] at hT1 hT2
  show partitionFunction kB T1 g E / partitionFunctionCut kB T1 cut g E
      < partitionFunction kB T2 g E / partitionFunctionCut kB T2 cut g E
  have hK1 : 0 < partitionFunctionCut kB T1 cut g E := partitionFunctionCut_pos hg hkeep
  have hK2 : 0 < partitionFunctionCut kB T2 cut g E := partitionFunctionCut_pos hg hkeep
  have hcross :
      (∑ k ∈ univ.filter (fun k => cut ≤ E k), g k * boltzmannFactor kB T1 (E k))
          * partitionFunctionCut kB T2 cut g E
        < (∑ k ∈ univ.filter (fun k => cut ≤ E k), g k * boltzmannFactor kB T2 (E k))
          * partitionFunctionCut kB T1 cut g E := by
    sorry   -- THE CRUX: see 4c
  rw [partitionFunction_eq_cut_add_tail kB T1 cut, partitionFunction_eq_cut_add_tail kB T2 cut,
    div_lt_div_iff₀ hK1 hK2]
  nlinarith [hcross]
```

### 4c. The crux `hcross` (the actual work)

1. `unfold partitionFunctionCut`, then `rw [Finset.sum_mul_sum, Finset.sum_mul_sum]` to get
   `∑ d ∈ drop, ∑ k ∈ keep, (g d * bf T1 (E d)) * (g k * bf T2 (E k))
    < ∑ d ∈ drop, ∑ k ∈ keep, (g d * bf T2 (E d)) * (g k * bf T1 (E k))`.
2. Outer strict sum: `Finset.sum_lt_sum_of_nonempty` with the nonempty dropped filter built
   from `hdrop` (`⟨d0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd0⟩⟩`).
3. Inner strict sum: `Finset.sum_lt_sum_of_nonempty` again with the kept filter (from `hkeep`).
4. Termwise: get `cut ≤ E d` and `E k < cut` from `(Finset.mem_filter.mp hd).2` /
   `(Finset.mem_filter.mp hk).2`; rewrite each side as `(g d * g k) * (bf … * bf …)` by `ring`;
   then `mul_lt_mul_of_pos_left (bf_cross_lt hkB hT1 hlt hk' hd') (mul_pos (hg d) (hg k))`.

## 5. Mathlib lemmas (all `#check`ed on the pinned v4.33.1 tree)

- `Finset.sum_mul_sum (s : Finset ι) (t : Finset κ) (f : ι → R) (g : κ → R) :
  (∑ i ∈ s, f i) * ∑ j ∈ t, g j = ∑ i ∈ s, ∑ j ∈ t, f i * g j`
  (`Algebra/BigOperators/Ring/Finset.lean:62`).
- `Finset.sum_lt_sum_of_nonempty : s.Nonempty → (∀ i ∈ s, f i < g i) → ∑ i ∈ s, f i < ∑ i ∈ s, g i`.
- `Finset.sum_filter_add_sum_filter_not (s) (p) (f) :
  ∑ x ∈ s with p x, f x + ∑ x ∈ s with ¬p x, f x = ∑ x ∈ s, f x`.
- `Finset.sum_pos : (∀ i ∈ s, 0 < f i) → s.Nonempty → 0 < ∑ i ∈ s, f i`.
- `Finset.mem_filter : a ∈ filter p s ↔ a ∈ s ∧ p a`; `Finset.filter_nonempty_iff`.
- `div_lt_div_iff₀ (hb : 0 < b) (hd : 0 < d) : a / b < c / d ↔ a * d < c * b`.
- `Real.exp_lt_exp : exp x < exp y ↔ x < y`; `Real.exp_add`.
- `one_div_lt_one_div_of_lt : 0 < a → a < b → 1 / b < 1 / a`; `mul_lt_mul_of_pos_left`.

## 6. Pitfalls

- Decidability: the filters use the classical instances for `<`/`≤` on `ℝ`; write the filter
  predicates exactly as `fun k => E k < cut` / `fun k => cut ≤ E k` so the helper `rw`s match.
  `sum_filter_add_sum_filter_not` produces `¬ E k < cut`; `simp only [not_lt]` converts it (as
  in the helper).
- Nothing from `SahaStability` or other modules is importable (verifier: no extra imports).
- Do not use `div_lt_div_iff` (deprecated/renamed); use `div_lt_div_iff₀`.
- Verifier rules: copy the `open` line, the `variable` line and the `partitionFunctionCut`
  definition byte-for-byte, with a blank line after the definition (the definition is matched
  textually up to the next blank line or `theorem`/`lemma`/docstring). Keep the theorem signature
  byte-identical. Helper names must not begin with `cutRatio_strictMonoOn_temp` and must come
  before the target. No new imports, no `set_option` beyond heartbeat/recursion limits, no `#`
  commands.

## 7. Scope

Own relation PURE-MATH; definitions used carry no policy; predicted published tag PURE-MATH.
Follow-ups (hand-landable once this lands): `cutRatio_injOn` (verifier's revision of (iii)) and
the two-temperature non-absorbability corollary. Consumers: BL-41, R1-02 (critical), R1-03,
R1-10, BL-47. Literature: none needed (PURE-MATH). Do not cite Mihalas 1978 (UNVERIFIED on the
whitelist) or Hummer & Mihalas 1988 (unverified).
