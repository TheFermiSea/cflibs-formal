# FT07-classicComposition-atomicData-error-rel: planning dossier

*Source: deep audit 2026-09-24 (`docs/research/audit-2026-09-24/REPORT.md` §5 FT-07, queue
decomposition item 5). The statement audit (2026-09-24) replaced the verifier's form
(`hδ : δ < 1/2`, constant `2δ/(1 − 2δ)`) with the **sharp form** below. It has the same premises
except `hδ1 : δ < 1` (the absolute twin's domain) and the constant `2δ/(1 − δ)`, so it strictly
dominates the old form. The old constant and the `δ < 1/2` restriction were artifacts of routing
through the additive density envelope. Group g3, priority 6. Toolchain: Lean / mathlib v4.33.1 (the
built `lean-main` checkout). Every Lean snippet below was compiled against that checkout on
2026-09-24 under the statement's own imports.*

## 1. Goal

Statement file: `statement.lean`, namespace `Plan.FT07`, imports `Mathlib` and
`CflibsFormal.AtomicDataPerturbation`, `open Finset CflibsFormal`,
`variable {ι : Type*} [Fintype ι] {κ : Type*} [Fintype κ]`.

```lean
theorem classicComposition_atomicData_error_rel [Nonempty ι] [Nonempty κ]
    {kB T Fcal δ : ℝ} {N : κ → ℝ} {g E A g' E' A' : κ → ι → ℝ} {u : κ → ι}
    (hg : ∀ s k, 0 < g s k) (hg' : ∀ s k, 0 < g' s k) (hFcal : 0 < Fcal)
    (hA : ∀ s, 0 < A s (u s)) (hA' : ∀ s, 0 < A' s (u s))
    (hN : ∀ s, 0 < N s) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hpert : ∀ s, |responseFactor kB T (g' s) (E' s) (A' s) (u s)
                    - responseFactor kB T (g s) (E s) (A s) (u s)|
                  ≤ δ * responseFactor kB T (g s) (E s) (A s) (u s))
    (s : κ) :
    |composition (recoveredDensity kB T Fcal g E A g' E' A' u N) s - composition N s|
      ≤ (2 * δ / (1 - δ)) * composition N s
```

Physics: species `s` (index `κ`) emitted with true atomic data at density `N s`, read back with
wrong data by the classic CF-LIBS reader; per-species relative response-factor error `≤ δ`.
Conclusion: the recovered number fraction's error scales with the true fraction.

## 2. Definitions (all in imported modules; no new definitions in the statement)

```lean
-- CflibsFormal/Closure.lean:41,46
noncomputable def totalDensity (n : κ → ℝ) : ℝ := ∑ s, n s
noncomputable def composition (n : κ → ℝ) (s : κ) : ℝ := n s / totalDensity n

-- CflibsFormal/AtomicDataPerturbation.lean:114
noncomputable def responseFactor (kB T : ℝ) (g E A : ι → ℝ) (u : ι) : ℝ :=
  g u * A u * boltzmannFactor kB T (E u) / partitionFunction kB T g E

-- CflibsFormal/AtomicDataPerturbation.lean:282
noncomputable def recoveredDensity (kB T Fcal : ℝ) (g E A g' E' A' : κ → ι → ℝ)
    (u : κ → ι) (N : κ → ℝ) (s : κ) : ℝ :=
  Classic.classicDensity kB T Fcal (g' s) (E' s) (A' s) (u s)
    (lineIntensity kB T (N s) Fcal (g s) (E s) (A s) (u s))
```

## 3. Proof route (two steps, both compiled)

Why it is true: the model gives `N̂_t = N_t·ρ_t/ρ'_t` exactly, and `hpert` gives
`(1 − δ)·ρ_t ≤ ρ'_t ≤ (1 + δ)·ρ_t`, so `(1 − δ)·N̂_t ≤ N_t ≤ (1 + δ)·N̂_t` for every species.
Summing gives the same two-sided bound on the totals, and closure puts `Ĉ_s/C_s` in
`[(1 − δ)/(1 + δ), (1 + δ)/(1 − δ)]`. **Do not** route through the additive envelope
`classicDensity_aliasing_error` (`|N̂ − N| ≤ N·δ/(1 − δ)`) plus an additive-to-relative closure
lemma: that route only reaches `2δ/(1 − 2δ)` on `δ < 1/2` and cannot prove this statement.

**Step 1: generic closure lemma under two-sided ratio bounds (not in the repo; paste it after the
`variable` line inside `namespace Plan.FT07`).**

```lean
/-- Closure under two-sided ratio bounds `(1 - δ)·N̂ ≤ N ≤ (1 + δ)·N̂`. -/
theorem comp_rel_ratio {N Nhat : κ → ℝ} {δ : ℝ} (hN : ∀ s, 0 < N s) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hlo : ∀ t, N t ≤ (1 + δ) * Nhat t) (hhi : ∀ t, (1 - δ) * Nhat t ≤ N t) (s : κ) :
    |composition Nhat s - composition N s| ≤ (2 * δ / (1 - δ)) * composition N s := by
  have hNh : ∀ t, 0 < Nhat t := fun t => by
    have := hlo t; have := hN t; nlinarith
  have hS : 0 < ∑ t, N t := Finset.sum_pos (fun t _ => hN t) ⟨s, Finset.mem_univ s⟩
  have hSh : 0 < ∑ t, Nhat t := Finset.sum_pos (fun t _ => hNh t) ⟨s, Finset.mem_univ s⟩
  have hSlo : ∑ t, N t ≤ (1 + δ) * ∑ t, Nhat t := by
    rw [Finset.mul_sum]; exact Finset.sum_le_sum fun t _ => hlo t
  have hShi : (1 - δ) * ∑ t, Nhat t ≤ ∑ t, N t := by
    rw [Finset.mul_sum]; exact Finset.sum_le_sum fun t _ => hhi t
  have h1δ : 0 < 1 - δ := by linarith
  unfold composition totalDensity
  set S := ∑ t, N t
  set Sh := ∑ t, Nhat t
  have key : Nhat s / Sh - N s / S = (Nhat s * S - N s * Sh) / (Sh * S) := by
    field_simp
  rw [key, abs_div, abs_of_pos (mul_pos hSh hS), div_le_iff₀ (mul_pos hSh hS)]
  have hrhs : 2 * δ / (1 - δ) * (N s / S) * (Sh * S) = 2 * δ * N s * Sh / (1 - δ) := by
    field_simp
  rw [hrhs, le_div_iff₀ h1δ]
  have hNs := hN s
  have hNhs := hNh s
  have p1 : (1 - δ) * Nhat s * S ≤ N s * S := mul_le_mul_of_nonneg_right (hhi s) hS.le
  have p2 : N s * S ≤ N s * ((1 + δ) * Sh) := mul_le_mul_of_nonneg_left hSlo hNs.le
  have p3 : N s * S ≤ (1 + δ) * Nhat s * S := mul_le_mul_of_nonneg_right (hlo s) hS.le
  have p4 : N s * ((1 - δ) * Sh) ≤ N s * S := mul_le_mul_of_nonneg_left hShi hNs.le
  have q : (1 - δ) * (N s * ((1 - δ) * Sh)) ≤ (1 - δ) * ((1 + δ) * Nhat s * S) :=
    mul_le_mul_of_nonneg_left (p4.trans p3) h1δ.le
  have hX : 0 ≤ δ ^ 2 * (N s * Sh) := by positivity
  rcases abs_cases (Nhat s * S - N s * Sh) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h]
  · nlinarith
  · nlinarith
```

The recovered densities' positivity (`hNh`) comes from `hlo` and `hN` alone, for every `δ < 1`.
The two `nlinarith` calls rely on the product facts `p1`–`p4`, `q`, `hX` being in context.

**Step 2: the target (per-species aliasing identity, then Step 1).** The aliasing identity is the
public EXACT lemma `classicDensity_aliasing` (`AtomicDataPerturbation.lean:191`):

```lean
theorem classicDensity_aliasing [Nonempty ι]
    {kB T N Fcal : ℝ} {g E A g' E' A' : ι → ℝ}
    (hg : ∀ k, 0 < g k) (hg' : ∀ k, 0 < g' k)
    (hFcal : 0 < Fcal) (u : ι) (hA' : 0 < A' u) :
    Classic.classicDensity kB T Fcal g' E' A' u (lineIntensity kB T N Fcal g E A u)
      = N * responseFactor kB T g E A u / responseFactor kB T g' E' A' u
```

Target body (compiled, passes `verify.py`; `staging/2026-09-24/_g3-verified`):

```lean
  have hρ : ∀ t, 0 < responseFactor kB T (g t) (E t) (A t) (u t) := fun t => by
    unfold responseFactor
    exact div_pos (mul_pos (mul_pos (hg t (u t)) (hA t)) (boltzmannFactor_pos _ _ _))
      (partitionFunction_pos (hg t))
  have hρ' : ∀ t, 0 < responseFactor kB T (g' t) (E' t) (A' t) (u t) := fun t => by
    unfold responseFactor
    exact div_pos (mul_pos (mul_pos (hg' t (u t)) (hA' t)) (boltzmannFactor_pos _ _ _))
      (partitionFunction_pos (hg' t))
  have hrec : ∀ t, recoveredDensity kB T Fcal g E A g' E' A' u N t
      = N t * responseFactor kB T (g t) (E t) (A t) (u t)
          / responseFactor kB T (g' t) (E' t) (A' t) (u t) := fun t => by
    unfold recoveredDensity
    exact classicDensity_aliasing (hg t) (hg' t) hFcal (u t) (hA' t)
  refine comp_rel_ratio hN hδ0 hδ1 (fun t => ?_) (fun t => ?_) s
  · rw [hrec t, mul_div_assoc', le_div_iff₀ (hρ' t)]
    have := (abs_le.mp (hpert t)).2
    have := hN t
    nlinarith
  · rw [hrec t, mul_div_assoc', div_le_iff₀ (hρ' t)]
    have := (abs_le.mp (hpert t)).1
    have := hN t
    nlinarith
```

`hρ` (positivity of the true response factor) is not needed by the two `nlinarith` steps; only
`hρ'` is (for `le_div_iff₀` / `div_le_iff₀`). `hρ` is the proof's only use of `hA`. A body without
`hρ` also compiles, with an unused-variable warning on `hA`. This is consistent with `hA` being
implied by the other hypotheses (statement-audit scratch `_statement-audit/ft07_hA_redundant.lean`).

## 4. Mathlib and repo lemmas (all resolved in v4.33.1)

`abs_le`, `abs_div`, `abs_of_pos`, `abs_cases`, `div_le_iff₀`, `le_div_iff₀`, `div_pos`,
`mul_pos`, `mul_div_assoc'`, `Finset.sum_pos`, `Finset.mul_sum`, `Finset.sum_le_sum`,
`mul_le_mul_of_nonneg_left`, `mul_le_mul_of_nonneg_right`; tactics `field_simp`, `nlinarith`,
`positivity`, `linarith`. Repo (public): `classicDensity_aliasing`, `boltzmannFactor_pos`,
`partitionFunction_pos`.

## 5. Pitfalls and verifier rules

- `responseFactor_pos` and `abs_scaled_ratio_sub_le` in `AtomicDataPerturbation` are **private**:
  not callable from the candidate. Prove response-factor positivity inline by `unfold
  responseFactor` and `div_pos (mul_pos (mul_pos …) (boltzmannFactor_pos _ _ _))
  (partitionFunction_pos …)`, as above.
- The additive route (`classicDensity_aliasing_error` with `η = δ/(1 − δ)`, then an
  additive-to-relative closure lemma) gives `2η/(1 − η) = 2δ/(1 − 2δ)`, which is **larger** than
  the target constant and needs `δ < 1/2`. It cannot close this goal; use the ratio route of §3.
- Keep the statement header verbatim: the two imports (no new ones), `open`, `namespace`,
  `variable` line, and the target signature text up to `:=`. State the target with `theorem`; do
  not name a helper `classicComposition_atomicData_error_rel'` (the verifier's regex would match it
  first).
- Forbidden: `sorry`, `admit`, `native_decide`, `axiom`, `macro`/`syntax`/`elab`, `#`-commands,
  `set_option` other than the heartbeat/recursion limits.

## 6. Scope, sanity numbers, consumers

Scope (two-axis): relation REDUCED (lumped uniform relative response error `δ`, reader at known
`T`); definitions: `lineIntensity` REDUCED (optically thin LTE), `composition` PURE-MATH;
published REDUCED. Citation: Tognoni 2010 (whitelisted, as for the absolute twin).

Sanity: `δ = 0.05` gives `2δ/(1 − δ) = 2/19 ≈ 0.105`; for `C_s = 0.005` the bound is
`≈ 5.26·10⁻⁴` (this matches the audit's number, now as a response-error bound). Tightness
(numerical, not Lean-checked; exact rational arithmetic, 2 species): species `s` read high
(`ρ'_s = (1 − δ)ρ_s`), the other read low (`ρ' = (1 + δ)ρ`), `s`'s share `→ 0`. The relative error
tends to `2δ/(1 − δ)` from below: 0.10526 at `δ = 0.05`, 0.6667 at `0.25`, 1.636 at `0.45`. The old
form's constant `2δ/(1 − 2δ)` is 0.111, 1.0 and 9.0 at the same `δ`, never tight for `δ > 0`.
`δ < 1` is necessary (by hand): at `δ ≥ 1` `hpert` lets `ρ'_s` approach `0`, so `Ĉ_s → 1` while
`C_s` can be small, and no bound `K·C_s` holds.

Non-vacuity witness (Lean-checked, `_statement-audit/ft07_witness.lean`): `ι = Fin 1`,
`κ = Fin 2`, `kB = T = Fcal = 1`, `g = g' = 1`, `E = E' = 0`, `A = 1`, `A'₀ = 1`, `A'₁ = 21/20`,
`δ = 1/20` (tight for species 1), `N = (1, 1)`. Recovered `C₀ = 21/41` vs true `1/2`, error
`1/82 ≈ 0.0122`; the bound gives `(2/19)·(1/2) = 1/19 ≈ 0.053` (informative, `< C₀ = 1/2`; the
old form gave `1/18`).

Consumers: [backlog-id] (critical), A5 trust stack, a relative C6, M8 flags, FT-03's `U_i`.
