# FT18-olsSlope-selfAbsorbed-ge: self-absorption raises the Boltzmann-plot slope when τ falls with E_upper

*Planning dossier for the proof queue. Source: 2026-09-24 deep audit, frontier FT-18 main
theorem in the verifier-revised form (strict-E `hanti`, no `hvar`); verdict REVISE, grade A.
Priority 16 in group g1. Every repo and mathlib name below was checked with `#check` on the
pinned toolchain (Lean/mathlib v4.33.1), 2026-09-24.*

**A complete candidate assembled from the route in this dossier passed `verify.py` on 2026-09-24** (text checks, compile, leanchecker kernel replay, olean axiom probe `[Classical.choice, Quot.sound, propext]`, elaborated type identical): `staging/2026-09-24/_g1-scratch-proofs/FT18-olsSlope-selfAbsorbed-ge.lean`.

## 1. Goal

```lean
theorem olsSlope_selfAbsorbed_ge [Nonempty ι] {E y τ : ι → ℝ} (hτ : ∀ k, 0 < τ k)
    (hanti : ∀ i j, E i < E j → τ j ≤ τ i) :
    olsSlope E y ≤ olsSlope E (fun k => y k + Real.log (selfAbsorptionFactor (τ k)))
```

in `namespace Plan.FT18`, `variable {ι : Type*} [Fintype ι]`, `open Finset CflibsFormal`.
Fully qualified name: `Plan.FT18.olsSlope_selfAbsorbed_ge`. Imports: `Mathlib`,
`CflibsFormal.OLS`, `CflibsFormal.SelfAbsorption` (no others may be added). No new definitions.

Informally: `E` = upper-level energies, `y` = thin Boltzmann-plot ordinates, `τ` = optical
depths. Adding `z k = log SA(τ k)` to every ordinate cannot lower the OLS slope when `τ` is
antitone in `E` (over strictly ordered pairs).

## 2. Repo definitions used (from imported modules; read-only)

```lean
-- CflibsFormal/OLS.lean
noncomputable def mean (f : ι → ℝ) : ℝ := (∑ k, f k) / (Fintype.card ι)
noncomputable def olsSlope (E y : ι → ℝ) : ℝ :=
  (∑ k, (E k - mean E) * (y k - mean y)) / (∑ k, (E k - mean E) ^ 2)
-- CflibsFormal/SelfAbsorption.lean
noncomputable def selfAbsorptionFactor (tau : ℝ) : ℝ :=
  if tau = 0 then 1 else (1 - Real.exp (-tau)) / tau
```

## 3. Repo lemmas available (imported; exact signatures from `#check`)

- `CflibsFormal.olsSlope_eq_centered : ∀ [Nonempty ι] (E y : ι → ℝ), olsSlope E y = (∑ k, (E k - mean E) * y k) / ∑ k, (E k - mean E) ^ 2`
- `CflibsFormal.centered_sum_zero : ∀ [Nonempty ι] (E : ι → ℝ), ∑ k, (E k - mean E) = 0`
- `CflibsFormal.olsSlope_sub_eq : ∀ [Nonempty ι] (E y yHat : ι → ℝ), olsSlope E yHat - olsSlope E y = (∑ k, (E k - mean E) * (yHat k - y k)) / ∑ k, (E k - mean E) ^ 2`
  (an alternative to additivity: the difference of the two slopes is the centred covariance of `E`
  with `z` over `SS_E`)
- `CflibsFormal.selfAbsorptionFactor_pos : ∀ {tau : ℝ}, 0 ≤ tau → 0 < selfAbsorptionFactor tau`
- `CflibsFormal.selfAbsorptionFactor_strictAntiOn : StrictAntiOn selfAbsorptionFactor (Set.Ioi 0)`
- NOT available: `olsSlope_add` exists only as a `private theorem` in
  `CflibsFormal/Alt/OLSAtomicDataPerturbation.lean:109`, a module that is not imported. Re-derive
  it (helper 1 below; 6 lines).

## 4. Proof route (all helpers and the assembly were checked end to end in scratch on
2026-09-24; axioms `[propext, Classical.choice, Quot.sound]`)

**Helper 1, OLS slope is additive in the ordinates:**

```lean
theorem olsSlope_add' [Nonempty ι] (E f h : ι → ℝ) :
    olsSlope E (fun k => f k + h k) = olsSlope E f + olsSlope E h := by
  rw [olsSlope_eq_centered, olsSlope_eq_centered, olsSlope_eq_centered, ← add_div]
  congr 1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  ring
```

**Helper 2, centred covariance of similarly ordered sequences is ≥ 0 (Chebyshev):**

```lean
theorem centered_cov_nonneg [Nonempty ι] (E z : ι → ℝ)
    (hmono : ∀ i j, E i < E j → z i ≤ z j) : 0 ≤ ∑ k, (E k - mean E) * z k := by
  have hM : Monovary z E := fun i j h => hmono i j h
  have hC := hM.sum_mul_sum_le_card_mul_sum
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hsplit : ∑ k, (E k - mean E) * z k = ∑ k, z k * E k - mean E * ∑ k, z k := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  rw [hsplit, mean]
  have : (∑ k, E k) / (Fintype.card ι : ℝ) * ∑ k, z k
      = ((∑ k, z k) * ∑ k, E k) / Fintype.card ι := by
    ring
  rw [this, sub_nonneg, div_le_iff₀ hn]
  linarith
```

**Helper 3, `log SA(τ)` is nondecreasing along `E`:**

```lean
theorem logSA_mono {E τ : ι → ℝ} (hτ : ∀ k, 0 < τ k)
    (hanti : ∀ i j, E i < E j → τ j ≤ τ i) :
    ∀ i j, E i < E j →
      Real.log (selfAbsorptionFactor (τ i)) ≤ Real.log (selfAbsorptionFactor (τ j)) := by
  intro i j hij
  apply Real.log_le_log (selfAbsorptionFactor_pos (hτ i).le)
  exact selfAbsorptionFactor_strictAntiOn.antitoneOn (hτ j) (hτ i) (hanti i j hij)
```

(It triggers a harmless "unused section variable `[Fintype ι]`" linter warning; prefix it with
`omit [Fintype ι] in` to silence it. Warnings do not fail verification.)

**Assembly:**

```lean
  rw [olsSlope_add' E y (fun k => Real.log (selfAbsorptionFactor (τ k)))]
  have h0 : 0 ≤ olsSlope E (fun k => Real.log (selfAbsorptionFactor (τ k))) := by
    rw [olsSlope_eq_centered]
    exact div_nonneg (centered_cov_nonneg E _ (logSA_mono hτ hanti))
      (Finset.sum_nonneg (fun k _ => sq_nonneg _))
  linarith
```

## 5. mathlib lemmas (checked)

- `Monovary f g : Prop := ∀ ⦃i j⦄, g i < g j → f i ≤ f j` (note the argument order: `Monovary z E`)
- `Monovary.sum_mul_sum_le_card_mul_sum : Monovary f g → (∑ i, f i) * ∑ i, g i ≤ ↑(Fintype.card ι) * ∑ i, f i * g i`
- `StrictAntiOn.antitoneOn : StrictAntiOn f s → AntitoneOn f s` (then apply to
  `a ∈ s → b ∈ s → a ≤ b → f b ≤ f a`)
- `Real.log_le_log : 0 < x → x ≤ y → Real.log x ≤ Real.log y`
- `div_nonneg`, `div_le_iff₀ : 0 < c → (b / c ≤ a ↔ b ≤ a * c)`, `sub_nonneg`,
  `Finset.sum_nonneg`, `Finset.mul_sum`, `Finset.sum_sub_distrib`, `Finset.sum_add_distrib`,
  `Fintype.card_pos`, `add_div`

## 6. Pitfalls

- `olsSlope_add` is private in a non-imported module: re-derive (helper 1).
- `Monovary` argument order: `Monovary z E` means `E i < E j → z i ≤ z j`.
- `mean` divides by a `ℕ` cast `(Fintype.card ι : ℝ)`; get positivity with
  `exact_mod_cast Fintype.card_pos` (needs `[Nonempty ι]`).
- `selfAbsorptionFactor` is defined by `if tau = 0 …`; never unfold it: use
  `selfAbsorptionFactor_pos` and `selfAbsorptionFactor_strictAntiOn` (domain `Set.Ioi 0`,
  membership `hτ k : 0 < τ k` is exactly `τ k ∈ Set.Ioi 0`).
- No energy-spread hypothesis exists or is needed: `div_nonneg` with the denominator
  `∑ (E k − mean E)^2 ≥ 0` handles `SS_E = 0`.

## 7. Scope and provenance

- Two-axis tag prediction: relation EXACT relative to its definitions (a mathematical
  inequality); model tags of the definitions used: `selfAbsorptionFactor` on integrated
  intensity is the flat-profile slab factor, REDUCED (RF-03 policy: rows consuming SA are
  REDUCED); `olsSlope` is unweighted OLS at one temperature. Published tag REDUCED.
- Not claimed: the reverse ordering (a two-line witness where the slope decreases is a separate
  target); the apparent-temperature corollary `apparentTemp_overestimate` (separate target, needs
  `hle`, `0 < kB`, `0 < T`); any statement about which ordering real line sets have. The
  audit's "settles the literature" wording was dropped by the verifier.
- Consumers: [backlog-id], [backlog-id], R3 resonance-line selection (companion); generalizes to FT-13's
  profile escape factor, whose log is also antitone in τ.
- Literature (whitelist rows 61, 54): Gornushkin et al. 1999, Spectrochim. Acta B 54, 491-503
  (slab curve of growth, `SA = (1 − e^{−τ})/τ`); Bulajic et al. 2002, Spectrochim. Acta B 57,
  339 (self-absorption correction in CF-LIBS).
- Novelty: `rg -l selfAbsorptionFactor CflibsFormal | xargs rg -l olsSlope` on main (fb1681d)
  finds only `Certificates.lean` and `DifferentialEstimator.lean` (matched-τ ratios, no slope
  sign theorem); `rg -c 'olsSlope_selfAbsorbed|selfAbsorbed_ge'`: 0 hits.
- Tactic battery (simp, linarith, positivity, nlinarith, field_simp, aesop, exact?, and an
  unfold+gcongr attempt): none closes it.
