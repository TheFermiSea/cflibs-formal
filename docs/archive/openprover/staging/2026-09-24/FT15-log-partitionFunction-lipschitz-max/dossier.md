# FT15: log-Lipschitz bound for the partition function via the mean excitation energy

Source: 2026-09-24 deep audit, FT-15 (verdict KEEP, grade B), in the verifier's form with `⟨E⟩`
at `max T1 T2`, which needs no monotonicity lemma (a leaf). Priority 11, group g2.

**Statement audit (2026-09-24, M6 round): FIX (process and docstrings); HAND-LAND, do not
queue.** The signature is unchanged. The target is not on main by name, but it is on main in
substance: `meanExcitation kB T g E = tiltMean g E (1/(kB·T))` (`tiltMean`,
`InhomogeneityBias.lean:165`), the crux is `logMixture_tangent_le` (`InhomogeneityBias.lean:239`),
and the sign step is `partitionFunction_mono_temp` (`SahaStability.lean:747`). The pre-audit plan
(port the Jensen template by copy) would have duplicated on-main mathematics in a second
parametrization, against AGENTS.md's "define each concept once". The statement file therefore
imports `CflibsFormal.InhomogeneityBias` and `CflibsFormal.SahaStability` (neither contains this
theorem) and carries two proved bridge lemmas, shared with `FT15-meanExcitation-monotoneOn-temp`
(land them once). A verified, axiom-clean proof with the auditor's two non-vacuity witnesses is at
`staging/2026-09-24/_hand-land/FT15-log-partitionFunction-lipschitz-max.proof.lean`.

## 1. Goal

```lean
theorem log_partitionFunction_lipschitz_max [Nonempty ι] {kB T1 T2 : ℝ} {g E : ι → ℝ}
    (hkB : 0 < kB) (hT1 : 0 < T1) (hT2 : 0 < T2) (hg : ∀ k, 0 < g k) (hE : ∀ k, 0 ≤ E k) :
    |Real.log (partitionFunction kB T1 g E) - Real.log (partitionFunction kB T2 g E)|
      ≤ meanExcitation kB (max T1 T2) g E * |1 / (kB * T1) - 1 / (kB * T2)|
```

Meaning: `log U` moves by at most the mean excitation energy at the hotter temperature times the
change in inverse temperature. The existing constants on main (`partitionFunction_lipschitz_temp`,
`PartitionLipschitz.lean:146`, and `sahaFactorLipConst`) are built from `∑ g·E` and bound `U` in
`T` rather than `log U` in `β`; in the audit's measurements (FT-15/PS-03: 7.7e5-9.7e7× the true
sensitivity against 2.8-4.3× for the `⟨E⟩` form) they are far looser, but those numbers come from
a narrow [0.8, 1.2] eV box only and are not a theorem.

## 2. Definitions

Statement file context: imports `Mathlib`, `CflibsFormal.Boltzmann`,
`CflibsFormal.InhomogeneityBias`, `CflibsFormal.SahaStability`; `open Finset CflibsFormal`;
namespace `Plan.FT15`; `variable {ι : Type*} [Fintype ι]`.

From `CflibsFormal/Boltzmann.lean`:

```lean
noncomputable def boltzmannFactor (kB T E : ℝ) : ℝ := Real.exp (-E / (kB * T))   -- line 37
noncomputable def partitionFunction (kB T : ℝ) (g E : ι → ℝ) : ℝ :=                -- line 42
  ∑ k, g k * boltzmannFactor kB T (E k)
lemma partitionFunction_pos [Nonempty ι] {kB T : ℝ} {g E : ι → ℝ}                   -- line 45
    (hg : ∀ k, 0 < g k) : 0 < partitionFunction kB T g E
```

From `CflibsFormal/InhomogeneityBias.lean` (namespace `CflibsFormal`, `ζ` a `Fintype`):

```lean
noncomputable def mixture (w b : ζ → ℝ) (E : ℝ) : ℝ := ∑ z, w z * Real.exp (-(E * b z))  -- 147
noncomputable def logMixture (w b : ζ → ℝ) (E : ℝ) : ℝ := Real.log (mixture w b E)     -- 152
noncomputable def tiltWeight (w b : ζ → ℝ) (a : ℝ) (z : ζ) : ℝ :=                      -- 158
  w z * Real.exp (-(a * b z)) / mixture w b a
noncomputable def tiltMean (w b : ζ → ℝ) (a : ℝ) : ℝ := ∑ z, tiltWeight w b a z * b z  -- 165
```

New, byte-identical in both FT15 targets (the definition is unchanged by the audit; only its
docstring gained the `tiltMean` sentence):

```lean
noncomputable def meanExcitation (kB T : ℝ) (g E : ι → ℝ) : ℝ :=
  (∑ k, g k * E k * boltzmannFactor kB T (E k)) / partitionFunction kB T g E
```

No module on main defines it by name
(`rg -i 'meanExcitation|meanLevel|meanEnergy|averageEnergy|expectedEnergy' CflibsFormal`: 0 hits),
but it is `tiltMean` in inverse-temperature form, with levels in the role of zones (weights
`g`, abscissae `E`, anchor `β = 1/(k_B T)`). The two bridge lemmas (section 4a) make this exact.

## 3. Mathematical proof (derivative-free)

By symmetry take `Ta ≤ Tb` (`le_total`; `max` becomes `Tb`, and `|x − y| = |y − x|`). Let
`βa = 1/(k_B Ta) ≥ βb = 1/(k_B Tb) > 0`.
1. **Sign.** `U` is nondecreasing in `T` when `E ≥ 0`, so `log U(Ta) ≤ log U(Tb)` and
   `|log U(Ta) − log U(Tb)| = log U(Tb) − log U(Ta)`. This is where `hE` is load-bearing (one level
   with `E < 0` makes the right side negative and the statement false).
2. **Tangent (the crux).** `log U(Tb) − (βa − βb)·⟨E⟩_{Tb} ≤ log U(Ta)`. With weights
   `p_k = g_k·bf(Tb, E_k)/U(Tb)` (positive, summing to 1),
   `U(Ta)/U(Tb) = ∑ p_k·exp(−(βa − βb)·E_k) ≥ exp(∑ p_k·(−(βa − βb)·E_k)) = exp(−(βa − βb)·⟨E⟩_{Tb})`
   by Jensen for `exp` (`convexOn_exp.map_sum_le`); take `log`.
3. Combine: `log U(Tb) − log U(Ta) ≤ ⟨E⟩_{Tb}·(βa − βb) = ⟨E⟩_{max}·|βa − βb|`.

Numerics (audit, `_plan/numcheck.py`): max LHS/RHS = 1.0000000000 over 20000 draws (a float tie
as `T1 → T2`); never above 1.

## 4. Lean route (verified; hand-land)

### 4a. Bridge lemmas (in the statement file, proved; shared with the monotonicity target)

```lean
lemma partitionFunction_eq_mixture (kB T : ℝ) (g E : ι → ℝ) :
    partitionFunction kB T g E = mixture g E (1 / (kB * T)) := by
  unfold partitionFunction mixture boltzmannFactor
  refine Finset.sum_congr rfl (fun k _ => ?_)
  congr 2; ring

lemma meanExcitation_eq_tiltMean (kB T : ℝ) (g E : ι → ℝ) :
    meanExcitation kB T g E = tiltMean g E (1 / (kB * T)) := by
  unfold meanExcitation tiltMean tiltWeight
  rw [partitionFunction_eq_mixture, Finset.sum_div]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  unfold boltzmannFactor
  have : -E k / (kB * T) = -(1 / (kB * T) * E k) := by ring
  rw [this]; ring
```

### 4b. Proof body (compiles against the statement file; axioms `[propext, Classical.choice,
Quot.sound]`)

```lean
  have core : ∀ {Ta Tb : ℝ}, 0 < Ta → Ta ≤ Tb →
      |Real.log (partitionFunction kB Ta g E) - Real.log (partitionFunction kB Tb g E)|
        ≤ meanExcitation kB Tb g E * |1 / (kB * Ta) - 1 / (kB * Tb)| := by
    intro Ta Tb hTa hab
    have hUa : 0 < partitionFunction kB Ta g E := partitionFunction_pos hg
    have hlow : Real.log (partitionFunction kB Ta g E)
        ≤ Real.log (partitionFunction kB Tb g E) :=
      Real.log_le_log hUa (partitionFunction_mono_temp hkB hTa hab hg hE)
    have hβ : 1 / (kB * Tb) ≤ 1 / (kB * Ta) :=
      one_div_le_one_div_of_le (mul_pos hkB hTa) (mul_le_mul_of_nonneg_left hab hkB.le)
    have htan := logMixture_tangent_le (b := E) hg (1 / (kB * Tb)) (1 / (kB * Ta))
    simp only [logMixture] at htan
    rw [← partitionFunction_eq_mixture, ← partitionFunction_eq_mixture,
      ← meanExcitation_eq_tiltMean] at htan
    rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]
    linarith
  rcases le_total T1 T2 with h | h
  · rw [max_eq_right h]; exact core hT1 h
  · rw [max_eq_left h, abs_sub_comm, abs_sub_comm (1 / (kB * T1))]; exact core hT2 h
```

`htan` is step 2 of section 3 (the tangent of the convex `β ↦ log U` at `βb`, read off at `βa`),
obtained from `logMixture_tangent_le` with anchor `1/(kB·Tb)` and evaluation point `1/(kB·Ta)`,
then rewritten backwards through both bridges.

## 5. Repo and Mathlib lemmas used (all on the pinned tree)

- `CflibsFormal.logMixture_tangent_le [Nonempty ζ] {w b : ζ → ℝ} (hw : ∀ z, 0 < w z) (a E : ℝ) :
  logMixture w b a - (E - a) * tiltMean w b a ≤ logMixture w b E`
  (`InhomogeneityBias.lean:239`).
- `CflibsFormal.partitionFunction_mono_temp {kB T1 T2 : ℝ} {g E : ι → ℝ} (hkB : 0 < kB)
  (hT1 : 0 < T1) (hT12 : T1 ≤ T2) (hg : ∀ k, 0 < g k) (hE : ∀ k, 0 ≤ E k) :
  partitionFunction kB T1 g E ≤ partitionFunction kB T2 g E` (`SahaStability.lean:747`).
- `CflibsFormal.partitionFunction_pos` (`Boltzmann.lean:45`).
- Mathlib: `Finset.sum_congr`, `Finset.sum_div`, `Real.log_le_log`,
  `one_div_le_one_div_of_le : 0 < a → a ≤ b → 1 / b ≤ 1 / a`, `mul_le_mul_of_nonneg_left`,
  `abs_of_nonpos`, `abs_of_nonneg`, `abs_sub_comm`, `max_eq_left`, `max_eq_right`, `le_total`.

## 6. Pitfalls

- Do not copy `partitionFunction_mono_temp`, `tiltWeight` lemmas or `logMixture_tangent_le` into
  the landing module; import them (define once). The only new declarations are
  `meanExcitation`, the two bridges and the theorem.
- The bridges put the level energies in `mixture`'s *abscissa* slot `b` and the inverse
  temperature in its *argument* slot; the physical reading of `tiltMean` in
  `InhomogeneityBias` (zones, inverse temperatures) differs, which is why a bridge lemma, not a
  rename, is the define-once fix.
- `logMixture_tangent_le` leaves `b` implicit and not determined by `hw`; pin it with
  `(b := E)`.
- Landing needs `docs/scope-tags.tsv` rows for `meanExcitation`'s bridges and the theorem, and
  the witnesses from the hand-land file.

## 7. Scope and consumers

Own relation PURE-MATH; definitions used: `partitionFunction`, `meanExcitation` (new); predicted
published tag PURE-MATH, REDUCED once bound to data (a physical `U` sums a truncated level list,
FT-05). Consumers: the EvaluatorSoundness envelope (RF-12), BL-07/F7, the certificate-gate HARD
set, FT-08(b), FT-09, the FT-01 physical gains; wave 2 is `log_sahaFactor_lipschitz`.
Literature: none needed (PURE-MATH).
