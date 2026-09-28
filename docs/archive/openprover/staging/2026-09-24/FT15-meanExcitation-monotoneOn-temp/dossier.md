# FT15: the mean excitation energy is nondecreasing in temperature

Source: 2026-09-24 deep audit, FT-15 first batch (`d⟨E⟩/dT = Var/(kT²) ≥ 0`, monotonicity);
verdict KEEP, grade B. Priority 17, group g2.

**Statement audit (2026-09-24, M6 round): FIX (process and docstrings); HAND-LAND, do not
queue.** The signature is unchanged. The target is not on main by name, but through the bridge
`meanExcitation kB T g E = tiltMean g E (1/(kB·T))` it says that `tiltMean` is antitone in its
anchor, which on main is the one-line chain `tiltMean_le_pairSlope`
(`InhomogeneityBias.lean:315`) then `pairSlope_le_tiltMean` (`InhomogeneityBias.lean:295`). The
pre-audit plan (hand-written double-sum symmetrization, 250k queue tokens) would have re-derived
content already on main. The statement file therefore imports `CflibsFormal.InhomogeneityBias`
(it does not contain this theorem) and carries two proved bridge lemmas, shared with
`FT15-log-partitionFunction-lipschitz-max` (land them once). A verified, axiom-clean proof with
the auditor's two non-vacuity witnesses (one with a negative energy) is at
`staging/2026-09-24/_hand-land/FT15-meanExcitation-monotoneOn-temp.proof.lean`.

## 1. Goal

```lean
theorem meanExcitation_monotoneOn_temp [Nonempty ι] {kB : ℝ} {g E : ι → ℝ} (hkB : 0 < kB)
    (hg : ∀ k, 0 < g k) :
    MonotoneOn (fun T => meanExcitation kB T g E) (Set.Ioi 0)
```

Meaning: the Boltzmann-weighted mean level energy never decreases as the plasma heats. No sign
condition on the energies. Needed to turn the `max T1 T2` log-Lipschitz bound into a box form and
for the `log S` Lipschitz bound (wave 2).

## 2. Definitions

Statement file context: imports `Mathlib`, `CflibsFormal.Boltzmann`,
`CflibsFormal.InhomogeneityBias`; `open Finset CflibsFormal`; namespace `Plan.FT15`;
`variable {ι : Type*} [Fintype ι]`.

`boltzmannFactor`, `partitionFunction`, `partitionFunction_pos` (`Boltzmann.lean:37-45`) and
`mixture`, `tiltWeight`, `tiltMean`, `apparentBeta`, `logMixture` (`InhomogeneityBias.lean`) as
in the Lipschitz target's dossier. `apparentBeta E₁ y₁ E₂ y₂ = (y₁ − y₂)/(E₂ − E₁)` is the negated
chord slope (`InhomogeneityBias.lean:176`).

New, byte-identical in both FT15 targets (the definition is unchanged by the audit; only its
docstring gained the `tiltMean` sentence):

```lean
noncomputable def meanExcitation (kB T : ℝ) (g E : ι → ℝ) : ℝ :=
  (∑ k, g k * E k * boltzmannFactor kB T (E k)) / partitionFunction kB T g E
```

No module on main defines it by name
(`rg -i 'meanExcitation|meanLevel|meanEnergy|averageEnergy|expectedEnergy' CflibsFormal`: 0 hits),
but it is `tiltMean` in inverse-temperature form, with levels in the role of zones (weights `g`,
abscissae `E`, anchor `β = 1/(k_B T)`); the bridge lemmas in 4a make this exact.

## 3. Mathematical proof

**Route used (on main, via the bridge).** Fix `0 < T1 < T2`, so `β2 = 1/(k_B T2) < β1 =
1/(k_B T1)`. For the mixture `β ↦ log U` with anchors `β2 < β1`, `InhomogeneityBias` proves the
pair-slope sandwich `tiltMean g E β1 ≤ apparentBeta β2 (log U(β2)) β1 (log U(β1)) ≤
tiltMean g E β2` (`tiltMean_le_pairSlope`, `pairSlope_le_tiltMean`; both are the tangent
inequality `logMixture_tangent_le`, i.e. Jensen for `exp`). Through the bridge this is
`⟨E⟩_{T1} ≤ ⟨E⟩_{T2}`. The case `T1 = T2` is trivial.

**Equivalent elementary argument (context; not used).**
Fix `0 < T1 ≤ T2`, write `bf_i(e) = boltzmannFactor kB T_i e`, `A_i = ∑ g E bf_i(E)`,
`U_i = ∑ g bf_i(E)`. Since `U_i > 0`, `A1/U1 ≤ A2/U2 ⟺ A1·U2 ≤ A2·U1`. Expand both products:

`A2·U1 − A1·U2 = ∑_j ∑_k F(j,k)`, with `F(j,k) = g_j g_k E_j (bf2(E_j) bf1(E_k) − bf1(E_j) bf2(E_k))`.

Swapping `j ↔ k` (`Finset.sum_comm`) gives the same total, and
`F(j,k) + F(k,j) = g_j g_k (E_j − E_k)(bf2(E_j) bf1(E_k) − bf1(E_j) bf2(E_k))` (`ring`). Each such term is
`≥ 0`: the exponent gap between the two products is `(β1 − β2)(E_j − E_k)` with `β1 ≥ β2`, so the
bracket has the sign of `E_j − E_k` (a `le_total` case split). Hence `2·∑∑F ≥ 0`.

Numerics (audit, `_plan/numcheck.py`): 0 violations over 20000 draws with energies allowed
negative.

## 4. Lean route (verified; hand-land)

### 4a. Bridge lemmas (in the statement file, proved; shared with the Lipschitz target)

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
  intro T1 hT1 T2 hT2 hle
  simp only [Set.mem_Ioi] at hT1 hT2
  show meanExcitation kB T1 g E ≤ meanExcitation kB T2 g E
  rw [meanExcitation_eq_tiltMean, meanExcitation_eq_tiltMean]
  rcases hle.lt_or_eq with hlt | heq
  · have hβ : 1 / (kB * T2) < 1 / (kB * T1) :=
      one_div_lt_one_div_of_lt (mul_pos hkB hT1) (mul_lt_mul_of_pos_left hlt hkB)
    exact le_trans (tiltMean_le_pairSlope hg hβ) (pairSlope_le_tiltMean hg hβ)
  · rw [heq]
```

## 5. Repo and Mathlib lemmas used (all on the pinned tree)

- `CflibsFormal.tiltMean_le_pairSlope [Nonempty ζ] {w b : ζ → ℝ} (hw : ∀ z, 0 < w z)
  {E₁ E₂ : ℝ} (h12 : E₁ < E₂) :
  tiltMean w b E₂ ≤ apparentBeta E₁ (logMixture w b E₁) E₂ (logMixture w b E₂)`
  (`InhomogeneityBias.lean:315`).
- `CflibsFormal.pairSlope_le_tiltMean [Nonempty ζ] {w b : ζ → ℝ} (hw : ∀ z, 0 < w z)
  {E₁ E₂ : ℝ} (h12 : E₁ < E₂) :
  apparentBeta E₁ (logMixture w b E₁) E₂ (logMixture w b E₂) ≤ tiltMean w b E₁`
  (`InhomogeneityBias.lean:295`).
- Mathlib: `Finset.sum_congr`, `Finset.sum_div`, `LE.le.lt_or_eq`,
  `one_div_lt_one_div_of_lt : 0 < a → a < b → 1 / b < 1 / a`, `mul_lt_mul_of_pos_left`.

## 6. Pitfalls and follow-ups

- Do not re-derive the symmetrization or copy the `tiltWeight` lemmas into the landing module;
  import them (define once). The only new declarations are `meanExcitation`, the two bridges and
  the theorem.
- Optional follow-up (not required): a `StrictMonoOn` version under `∃ j k, E j ≠ E k` follows
  from `pairSlope_lt_tiltMean` (`InhomogeneityBias.lean:304`) in place of `pairSlope_le_tiltMean`.
- Landing needs `docs/scope-tags.tsv` rows and the witnesses from the hand-land file.

## 7. Scope and consumers

Own relation PURE-MATH; definitions used: `partitionFunction`, `meanExcitation` (new); predicted
published tag PURE-MATH, REDUCED once bound to data (a physical `U` sums a truncated level list,
FT-05). Consumers: the EvaluatorSoundness envelope (RF-12), BL-07/F7, the certificate-gate HARD
set, FT-08(b), FT-09, the FT-01 physical gains; wave 2 is `log_sahaFactor_lipschitz`.
Literature: none needed (PURE-MATH).
