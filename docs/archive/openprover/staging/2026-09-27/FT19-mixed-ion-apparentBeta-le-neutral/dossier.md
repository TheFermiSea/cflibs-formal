# FT19-mixed-ion-apparentBeta-le-neutral: ion-pair apparent β ≤ neutral-pair apparent β

Planning dossier for the proof queue (2026-09-24 audit, frontier FT-19 assembly, REVISE verdict
applied). Written for a planner who cannot open the repository. Every repo definition and lemma
is quoted, and every Mathlib name was checked with `#check` against the pinned Mathlib (v4.33.1).

Dependency note: two sibling targets are NOT on main and must be re-proved inline as helper
lemmas (or this target queued after them): `FT19-ionReweight-strictMonoOn` (route: dossier §4
there; ~20 lines) and `FT19-tiltMean-reweight-le` (weighted Chebyshev; ~40 lines).

## 1. Goal

```lean
import Mathlib
import CflibsFormal.InhomogeneityBias
import CflibsFormal.SahaStability

open CflibsFormal

namespace Plan.FT19

theorem mixed_ion_apparentBeta_le_neutral {ζ ι κ : Type*} [Fintype ζ] [Fintype ι] [Fintype κ]
    [Nonempty ζ] [Nonempty ι] [Nonempty κ]
    {kB Fcal me h chi ne : ℝ} {T NI NII : ζ → ℝ}
    {gZ EZ AI : ι → ℝ} {gZ1 EZ1 AII : κ → ℝ}
    (hkB : 0 < kB) (hme : 0 < me) (hh : 0 < h) (hchi : 0 ≤ chi) (hne : 0 < ne)
    (hFcal : 0 < Fcal) (hT : ∀ z, 0 < T z) (hNI : ∀ z, 0 < NI z)
    (hgZ : ∀ k, 0 < gZ k) (hgZ1 : ∀ k, 0 < gZ1 k)
    (hAI : ∀ k, 0 < AI k) (hAII : ∀ k, 0 < AII k)
    (hNII : ∀ z, NII z = NI z * sahaFactor kB (T z) me h chi gZ EZ gZ1 EZ1 / ne)
    (i j : ι) (hij : EZ i < EZ j) (i' j' : κ) (hij' : EZ1 i' < EZ1 j')
    (hanchor : EZ j ≤ EZ1 i') :
    apparentBeta (EZ1 i')
        (Real.log (mixedLineIntensity kB T NII Fcal gZ1 EZ1 AII i' / (gZ1 i' * AII i')))
        (EZ1 j')
        (Real.log (mixedLineIntensity kB T NII Fcal gZ1 EZ1 AII j' / (gZ1 j' * AII j')))
      ≤ apparentBeta (EZ i)
        (Real.log (mixedLineIntensity kB T NI Fcal gZ EZ AI i / (gZ i * AI i)))
        (EZ j)
        (Real.log (mixedLineIntensity kB T NI Fcal gZ EZ AI j / (gZ j * AI j))) := by
  sorry
```

No new definitions in the statement. Keep the signature verbatim; helper lemmas (and a helper
`def`, e.g. `ionReweight` from the sibling target) may be added.

## 2. Definitions (namespace `CflibsFormal`)

```lean
-- Boltzmann.lean
noncomputable def boltzmannFactor (kB T E : ℝ) : ℝ := Real.exp (-E / (kB * T))
noncomputable def partitionFunction (kB T : ℝ) (g E : ι → ℝ) : ℝ :=
  ∑ k, g k * boltzmannFactor kB T (E k)
noncomputable def population (kB T N : ℝ) (g E : ι → ℝ) (k : ι) : ℝ :=
  N * g k * boltzmannFactor kB T (E k) / partitionFunction kB T g E
-- ForwardMap.lean
noncomputable def lineIntensity (kB T N Fcal : ℝ) (g E A : ι → ℝ) (k : ι) : ℝ :=
  Fcal * A k * population kB T N g E k
-- Saha.lean
noncomputable def thermalBracket (kB T me h : ℝ) : ℝ :=
  (2 * Real.pi * me * kB * T) / h ^ 2
noncomputable def sahaFactor (kB T me h chi : ℝ) (gZ EZ : ι → ℝ) (gZ1 EZ1 : κ → ℝ) : ℝ :=
  2 * (partitionFunction kB T gZ1 EZ1 / partitionFunction kB T gZ EZ)
    * (thermalBracket kB T me h) ^ (3 / 2 : ℝ)
    * Real.exp (-chi / (kB * T))
-- InhomogeneityBias.lean
noncomputable def mixture (w b : ζ → ℝ) (E : ℝ) : ℝ := ∑ z, w z * Real.exp (-(E * b z))
noncomputable def logMixture (w b : ζ → ℝ) (E : ℝ) : ℝ := Real.log (mixture w b E)
noncomputable def tiltWeight (w b : ζ → ℝ) (a : ℝ) (z : ζ) : ℝ :=
  w z * Real.exp (-(a * b z)) / mixture w b a
noncomputable def tiltMean (w b : ζ → ℝ) (a : ℝ) : ℝ := ∑ z, tiltWeight w b a z * b z
noncomputable def apparentBeta (E₁ y₁ E₂ y₂ : ℝ) : ℝ := (y₁ - y₂) / (E₂ - E₁)
noncomputable def mixedLineIntensity (kB : ℝ) (T N : ζ → ℝ) (Fcal : ℝ)
    (g E A : ι → ℝ) (k : ι) : ℝ :=
  ∑ z, lineIntensity kB (T z) (N z) Fcal g E A k
noncomputable def zoneWeight (kB Fcal : ℝ) (T N : ζ → ℝ) (g E : ι → ℝ) (z : ζ) : ℝ :=
  Fcal * N z / partitionFunction kB (T z) g E
noncomputable def zoneBeta (kB : ℝ) (T : ζ → ℝ) (z : ζ) : ℝ := 1 / (kB * T z)
```

## 3. Repo lemmas (signatures checked)

- `mixed_boltzmann_ordinate [Nonempty ι] {kB Fcal} {T N : ζ → ℝ} {g E A : ι → ℝ} (hkB : 0 < kB)
  (hT : ∀ z, 0 < T z) (hg : ∀ k, 0 < g k) (hA : ∀ k, 0 < A k) (k : ι) :
  Real.log (mixedLineIntensity kB T N Fcal g E A k / (g k * A k))
    = logMixture (zoneWeight kB Fcal T N g E) (zoneBeta kB T) (E k)`
- `pairSlope_le_tiltMean [Nonempty ζ] {w b} (hw : ∀ z, 0 < w z) {E₁ E₂} (h12 : E₁ < E₂) :
  apparentBeta E₁ (logMixture w b E₁) E₂ (logMixture w b E₂) ≤ tiltMean w b E₁`
- `tiltMean_le_pairSlope [Nonempty ζ] {w b} (hw : ∀ z, 0 < w z) {E₁ E₂} (h12 : E₁ < E₂) :
  tiltMean w b E₂ ≤ apparentBeta E₁ (logMixture w b E₁) E₂ (logMixture w b E₂)`
- `zoneWeight_pos [Nonempty ι] (hg : ∀ k, 0 < g k) (hN : ∀ z, 0 < N z) (hFcal : 0 < Fcal) (z) :
  0 < zoneWeight kB Fcal T N g E z`
- `sahaFactor_pos [Nonempty ι] [Nonempty κ] (hkB : 0 < kB) (hT : 0 < T) (hme : 0 < me)
  (hh : 0 < h) (hgZ : ∀ k, 0 < gZ k) (hgZ1 : ∀ k, 0 < gZ1 k) :
  0 < sahaFactor kB T me h chi gZ EZ gZ1 EZ1`
- `partitionFunction_pos [Nonempty ι] (hg : ∀ k, 0 < g k) : 0 < partitionFunction kB T g E`
- `thermalBracket_pos (hkB) (hT) (hme) (hh) : 0 < thermalBracket kB T me h`;
  `thermalBracket_strictMono (hkB) (hme) (hh) (hab : Ta < Tb) :
  thermalBracket kB Ta me h < thermalBracket kB Tb me h`
- `mixture_pos`, `tiltWeight_pos`, `tiltWeight_sum_one` (as in the sibling dossier).

## 4. Proof route (the verdict's chain)

Let `wI := zoneWeight kB Fcal T NI gZ EZ`, `b := zoneBeta kB T`,
`ρ z := 2 * thermalBracket kB (T z) me h ^ (3/2 : ℝ) * Real.exp (-chi / (kB * T z)) / ne`.
1. `hwI : ∀ z, 0 < wI z` (`zoneWeight_pos hgZ hNI hFcal`); `hρ : ∀ z, 0 < ρ z` (positivity).
2. Ion weight identity: `zoneWeight kB Fcal T NII gZ1 EZ1 = fun z => wI z * ρ z`
   (`funext z; simp only [zoneWeight, hNII, sahaFactor]; field_simp`, with
   `partitionFunction_pos hgZ`, `partitionFunction_pos hgZ1`, `hne.ne'`). U_II/U_I cancels.
3. Rewrite both sides with `mixed_boltzmann_ordinate` (ion: `hgZ1 hAII`; neutral: `hgZ hAI`),
   then rewrite the ion weight by step 2.
4. `β_ion ≤ tiltMean (fun z => wI z * ρ z) b (EZ1 i')`: `pairSlope_le_tiltMean (hwρ) hij'`.
5. `≤ tiltMean wI b (EZ1 i')`: weighted Chebyshev (sibling target), with antivariance:
   `b x < b y` means `1/(kB*T x) < 1/(kB*T y)`, so `T y < T x` (`one_div_lt_one_div`,
   `lt_of_mul_lt_mul_left`), so `ρ y < ρ x` (sibling monotonicity target).
6. `≤ tiltMean wI b (EZ j)`: anchor antitonicity. `hanchor.lt_or_eq`; if `EZ j < EZ1 i'`,
   `(tiltMean_le_pairSlope hwI h).trans (pairSlope_le_tiltMean hwI h)`; if equal, `rw`.
7. `≤ β_neu`: `tiltMean_le_pairSlope hwI hij`. Chain with `le_trans` / `calc`.

## 5. Mathlib lemmas (signatures checked)

`one_div_lt_one_div : 0 < a → 0 < b → (1 / a < 1 / b ↔ b < a)`; `lt_of_mul_lt_mul_left :
a * b < a * c → 0 ≤ a → b < c`; `LE.le.lt_or_eq : a ≤ b → a < b ∨ a = b`; plus those of the
sibling dossiers (`Real.rpow_lt_rpow`, `Real.exp_le_exp`, `div_le_div_iff₀`,
`Finset.sum_mul_sum`, `Finset.sum_comm`, `Finset.sum_nonpos`, ...).

## 6. Pitfalls

- Energies: ion line energies `EZ1` are measured from the ion ground state (the repo convention:
  the same `EZ1` feeds the ion partition function and the ion Boltzmann exponent). `ρ` therefore
  includes `e^{−χ/(k_B T)}`; do not shift ion energies by `χ` (that is `Alt/CSigma`'s
  Saha–Boltzmann convention, a different bookkeeping).
- Step 2: `sahaFactor` writes `(thermalBracket kB T me h) ^ (3 / 2 : ℝ)`; `ρ` writes
  `thermalBracket kB (T z) me h ^ (3/2 : ℝ)` - the same term. `field_simp` needs the two
  partition functions and `ne` nonzero.
- `hchi` is needed only in step 5 (monotone exponential). `hij` and `hij'` feed the bracket
  lemmas; `hanchor` is used only in step 6.
- Budget: high (three helper lemmas plus assembly). Split into helpers.

## 7. Satisfiability witness (hypothesis part checked)

`ζ = ι = κ = Fin 2`; `kB = me = h = ne = Fcal = chi = 1`; `T = ![1, 2]`; `NI = 1`; all `g, A = 1`;
`EZ = ![0, 1]`, `EZ1 = ![1, 2]`, `i = i' = 0`, `j = j' = 1`; `NII z := NI z * sahaFactor … / ne`
(positive by `sahaFactor_pos`). Then `EZ 0 < EZ 1`, `EZ1 0 < EZ1 1` and the anchor `EZ 1 = 1 ≤ 1 =
EZ1 0` hold (checked with `norm_num`); the zones are genuinely inhomogeneous (`T` differs).

## 8. Scope

REDUCED (uniform `n_e`, LTE Saha balance per zone, optically thin, two-line pairs; not the
`n`-line OLS slope). Consistent with, and does not prove, Aguilera & Aragón 2007 (J. Phys.: Conf.
Ser. 59:210-217, doi 10.1088/1742-6596/59/1/046: Fe I 9890 K vs Fe II 11400 K from multi-line
plots of a plasma with varying `n_e`). That paper needs its own literature row, distinct from the
SAB 62:378 row. The anchor may fail for line pairs used in practice.

## 9. Audit note (not for the prover)

The chain also closes under the weaker anchor `EZ j ≤ EZ1 i' + chi`, using the reweight
`2 θ^{3/2}/n_e` (no exponential; its log is `Alt/CSigma.sahaBracketLog`) and the χ-shift
`tiltWeight (w·ρ) b a = tiltWeight (w·ρ') b (a + χ)`. The verdict's form is staged here as
binding; the Mode B audit should decide whether to strengthen.
