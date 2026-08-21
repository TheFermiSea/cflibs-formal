/-
Copyright (c) 2026 Brian Squires. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Squires
-/
import Mathlib
import CflibsFormal.OLS
import CflibsFormal.Certificates
import CflibsFormal.Alt.OLSVariance

/-!
# CF-LIBS formalization — D-optimal line selection for the Boltzmann plot

**The experimentalist's question this module answers: *which spectral lines should I measure?***

Every other module in the stack takes the line set as *given* and asks what the fit does with it.
This module inverts the question. Given a pool of candidate lines with known upper-level energies,
it proves that the **single scalar that ranks candidate line sets is the upper-level energy spread**

  `SS_E = ∑ₖ (Eₖ − Ē)²`   (`energySpread`),

and that ranking is *exact*, not heuristic: under the Gauss–Markov noise model of
`Alt.OLSVariance` the recovered-slope variance is `σ²/SS_E`, a strictly decreasing function of
`SS_E` alone. Nothing else about the candidate set — how many lines it has, where the lines sit,
how their energies are distributed — enters the comparison. This is the one-parameter
specialization of classical **D-optimal design** (maximize `det(XᵀX)`; for the centered
straight-line design `det = n·SS_E`, see `OLS.det_centeredDesignNormalMatrix`).

## What is proven

* `energySpread` — the design objective `SS_E = ∑ₖ (Eₖ − Ē)²`, with `energySpread_nonneg` and
  `energySpreadCert_iff` (**the runtime gate the pipeline already checks, `Certificates.C1`, is
  exactly positivity of this objective** — the selection criterion and the well-posedness
  certificate are the same number).
* `slopeVariance_le_of_spread_ge` — **the monotone comparison.** If candidate set `A` has at least
  the energy spread of candidate set `B`, then `A`'s slope variance is at most `B`'s. Pick the
  wider spread.
* `slopeVariance_le_iff_spread_le` — **the criterion is exact, not merely sufficient.** For
  nondegenerate noise (`σ ≠ 0`), `A` beats `B` on variance **iff** `A` beats `B` on spread. No
  finer criterion exists at this level of the model, and no tie-break rule is needed.
* `slopeVariance_lt_of_spread_lt` — the strict form: strictly more spread ⇒ strictly less variance.
* `exists_dOptimal_lineSet` — **the optimality statement.** Over any finite nonempty family of
  candidate line sets, a spread-maximizer exists and it minimizes the slope variance over the whole
  family. This is "the argmax of `SS_E` is the argmin of `Var(β̂)`".
* `spreadOn`, `spreadOn_eq` — the spread of a **subset** `S` of a master line pool, so candidate
  sets of *different sizes* can be compared; `spreadOn_eq` gives the concrete Finset formula.
* `slopeVariance_le_of_spreadOn_ge`, `exists_dOptimal_subset` — the subset versions of the
  comparison and of the optimality statement: among the (finitely many) subsets of a measured line
  pool that pass the spread gate, the `SS_E`-maximizer minimizes the temperature-slope variance.
  Note the selected subsets need not have equal cardinality: `Var(β̂) = σ²/SS_E` carries no line
  count, so a *smaller* set with wider energy spread genuinely beats a larger bunched one.
* `fairCoins`, `radNoise` and their four laws — an **explicit nondegenerate (`σ = 1`) Gauss–Markov
  noise model**, so that every hypothesis of the theorems above is discharged by construction and
  the strict conclusions are realized with numbers (see *Non-vacuity*).

## Non-vacuity

Explicit two-line data: the narrow pair `E = (0,1)` (`SS_E = 1/2`) versus the wide pair
`E = (0,3)` (`SS_E = 9/2`), whose noise gains `∑ₖ wₖ² = 1/SS_E` are `2` and `2/9`
(`nonvacuity_energySpread_values`). The wide pair wins by exactly a factor `9` in slope variance
under *every* Gauss–Markov noise law (`nonvacuity_variance_ratio_nine`) and strictly so whenever
the noise is nondegenerate (`nonvacuity_wider_pair_strictly_better`).

The Gauss–Markov hypotheses are then discharged **with `σ = 1`** by an explicit construction — the
uniform measure on two fair coins (`fairCoins`, a genuine `IsProbabilityMeasure`) carrying the
Rademacher noise pair (`radNoise`, proven centered, unit-variance and uncorrelated:
`radNoise_mean`, `radNoise_variance`, `radNoise_uncorr`). On that model the two candidates have
slope variances `2` and `2/9` (`nonvacuity_rademacher_values`) and the D-optimality theorem fires
(`nonvacuity_dOptimal_fires`). Nothing here degenerates to `0 ≤ 0`: unlike the zero-noise
`Measure.dirac` witnesses used elsewhere in the stack (`Alt.StochasticBudget`), this witness has
`σ ≠ 0`, so the strict conclusions are genuinely realized.

## Literature and scope

**Scope tag: PURE-MATH** for every declaration. No physical constant, no atomic datum and no
spectroscopic model appears in any statement here: the module is a statement about the variance of
an ordinary-least-squares slope as a function of the abscissa configuration. The *physics reading*
is prose only — for the Boltzmann plot `yₖ = log(Iₖ/(gₖAₖ))` against upper-level energy `Eₖ` the
slope is `β = −1/(k_B T)`, so `Var(β̂) = σ²/SS_E` transfers to the temperature via
`ErrorBudget.temp_rel_error_eq`, and "maximize the upper-level energy spread" is the actionable
line-selection rule. Whether a candidate line is *usable* (optically thin, unblended, with reliable
`gA`) is a separate question this module does not address; see the honest-limitations note below.

Citation: **—** (pure mathematics). The design-theoretic ancestry is Kiefer & Wolfowitz's
equivalence theory of optimal design (*Canadian Journal of Mathematics* **12** (1960) 363–366) and
the Gauss–Markov slope-variance law of A. C. Aitken (*Proceedings of the Royal Society of
Edinburgh* **55** (1935) 42–48), formalized in `Alt.OLSVariance` as `olsSlope_variance_eq`. The
spectroscopic practice of choosing widely separated upper-level energies for the Boltzmann plot
is folklore going back to the two-line method of R. D. Cowan and G. H. Dieke, "Self-Absorption of
Spectrum Lines," *Reviews of Modern Physics* **20** (1948) 418–455.

## Honest limitations

* **The comparison holds the noise law fixed.** `σ²` is the *same* for both candidate sets: the
  theorems compare designs, not signal-to-noise ratios. A real candidate line with a wide energy
  but a poor SNR violates the homoscedasticity hypothesis shared by the two sides, and the
  comparison does not apply to it. Heteroscedastic (weighted) line selection is not formalized.
* **No line is modelled as unusable.** Optical thickness, blending and atomic-data quality are the
  other half of real line selection and appear nowhere in these statements; the theorems rank
  candidate sets that are *already* admissible under the pipeline's other gates.
* **Slope only.** The objective is the slope (temperature) variance. The intercept
  (concentration) variance `σ²(1/n + Ē²/SS_E)` (`Alt.StochasticBudget.alphaHat_variance_eq`) is a
  *different* functional of the design — it rewards both a large `n` and a small `|Ē|` — so the
  `SS_E`-maximizer is not in general jointly optimal for concentration. A genuine multi-objective
  (D- versus A-optimal) treatment is future work.
-/

namespace CflibsFormal

open CflibsFormal.Alt
open MeasureTheory ProbabilityTheory
open Finset Real
open scoped BigOperators ProbabilityTheory ENNReal

variable {ι : Type*} [Fintype ι]

/-! ## The design objective -/

/-- **The D-optimality objective for a candidate line set**: the upper-level **energy spread**
`SS_E = ∑ₖ (Eₖ − Ē)²` of the candidate's energies. This single scalar is what ranks candidate line
sets (`slopeVariance_le_iff_spread_le`): the slope variance is `σ²/SS_E`, so maximizing the spread
minimizes the recovered-temperature uncertainty. -/
noncomputable def energySpread (E : ι → ℝ) : ℝ := ∑ k, (E k - mean E) ^ 2

/-- The energy spread is a sum of squares, hence nonnegative. -/
theorem energySpread_nonneg (E : ι → ℝ) : 0 ≤ energySpread E :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- **The selection objective and the well-posedness gate are the same number.** The pipeline's
runtime rank gate `Certificates.energySpreadCert` (C1, the guard that certifies the Boltzmann
normal matrix is nonsingular) is *definitionally* the statement that the D-optimality objective is
positive. So a candidate line set is admissible exactly when its objective is nonzero, and among
admissible sets the ranking below applies. -/
theorem energySpreadCert_iff (E : ι → ℝ) : energySpreadCert E ↔ 0 < energySpread E := Iff.rfl

/-! ## The comparison theorems -/

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **THE LINE-SELECTION COMPARISON.** Two candidate line sets `A` and `B` are measured on the same
apparatus (same noise law: zero-mean, homoscedastic with common `σ²`, pairwise uncorrelated, `L²`
ordinate errors — the classical Gauss–Markov hypotheses). If the candidate `A` has **at least the
upper-level energy spread** of the candidate `B`, then fitting the Boltzmann plot on `A` gives a
recovered slope — hence a recovered temperature — of **at most the variance** obtained on `B`.

*Experimental reading:* given two admissible sets of lines you could measure, choose the one whose
upper-level energies are more widely spread; you cannot lose by doing so. Both candidates must pass
the spread gate (`0 < energySpread`, i.e. at least two distinct upper-level energies), which is the
pipeline's C1 certificate (`energySpreadCert_iff`).

This is the line-selection framing of `Alt.OLSVariance.olsSlope_variance_antitone`. -/
theorem slopeVariance_le_of_spread_ge [Nonempty ι] (A B : ι → ℝ) (α β σ : ℝ) (ε : ι → Ω → ℝ)
    (hA : 0 < energySpread A) (hB : 0 < energySpread B)
    (hAB : energySpread B ≤ energySpread A)
    (hL2 : ∀ k, MemLp (ε k) 2 μ)
    (huncorr : ∀ i j, i ≠ j → covariance (ε i) (ε j) μ = 0)
    (hhom : ∀ k, variance (ε k) μ = σ ^ 2) :
    variance (betaHat A α β ε) μ ≤ variance (betaHat B α β ε) μ :=
  olsSlope_variance_antitone B A α β σ ε hB hA hAB hL2 huncorr hhom

/-- **The energy spread is an EXACT ranking criterion, not merely a sufficient one.** For
nondegenerate noise (`σ ≠ 0`) the candidate `A` beats the candidate `B` on slope variance **if and
only if** it beats it on energy spread. Consequences for the experimentalist: (i) `SS_E` loses no
information — two candidate sets with equal spread are exactly equally good, whatever else differs
between them, including their line counts; (ii) no secondary tie-break criterion can improve on
`SS_E` at this level of the model. -/
theorem slopeVariance_le_iff_spread_le [Nonempty ι] (A B : ι → ℝ) (α β σ : ℝ) (ε : ι → Ω → ℝ)
    (hσ : σ ≠ 0) (hA : 0 < energySpread A) (hB : 0 < energySpread B)
    (hL2 : ∀ k, MemLp (ε k) 2 μ)
    (huncorr : ∀ i j, i ≠ j → covariance (ε i) (ε j) μ = 0)
    (hhom : ∀ k, variance (ε k) μ = σ ^ 2) :
    variance (betaHat A α β ε) μ ≤ variance (betaHat B α β ε) μ ↔ energySpread B ≤ energySpread A
    := by
  have hσ2 : (0 : ℝ) < σ ^ 2 := by positivity
  rw [olsSlope_variance_eq A α β σ ε hA hL2 huncorr hhom,
    olsSlope_variance_eq B α β σ ε hB hL2 huncorr hhom]
  simp only [energySpread]
  exact div_le_div_iff_of_pos_left hσ2 hA hB

/-- **Strict form: strictly more spread ⇒ strictly less variance.** With nondegenerate noise
(`σ ≠ 0`) the gain from widening the upper-level energy range is genuine, not a tie. -/
theorem slopeVariance_lt_of_spread_lt [Nonempty ι] (A B : ι → ℝ) (α β σ : ℝ) (ε : ι → Ω → ℝ)
    (hσ : σ ≠ 0) (hA : 0 < energySpread A) (hB : 0 < energySpread B)
    (hAB : energySpread B < energySpread A)
    (hL2 : ∀ k, MemLp (ε k) 2 μ)
    (huncorr : ∀ i j, i ≠ j → covariance (ε i) (ε j) μ = 0)
    (hhom : ∀ k, variance (ε k) μ = σ ^ 2) :
    variance (betaHat A α β ε) μ < variance (betaHat B α β ε) μ := by
  have hσ2 : (0 : ℝ) < σ ^ 2 := by positivity
  rw [olsSlope_variance_eq A α β σ ε hA hL2 huncorr hhom,
    olsSlope_variance_eq B α β σ ε hB hL2 huncorr hhom]
  exact div_lt_div_of_pos_left hσ2 hB hAB

/-! ## D-optimality over a family of candidate line sets -/

/-- **THE D-OPTIMALITY THEOREM: the argmax of the energy spread is the argmin of the slope
variance.** Given *any* finite nonempty family `cand : κ → (ι → ℝ)` of candidate line sets (each
admissible, i.e. each passing the spread gate), there exists a candidate `c★` that
(i) **maximizes the upper-level energy spread** over the family and
(ii) **minimizes the recovered-slope (hence recovered-temperature) variance** over the family.

*Experimental reading:* to choose the optimal line set, you never need to model the noise, estimate
`σ`, or run the fit. Compute one number per candidate — `SS_E = ∑ₖ (Eₖ − Ē)²`, from tabulated
upper-level energies alone — and take the largest. That choice is provably variance-optimal within
the family. -/
theorem exists_dOptimal_lineSet [Nonempty ι] {κ : Type*} [Finite κ] [Nonempty κ]
    (cand : κ → ι → ℝ) (α β σ : ℝ) (ε : ι → Ω → ℝ)
    (hpos : ∀ c, 0 < energySpread (cand c))
    (hL2 : ∀ k, MemLp (ε k) 2 μ)
    (huncorr : ∀ i j, i ≠ j → covariance (ε i) (ε j) μ = 0)
    (hhom : ∀ k, variance (ε k) μ = σ ^ 2) :
    ∃ cStar : κ, (∀ c, energySpread (cand c) ≤ energySpread (cand cStar)) ∧
      ∀ c, variance (betaHat (cand cStar) α β ε) μ ≤ variance (betaHat (cand c) α β ε) μ := by
  obtain ⟨cStar, hmax⟩ := Finite.exists_max (fun c => energySpread (cand c))
  refine ⟨cStar, hmax, fun c => ?_⟩
  exact slopeVariance_le_of_spread_ge (cand cStar) (cand c) α β σ ε (hpos cStar) (hpos c)
    (hmax c) hL2 huncorr hhom

/-! ## Selecting a SUBSET of a measured line pool

The comparisons above vary the energies at a fixed line count. Real line selection instead picks a
**subset** `S` of a measured pool `ι`, and competing subsets have different cardinalities. Because
`Var(β̂) = σ²/SS_E` carries **no line count**, the same single criterion still decides — a smaller
subset with wider energy spread genuinely beats a larger bunched one.

**Terminology, precisely.** At *fixed* line count (the theorems above) maximizing `SS_E` is
literally D-optimality: `det = n·SS_E` (`OLS.det_centeredDesignNormalMatrix`) and `n` is constant,
so argmax `SS_E` = argmax `det`. When the cardinalities *differ* the two criteria come apart, and
what the subset theorems below maximize is `SS_E`, i.e. they target the **slope (temperature)
variance alone** — `c`- or `D_s`-optimality for `β`, not full D-optimality. That is the honest
reading
and it is also the physically right one here: full D-optimality would additionally reward line
count, which the temperature objective `σ²/SS_E` provably does not. The statements below claim
variance-minimization only; none of them claims determinant-maximization. -/

/-- **The energy spread of a chosen SUBSET `S` of the measured line pool.** The fit is performed on
the selected lines only, so both the mean and the sum range over `S` (see `spreadOn_eq` for the
concrete Finset formula). -/
noncomputable def spreadOn (E : ι → ℝ) (S : Finset ι) : ℝ := energySpread (fun k : S => E k.1)

omit [Fintype ι] in
/-- **The subset objective in closed Finset form**:
`spreadOn E S = ∑_{k ∈ S} (Eₖ − (∑_{j ∈ S} Eⱼ)/|S|)²` — the ordinary energy spread computed over
the selected lines only. -/
theorem spreadOn_eq (E : ι → ℝ) (S : Finset ι) :
    spreadOn E S = ∑ k ∈ S, (E k - (∑ j ∈ S, E j) / (S.card : ℝ)) ^ 2 := by
  simp only [spreadOn, energySpread, mean, Fintype.card_coe, Finset.sum_coe_sort]
  exact Finset.sum_coe_sort S fun k => (E k - (∑ j ∈ S, E j) / (S.card : ℝ)) ^ 2

omit [Fintype ι] in
/-- **Subset line selection: the wider-spread subset wins, whatever the cardinalities.** Two
candidate *subsets* `S`, `T` of the same measured line pool, fitted with the same noise law. If `S`
has at least the energy spread of `T` then the fit on `S` has at most the slope variance of the fit
on `T` — even when `S` contains **fewer** lines than `T`, because the Gauss–Markov slope variance
`σ²/SS_E` carries no line count. -/
theorem slopeVariance_le_of_spreadOn_ge (E : ι → ℝ) (S T : Finset ι)
    (hS : S.Nonempty) (hT : T.Nonempty) (α β σ : ℝ) (ε : ι → Ω → ℝ)
    (hSpos : 0 < spreadOn E S) (hTpos : 0 < spreadOn E T)
    (hST : spreadOn E T ≤ spreadOn E S)
    (hL2 : ∀ k, MemLp (ε k) 2 μ)
    (huncorr : ∀ i j, i ≠ j → covariance (ε i) (ε j) μ = 0)
    (hhom : ∀ k, variance (ε k) μ = σ ^ 2) :
    variance (betaHat (fun k : S => E k.1) α β (fun k : S => ε k.1)) μ
      ≤ variance (betaHat (fun k : T => E k.1) α β (fun k : T => ε k.1)) μ := by
  haveI := hS.to_subtype
  haveI := hT.to_subtype
  have hSvar : variance (betaHat (fun k : S => E k.1) α β (fun k : S => ε k.1)) μ
      = σ ^ 2 / spreadOn E S :=
    olsSlope_variance_eq _ α β σ _ hSpos (fun k => hL2 k.1)
      (fun i j hij => huncorr i.1 j.1 (fun h => hij (Subtype.ext h))) (fun k => hhom k.1)
  have hTvar : variance (betaHat (fun k : T => E k.1) α β (fun k : T => ε k.1)) μ
      = σ ^ 2 / spreadOn E T :=
    olsSlope_variance_eq _ α β σ _ hTpos (fun k => hL2 k.1)
      (fun i j hij => huncorr i.1 j.1 (fun h => hij (Subtype.ext h))) (fun k => hhom k.1)
  rw [hSvar, hTvar]
  gcongr

omit [Fintype ι] in
/-- **D-optimal SUBSET selection.** Over any finite nonempty family of candidate subsets of the
measured line pool (each nonempty and each passing the spread gate), the `spreadOn`-maximizer
minimizes the recovered-slope variance over the whole family. The candidate subsets may have
different cardinalities. This is the form the question "which of my measured lines should I keep in
the Boltzmann plot?" actually takes. -/
theorem exists_dOptimal_subset (E : ι → ℝ) {κ : Type*} [Finite κ] [Nonempty κ]
    (cand : κ → Finset ι) (α β σ : ℝ) (ε : ι → Ω → ℝ)
    (hne : ∀ c, (cand c).Nonempty) (hpos : ∀ c, 0 < spreadOn E (cand c))
    (hL2 : ∀ k, MemLp (ε k) 2 μ)
    (huncorr : ∀ i j, i ≠ j → covariance (ε i) (ε j) μ = 0)
    (hhom : ∀ k, variance (ε k) μ = σ ^ 2) :
    ∃ cStar : κ, (∀ c, spreadOn E (cand c) ≤ spreadOn E (cand cStar)) ∧
      ∀ c, variance (betaHat (fun k : (cand cStar) => E k.1) α β
              (fun k : (cand cStar) => ε k.1)) μ
          ≤ variance (betaHat (fun k : (cand c) => E k.1) α β (fun k : (cand c) => ε k.1)) μ := by
  obtain ⟨cStar, hmax⟩ := Finite.exists_max (fun c => spreadOn E (cand c))
  refine ⟨cStar, hmax, fun c => ?_⟩
  exact slopeVariance_le_of_spreadOn_ge E (cand cStar) (cand c) (hne cStar) (hne c) α β σ ε
    (hpos cStar) (hpos c) (hmax c) hL2 huncorr hhom

/-! ## Non-vacuity on explicit data: `E = (0,1)` versus `E = (0,3)` -/

/-- **Non-vacuity — the two candidate line sets are genuinely different and both admissible.** The
narrow pair `E = (0,1)` has `SS_E = 1/2`; the wide pair `E = (0,3)` has `SS_E = 9/2`. Both are
strictly positive (both pass the C1 spread gate, so both fits are well-posed), and the wide pair's
spread is strictly larger — so the strict comparison theorems apply, non-vacuously. The
corresponding OLS noise gains `∑ₖ wₖ² = 1/SS_E` are `2` and `2/9`. -/
theorem nonvacuity_energySpread_values :
    energySpread (ι := Fin 2) ![0, 1] = 1 / 2 ∧ energySpread (ι := Fin 2) ![0, 3] = 9 / 2 ∧
      energySpread (ι := Fin 2) ![0, 1] < energySpread (ι := Fin 2) ![0, 3] ∧
      1 / energySpread (ι := Fin 2) ![0, 3] < 1 / energySpread (ι := Fin 2) ![0, 1] := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [energySpread, mean, Fin.sum_univ_two] <;> norm_num

/-- **Non-vacuity — the wider pair wins by exactly a factor of nine.** On the explicit data
`E = (0,1)` versus `E = (0,3)`, under any Gauss–Markov noise law, the slope variance of the wide
pair is exactly `1/9` of the narrow pair's: `Var_narrow = 9 · Var_wide`. The improvement is an
identity, not a bound — moving one line's upper level from `1` to `3` cuts the temperature-slope
variance ninefold. -/
theorem nonvacuity_variance_ratio_nine (α β σ : ℝ) (ε : Fin 2 → Ω → ℝ)
    (hL2 : ∀ k, MemLp (ε k) 2 μ)
    (huncorr : ∀ i j, i ≠ j → covariance (ε i) (ε j) μ = 0)
    (hhom : ∀ k, variance (ε k) μ = σ ^ 2) :
    variance (betaHat ![0, 1] α β ε) μ = 9 * variance (betaHat ![0, 3] α β ε) μ := by
  have h1 : (0 : ℝ) < ∑ k, (![(0 : ℝ), 1] k - mean ![(0 : ℝ), 1]) ^ 2 := by
    simp [mean, Fin.sum_univ_two]; norm_num
  have h3 : (0 : ℝ) < ∑ k, (![(0 : ℝ), 3] k - mean ![(0 : ℝ), 3]) ^ 2 := by
    simp [mean, Fin.sum_univ_two]; norm_num
  rw [olsSlope_variance_eq ![0, 1] α β σ ε h1 hL2 huncorr hhom,
    olsSlope_variance_eq ![0, 3] α β σ ε h3 hL2 huncorr hhom]
  have e1 : (∑ k, (![(0 : ℝ), 1] k - mean ![(0 : ℝ), 1]) ^ 2) = 1 / 2 := by
    simp [mean, Fin.sum_univ_two]; norm_num
  have e3 : (∑ k, (![(0 : ℝ), 3] k - mean ![(0 : ℝ), 3]) ^ 2) = 9 / 2 := by
    simp [mean, Fin.sum_univ_two]; norm_num
  rw [e1, e3]
  ring

/-- **Non-vacuity — the strict comparison fires on explicit data.** With nondegenerate noise
(`σ ≠ 0`), the wide pair `E = (0,3)` gives a **strictly** smaller slope variance than the narrow
pair `E = (0,1)`: an instance of `slopeVariance_lt_of_spread_lt` on real numbers, so the hypotheses
of the comparison theorems are jointly satisfiable with a strict conclusion. -/
theorem nonvacuity_wider_pair_strictly_better (α β σ : ℝ) (ε : Fin 2 → Ω → ℝ) (hσ : σ ≠ 0)
    (hL2 : ∀ k, MemLp (ε k) 2 μ)
    (huncorr : ∀ i j, i ≠ j → covariance (ε i) (ε j) μ = 0)
    (hhom : ∀ k, variance (ε k) μ = σ ^ 2) :
    variance (betaHat ![0, 3] α β ε) μ < variance (betaHat ![0, 1] α β ε) μ := by
  obtain ⟨e1, e3, hlt, -⟩ := nonvacuity_energySpread_values
  exact slopeVariance_lt_of_spread_lt ![0, 3] ![0, 1] α β σ ε hσ (e3 ▸ by norm_num)
    (e1 ▸ by norm_num) hlt hL2 huncorr hhom

/-! ### An explicit NONDEGENERATE noise model (`σ = 1`)

The comparison theorems are quantified over Gauss–Markov noise laws, so a witness that the
hypotheses are jointly satisfiable **with `σ ≠ 0`** is what makes the strict conclusions real. The
zero-noise `Measure.dirac` witness used elsewhere in the stack (`Alt.StochasticBudget`) forces
`σ = 0` and collapses every variance to `0`; here we build an honest one instead. The sample space
is a fair pair of coins `Bool × Bool` and the noise is the **Rademacher pair** `ε₀ = ±1` from the
first coin, `ε₁ = ±1` from the second: zero-mean, unit-variance and *uncorrelated* — exactly the
classical Gauss–Markov hypotheses with `σ = 1`, on a genuine `IsProbabilityMeasure`. -/

/-- The fair four-point sample space: uniform probability on `Bool × Bool` (two fair coins). -/
noncomputable def fairCoins : Measure (Bool × Bool) := (4 : ℝ≥0∞)⁻¹ • Measure.count

instance fairCoins_isProbabilityMeasure : IsProbabilityMeasure fairCoins := by
  constructor
  unfold fairCoins
  rw [Measure.smul_apply, smul_eq_mul, Measure.count_apply_finite _ Set.finite_univ]
  simp only [Set.toFinite_toFinset, Set.toFinset_univ, card_univ, Fintype.card_prod,
    Fintype.card_bool, Nat.reduceMul, Nat.cast_ofNat]
  rw [ENNReal.inv_mul_cancel] <;> norm_num

/-- Integration against `fairCoins` is the plain four-point average. -/
theorem fairCoins_integral (f : Bool × Bool → ℝ) :
    ∫ ω, f ω ∂fairCoins = (∑ a, f a) / 4 := by
  unfold fairCoins
  rw [integral_smul_measure, integral_count]
  simp
  ring

/-- **The Rademacher noise pair**: `ε₀` reads the first coin and `ε₁` the second, each `±1`. -/
noncomputable def radNoise : Fin 2 → Bool × Bool → ℝ
  | 0 => fun ω => if ω.1 then 1 else -1
  | 1 => fun ω => if ω.2 then 1 else -1

/-- Every `radNoise k` is square-integrable (a bounded function on a finite probability space). -/
theorem radNoise_memLp (k : Fin 2) : MemLp (radNoise k) 2 fairCoins := MemLp.of_discrete

/-- The Rademacher noise is centered: `𝔼[εₖ] = 0`. -/
theorem radNoise_mean (k : Fin 2) : fairCoins[radNoise k] = 0 := by
  fin_cases k <;>
    (rw [fairCoins_integral]; simp [radNoise, Fintype.sum_prod_type])

/-- The Rademacher noise is homoscedastic with **`σ = 1`**: `Var(εₖ) = 1²`. This is the hypothesis
the zero-noise `dirac` witness cannot supply. -/
theorem radNoise_variance (k : Fin 2) : variance (radNoise k) fairCoins = 1 ^ 2 := by
  rw [← covariance_self (radNoise_memLp k).aestronglyMeasurable.aemeasurable,
    covariance_eq_sub (radNoise_memLp k) (radNoise_memLp k), radNoise_mean]
  fin_cases k <;>
    (rw [fairCoins_integral]; simp [radNoise, Fintype.sum_prod_type]; norm_num)

/-- The two coins are uncorrelated: `cov(ε₀, ε₁) = 0` — the classical Gauss–Markov hypothesis. -/
theorem radNoise_uncorr (i j : Fin 2) (hij : i ≠ j) :
    covariance (radNoise i) (radNoise j) fairCoins = 0 := by
  rw [covariance_eq_sub (radNoise_memLp i) (radNoise_memLp j), radNoise_mean, radNoise_mean]
  fin_cases i <;> fin_cases j <;>
    simp_all only [Nat.reduceAdd, Fin.zero_eta, Fin.isValue, Fin.mk_one, ne_eq,
      not_true_eq_false, zero_ne_one, one_ne_zero, not_false_eq_true] <;>
    (rw [fairCoins_integral]; simp [radNoise, Fintype.sum_prod_type])

/-- **Non-vacuity — the whole comparison is realized, with numbers, on a real probability space
carrying real noise.** With the fair-coin Rademacher model (`σ = 1`) the two candidate line sets
give slope variances `Var = 2` (narrow pair `E = (0,1)`) and `Var = 2/9` (wide pair `E = (0,3)`),
so the wide pair is **strictly** better and by exactly the ninefold factor predicted by
`nonvacuity_variance_ratio_nine`. Every Gauss–Markov hypothesis is discharged by an explicit
construction, and no variance is degenerate — nothing here is `0 ≤ 0`. -/
theorem nonvacuity_rademacher_values (α β : ℝ) :
    variance (betaHat ![0, 1] α β radNoise) fairCoins = 2 ∧
      variance (betaHat ![0, 3] α β radNoise) fairCoins = 2 / 9 ∧
      variance (betaHat ![0, 3] α β radNoise) fairCoins
        < variance (betaHat ![0, 1] α β radNoise) fairCoins := by
  have h1 : (0 : ℝ) < ∑ k, (![(0 : ℝ), 1] k - mean ![(0 : ℝ), 1]) ^ 2 := by
    simp [mean, Fin.sum_univ_two]; norm_num
  have h3 : (0 : ℝ) < ∑ k, (![(0 : ℝ), 3] k - mean ![(0 : ℝ), 3]) ^ 2 := by
    simp [mean, Fin.sum_univ_two]; norm_num
  have v1 : variance (betaHat ![0, 1] α β radNoise) fairCoins = 2 := by
    rw [olsSlope_variance_eq ![0, 1] α β 1 radNoise h1 radNoise_memLp radNoise_uncorr
      radNoise_variance]
    simp [mean, Fin.sum_univ_two]; norm_num
  have v3 : variance (betaHat ![0, 3] α β radNoise) fairCoins = 2 / 9 := by
    rw [olsSlope_variance_eq ![0, 3] α β 1 radNoise h3 radNoise_memLp radNoise_uncorr
      radNoise_variance]
    simp [mean, Fin.sum_univ_two]; norm_num
  exact ⟨v1, v3, by rw [v1, v3]; norm_num⟩

/-- **Non-vacuity — the D-optimality theorem fires on a genuine probability measure with genuine
noise.** All hypotheses of `exists_dOptimal_lineSet` are jointly satisfiable: the two-element
candidate family `{(0,1), (0,3)}` (both admissible) under the fair-coin Rademacher law with
`σ = 1`. The conclusion is *existential* — it produces some maximizer `cStar`, and does not itself
name which candidate that is. What makes it non-degenerate rather than a tie between zeros is the
separate computation `nonvacuity_rademacher_values`: the two candidates have distinct variances
`2` and `2/9`, so the optimum here is a strict improvement, not an artifact of everything
vanishing. -/
theorem nonvacuity_dOptimal_fires (α β : ℝ) :
    ∃ cStar : Fin 2,
      (∀ c, energySpread (![![0, 1], ![0, 3]] c) ≤ energySpread (![![0, 1], ![0, 3]] cStar)) ∧
        ∀ c, variance (betaHat (![![0, 1], ![0, 3]] cStar) α β radNoise) fairCoins
            ≤ variance (betaHat (![![0, 1], ![0, 3]] c) α β radNoise) fairCoins := by
  refine exists_dOptimal_lineSet (μ := fairCoins)
    ![![0, 1], ![0, 3]] α β 1 radNoise (fun c => ?_) radNoise_memLp radNoise_uncorr
    radNoise_variance
  fin_cases c <;> (simp [energySpread, mean, Fin.sum_univ_two]; norm_num)

end CflibsFormal
