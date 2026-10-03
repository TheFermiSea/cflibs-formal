/-
Copyright (c) 2026 Brian Squires. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Squires
-/
import Mathlib

/-!
# CF-LIBS formalization — when is a missing line evidence of absence? (two gates)

Two decision rules for an element-detection comb and a wavelength-registration scan, stated
so that a pipeline can gate on them and a metamorphic fixture can check the gate.

## 1. Detectability is conditioned on the instrument response

A spectrometer records the emitted intensity times a response `R λ ≥ 0`. In a band where `R = 0`
(a dead detector region) the recording is identical whether the element is present or absent, so
a missing line there is **not** evidence of absence. This module proves that
(`signal_eq_of_dead`, `not_isEvidence_of_dead`), defines the set of *informative* expected lines
(`informative`: those whose expected recorded signal `R k · I k` clears the noise floor), and shows
that the detections that count (those on informative lines) score at least as high over the
informative lines as over the whole comb (`conditionedRecall_ge`; `conditionedRecall_le_one`
keeps it a recall): dead teeth deflate the score without carrying information. The conditioned
recall is `|D ∩ informative| / |informative|`. It is **not** ordered against the naive recall
`|D| / |S|` that also counts detections on non-informative lines: a detection on a line whose
expected signal is below the floor is ignored, so the conditioned recall can be lower (the
`example` after `conditionedRecall_le_one` has naive `1/2` and conditioned `0`).

## 2. A registration shift at the edge of its scan is not identified

If the objective of a bounded shift scan is strictly monotone on the scan interval, its minimizer
is an endpoint (`argmin_eq_left_of_strictMonoOn`, `argmin_eq_right_of_strictAntiOn`). An applied
shift sitting at the scan boundary is therefore what a monotone objective produces, not evidence
of a shift of that size; the rule is to refuse or widen the scan (`AtScanBoundary`).

## Honest limitations

* **Pure mathematics with abstract inputs.** The response `R`, the expected intensity `I` and the
  noise floor are inputs; nothing here says which band is dead, how `R` is measured, or that an
  uncalibrated epoch has a usable `R`. The expected intensity is a model value, not a measurement.
* **The comb statement is about scoring, not about the element.** Conditioning on informative
  lines changes what a missing line means; with few informative lines the right outcome is to
  abstain (the fixtures carry a minimum-informative-lines input), not to report a perfect recall.
* **Only informative detections are counted.** Both recall theorems are about
  `D ∩ informative`, for any detected set `D`. A detection on a non-informative line (a false
  positive, an interferent, or a line the model under-predicts) is dropped by the conditioned
  score, so conditioning can lower a naive score that counted it. Whether such a detection
  should count is a modeling question this module does not settle.
* **The shift statement is a decision rule.** Landing on the boundary is necessary, not
  sufficient, for monotonicity of the objective (it can also be an interior-optimum truncation);
  the lemma says only what a strictly monotone objective forces.

## Literature

**Scope: PURE-MATH.** Finite counting and monotone-function elementary facts; no spectroscopy
source is relied on. The comb/detection-by-expected-lines practice is the pipeline's convention.
-/

namespace CflibsFormal.LineEvidence

open Finset

variable {ι : Type*}

/-- A line is *evidence* when its expected recorded signal `R k · I k` (response times expected
emitted intensity) clears the noise floor. -/
def IsEvidence (floor : ℝ) (R I : ι → ℝ) (k : ι) : Prop := floor < R k * I k

open Classical in
/-- The informative expected lines of a comb `S`: those whose expected recorded signal clears the
noise floor. -/
noncomputable def informative (floor : ℝ) (R I : ι → ℝ) (S : Finset ι) : Finset ι :=
  S.filter (fun k => floor < R k * I k)

/-- In a dead band (`R k = 0`) the recorded signal is the same for every emitted intensity, in
particular for presence and absence of the element. -/
theorem signal_eq_of_dead {R I I' : ι → ℝ} {k : ι} (hR : R k = 0) : R k * I k = R k * I' k := by
  rw [hR]
  simp

/-- In a dead band, with a nonnegative noise floor, a missing line is not evidence. -/
theorem not_isEvidence_of_dead {floor : ℝ} (hfloor : 0 ≤ floor) {R I : ι → ℝ} {k : ι}
    (hR : R k = 0) : ¬ IsEvidence floor R I k := by
  unfold IsEvidence
  rw [hR, zero_mul]
  exact not_lt.mpr hfloor

/-- The informative lines are among the expected ones. -/
theorem informative_subset (floor : ℝ) (R I : ι → ℝ) (S : Finset ι) :
    informative floor R I S ⊆ S := by
  classical
  unfold informative
  exact Finset.filter_subset _ _

/-- A dead-band line is never informative (for a nonnegative floor). -/
theorem not_mem_informative_of_dead {floor : ℝ} (hfloor : 0 ≤ floor) {R I : ι → ℝ} {k : ι}
    (S : Finset ι) (hR : R k = 0) : k ∉ informative floor R I S := by
  classical
  unfold informative
  intro h
  exact not_isEvidence_of_dead hfloor hR (Finset.mem_filter.mp h).2

/-- **Conditioning on the informative lines never lowers the score of the informative
detections.** For any detected set `D` and a nonempty informative set, with
`D' = D ∩ informative S` the detections that count,
`|D'|/|S| ≤ |D'|/|informative S|`: expected-but-uninformative lines only deflate the score.
The left side is the naive recall when every detection is informative; it is *not* the naive
recall `|D|/|S|` in general (see the `example` below). -/
theorem conditionedRecall_ge [DecidableEq ι] {floor : ℝ} {R I : ι → ℝ} {S : Finset ι}
    (D : Finset ι)
    (hne : (informative floor R I S).Nonempty) :
    ((D ∩ informative floor R I S).card : ℝ) / S.card
      ≤ ((D ∩ informative floor R I S).card : ℝ) / (informative floor R I S).card := by
  have hpos : (0 : ℝ) < (informative floor R I S).card := by
    exact_mod_cast Finset.card_pos.mpr hne
  have hle : ((informative floor R I S).card : ℝ) ≤ S.card := by
    exact_mod_cast Finset.card_le_card (informative_subset floor R I S)
  exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hpos hle

/-- The conditioned recall `|D ∩ informative S| / |informative S|` is a genuine recall: at most
`1`, for any detected set `D`. -/
theorem conditionedRecall_le_one [DecidableEq ι] {floor : ℝ} {R I : ι → ℝ} {S : Finset ι}
    (D : Finset ι)
    (hne : (informative floor R I S).Nonempty) :
    ((D ∩ informative floor R I S).card : ℝ) / (informative floor R I S).card ≤ 1 := by
  have hpos : (0 : ℝ) < (informative floor R I S).card := by
    exact_mod_cast Finset.card_pos.mpr hne
  rw [div_le_one hpos]
  exact_mod_cast Finset.card_le_card Finset.inter_subset_right

/-- The conditioned recall is not bounded below by the naive recall that counts every detection.
Two expected lines, line `0` in a dead band and line `1` live; the only detection is on line
`0`. The naive recall is `1/2`, the conditioned recall is `0`. -/
example :
    (((({0} : Finset (Fin 2)) ∩ informative 1 ![0, 1] ![100, 100] Finset.univ).card : ℝ)
        / (informative 1 ![0, 1] ![100, 100] Finset.univ).card)
      < (({0} : Finset (Fin 2)).card : ℝ) / (Finset.univ : Finset (Fin 2)).card := by
  have hinf : informative (1 : ℝ) (![0, 1] : Fin 2 → ℝ) ![100, 100] Finset.univ = {1} := by
    ext k
    simp only [informative, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    fin_cases k <;> norm_num
  rw [hinf]; simp

/-- A shift `s` is at the *scan boundary* of the interval `[lo, hi]` when it lies within `ε` of
either end. -/
def AtScanBoundary (lo hi ε s : ℝ) : Prop := s ≤ lo + ε ∨ hi - ε ≤ s

/-- A strictly increasing objective on `[lo, hi]` has its minimizer at the left end. -/
theorem argmin_eq_left_of_strictMonoOn {f : ℝ → ℝ} {lo hi s : ℝ} (hs : s ∈ Set.Icc lo hi)
    (hf : StrictMonoOn f (Set.Icc lo hi)) (hmin : ∀ t ∈ Set.Icc lo hi, f s ≤ f t) : s = lo := by
  by_contra hne
  have hlo : lo ∈ Set.Icc lo hi := ⟨le_rfl, hs.1.trans hs.2⟩
  have hlt : lo < s := lt_of_le_of_ne hs.1 (Ne.symm hne)
  exact absurd (hmin lo hlo) (not_le.mpr (hf hlo hs hlt))

/-- A strictly decreasing objective on `[lo, hi]` has its minimizer at the right end. -/
theorem argmin_eq_right_of_strictAntiOn {f : ℝ → ℝ} {lo hi s : ℝ} (hs : s ∈ Set.Icc lo hi)
    (hf : StrictAntiOn f (Set.Icc lo hi)) (hmin : ∀ t ∈ Set.Icc lo hi, f s ≤ f t) : s = hi := by
  by_contra hne
  have hhi : hi ∈ Set.Icc lo hi := ⟨hs.1.trans hs.2, le_rfl⟩
  have hlt : s < hi := lt_of_le_of_ne hs.2 hne
  exact absurd (hmin hi hhi) (not_le.mpr (hf hs hhi hlt))

/-- The minimizer of a strictly monotone scan objective is at the scan boundary, for every
tolerance `ε ≥ 0`. -/
theorem atScanBoundary_of_strictMonoOn {f : ℝ → ℝ} {lo hi ε s : ℝ} (hε : 0 ≤ ε)
    (hs : s ∈ Set.Icc lo hi) (hf : StrictMonoOn f (Set.Icc lo hi))
    (hmin : ∀ t ∈ Set.Icc lo hi, f s ≤ f t) : AtScanBoundary lo hi ε s := by
  left
  rw [argmin_eq_left_of_strictMonoOn hs hf hmin]
  linarith

end CflibsFormal.LineEvidence
