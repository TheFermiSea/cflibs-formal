/-
Copyright (c) 2026 Brian Squires. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Squires
-/
import Mathlib
import CflibsFormal.ForwardMapEnergy

/-!
# CF-LIBS formalization — lines from a shared upper level: an atomic-data consistency gate

Two optically thin lines emitted from the **same upper level** have the same Boltzmann-plot
ordinate, at every temperature, density and calibration: the level population is common, and
dividing each intensity by its own `g·A` removes what differs. So the measured ordinates of such
a pair must agree to within their measurement errors, and that can be checked from a single
spectrum with no knowledge of `T`, `n_e` or the composition.

What is proved:

* `ordinate_eq_of_energy_eq`, `ordinate_wavelength_eq_of_energy_eq` — the equality, for the
  photon-rate ordinate `log(I/(gA))` and for the wavelength ordinate `log(I·λ/(gA))`.
* `ordinate_gap_of_wrong_weight` — if the reader's `g·A` for one line of the pair is off by a
  factor `c` (a wrong statistical weight or a wrong transition probability in the atomic-data
  row), the two ordinates differ by exactly `−log c`. A weight entered as `1` where it is `3`
  gives a gap of `log 3 ≈ 1.10`.
* `SharedLevelConsistent` and `sharedLevelConsistent_of_within` — the gate
  `|ŷ_j − ŷ_k| ≤ ε_j + ε_k`, and that it holds whenever both measured ordinates are within their
  error bars of a common true value. `not_both_within_of_inconsistent` is the contrapositive:
  a failed gate means at least one of the two is outside its error bar.
* `wrong_weight_detected` — detection power: a `g·A` factor `c` with `|log c| > 2(ε_j + ε_k)`
  on one line always fails the gate.

## Honest limitations

* **A failed gate does not say what is wrong.** The equality is a statement about the optically
  thin LTE forward model with correct atomic data. A real pair can fail it because of an
  atomic-data error, self-absorption (the two lines end on different lower levels and have
  different optical depths), a blend, a misassigned line, a wavelength-dependent response that
  was not removed, or an understated error bar. The gate flags the pair; it does not diagnose.
* **A common error is invisible.** If both lines' `g·A` are off by the same factor, or the
  shared upper-level energy is wrong, the ordinates still agree. The gate checks the *ratio*
  of the two `g·A` values only.
* **"Same upper level" must come from the level assignment, not from the tabulated energy.**
  The theorems take `E j = E k` as the hypothesis. A database row whose upper-level energy is
  itself wrong would not be grouped with its true partners by an energy match; group by the
  level label.
* **The detection threshold is sufficient, not necessary.** A factor with
  `|log c| ≤ 2(ε_j + ε_k)` may or may not fail the gate.
* **Model idealization.** In `lineIntensity` the index enumerates lines, each with its own
  `(g, E, A)`, and the partition function sums over that index, so a level shared by two lines
  is counted twice in `U`. `U` is common to the pair and cancels here, so the equality does not
  depend on it.

## Literature

The equality is the Boltzmann-plot identity (`ForwardMap.boltzmann_plot_intensity`, Ciucci et
al. 1999; wavelength form `ForwardMapEnergy.boltzmann_plot_intensity_wavelength`, Aragón &
Aguilera 2008) evaluated at two lines of equal upper-level energy. Using lines from a common
upper level to test relative transition probabilities is the branching-ratio idea of atomic
spectroscopy; no source is cited for it here, and nothing in this module depends on one.
-/

namespace CflibsFormal

open Finset Real

variable {ι : Type*} [Fintype ι]

/-- **Lines from a shared upper level have equal Boltzmann ordinates (photon-rate form).** If
lines `j` and `k` have the same upper-level energy, then
`log(I_j/(g_j A_j)) = log(I_k/(g_k A_k))`, whatever the temperature, the density and the
calibration. Immediate from `boltzmann_plot_intensity`: the intercept is common and the slope
term depends only on the energy. -/
theorem ordinate_eq_of_energy_eq [Nonempty ι] {kB T N Fcal : ℝ} {g E A : ι → ℝ}
    (hg : ∀ k, 0 < g k) (hN : 0 < N) (hFcal : 0 < Fcal) (hA : ∀ k, 0 < A k) {j k : ι}
    (hE : E j = E k) :
    Real.log (lineIntensity kB T N Fcal g E A j / (g j * A j))
      = Real.log (lineIntensity kB T N Fcal g E A k / (g k * A k)) := by
  rw [boltzmann_plot_intensity hg hN hFcal hA j, boltzmann_plot_intensity hg hN hFcal hA k, hE]

/-- **Lines from a shared upper level have equal Boltzmann ordinates (wavelength form).** For
energy-calibrated intensities the ordinate is `log(I·λ/(gA))`, and it is again equal for two
lines of equal upper-level energy, even though their wavelengths differ. -/
theorem ordinate_wavelength_eq_of_energy_eq [Nonempty ι] {hc fourPi kB T N Fgeo : ℝ}
    {g E A lam : ι → ℝ} (hg : ∀ k, 0 < g k) (hN : 0 < N) (hhc : 0 < hc) (hfp : 0 < fourPi)
    (hFgeo : 0 < Fgeo) (hA : ∀ k, 0 < A k) (hlam : ∀ k, 0 < lam k) {j k : ι} (hE : E j = E k) :
    Real.log (lineIntensityEnergy hc fourPi kB T N Fgeo g E A lam j * lam j / (g j * A j))
      = Real.log (lineIntensityEnergy hc fourPi kB T N Fgeo g E A lam k * lam k / (g k * A k)) := by
  rw [boltzmann_plot_intensity_wavelength hg hN hhc hfp hFgeo hA hlam j,
    boltzmann_plot_intensity_wavelength hg hN hhc hfp hFgeo hA hlam k, hE]

/-- **A wrong `g·A` on one line of the pair opens a gap of exactly `−log c`.** If the reader
divides line `j` by `c·(g_j A_j)` in place of `g_j A_j` (its atomic-data row has the statistical
weight or the transition probability off by the factor `c > 0`), while line `k`, from the same
upper level, is read correctly, the two ordinates differ by `−log c`. For `c = 1/3` (a weight
entered as `1` where it is `3`) the gap is `log 3`. -/
theorem ordinate_gap_of_wrong_weight [Nonempty ι] {kB T N Fcal c : ℝ} {g E A : ι → ℝ}
    (hg : ∀ k, 0 < g k) (hN : 0 < N) (hFcal : 0 < Fcal) (hA : ∀ k, 0 < A k) (hc : 0 < c)
    {j k : ι} (hE : E j = E k) :
    Real.log (lineIntensity kB T N Fcal g E A j / (c * (g j * A j)))
        - Real.log (lineIntensity kB T N Fcal g E A k / (g k * A k))
      = - Real.log c := by
  have hI := lineIntensity_pos (kB := kB) (T := T) (E := E) hg hN hFcal hA j
  have hgA : 0 < g j * A j := mul_pos (hg j) (hA j)
  have hsplit : lineIntensity kB T N Fcal g E A j / (c * (g j * A j))
      = (lineIntensity kB T N Fcal g E A j / (g j * A j)) / c := by
    field_simp
  rw [hsplit, Real.log_div (div_pos hI hgA).ne' hc.ne',
    ordinate_eq_of_energy_eq hg hN hFcal hA hE]
  ring

/-- The shared-upper-level consistency gate on two measured ordinates `yj`, `yk` with error
bars `εj`, `εk`: they agree to within the sum of the error bars. -/
def SharedLevelConsistent (yj yk εj εk : ℝ) : Prop := |yj - yk| ≤ εj + εk

/-- **The gate passes when both measurements are within their error bars.** If two measured
ordinates lie within `εj`, `εk` of a common true value `y`, they differ by at most `εj + εk`.
With `ordinate_eq_of_energy_eq` supplying the common value, this is the soundness of the gate
for a pair of lines from one upper level. -/
theorem sharedLevelConsistent_of_within {y yj yk εj εk : ℝ} (hj : |yj - y| ≤ εj)
    (hk : |yk - y| ≤ εk) : SharedLevelConsistent yj yk εj εk := by
  unfold SharedLevelConsistent
  calc |yj - yk| = |(yj - y) - (yk - y)| := by ring_nf
    _ ≤ |yj - y| + |yk - y| := abs_sub _ _
    _ ≤ εj + εk := add_le_add hj hk

/-- **A failed gate means a measurement is outside its error bar.** The contrapositive of
`sharedLevelConsistent_of_within`: if the two measured ordinates disagree by more than
`εj + εk`, they cannot both be within their error bars of any one common value. What that
implies physically (bad atomic data, self-absorption, a blend, a wrong error bar) is not
decided here. -/
theorem not_both_within_of_inconsistent {y yj yk εj εk : ℝ}
    (h : ¬ SharedLevelConsistent yj yk εj εk) : ¬ (|yj - y| ≤ εj ∧ |yk - y| ≤ εk) :=
  fun ⟨hj, hk⟩ => h (sharedLevelConsistent_of_within hj hk)

/-- **Detection power.** Suppose both measured ordinates are within their error bars of the
common true value `y`, but line `j` is then read with a `g·A` off by the factor `c`, which
moves its ordinate to `yj − log c` (`ordinate_gap_of_wrong_weight`). If
`|log c| > 2·(εj + εk)` the gate fails. Sufficient, not necessary. -/
theorem wrong_weight_detected {y yj yk εj εk c : ℝ} (hj : |yj - y| ≤ εj) (hk : |yk - y| ≤ εk)
    (hc : 2 * (εj + εk) < |Real.log c|) :
    ¬ SharedLevelConsistent (yj - Real.log c) yk εj εk := by
  unfold SharedLevelConsistent
  have hclose : |yj - yk| ≤ εj + εk := sharedLevelConsistent_of_within hj hk
  have htri : |Real.log c| ≤ |yj - Real.log c - yk| + |yj - yk| := by
    calc |Real.log c| = |(yj - yk) - (yj - Real.log c - yk)| := by ring_nf
      _ ≤ |yj - yk| + |yj - Real.log c - yk| := abs_sub _ _
      _ = |yj - Real.log c - yk| + |yj - yk| := add_comm _ _
  intro hcons
  linarith

/-- Non-vacuity of the detection threshold: a weight entered as `1` where it is `3`
(`c = 1/3`, gap `log 3 > 1`) is detected with error bars `εj = εk = 1/8`. -/
example {y yj yk : ℝ} (hj : |yj - y| ≤ 1 / 8) (hk : |yk - y| ≤ 1 / 8) :
    ¬ SharedLevelConsistent (yj - Real.log (1 / 3)) yk (1 / 8) (1 / 8) := by
  refine wrong_weight_detected hj hk ?_
  have h3 : (1 : ℝ) < Real.log 3 := by
    have he : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ < Real.log 3 := Real.log_lt_log (Real.exp_pos 1) he
  have hlog : Real.log (1 / 3) = - Real.log 3 := by rw [one_div, Real.log_inv]
  rw [hlog, abs_neg, abs_of_pos (lt_trans one_pos h3)]
  linarith

end CflibsFormal
