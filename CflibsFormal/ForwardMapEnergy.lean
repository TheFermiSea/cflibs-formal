/-
Copyright (c) 2026 Brian Squires. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Squires
-/
import Mathlib
import CflibsFormal.Boltzmann
import CflibsFormal.ForwardMap

/-!
# CF-LIBS formalization — the energy-intensity forward map and convention equivalence

The canonical forward map `ForwardMap.lineIntensity = Fcal · A_k · n_k` uses the **photon-rate
(calibration-absorbed)** convention (Ciucci et al. 1999; Tognoni et al. 2010): the
line-independent prefactors — collection efficiency, plasma volume, `h c / 4π` — are lumped into
the scalar `Fcal`, and the Boltzmann-plot ordinate is `log(I/(g_k A_k))`, with no explicit `λ`.

A real spectrometer integrates an **energy/radiance** quantity, for which the standard CF-LIBS
ordinate carries the wavelength explicitly: `log(I·λ_k/(g_k A_k))` (Aragón & Aguilera 2008;
Thouin et al. 2023). The two differ by the **per-line** photon-energy factor `h c / 4π λ_{ki}`,
which a *scalar* `Fcal` cannot literally carry. This module makes that factor explicit in a thin
**energy-intensity sibling** and machine-proves the two conventions yield the **same
Boltzmann-plot slope** `-1/(k_B T)` (hence the same recovered temperature) — closing a
literature-review flag that the reduced ordinate "omits λ" (it does not: `λ` is folded into
`Fcal`). The two *intercepts* differ by the calibration identification `Fcal = h c · Fgeo / 4π`;
it is the slope (the temperature observable) that the conventions share. The canonical
`lineIntensity` is **unchanged**; everything here is a sibling that reduces to it (pure
`log`/`ring`, no new axioms).

* `lineIntensityEnergy` — the energy forward map `I = (h c /(4π λ_k)) · A_k · n_k · Fgeo`, with an
  **explicit per-line wavelength** `λ : ι → ℝ` and a λ-free geometry/calibration `Fgeo`.
* `lineIntensityEnergy_eq_lineIntensity` — **reduction**: with `Fcal := h c · Fgeo /(4π λ_k)`
  (per-line) the energy map equals the canonical `lineIntensity`. Unconditional (`ring`).
* `lineIntensityEnergy_mul_lam` — the crux of the equivalence: `I · λ_k` equals `lineIntensity`
  with the **λ-free** calibration `h c · Fgeo / 4π`. Multiplying the energy intensity by its own
  wavelength cancels the `1/λ_k` photon-energy factor, recovering the photon-rate map.
* `boltzmann_plot_intensity_wavelength` — the **wavelength-form** Boltzmann plot
  `log(I·λ_k/(g_k A_k))` is affine in `E_k` with the **same** slope `-1/(k_B T)` and a
  λ-independent intercept `log(h c · Fgeo · N /(4π U))` — the energy form used by the companion
  numerical pipeline.
* `temperature_from_two_lines_wavelength` — the wavelength-form two-line slope recovers
  `1/(k_B T)` exactly, identically to `temperature_from_two_lines`; `h c`, `Fgeo`, `λ`, `N`, `U`,
  `g`, `A` all cancel. The two conventions agree on the recovered temperature.

All quantities are real.

## Literature

The wavelength (energy) ordinate `ln(I·λ/(g A))` vs `E` with slope `−1/(k_B T)` is the
literature-standard Saha–Boltzmann form: Aragón, C.; Aguilera, J. A. "Characterization of
laser induced plasmas by optical emission spectroscopy: A review of experiments and methods."
*Spectrochim. Acta B* **63** (2008) 893–916; and Thouin, J.; Benmouffok, M.; Freton, P.;
Gonzalez, J.-J. "Interpretation of temperature measurements by the Boltzmann plot method on
spatially integrated plasma oxygen spectral lines." *EPJ Appl. Phys.* **98** (2023) 65 (art.
ap230072), which uses the wavelength Boltzmann ordinate `ln(J·λ/(A g)) = const − E/(kT)` with the
`λ` multiplying `J` precisely to cancel the `1/λ` photon-energy factor. The photon-rate /
calibration-absorbed form `ln(I/(g A))` (λ folded into the lumped factor `F`) is the original
Ciucci, A. et al. "New Procedure for Quantitative Elemental Analysis by Laser-Induced Plasma
Spectroscopy." *Appl. Spectrosc.* **53** (1999) 960–964, and the review Tognoni, E. et al.
*Spectrochim. Acta B* **65** (2010) 1–14 (`I_ij = F · n_i · A_ij`). This module proves the two
share the same Boltzmann-plot slope `−1/(k_B T)` (the intercepts coincide once
`Fcal = h c · Fgeo / 4π`), so they recover the same temperature once the per-line `λ` is placed
consistently.
-/

namespace CflibsFormal

open Finset Real
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- **Energy-intensity forward map.** The integrated *energy/radiance* line intensity with the
per-line photon-energy factor made EXPLICIT:
  `I_{ki} = (h c /(4π λ_k)) · A_k · n_k · Fgeo`,
where `λ : ι → ℝ` is the **per-line** transition wavelength, `Fgeo` is the λ-free
geometry/efficiency calibration, and `n_k = population kB T N g E k` is reused verbatim from
`Boltzmann.lean`. The `h c /(4π λ_k)` is the per-photon energy `hc/λ` over the `4π` solid angle —
the term a *scalar* `Fcal` cannot carry. Reduces to `ForwardMap.lineIntensity` (below). -/
noncomputable def lineIntensityEnergy (hc fourPi kB T N Fgeo : ℝ) (g E A lam : ι → ℝ) (k : ι) :
    ℝ :=
  (hc / (fourPi * lam k)) * A k * population kB T N g E k * Fgeo

/-- **Positivity of the energy observable.** Positive given positive `hc`, `4π`, wavelength,
Einstein coefficient, density, degeneracies, and geometry. Mirrors `lineIntensity_pos`; the
precondition for `Real.log` in the wavelength Boltzmann plot. -/
theorem lineIntensityEnergy_pos [Nonempty ι] {hc fourPi kB T N Fgeo : ℝ} {g E A lam : ι → ℝ}
    (hg : ∀ k, 0 < g k) (hN : 0 < N) (hhc : 0 < hc) (hfp : 0 < fourPi) (hFgeo : 0 < Fgeo)
    (hA : ∀ k, 0 < A k) (hlam : ∀ k, 0 < lam k) (k : ι) :
    0 < lineIntensityEnergy hc fourPi kB T N Fgeo g E A lam k := by
  unfold lineIntensityEnergy population
  exact mul_pos (mul_pos (mul_pos (div_pos hhc (mul_pos hfp (hlam k))) (hA k))
    (div_pos (mul_pos (mul_pos hN (hg k)) (boltzmannFactor_pos _ _ _))
      (partitionFunction_pos hg))) hFgeo

/-- **Reduction to the canonical map.** With the **per-line** calibration
`Fcal := h c · Fgeo /(4π λ_k)` the energy forward map equals `ForwardMap.lineIntensity`. This is
WHY the spec's `Fcal`-absorbed convention is not "missing λ": the per-line `λ_k` lives inside
`Fcal` exactly. An unconditional algebraic identity (`ring`) — no positivity needed. -/
theorem lineIntensityEnergy_eq_lineIntensity (hc fourPi kB T N Fgeo : ℝ) (g E A lam : ι → ℝ)
    (k : ι) :
    lineIntensityEnergy hc fourPi kB T N Fgeo g E A lam k
      = lineIntensity kB T N (hc * Fgeo / (fourPi * lam k)) g E A k := by
  unfold lineIntensityEnergy lineIntensity
  ring

/-- **The wavelength factor cancels the photon-energy factor.** `I · λ_k` equals
`ForwardMap.lineIntensity` with the **λ-free** calibration `Fcal := h c · Fgeo / 4π`: multiplying
the measured energy intensity by its own wavelength removes the per-line `1/λ_k`, recovering the
photon-rate map. This is the crux of why `ln(I·λ/(g A))` (energy) and `ln(I/(g A))` (photon-rate)
are the same Boltzmann plot. Needs only `λ_k ≠ 0`. -/
theorem lineIntensityEnergy_mul_lam {hc fourPi kB T N Fgeo : ℝ} {g E A lam : ι → ℝ}
    (k : ι) (hlam : lam k ≠ 0) :
    lineIntensityEnergy hc fourPi kB T N Fgeo g E A lam k * lam k
      = lineIntensity kB T N (hc * Fgeo / fourPi) g E A k := by
  unfold lineIntensityEnergy lineIntensity
  field_simp

/-- **Wavelength-form Boltzmann plot.** `log(I·λ_k/(g_k A_k))` is affine in the upper-level energy
`E_k` with slope `-1/(k_B T)` and intercept `log(h c · Fgeo · N /(4π U(T)))`. The explicit `λ_k`
cancels the `1/λ_k` photon-energy factor, so the intercept is λ-INDEPENDENT and the slope is
identical to the reduced `boltzmann_plot_intensity`. This is the energy ordinate of the companion
numerical pipeline (`y = ln(I·λ/(g·A))`); its slope `-1/(k_B T)` is identical to the reduced
`boltzmann_plot_intensity` (the intercepts coincide when `Fcal = h c · Fgeo / 4π`). -/
theorem boltzmann_plot_intensity_wavelength [Nonempty ι] {hc fourPi kB T N Fgeo : ℝ}
    {g E A lam : ι → ℝ} (hg : ∀ k, 0 < g k) (hN : 0 < N) (hhc : 0 < hc) (hfp : 0 < fourPi)
    (hFgeo : 0 < Fgeo) (hA : ∀ k, 0 < A k) (hlam : ∀ k, 0 < lam k) (k : ι) :
    Real.log (lineIntensityEnergy hc fourPi kB T N Fgeo g E A lam k * lam k / (g k * A k))
      = Real.log (hc * Fgeo * N / (fourPi * partitionFunction kB T g E)) - E k / (kB * T) := by
  have hU : 0 < partitionFunction kB T g E := partitionFunction_pos hg
  have hgk : g k ≠ 0 := (hg k).ne'
  have hAne : A k ≠ 0 := (hA k).ne'
  have hlamne : lam k ≠ 0 := (hlam k).ne'
  have hfpne : fourPi ≠ 0 := hfp.ne'
  have hUne : partitionFunction kB T g E ≠ 0 := hU.ne'
  have hfac : 0 < hc * Fgeo * N / (fourPi * partitionFunction kB T g E) :=
    div_pos (by positivity) (mul_pos hfp hU)
  have hsplit : lineIntensityEnergy hc fourPi kB T N Fgeo g E A lam k * lam k / (g k * A k)
      = (hc * Fgeo * N / (fourPi * partitionFunction kB T g E)) * Real.exp (-E k / (kB * T)) := by
    simp only [lineIntensityEnergy, population, boltzmannFactor]
    field_simp
  rw [hsplit, Real.log_mul hfac.ne' (Real.exp_ne_zero _), Real.log_exp]
  ring

/-- **Temperature from two lines, wavelength form.** The slope of the wavelength-form Boltzmann
plot `log(I·λ/(g A))` between any two distinct-energy lines recovers `1/(k_B T)` exactly — `h c`,
`Fgeo`, `λ`, `N`, `U`, `g`, `A` all cancel. Identical conclusion to `temperature_from_two_lines`:
the energy and photon-rate conventions agree on the recovered temperature. -/
theorem temperature_from_two_lines_wavelength [Nonempty ι] {hc fourPi kB T N Fgeo : ℝ}
    {g E A lam : ι → ℝ} (hg : ∀ k, 0 < g k) (hN : 0 < N) (hhc : 0 < hc) (hfp : 0 < fourPi)
    (hFgeo : 0 < Fgeo) (hA : ∀ k, 0 < A k) (hlam : ∀ k, 0 < lam k) (i j : ι) (hE : E i ≠ E j) :
    (Real.log (lineIntensityEnergy hc fourPi kB T N Fgeo g E A lam j * lam j / (g j * A j))
        - Real.log (lineIntensityEnergy hc fourPi kB T N Fgeo g E A lam i * lam i / (g i * A i)))
        / (E i - E j)
      = 1 / (kB * T) := by
  have hEij : E i - E j ≠ 0 := sub_ne_zero.mpr hE
  rw [boltzmann_plot_intensity_wavelength hg hN hhc hfp hFgeo hA hlam i,
    boltzmann_plot_intensity_wavelength hg hN hhc hfp hFgeo hA hlam j]
  field_simp
  ring

end CflibsFormal
