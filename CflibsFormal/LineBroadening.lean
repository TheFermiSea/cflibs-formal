/-
Copyright (c) 2026 Brian Squires. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Squires
-/
import Mathlib

/-!
# CF-LIBS formalization — line broadening (Doppler width + the Voigt Gaussian budget)

A first step in relaxing the integrated-intensity idealization toward real **line profiles**. The
forward map `ForwardMap.lineIntensity` and the Stark diagnostic `StarkBroadening.starkDensity`
treat the line as a point / a known width; a measured LIBS line is a **Voigt** profile — the
convolution of a **Gaussian** part (thermal Doppler + instrument) and a **Lorentzian** part
(Stark + natural). This module formalizes the two pieces that are *exact* and that the electron-
density diagnostic depends on:

* **Thermal Doppler width** — the Gaussian FWHM from the Maxwell–Boltzmann velocity distribution,
  `Δλ_D = λ₀·√(8·ln2·k_B·T / (m·c²))`: positive, strictly increasing in `T`, and invertible
  (a measured Doppler width recovers `T`).
* **Gaussian quadrature** — Gaussian profiles convolve to a Gaussian whose **variance adds**, so
  FWHMs combine as `w = √(w₁² + w₂²)`; the inverse, `deconvolveGaussian`, removes a known Gaussian
  component exactly. This is how the instrument and Doppler contributions are stripped to expose
  the Stark Lorentzian fed to `StarkBroadening.starkDensity` (cf. the companion pipeline's
  `deconvolve_stark_fwhm`).

Honesty: the Gaussian-quadrature law is **exact** for Gaussian⊗Gaussian convolution (asserted here
as the operational width rule, the standard consequence of `gaussian ⋆ gaussian = gaussian`).
Using it to extract the Stark **Lorentzian** from a Voigt is the standard *approximation* — exact
only in the Gaussian-dominated limit; the full Voigt FWHM combination (Olivero–Longbothum) is not
a simple quadrature and is out of scope here.

## Literature

Thermal Doppler broadening (Maxwell–Boltzmann): Griem, H. R. *Principles of Plasma Spectroscopy*
(Cambridge, 1997); Demtröder, *Laser Spectroscopy*. Voigt = Gaussian ⊗ Lorentzian and the
instrument/Doppler quadrature: Olivero, J. J.; Longbothum, R. L. "Empirical fits to the Voigt line
width." *J. Quant. Spectrosc. Radiat. Transfer* **17** (1977) 233–236. The Stark-width extraction
by Gaussian deconvolution is standard LIBS practice (Aragón & Aguilera, *Spectrochim. Acta B*
**63** (2008) 893).
-/

namespace CflibsFormal

open Real

/-! ## A. Thermal Doppler broadening -/

/-- **Thermal Doppler FWHM.** The Gaussian line width from the Maxwell–Boltzmann velocity
distribution of emitters of mass `m` at temperature `T`:
`Δλ_D = λ₀·√(8·ln2·k_B·T / (m·c²))`. -/
noncomputable def dopplerFWHM (lam kB T m c : ℝ) : ℝ :=
  lam * Real.sqrt (8 * Real.log 2 * kB * T / (m * c ^ 2))

/-- **Recovered temperature from a Doppler width** (the inverse of `dopplerFWHM`):
`T = (Δλ_D / λ₀)² · m·c² / (8·ln2·k_B)`. -/
noncomputable def temperatureFromDoppler (lam kB wD m c : ℝ) : ℝ :=
  wD ^ 2 * (m * c ^ 2) / (lam ^ 2 * (8 * Real.log 2 * kB))

/-- The Doppler width is strictly positive for positive wavelength, constants, and temperature. -/
lemma dopplerFWHM_pos {lam kB T m c : ℝ}
    (hlam : 0 < lam) (hkB : 0 < kB) (hT : 0 < T) (hm : 0 < m) (hc : 0 < c) :
    0 < dopplerFWHM lam kB T m c := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold dopplerFWHM
  have harg : 0 < 8 * Real.log 2 * kB * T / (m * c ^ 2) := by positivity
  exact mul_pos hlam (Real.sqrt_pos.mpr harg)

/-- **Doppler width is a thermometer (monotone).** At fixed wavelength, mass, and constants, the
thermal Doppler FWHM is strictly increasing in temperature — hotter plasma, wider line. -/
theorem dopplerFWHM_strictMono_T {lam kB m c : ℝ}
    (hlam : 0 < lam) (hkB : 0 < kB) (hm : 0 < m) (hc : 0 < c) {T₁ T₂ : ℝ}
    (hT₁ : 0 < T₁) (hT : T₁ < T₂) :
    dopplerFWHM lam kB T₁ m c < dopplerFWHM lam kB T₂ m c := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold dopplerFWHM
  have hpos : 0 ≤ 8 * Real.log 2 * kB * T₁ / (m * c ^ 2) := by positivity
  have hlt : 8 * Real.log 2 * kB * T₁ / (m * c ^ 2)
      < 8 * Real.log 2 * kB * T₂ / (m * c ^ 2) := by gcongr
  exact mul_lt_mul_of_pos_left (Real.sqrt_lt_sqrt hpos hlt) hlam

/-- **Doppler thermometry is exact.** Feeding the forward Doppler width back through the inverse
recovers the true temperature. -/
theorem doppler_recovers {lam kB T m c : ℝ}
    (hlam : 0 < lam) (hkB : 0 < kB) (hT : 0 < T) (hm : 0 < m) (hc : 0 < c) :
    temperatureFromDoppler lam kB (dopplerFWHM lam kB T m c) m c = T := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold temperatureFromDoppler dopplerFWHM
  have harg : 0 ≤ 8 * Real.log 2 * kB * T / (m * c ^ 2) := by positivity
  rw [mul_pow, Real.sq_sqrt harg]
  field_simp

/-! ## B. The Gaussian width budget (quadrature) and deconvolution -/

/-- **Gaussian widths add in quadrature.** Two Gaussian profiles convolve to a Gaussian whose
variance is the sum, so the FWHMs combine as `√(w₁² + w₂²)` — e.g. the total Gaussian width from
the instrument and the thermal Doppler contributions. -/
noncomputable def gaussQuadrature (w₁ w₂ : ℝ) : ℝ := Real.sqrt (w₁ ^ 2 + w₂ ^ 2)

/-- **Gaussian deconvolution.** Remove a known Gaussian component `wG` from a total Gaussian width
`wTot`: `√(wTot² − wG²)`. The exact inverse of `gaussQuadrature` (see
`deconvolveGaussian_quadrature`), used to strip the instrument + Doppler Gaussian from a measured
line and expose the Stark Lorentzian fed to `StarkBroadening.starkDensity`. -/
noncomputable def deconvolveGaussian (wTot wG : ℝ) : ℝ := Real.sqrt (wTot ^ 2 - wG ^ 2)

/-- Gaussian quadrature is symmetric in its two contributions. -/
lemma gaussQuadrature_comm (w₁ w₂ : ℝ) : gaussQuadrature w₁ w₂ = gaussQuadrature w₂ w₁ := by
  unfold gaussQuadrature; rw [add_comm (w₁ ^ 2) (w₂ ^ 2)]

/-- **Deconvolution exactly inverts quadrature.** Removing a Gaussian component `b` from the
combined Gaussian width `√(a²+b²)` recovers the other component `a` (for nonnegative `a`). This is
the exactness of the instrument/Doppler stripping that precedes the Stark diagnostic. -/
theorem deconvolveGaussian_quadrature {a b : ℝ} (ha : 0 ≤ a) :
    deconvolveGaussian (gaussQuadrature a b) b = a := by
  unfold deconvolveGaussian gaussQuadrature
  rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ a ^ 2 + b ^ 2),
    show a ^ 2 + b ^ 2 - b ^ 2 = a ^ 2 by ring]
  exact Real.sqrt_sq ha

end CflibsFormal
