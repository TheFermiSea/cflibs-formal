/-
Copyright (c) 2026 Brian Squires. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Squires
-/
import Mathlib

/-!
# CF-LIBS formalization — a dimensional-analysis layer

The verified spec is deliberately **dimensionless** (bare `ℝ`; units are human discipline — see
`CONTEXT.md` design decision #1), because the inverse-problem theorems (soundness,
identifiability, error bounds) are dimensionally trivial and a unit-carrying type would obstruct
`field_simp`/`ring`/`log`/`exp`. This module **adds** a lightweight, *additive* dimensional layer
— it does not touch the dimensionless core — that machine-checks the **dimensional homogeneity**
of the forward physical relations the spec rests on. Cued by physlib's `Units`/`Dimension` and
Lean4PHYS's unit systems, without taking either as a dependency (see
`docs/upstream-physlib-plan.md`).

A `Dimension` is a vector of **rational** exponents over the SI base dimensions CF-LIBS needs —
length `L`, mass `M`, time, temperature `Θ` — rational so the Saha `(·)^{3/2}` is representable.
Dimensions form an abelian group under multiplication (exponents add); `qpow` is the rational
power. We then assign dimensions to the spec's quantities and prove:

* `boltzmann_arg_dimensionless` — the Boltzmann-factor argument `E/(k_B T)` is dimensionless, so
  `exp(−E/(k_B T))` and the partition function `U = Σ gₖ exp(…)` are dimensionless;
* `thermalBracket_dim` — the de-Broglie bracket `2π m_e k_B T / h²` has dimension `L⁻²`;
* `sahaFactor_dim` — hence `(bracket)^{3/2}` (the only dimensionful part of the Saha factor) has
  dimension `L⁻³` = number density;
* `sahaLaw_homogeneous` — both sides of the Saha law `n_{z+1} n_e / n_z = S(T)` have dimension of
  number density.
-/

namespace CflibsFormal

/-- A physical dimension as exponents over the SI base dimensions used by CF-LIBS: length `L`,
mass `M`, time, temperature `Θ`. Rational exponents so half-integer powers (the Saha factor's
`(·)^{3/2}`) are representable. (Amount/charge are omitted — the CF-LIBS forward physics needs
only `L, M, time, Θ`.) -/
@[ext]
structure Dimension where
  /-- Exponent of length `L`. -/
  length : ℚ
  /-- Exponent of mass `M`. -/
  mass : ℚ
  /-- Exponent of time. -/
  time : ℚ
  /-- Exponent of temperature `Θ`. -/
  temperature : ℚ
  deriving DecidableEq

namespace Dimension

/-! ## A. The dimension algebra (abelian group under multiplication) -/

/-- The dimensionless dimension (all exponents zero) — the multiplicative identity. -/
def one : Dimension := ⟨0, 0, 0, 0⟩

/-- Product of dimensions: exponents add. -/
def mul (a b : Dimension) : Dimension :=
  ⟨a.length + b.length, a.mass + b.mass, a.time + b.time, a.temperature + b.temperature⟩

/-- Inverse dimension: exponents negate. -/
def inv (a : Dimension) : Dimension :=
  ⟨-a.length, -a.mass, -a.time, -a.temperature⟩

/-- Quotient of dimensions: `a / b = a · b⁻¹`. -/
def div (a b : Dimension) : Dimension := mul a (inv b)

/-- Rational power of a dimension: exponents scale by `q`. -/
def qpow (a : Dimension) (q : ℚ) : Dimension :=
  ⟨q * a.length, q * a.mass, q * a.time, q * a.temperature⟩

/-! ## A.1. Base and derived dimensions -/

/-- Length `L`. -/
def lengthDim : Dimension := ⟨1, 0, 0, 0⟩
/-- Mass `M`. -/
def massDim : Dimension := ⟨0, 1, 0, 0⟩
/-- Time. -/
def timeDim : Dimension := ⟨0, 0, 1, 0⟩
/-- Temperature `Θ`. -/
def tempDim : Dimension := ⟨0, 0, 0, 1⟩

/-- Energy `M L² time⁻²`. -/
def energy : Dimension := ⟨2, 1, -2, 0⟩
/-- Number density `L⁻³`. -/
def numberDensity : Dimension := ⟨-3, 0, 0, 0⟩
/-- Boltzmann constant `k_B` = energy / temperature. -/
def boltzmannConstant : Dimension := ⟨2, 1, -2, -1⟩
/-- Planck constant `h` (action) = energy · time = `M L² time⁻¹`. -/
def planckConstant : Dimension := ⟨2, 1, -1, 0⟩
/-- Einstein spontaneous-emission coefficient `A` (a rate) = `time⁻¹`. -/
def einsteinA : Dimension := ⟨0, 0, -1, 0⟩

/-! ## A.2. Sanity checks on the derived dimensions -/

/-- Energy is `M·L²·time⁻²`. -/
theorem energy_eq : energy = div (mul massDim (qpow lengthDim 2)) (qpow timeDim 2) := by
  unfold energy div mul inv qpow massDim lengthDim timeDim; ext <;> norm_num

/-- The Boltzmann constant is energy per temperature. -/
theorem boltzmannConstant_eq : boltzmannConstant = div energy tempDim := by
  unfold boltzmannConstant div mul inv energy tempDim; ext <;> norm_num

/-- The Planck constant has the dimension of action, energy·time. -/
theorem planckConstant_eq : planckConstant = mul energy timeDim := by
  unfold planckConstant mul energy timeDim; ext <;> norm_num

/-! ## B. Dimensional homogeneity of the CF-LIBS forward relations -/

/-- **The Boltzmann-factor argument is dimensionless.** `E/(k_B T)` has no dimension, so
`exp(−E/(k_B T))` (and hence the partition function `U = Σ gₖ exp(−Eₖ/(k_B T))` with dimensionless
degeneracies `gₖ`) is dimensionless. This is the dimensional precondition for `Boltzmann.lean`. -/
theorem boltzmann_arg_dimensionless : div energy (mul boltzmannConstant tempDim) = one := by
  unfold div mul inv energy boltzmannConstant tempDim one; ext <;> norm_num

/-- **The thermal-de-Broglie bracket has dimension `L⁻²`.** `2π m_e k_B T / h²` (the `2π` is
dimensionless) carries dimension inverse-length-squared — matching `Saha.thermalBracket`. -/
theorem thermalBracket_dim :
    div (mul (mul massDim boltzmannConstant) tempDim) (qpow planckConstant 2)
      = qpow lengthDim (-2) := by
  unfold div mul inv qpow massDim boltzmannConstant tempDim planckConstant lengthDim
  ext <;> norm_num

/-- **The Saha factor has dimension of number density.** Its only dimensionful part is
`(bracket)^{3/2}`: with `bracket` of dimension `L⁻²`, the `3/2` power gives `L⁻³` = number
density. (The leading `2`, the partition-function ratio, and `exp(−χ/(k_B T))` are all
dimensionless.) Matches `Saha.sahaFactor`. -/
theorem sahaFactor_dim :
    qpow (div (mul (mul massDim boltzmannConstant) tempDim) (qpow planckConstant 2)) (3 / 2)
      = numberDensity := by
  unfold div mul inv qpow massDim boltzmannConstant tempDim planckConstant numberDensity
  ext <;> norm_num

/-- **The Saha law is dimensionally homogeneous.** Both sides of `n_{z+1} n_e / n_z = S(T)` carry
dimension of number density: the left side is `(L⁻³·L⁻³)/L⁻³ = L⁻³`, and the right side
`S(T) = L⁻³` by `sahaFactor_dim`. So `electronDensityFromRatio = S/R` is dimensionally consistent
(`R = n_{z+1}/n_z` is dimensionless). -/
theorem sahaLaw_homogeneous :
    div (mul numberDensity numberDensity) numberDensity = numberDensity := by
  unfold div mul inv numberDensity; ext <;> norm_num

end Dimension

end CflibsFormal
