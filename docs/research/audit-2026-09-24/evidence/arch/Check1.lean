import CflibsFormal.OLS
import CflibsFormal.Analysis
import CflibsFormal.EquivalentWidth
import CflibsFormal.LadenburgReiche
import CflibsFormal.Closure
import CflibsFormal.Aitchison
open Finset

-- 1. OLS.sq_mul_sq_sub_sq_sum_nonneg is a one-liner from mathlib Cauchy-Schwarz
example {ι : Type*} [Fintype ι] (a b : ι → ℝ) :
    0 ≤ (∑ k, a k ^ 2) * (∑ k, b k ^ 2) - (∑ k, a k * b k) ^ 2 :=
  sub_nonneg.mpr (Finset.sum_mul_sq_le_sq_mul_sq univ a b)

-- 2. ErrorBudget.recip_lip_floor is Analysis.inv_kT_sub_le up to rearrangement
example {kB m x y : ℝ} (hkB : 0 < kB) (hm : 0 < m) (hx : m ≤ x) (hy : m ≤ y) :
    |1 / (kB * x) - 1 / (kB * y)| ≤ 1 / (kB * m ^ 2) * |x - y| := by
  have := CflibsFormal.inv_kT_sub_le hkB hm hx hy
  rw [one_div_mul_eq_div]; exact this

-- 3. lorentzianG γ = mathlib cauchyPDFReal 0 γ (for γ ≥ 0), so ∫ lorentzianG γ = 1 for free
example (γ : NNReal) (x : ℝ) :
    CflibsFormal.lorentzianG γ x = ProbabilityTheory.cauchyPDFReal 0 γ x := by
  unfold CflibsFormal.lorentzianG ProbabilityTheory.cauchyPDFReal
  simp only [one_div, sub_zero]; ring

example (γ : NNReal) (hγ : γ ≠ 0) : ∫ x, CflibsFormal.lorentzianG γ x = 1 := by
  have h : (fun x => CflibsFormal.lorentzianG γ x) = ProbabilityTheory.cauchyPDFReal 0 γ := by
    funext x; unfold CflibsFormal.lorentzianG ProbabilityTheory.cauchyPDFReal
    simp only [one_div, sub_zero]; ring
  rw [h]; exact ProbabilityTheory.integral_cauchyPDFReal_eq_one 0 hγ

-- 4. Aitchison.closure is definitionally Closure.composition
example {ι : Type*} [Fintype ι] (x : ι → ℝ) : CflibsFormal.closure x = CflibsFormal.composition x := rfl
