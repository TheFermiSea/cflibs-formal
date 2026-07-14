/-
Copyright (c) 2026 Brian Squires. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Squires
-/
import Mathlib
import CflibsFormal.Aitchison

/-!
# Aitchison compositional data — a genuine isometric log-ratio (ilr) transform

`CflibsFormal.Aitchison` proves the audit-critical C3 identity (`softmax∘log = closure`,
NOT ilr) and records the *genuine* Isometric Log-Ratio transform and its isometry as an
open target: it needs an orthonormal basis of the `(D−1)`-dimensional clr-hyperplane
`{y : ∑ y = 0}` and the fact that the basis representation is a linear isometry
(Egozcue et al. 2003). This module discharges that target.

Working in `EuclideanSpace ℝ ι` (so the norm is the genuine `L²`/Euclidean norm — the
typing guard that makes the word "isometry" meaningful):

* `hyperplane` — the submodule `{y : ∑ i, y i = 0}` as `LinearMap.ker` of the
  coordinate-sum functional; `clr x` lands there (`clrE_mem`, via `Aitchison.clr_sum_zero`).
* `ilrBasis` — an arbitrarily-chosen `OrthonormalBasis` of that finite-dimensional
  hyperplane (`stdOrthonormalBasis`); its `repr` is a `LinearIsometryEquiv`
  `hyperplane ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ hyperplane))`.
* `ilr x := ilrBasis.repr ⟨clrE x, _⟩` — the ilr coordinates, in `ℝ^(finrank)` (`= ℝ^(D−1)`,
  that equality not separately proved here).
* `aitchisonDist x y := ‖clrE x − clrE y‖` — the Aitchison distance.
* `ilr_isometry` (**headline**): `‖ilr x − ilr y‖ = aitchisonDist x y` — ilr realises the
  Aitchison distance exactly, because `ilrBasis.repr` is linear and norm-preserving.
* `ilr_inner` — the companion inner-product-preservation corollary.

## Literature and scope

Scope tag: **PURE-MATH**. This is theorem-for-theorem the classical fact that the ilr
transform is an isometry from the clr-hyperplane onto Euclidean coordinate space; it
carries no physical modelling assumptions. Citation: —.

* J. J. Egozcue, V. Pawlowsky-Glahn, G. Mateu-Figueras, C. Barceló-Vidal,
  *Isometric logratio transformations for compositional data analysis*,
  Math. Geol. 35(3):279–300 (2003) — ilr `= Vᵀ clr(x)`, isometry onto `ℝ^(D−1)`.
* J. Aitchison, *The Statistical Analysis of Compositional Data*, Chapman & Hall (1986).
-/

namespace CflibsFormal

open Finset Real
open scoped BigOperators RealInnerProductSpace

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- The coordinate-sum functional `y ↦ ∑ i, y i` on `EuclideanSpace ℝ ι`, as an `ℝ`-linear
map. Built by transporting the plain sum-of-projections functional on `ι → ℝ` across the
canonical linear equivalence `EuclideanSpace ℝ ι ≃ₗ (ι → ℝ)`. -/
noncomputable def sumLin : EuclideanSpace ℝ ι →ₗ[ℝ] ℝ :=
  (∑ i, LinearMap.proj i) ∘ₗ (WithLp.linearEquiv 2 ℝ (ι → ℝ)).toLinearMap

/-- The **clr-hyperplane** `{y : EuclideanSpace ℝ ι | ∑ i, y i = 0}`, as the kernel of the
coordinate-sum functional. This is the `(D−1)`-dimensional plane on which the clr
coordinates live and on which a genuine ilr picks an orthonormal basis. -/
noncomputable def hyperplane : Submodule ℝ (EuclideanSpace ℝ ι) :=
  LinearMap.ker (sumLin (ι := ι))

/-- The clr coordinates, viewed as a point of `EuclideanSpace ℝ ι` (so norms are `L²`). -/
noncomputable def clrE (x : ι → ℝ) : EuclideanSpace ℝ ι :=
  (WithLp.linearEquiv 2 ℝ (ι → ℝ)).symm (clr x)

/-- `clr x` lands in the clr-hyperplane `∑ = 0` — this is `clr_sum_zero` transported to
`EuclideanSpace`. -/
theorem clrE_mem (x : ι → ℝ) : clrE x ∈ hyperplane (ι := ι) := by
  simp only [hyperplane, LinearMap.mem_ker, sumLin, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.sum_apply, LinearMap.proj_apply, clrE,
    LinearEquiv.coe_coe, WithLp.linearEquiv_apply]
  exact clr_sum_zero

/-- An arbitrarily-chosen orthonormal basis of the (finite-dimensional) clr-hyperplane.
Its `repr` is the `LinearIsometryEquiv` onto `ℝ^(D−1)` that defines the ilr transform. -/
noncomputable def ilrBasis :
    OrthonormalBasis (Fin (Module.finrank ℝ (hyperplane (ι := ι)))) ℝ (hyperplane (ι := ι)) :=
  stdOrthonormalBasis ℝ (hyperplane (ι := ι))

/-- The **Isometric Log-Ratio (ilr) transform**: the clr coordinates read off in the
orthonormal basis `ilrBasis` of the clr-hyperplane, a point of `EuclideanSpace ℝ (Fin r)` with
`r = finrank` of that hyperplane (this rank is `D−1`, `D = |ι|`, though `r = D−1` is not separately
proved here). The map is *total* on `ι → ℝ`, but is compositionally meaningful only on **positive**
inputs (a composition after closure), since `clr` uses `Real.log`; the isometry below holds for the
`clr` images whatever the inputs. Egozcue et al. 2003. -/
noncomputable def ilr (x : ι → ℝ) :
    EuclideanSpace ℝ (Fin (Module.finrank ℝ (hyperplane (ι := ι)))) :=
  (ilrBasis (ι := ι)).repr ⟨clrE x, clrE_mem x⟩

/-- The **Aitchison distance** `d_A(x, y) = ‖clr x − clr y‖` in the `L²` norm. -/
noncomputable def aitchisonDist (x y : ι → ℝ) : ℝ :=
  ‖clrE x - clrE y‖

/-- **The ilr isometry (headline).** The ilr transform realises the Aitchison distance
exactly: `‖ilr x − ilr y‖ = d_A(x, y)`. The crux is that `ilrBasis.repr` is a linear
isometry, so `ilr x − ilr y = ilrBasis.repr (⟨clr x,_⟩ − ⟨clr y,_⟩)` and its norm equals
the norm of `⟨clr x,_⟩ − ⟨clr y,_⟩`, which is `‖clr x − clr y‖`. Egozcue et al. 2003. -/
theorem ilr_isometry (x y : ι → ℝ) :
    ‖ilr x - ilr y‖ = aitchisonDist x y := by
  simp only [ilr]
  rw [← LinearIsometryEquiv.map_sub, LinearIsometryEquiv.norm_map, aitchisonDist,
    Submodule.coe_norm, AddSubgroupClass.coe_sub]

/-- **ilr preserves inner products (companion corollary).** Since `ilrBasis.repr` is a
linear isometry it preserves the inner product: `⟪ilr x, ilr y⟫ = ⟪clr x, clr y⟫`. -/
theorem ilr_inner (x y : ι → ℝ) :
    ⟪ilr x, ilr y⟫ = ⟪clrE x, clrE y⟫ := by
  simp only [ilr]
  rw [LinearIsometryEquiv.inner_map_map, Submodule.coe_inner]

/-! ### Non-vacuity witnesses (concrete data, `D = 3`, `x = (1, 2, 4)` positive) -/

/-- The ilr transform is well-defined on the concrete positive datum `(1, 2, 4)` and the
isometry identity fires there against the neutral composition `(1, 1, 1)`. -/
example :
    ‖ilr (![1, 2, 4] : Fin 3 → ℝ) - ilr ![1, 1, 1]‖
      = aitchisonDist (![1, 2, 4] : Fin 3 → ℝ) ![1, 1, 1] :=
  ilr_isometry _ _

/-- **Non-triviality (shared).** `(1, 2, 4)` and the neutral `(1, 1, 1)` have distinct clr
coordinates, so their Aitchison distance is nonzero — ruling out a vacuous "isometry between
zero-distance points". Backs the two non-vacuity witnesses below. -/
private lemma aitchisonDist_neutral_ne_zero :
    aitchisonDist (![1, 2, 4] : Fin 3 → ℝ) ![1, 1, 1] ≠ 0 := by
  rw [aitchisonDist, ne_eq, norm_eq_zero, sub_eq_zero]
  intro h
  have hclr : clr (![1, 2, 4] : Fin 3 → ℝ) = clr ![1, 1, 1] :=
    (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).symm.injective h
  have h0 := congrFun hclr 0
  simp only [clr, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Fintype.card_fin, Real.log_one] at h0
  -- h0 forces `log 2 + log 4 = 0`, impossible since both logs are positive.
  have hpos : (0 : ℝ) < Real.log 2 + Real.log 4 :=
    add_pos (Real.log_pos (by norm_num)) (Real.log_pos (by norm_num))
  nlinarith [h0, hpos]

/-- **Non-triviality.** The Aitchison distance between `(1, 2, 4)` and the neutral `(1, 1, 1)`
is nonzero (so the isometry is not between zero-distance points). -/
example : aitchisonDist (![1, 2, 4] : Fin 3 → ℝ) ![1, 1, 1] ≠ 0 :=
  aitchisonDist_neutral_ne_zero

/-- The isometry combined with non-triviality: `‖ilr x − ilr y‖ ≠ 0` for `x = (1,2,4)`,
`y = (1,1,1)` — the ilr images are genuinely distinct. -/
example : ‖ilr (![1, 2, 4] : Fin 3 → ℝ) - ilr ![1, 1, 1]‖ ≠ 0 := by
  rw [ilr_isometry]; exact aitchisonDist_neutral_ne_zero

end CflibsFormal
