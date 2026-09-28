import Mathlib

/-!
# Queue target FT16-kernelLS-error-linfty (deep audit 2026-09-24, FT-16 item 3)

Line extraction by kernel least squares under profile misspecification: a row-diagonal-dominance
margin of the Gram matrix turns a bound on the misspecification-plus-noise residual into an
entrywise (ℓ∞) bound on the extracted intensities. Statement file for the proof queue: one target
theorem, one `sorry`.
-/

open Finset Matrix

namespace Plan.FT16

variable {P L : Type*} [Fintype P] [Fintype L] [DecidableEq L]

/-- **ℓ∞ error of kernel least-squares line extraction under a misspecified profile kernel.**
Pixels `P`, lines `L`. The data are `d = K_t·I + η` (true kernel `Kt`, true line intensities
`I`, noise `η`); the extractor uses an assumed kernel `K` and returns any `Î` solving the normal
equations `KᵀK·Î = Kᵀ·d` (`hnormal`). If the Gram matrix `KᵀK` is strictly row-diagonally
dominant with margin `δ > 0` (`hdom`), then every extracted intensity satisfies
  `|Î_l − I_l| ≤ max_k |(Kᵀ((K_t − K)·I + η))_k| / δ`.
Reason: `KᵀK·(Î − I) = Kᵀ((K_t − K)·I + η)` exactly, and for a row-diagonally dominant `M` with
margin `δ`, `δ·‖x‖∞ ≤ ‖M·x‖∞` (take the row of a maximal `|x_i|`). Not vacuous: with `K_t = K`
and `η = 0` the right side is `0` and the extraction is exact.

Honest reading: the numerator is an **assumed** input (a bound on the profile misspecification
`K_t − K` acting on `I`, plus a noise bound); only the margin `δ` of `hdom` is checkable at runtime
from the extractor's own kernel. `hdom` also makes `KᵀK` invertible, so `Î` is unique, but the
theorem does not need that. Hypotheses: `hδ` (a strict margin; the division by `δ` needs
`δ > 0`); `hdom` (the checkable margin condition); `hnormal` (what the extractor computes);
`[Nonempty L]` (the maximum over lines is over a nonempty set); `[DecidableEq L]` (for
`univ.erase`).

Scope (two-axis): relation PURE-MATH (abstract real matrices); no physics definitions are used;
published PURE-MATH. The physics reading (optically thin, additive line profiles, kernel fixed per
solver step) is REDUCED and stays in prose. Citation pending citation-integrity (the classical
diagonal-dominance bound is not on the whitelist; do not cite it until it is). -/
theorem kernelLS_error_linfty [Nonempty L] (K Kt : Matrix P L ℝ) (I Ihat : L → ℝ) (η : P → ℝ)
    {δ : ℝ} (hδ : 0 < δ)
    (hdom : ∀ k, δ + ∑ j ∈ univ.erase k, |(Kᵀ * K) k j| ≤ |(Kᵀ * K) k k|)
    (hnormal : (Kᵀ * K).mulVec Ihat = Kᵀ.mulVec (Kt.mulVec I + η)) (l : L) :
    |Ihat l - I l|
      ≤ (univ.sup' univ_nonempty fun k => |(Kᵀ.mulVec ((Kt - K).mulVec I + η)) k|) / δ := by
  sorry

end Plan.FT16
