import CflibsFormal

/-!
Statement sketches for the frontier-theorem slate (frontier-proposer, 2026-09-23).
All statements except gaussSeidel_det_trace and sahaConsistency_trivial_of_sbOffset are
`sorry`-proved; the point of this file is that each sketch elaborates against the real repo
definitions at lean-main fb1681d.
-/

open Finset Real MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators

namespace Slate
open CflibsFormal

/-! ## FT-01 outer-iteration fixed point / stop certificate -/
namespace FT01

/-- Krasnoselskii–Mann damped map, `λ = 1/2` in the pipeline (iterative.py:2454/2531). -/
def dampedMap (lam : ℝ) (g : ℝ → ℝ) (u : ℝ) : ℝ := (1 - lam) * u + lam * g u

/-- Exact affine error recursion. -/
theorem dampedAffine_iterate (lam g c u0 : ℝ) (hg : g ≠ 1) (n : ℕ) :
    (dampedMap lam (fun u => g * u + c))^[n] u0 - c / (1 - g)
      = (1 - lam + lam * g) ^ n * (u0 - c / (1 - g)) := by sorry

/-- Exact convergence window for the affine reduced map. -/
theorem dampedAffine_tendsto_iff (lam g c : ℝ) (hlam : 0 < lam) (hg : g ≠ 1) :
    (∀ u0, Tendsto (fun n => (dampedMap lam (fun u => g * u + c))^[n] u0) atTop
        (𝓝 (c / (1 - g)))) ↔ (1 - 2 / lam < g ∧ g < 1) := by sorry

/-- Nonlinear version: derivative window on an invariant box. -/
theorem dampedMap_contracts {g g' : ℝ → ℝ} {a b m M lam : ℝ} (hlam0 : 0 < lam)
    (hlam1 : lam ≤ 1) (hd : ∀ T ∈ Set.Icc a b, HasDerivAt g (g' T) T)
    (hmM : ∀ T ∈ Set.Icc a b, m ≤ g' T ∧ g' T ≤ M) (hlo : 1 - 2 / lam < m) (hhi : M < 1)
    (hmaps : Set.MapsTo (dampedMap lam g) (Set.Icc a b) (Set.Icc a b)) (hab : a ≤ b) :
    ∃ Tstar ∈ Set.Icc a b, dampedMap lam g Tstar = Tstar ∧
      ∀ T0 ∈ Set.Icc a b,
        Tendsto (fun n => (dampedMap lam g)^[n] T0) atTop (𝓝 Tstar) := by sorry

/-- A positive-feedback fixed point (`g' > 1`) repels for every damping. -/
theorem dampedMap_repelling {g : ℝ → ℝ} {d Tstar lam : ℝ} (hfix : g Tstar = Tstar)
    (hd : HasDerivAt g d Tstar) (hd1 : 1 < d) (hlam : 0 < lam) :
    ∃ ε > 0, ∀ T, 0 < |T - Tstar| → |T - Tstar| < ε →
      |T - Tstar| < |dampedMap lam g T - Tstar| := by sorry

/-- A-posteriori residual stop rule (Banach). -/
theorem residual_stop {Φ : ℝ → ℝ} {s : Set ℝ} {q u ustar : ℝ} (hq : q < 1)
    (hLip : ∀ x ∈ s, ∀ y ∈ s, |Φ x - Φ y| ≤ q * |x - y|) (hu : u ∈ s) (hs : ustar ∈ s)
    (hfix : Φ ustar = ustar) : |u - ustar| ≤ |Φ u - u| / (1 - q) := by sorry

/-- 2×2 Schur–Cohn (Jury) criterion for a real characteristic polynomial. -/
theorem jury_two (t d : ℝ) :
    (∀ z : ℂ, z ^ 2 - (t : ℂ) * z + (d : ℂ) = 0 → ‖z‖ < 1) ↔ (|d| < 1 ∧ |t| < 1 + d) := by
  sorry

/-- Pipeline Gauss–Seidel Jacobian (R9-02 corrected evidence), `λ = 1/2`:
`1 + det − trace = (1 − g)/4` with `g = A + B·C`, so `g < 1` is exactly the monotone boundary. -/
theorem gaussSeidel_det_trace (A B C : ℝ) :
    let J : Matrix (Fin 2) (Fin 2) ℝ :=
      !![1/2 + A/2, B/2; C/2 * (1/2 + A/2), 1/2 + B*C/4]
    J.det = (1 + A) / 4 ∧ 1 + J.det - J.trace = (1 - (A + B * C)) / 4 := by
  simp [Matrix.det_fin_two, Matrix.trace_fin_two]; constructor <;> ring

/-- Unit-invariant 2×2 gate (weighted max norm). -/
theorem exists_weights_iff {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    (∃ wT wn : ℝ, 0 < wT ∧ 0 < wn ∧ max (a + b * wn / wT) (c * wT / wn + d) < 1)
      ↔ (a < 1 ∧ d < 1 ∧ b * c < (1 - a) * (1 - d)) := by sorry

end FT01

/-! ## FT-04 fixed-effects (element-dummy) Saha–Boltzmann design -/
namespace FT04
variable {ι κ : Type*} [Fintype ι] [DecidableEq κ]

noncomputable def gMean (grp : ι → κ) (w f : ι → ℝ) (e : κ) : ℝ :=
  (∑ k ∈ univ.filter (fun k => grp k = e), w k * f k) /
    ∑ k ∈ univ.filter (fun k => grp k = e), w k

noncomputable def withinCross (grp : ι → κ) (w x y : ι → ℝ) : ℝ :=
  ∑ k, w k * (x k - gMean grp w x (grp k)) * (y k - gMean grp w y (grp k))

noncomputable def withinSS (grp : ι → κ) (w x : ι → ℝ) : ℝ := withinCross grp w x x

noncomputable def feSlope (grp : ι → κ) (w x y : ι → ℝ) : ℝ :=
  withinCross grp w x y / withinSS grp w x

theorem fe_identifiable_iff (grp : ι → κ) (w x : ι → ℝ) (hw : ∀ k, 0 < w k) :
    (∀ (a a' : κ → ℝ) (β β' : ℝ),
        (∀ k, a (grp k) + β * x k = a' (grp k) + β' * x k) → β = β')
      ↔ 0 < withinSS grp w x := by sorry

/-- The within slope is affine in an offset carried by a covariate `s` (the ion indicator). -/
theorem feSlope_add_smul (grp : ι → κ) (w x y s : ι → ℝ) (c : ℝ) :
    feSlope grp w x (fun k => y k + c * s k) = feSlope grp w x y + c * feSlope grp w x s := by
  sorry

theorem feSlope_isMin (grp : ι → κ) (w x y : ι → ℝ) (hw : ∀ k, 0 < w k)
    (hSS : 0 < withinSS grp w x) (a : κ → ℝ) (β : ℝ) :
    ∑ k, w k * (y k - (gMean grp w y (grp k) - feSlope grp w x y * gMean grp w x (grp k))
        - feSlope grp w x y * x k) ^ 2
      ≤ ∑ k, w k * (y k - a (grp k) - β * x k) ^ 2 := by sorry

theorem feJoint_identifiable_iff (grp : ι → κ) (w x s : ι → ℝ) (hw : ∀ k, 0 < w k) :
    (∀ (a a' : κ → ℝ) (β β' ν ν' : ℝ),
        (∀ k, a (grp k) + β * x k + ν * s k = a' (grp k) + β' * x k + ν' * s k) →
          β = β' ∧ ν = ν')
      ↔ 0 < withinSS grp w x * withinSS grp w s - withinCross grp w x s ^ 2 := by sorry

/-- Pooled C1 passes, the production (within) design is rank-deficient (executed c1_within.py). -/
example : 0 < ∑ k : Fin 4, (![3, 3, 5, 5] k - mean ![(3 : ℝ), 3, 5, 5]) ^ 2 ∧
    withinSS (![0, 0, 1, 1] : Fin 4 → ℕ) (fun _ => 1) ![(3 : ℝ), 3, 5, 5] = 0 := by sorry

end FT04

/-! ## FT-02 IPD gauge and the implicit IPD-aware Saha inverse -/
namespace FT02
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem sahaFactor_ipd_gauge (kB T me h chi d : ℝ) (gZ EZ : ι → ℝ) (gZ1 EZ1 : κ → ℝ) :
    sahaFactor kB T me h (chi - d) gZ EZ gZ1 EZ1
      = sahaFactor kB T me h chi gZ EZ gZ1 EZ1 * Real.exp (d / (kB * T)) := by sorry

theorem ne_ipd_mismatch {kB T me h chi d R ne : ℝ} {gZ EZ : ι → ℝ} {gZ1 EZ1 : κ → ℝ}
    (hR : R ≠ 0) (hfwd : R * ne = sahaFactor kB T me h (chi - d) gZ EZ gZ1 EZ1) :
    electronDensityFromRatio kB T me h chi gZ EZ gZ1 EZ1 R = ne * Real.exp (-(d / (kB * T))) := by
  sorry

/-- Log-coordinate IPD inverse map `ℓ = log n_e`, `b·e^{ℓ/2} = Δχ(n_e)/(k_B T)` (DH form). -/
noncomputable def ipdLogMap (a b ℓ : ℝ) : ℝ := Real.log a + b * Real.exp (ℓ / 2)

theorem ipdLogMap_root_subsingleton {a b : ℝ} (hb : 0 < b) :
    {ℓ | ipdLogMap a b ℓ = ℓ ∧ b * Real.exp (ℓ / 2) < 2}.Subsingleton := by sorry

theorem ipdLogMap_contracts {a b ℓ1 q : ℝ} (hb : 0 ≤ b)
    (hq : b * Real.exp (ℓ1 / 2) / 2 ≤ q) (hq1 : q < 1)
    (hmaps : Set.MapsTo (ipdLogMap a b) (Set.Iic ℓ1) (Set.Iic ℓ1)) :
    ∃ ℓs ∈ Set.Iic ℓ1, ipdLogMap a b ℓs = ℓs ∧
      (∀ ℓ ∈ Set.Iic ℓ1, ipdLogMap a b ℓ = ℓ → ℓ = ℓs) ∧
      ∀ ℓ0 ∈ Set.Iic ℓ1, Tendsto (fun n => (ipdLogMap a b)^[n] ℓ0) atTop (𝓝 ℓs) := by sorry

end FT02

/-! ## FT-05 partition-function truncation / cutoff policy -/
namespace FT05
variable {ι : Type*} [Fintype ι]

noncomputable def partitionFunctionCut (kB T cut : ℝ) (g E : ι → ℝ) : ℝ :=
  ∑ k ∈ univ.filter (fun k => E k < cut), g k * boltzmannFactor kB T (E k)

theorem partitionFunction_sub_cut_bounds {kB T cut : ℝ} {g E : ι → ℝ} (hg : ∀ k, 0 ≤ g k)
    (hkT : 0 < kB * T) :
    0 ≤ partitionFunction kB T g E - partitionFunctionCut kB T cut g E ∧
      partitionFunction kB T g E - partitionFunctionCut kB T cut g E
        ≤ (∑ k ∈ univ.filter (fun k => cut ≤ E k), g k) * Real.exp (-cut / (kB * T)) := by
  sorry

theorem cutRatio_strictMonoOn_temp {kB cut : ℝ} {g E : ι → ℝ} (hkB : 0 < kB)
    (hg : ∀ k, 0 < g k) (hkeep : ∃ k, E k < cut) (hdrop : ∃ k, cut ≤ E k) :
    StrictMonoOn (fun T => partitionFunction kB T g E / partitionFunctionCut kB T cut g E)
      (Set.Ioi 0) := by sorry

/-- No `T`-independent factor (e.g. a gA calibration) absorbs a cutoff-policy change. -/
theorem cutRatio_not_absorbable {kB cut : ℝ} {g E : ι → ℝ} (hkB : 0 < kB)
    (hg : ∀ k, 0 < g k) (hkeep : ∃ k, E k < cut) (hdrop : ∃ k, cut ≤ E k) (c : ℝ) :
    ¬ ∀ T ∈ Set.Ioi (0 : ℝ),
        partitionFunction kB T g E = c * partitionFunctionCut kB T cut g E := by sorry

end FT05

/-! ## FT-03 refuse-to-report (certified abstention on the PAS loss) -/
namespace FT03

/-- Gated PAS sum: answer iff the certified upper bound is `≤ λ`. -/
noncomputable def pasGated {N : ℕ} (l U : Fin N → ℝ) (lam : ℝ) : ℝ :=
  ∑ i, if U i ≤ lam then l i else lam

theorem pas_certified_le_lambda {N : ℕ} (l U : Fin N → ℝ) (lam : ℝ) (hU : ∀ i, l i ≤ U i) :
    pasGated l U lam ≤ N * lam := by sorry

theorem pas_interval_regret {N : ℕ} (l L U : Fin N → ℝ) (lam : ℝ) (hL : ∀ i, L i ≤ l i)
    (hU : ∀ i, l i ≤ U i) :
    pasGated l U lam - ∑ i, min (l i) lam
      ≤ ∑ i, (if L i ≤ lam ∧ lam < U i then U i - L i else 0) := by sorry

theorem pas_gate_value_nonneg {N : ℕ} (l L : Fin N → ℝ) (lam : ℝ) (hL : ∀ i, L i ≤ l i) :
    (∑ i, if lam < L i then lam else l i) ≤ ∑ i, l i := by sorry

/-- TS-01 as a theorem: on the sb_offset route the Saha-consistency residual is identically 0. -/
theorem sahaConsistency_trivial_of_sbOffset {ι κ : Type*} [Fintype ι] [Fintype κ]
    {kB T me h chi Rhat : ℝ} {gZ EZ : ι → ℝ} {gZ1 EZ1 : κ → ℝ} (hR : Rhat ≠ 0) :
    Rhat * electronDensityFromRatio kB T me h chi gZ EZ gZ1 EZ1 Rhat
      = sahaFactor kB T me h chi gZ EZ gZ1 EZ1 := by
  unfold electronDensityFromRatio; field_simp

end FT03

/-! ## FT-07 Aitchison error transfer and relative closure bounds -/
namespace FT07
variable {ι : Type*} [Fintype ι]

theorem clr_mul {x a : ι → ℝ} (hx : ∀ k, 0 < x k) (ha : ∀ k, 0 < a k) :
    clr (fun k => a k * x k) = fun k => clr a k + clr x k := by sorry

theorem aitchisonDist_perturb [Nonempty ι] {x y a : ι → ℝ} (hx : ∀ k, 0 < x k)
    (hy : ∀ k, 0 < y k) (ha : ∀ k, 0 < a k) :
    aitchisonDist (fun k => a k * x k) (fun k => a k * y k) = aitchisonDist x y := by sorry

theorem aitchisonDist_smul [Nonempty ι] {x y : ι → ℝ} {c : ℝ} (hc : 0 < c)
    (hx : ∀ k, 0 < x k) : aitchisonDist (fun k => c * x k) y = aitchisonDist x y := by sorry

theorem aitchisonDist_le_logErr [Nonempty ι] {x y : ι → ℝ} (hx : ∀ k, 0 < x k)
    (hy : ∀ k, 0 < y k) (c : ℝ) :
    aitchisonDist y x ≤ Real.sqrt (∑ s, (Real.log (y s / x s) - c) ^ 2) := by sorry

theorem composition_rel_error_mul {N Nhat : ι → ℝ} {η : ℝ} (hN : ∀ s, 0 < N s)
    (hη0 : 0 ≤ η) (hη1 : η < 1) (hmul : ∀ s, |Nhat s - N s| ≤ η * N s) (s : ι) :
    |composition Nhat s - composition N s| ≤ (2 * η / (1 - η)) * composition N s := by sorry

end FT07

/-! ## FT-06 two-diagnostic LTE certificate C8 (+ refusal) -/
namespace FT06

def starkSahaCert (lS uS lR uR C T dE : ℝ) : Prop :=
  max lS lR ≤ min uS uR ∧ C * Real.sqrt T * dE ^ 3 ≤ max lS lR

theorem starkSaha_certificate_sound {lS uS lR uR C T dE ne : ℝ}
    (hS : lS ≤ ne ∧ ne ≤ uS) (hR : lR ≤ ne ∧ ne ≤ uR)
    (h : starkSahaCert lS uS lR uR C T dE) : mcWhirterCert C T dE ne := by sorry

theorem starkSaha_refusal_sound {lS uS lR uR ne : ℝ} (hdis : min uS uR < max lS lR) :
    ¬ ((lS ≤ ne ∧ ne ≤ uS) ∧ (lR ≤ ne ∧ ne ≤ uR)) := by sorry

/-- Saha-side R1 premise from an unresolved IPD band `0 ≤ d ≤ dmax`: an IPD-off inverse brackets
the true `n_e` multiplicatively. -/
theorem saha_ipd_bracket {ι κ : Type*} [Fintype ι] [Fintype κ]
    {kB T me h chi d dmax R ne : ℝ} {gZ EZ : ι → ℝ} {gZ1 EZ1 : κ → ℝ}
    (hkT : 0 < kB * T) (hR : 0 < R) (hne : 0 < ne) (hd : 0 ≤ d) (hdm : d ≤ dmax)
    (hfwd : R * ne = sahaFactor kB T me h (chi - d) gZ EZ gZ1 EZ1) :
    electronDensityFromRatio kB T me h chi gZ EZ gZ1 EZ1 R ≤ ne ∧
      ne ≤ electronDensityFromRatio kB T me h chi gZ EZ gZ1 EZ1 R
            * Real.exp (dmax / (kB * T)) := by sorry

end FT06

/-! ## FT-12 heteroscedastic statistical slope certificate + exact Gaussian law -/
namespace FT12
variable {ι : Type*} [Fintype ι] {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ]

def slopeTailCert (E : ι → ℝ) (c : ι → NNReal) (tauBeta alpha : ℝ) : Prop :=
  2 * Real.exp (-(tauBeta ^ 2) / (2 * ∑ k, olsWeight E k ^ 2 * (c k : ℝ))) ≤ alpha

theorem olsSlope_subGaussian_tail_hetero [Nonempty ι] (E : ι → ℝ) (α β : ℝ) (ε : ι → Ω → ℝ)
    {c : ι → NNReal} {δ : ℝ} (hvar : 0 < ∑ k, (E k - mean E) ^ 2) (hδ : 0 ≤ δ)
    (hc : 0 < ∑ k, olsWeight E k ^ 2 * (c k : ℝ))
    (hindep : iIndepFun ε μ) (hsubG : ∀ k, HasSubgaussianMGF (ε k) (c k) μ) :
    μ.real {ω | δ ≤ |Alt.betaHat E α β ε ω - β|}
      ≤ 2 * Real.exp (-(δ ^ 2) / (2 * ∑ k, olsWeight E k ^ 2 * (c k : ℝ))) := by sorry

theorem betaHat_map_eq_gaussianReal [Nonempty ι] (E : ι → ℝ) (α β : ℝ) (ε : ι → Ω → ℝ)
    (σ : NNReal) (hvar : 0 < ∑ k, (E k - mean E) ^ 2)
    (hlaw : ∀ k, HasLaw (ε k) (gaussianReal 0 (σ ^ 2)) μ) (hind : iIndepFun ε μ) :
    μ.map (Alt.betaHat E α β ε)
      = gaussianReal β (σ ^ 2 * ⟨1 / ∑ k, (E k - mean E) ^ 2, by positivity⟩) := by sorry

end FT12

/-! ## FT-10 information floor: heteroscedastic Aitken BLUE + common-slope log-ratio -/
namespace FT10
variable {ι : Type*} [Fintype ι]

noncomputable def wMean (w E : ι → ℝ) : ℝ := (∑ k, w k * E k) / ∑ k, w k

noncomputable def wSS (w E : ι → ℝ) : ℝ := ∑ k, w k * (E k - wMean w E) ^ 2

noncomputable def wlsWeight (w E : ι → ℝ) (k : ι) : ℝ := w k * (E k - wMean w E) / wSS w E

/-- Deterministic Aitken core: among unbiased linear weights (`∑a = 0`, `∑aE = 1`), the WLS weights
minimise the noise gain `∑ a²σ²` with `σ_k² = 1/w_k`, and the minimum is `1/wSS`. -/
theorem wls_min_noiseGain {w E a : ι → ℝ} (hw : ∀ k, 0 < w k) (hSS : 0 < wSS w E)
    (ha0 : ∑ k, a k = 0) (ha1 : ∑ k, a k * E k = 1) :
    ∑ k, wlsWeight w E k ^ 2 / w k = 1 / wSS w E ∧
      1 / wSS w E ≤ ∑ k, a k ^ 2 / w k := by sorry

/-- Unweighted OLS is not monotone in line count under heteroscedastic noise. -/
example : ∃ (E σ2 : Fin 3 → ℝ),
    (∑ k, olsWeight E k ^ 2 * σ2 k) >
      ∑ k : Fin 2, olsWeight (E ∘ Fin.castSucc) k ^ 2 * σ2 (Fin.castSucc k) := by sorry

/-- Common-slope (ANCOVA) intercept-difference noise gain, deterministic core. -/
theorem interceptDiff_noiseGain {ιa ιb : Type*} [Fintype ιa] [Fintype ιb] [Nonempty ιa]
    [Nonempty ιb] (Ea : ιa → ℝ) (Eb : ιb → ℝ)
    (hSS : 0 < ∑ k, (Ea k - mean Ea) ^ 2 + ∑ k, (Eb k - mean Eb) ^ 2) :
    -- weights of d̂ = (ȳa − ȳb) − β̂_common·(Ēa − Ēb) on the pooled lines
    let SS := ∑ k, (Ea k - mean Ea) ^ 2 + ∑ k, (Eb k - mean Eb) ^ 2
    let wa : ιa → ℝ := fun k => 1 / Fintype.card ιa - (mean Ea - mean Eb) * (Ea k - mean Ea) / SS
    let wb : ιb → ℝ := fun k => -(1 / Fintype.card ιb) - (mean Ea - mean Eb) * (Eb k - mean Eb) / SS
    ∑ k, wa k ^ 2 + ∑ k, wb k ^ 2
      = 1 / Fintype.card ιa + 1 / Fintype.card ιb + (mean Ea - mean Eb) ^ 2 / SS := by sorry

end FT10

/-! ## FT-11 SahaCascade (spec 03 §1) + IPD-aware S10 -/
namespace FT11

noncomputable def sahaStageProduct (S : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1
  | z + 1 => sahaStageProduct S z * S z

noncomputable def stageFraction (Z : ℕ) (S : ℕ → ℝ) (ne : ℝ) (z : ℕ) : ℝ :=
  (sahaStageProduct S z / ne ^ z) / ∑ k ∈ Finset.range (Z + 1), sahaStageProduct S k / ne ^ k

noncomputable def speciesCharge (Z : ℕ) (S : ℕ → ℝ) (Ntot ne : ℝ) : ℝ :=
  Ntot * ∑ z ∈ Finset.range (Z + 1), (z : ℝ) * stageFraction Z S ne z

noncomputable def totalIonizedCharge {κ : Type*} [Fintype κ] (Z : κ → ℕ) (S : κ → ℕ → ℝ)
    (Ntot : κ → ℝ) (ne : ℝ) : ℝ := ∑ s, speciesCharge (Z s) (S s) (Ntot s) ne

theorem speciesCharge_strictAntiOn {Z : ℕ} {S : ℕ → ℝ} {Ntot : ℝ} (hZ : 1 ≤ Z)
    (hN : 0 < Ntot) (hS : ∀ z < Z, 0 < S z) :
    StrictAntiOn (speciesCharge Z S Ntot) (Set.Ioi 0) := by sorry

theorem cascade_exists_unique {κ : Type*} [Fintype κ] [Nonempty κ] {Z : κ → ℕ}
    {S : κ → ℕ → ℝ} {Ntot : κ → ℝ} (hZ : ∀ s, 1 ≤ Z s) (hN : ∀ s, 0 < Ntot s)
    (hS : ∀ s, ∀ z < Z s, 0 < S s z) :
    ∃! ne, 0 < ne ∧ ne = totalIonizedCharge Z S Ntot ne := by sorry

theorem totalIonizedCharge_Z_one {κ : Type*} [Fintype κ] {S : κ → ℕ → ℝ} {Ntot : κ → ℝ}
    {Z : κ → ℕ} {ne : ℝ} (hne : ne ≠ 0) (hZ : ∀ s, Z s = 1) :
    totalIonizedCharge Z S Ntot ne = multiElementIonized (fun s => S s 0) Ntot ne := by sorry

/-- S10: IPD-aware stage factors `S_z(n) = S0_z · exp((z+1)·φ(n))`, `φ = Δχ₁/(k_B T)`; strict
antitonicity survives iff the per-edge elasticity condition holds (DH: `(z+1)Δχ/(2kT) < 1`). -/
theorem speciesCharge_ipd_strictAntiOn {Z : ℕ} {S0 : ℕ → ℝ} {φ : ℝ → ℝ} {Ntot lo hi : ℝ}
    (hZ : 1 ≤ Z) (hN : 0 < Ntot) (hS : ∀ z < Z, 0 < S0 z) (hlo : 0 < lo)
    (hMLR : ∀ n1 ∈ Set.Icc lo hi, ∀ n2 ∈ Set.Icc lo hi, n1 < n2 →
        ∀ z < Z, ((z : ℝ) + 1) * (φ n2 - φ n1) < Real.log (n2 / n1)) :
    StrictAntiOn
      (fun n => speciesCharge Z (fun z => S0 z * Real.exp (((z : ℝ) + 1) * φ n)) Ntot n)
      (Set.Icc lo hi) := by sorry

end FT11

/-! ## FT-08 closure-free ratio mode vs NeutralityScale -/
namespace FT08
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Ratio mode is invariant under every common-mode normalization (closure, Fcal, neutrality). -/
theorem ratio_mode_normalization_invariant {N : κ → ℝ} {c : ℝ} (hc : c ≠ 0) (a b : κ)
    (hsum : ∑ t, N t ≠ 0) :
    composition (fun t => c * N t) a / composition (fun t => c * N t) b = N a / N b := by sorry

/-- Neutrality-normalized and closure-normalized readers give the same ratios (NeutralityScale is
orthogonal to ratio mode), even with an undetected species. -/
theorem neutrality_closure_same_ratio {kB T Fcal ne : ℝ} {g E A : ι → ℝ} {N R : κ → ℝ}
    {emit : κ → ι} (hFcal : 0 < Fcal) (hunit : ∀ s, 0 < lineIntensity kB T 1 1 g E A (emit s))
    (hN : ∀ s, 0 < N s) (a b : κ) :
    (Alt.closureEstimate (fun s => lineIntensity kB T (N s) Fcal g E A (emit s))
        (fun s => lineIntensity kB T 1 1 g E A (emit s)) a /
      Alt.closureEstimate (fun s => lineIntensity kB T (N s) Fcal g E A (emit s))
        (fun s => lineIntensity kB T 1 1 g E A (emit s)) b = N a / N b) ∧
    ∀ R : κ → ℝ, Alt.neutralityScale (fun s => lineIntensity kB T (N s) Fcal g E A (emit s))
        (fun s => lineIntensity kB T 1 1 g E A (emit s)) R ne ≠ 0 →
      (lineIntensity kB T (N a) Fcal g E A (emit a) / lineIntensity kB T 1 1 g E A (emit a)
          / Alt.neutralityScale (fun s => lineIntensity kB T (N s) Fcal g E A (emit s))
              (fun s => lineIntensity kB T 1 1 g E A (emit s)) R ne) /
        (lineIntensity kB T (N b) Fcal g E A (emit b) / lineIntensity kB T 1 1 g E A (emit b)
          / Alt.neutralityScale (fun s => lineIntensity kB T (N s) Fcal g E A (emit s))
              (fun s => lineIntensity kB T 1 1 g E A (emit s)) R ne) = N a / N b := by sorry

/-- ΔIP sensitivity (neutral lines, two-stage totals `N_tot = n_I(1 + S/n_e)`), in `β = 1/(k_B T)`:
the assumed-`β̂` log-ratio error is `Δ(β̂) − Δ(β)` with exact derivative
`(E_a − ⟨E⟩_{I,A}) − (E_b − ⟨E⟩_{I,B}) − f_A·κ_A + f_B·κ_B`,
`κ_X = χ_X + 3/(2β) + ⟨E⟩_{II,X} − ⟨E⟩_{I,X}`, `f_X = ρ_X/(1+ρ_X)`. Abstract-derivative form. -/
theorem ratioEstimate_hasDerivAt {lnUa lnUb lnSa lnSb : ℝ → ℝ} {Ea Eb β ne : ℝ}
    {dUa dUb dSa dSb : ℝ} (hne : 0 < ne)
    (hUa : HasDerivAt lnUa dUa β) (hUb : HasDerivAt lnUb dUb β)
    (hSa : HasDerivAt lnSa dSa β) (hSb : HasDerivAt lnSb dSb β) :
    HasDerivAt (fun b => b * (Ea - Eb) + (lnUa b - lnUb b)
        + Real.log (1 + Real.exp (lnSa b) / ne) - Real.log (1 + Real.exp (lnSb b) / ne))
      ((Ea - Eb) + (dUa - dUb)
        + (Real.exp (lnSa β) / ne) / (1 + Real.exp (lnSa β) / ne) * dSa
        - (Real.exp (lnSb β) / ne) / (1 + Real.exp (lnSb β) / ne) * dSb) β := by sorry

end FT08

/-! ## FT-09 energy-affine gA gauge -/
namespace FT09
variable {ι : Type*} [Fintype ι]

theorem olsSlope_add_affine [Nonempty ι] (E y : ι → ℝ) (α b : ℝ)
    (hvar : 0 < ∑ k, (E k - mean E) ^ 2) :
    olsSlope E (fun k => y k + α + b * E k) = olsSlope E y + b := by sorry

theorem affine_gA_gauge [Nonempty ι] {kB T N Fcal α b : ℝ} {g E A A' : ι → ℝ}
    (hkB : 0 < kB) (hT : 0 < T) (hg : ∀ k, 0 < g k) (hA : ∀ k, 0 < A k) (hN : 0 < N)
    (hFcal : 0 < Fcal) (haff : ∀ k, A' k = A k * Real.exp (-(α + b * E k)))
    (hvar : 0 < ∑ k, (E k - mean E) ^ 2) :
    olsSlope E (fun k => Real.log (lineIntensity kB T N Fcal g E A k / (g k * A' k)))
      = -(1 / (kB * T)) + b := by sorry

end FT09

/-! ## FT-13 escape factor vs slab SA, ½-Lipschitz log SA, robust C12 -/
namespace FT13

theorem escape_ge_slab {ψ : ℝ → ℝ} {τ0 : ℝ} (hψ0 : 0 ≤ ψ) (hψ1 : ∀ x, ψ x ≤ 1)
    (hint : Integrable ψ) (hτ : 0 < τ0) :
    selfAbsorptionFactor τ0 * (τ0 * ∫ x, ψ x) ≤ equivWidth ψ τ0 := by sorry

theorem log_selfAbsorptionFactor_lipschitz {τ τ' : ℝ} (hτ : 0 ≤ τ) (hτ' : 0 ≤ τ') :
    |Real.log (selfAbsorptionFactor τ) - Real.log (selfAbsorptionFactor τ')| ≤ |τ - τ'| / 2 := by
  sorry

/-- Robust replacement for C12: an estimated optical depth within `Δ` of the true one recovers the
thin log-intensity to within `Δ/2`. -/
theorem robustTau_sound {ι : Type*} [Fintype ι] [Nonempty ι] {kB T N Fcal τ τhat Δ : ℝ}
    {g E A : ι → ℝ} {k : ι} (hg : ∀ k, 0 < g k) (hN : 0 < N) (hFcal : 0 < Fcal)
    (hA : ∀ k, 0 < A k) (hτ : 0 ≤ τ) (hτh : 0 ≤ τhat) (hΔ : |τhat - τ| ≤ Δ) :
    |Real.log (selfAbsorbedIntensity kB T N Fcal g E A k τ / selfAbsorptionFactor τhat)
        - Real.log (lineIntensity kB T N Fcal g E A k)| ≤ Δ / 2 := by sorry

end FT13

/-! ## FT-14 physically scaled self-absorption (Kirchhoff layer + transfer before instrument) -/
namespace FT14

/-- Per-line opacity with an explicit stimulated-emission factor; constants abstract (`κ0` stands
for `(λ²/8π)(g_u/g_l)A_ul·φ(0)` pending the Griem-checked convention). -/
noncomputable def lineOpacity (κ0 nl x : ℝ) : ℝ := κ0 * nl * (1 - Real.exp (-x))

noncomputable def lineEmissivity (ε0 nu : ℝ) : ℝ := ε0 * nu

/-- Kirchhoff: with Boltzmann-ratio populations and the Einstein relation `ε0 = κ0·B0`, the source
function `ε/κ` is the Planck-form `B0/(e^x − 1)`, free of `N`, `U`, `A`, `L`. -/
theorem source_eq_planck {κ0 ε0 B0 nl nu x gu gl : ℝ} (hx : 0 < x) (hκ : 0 < κ0) (hnl : 0 < nl)
    (hpop : nu / nl = gu / gl * Real.exp (-x)) (hein : ε0 * gu / gl = κ0 * B0) :
    lineEmissivity ε0 nu / lineOpacity κ0 nl x = B0 / (Real.exp x - 1) := by sorry

/-- Emergent integrated slab intensity `S·∫(1 − e^{−κ L ψ})` is strictly increasing in `L`
(fixes LF-02's ℓ-decreasing thickLineIntensity). -/
theorem slabIntegrated_strictMono_L {S κ : ℝ} {ψ : ℝ → ℝ} (hS : 0 < S) (hκ : 0 < κ)
    (hψ0 : 0 ≤ ψ) (hint : Integrable ψ) (hpos : 0 < ∫ x, ψ x) :
    StrictMonoOn (fun L => S * equivWidth ψ (κ * L)) (Set.Ioi 0) := by sorry

/-- Transfer before instrument (Jensen): folding the instrument into the opacity overestimates
the emergent equivalent width. -/
theorem equivWidth_le_conv {R φ : ℝ → ℝ} {τ : ℝ} (hR : ∀ x, 0 ≤ R x) (hR1 : ∫ x, R x = 1)
    (hRint : Integrable R) (hφ : 0 ≤ φ) (hint : Integrable φ) (hτ : 0 ≤ τ) :
    equivWidth φ τ ≤ equivWidth (fun x => ∫ y, R (x - y) * φ y) τ := by sorry

end FT14

/-! ## FT-15 log-derivative partition / Saha Lipschitz constants -/
namespace FT15
variable {ι : Type*} [Fintype ι]

noncomputable def meanExcitation (kB T : ℝ) (g E : ι → ℝ) : ℝ :=
  (∑ k, g k * E k * boltzmannFactor kB T (E k)) / partitionFunction kB T g E

theorem meanExcitation_monotoneOn_temp [Nonempty ι] {kB : ℝ} {g E : ι → ℝ} (hkB : 0 < kB)
    (hg : ∀ k, 0 < g k) :
    MonotoneOn (fun T => meanExcitation kB T g E) (Set.Ioi 0) := by sorry

theorem log_partitionFunction_lipschitz [Nonempty ι] {kB Tmin Tmax T1 T2 : ℝ} {g E : ι → ℝ}
    (hkB : 0 < kB) (hTmin : 0 < Tmin) (hT1 : Tmin ≤ T1) (hT1M : T1 ≤ Tmax) (hT2 : Tmin ≤ T2)
    (hT2M : T2 ≤ Tmax) (hg : ∀ k, 0 < g k) (hE : ∀ k, 0 ≤ E k) :
    |Real.log (partitionFunction kB T1 g E) - Real.log (partitionFunction kB T2 g E)|
      ≤ meanExcitation kB Tmax g E * |1 / (kB * T1) - 1 / (kB * T2)| := by sorry

theorem log_sahaFactor_lipschitz {κ : Type*} [Fintype κ] [Nonempty ι] [Nonempty κ]
    {kB me h chi Tmin Tmax T1 T2 : ℝ} {gZ EZ : ι → ℝ} {gZ1 EZ1 : κ → ℝ}
    (hkB : 0 < kB) (hme : 0 < me) (hh : 0 < h) (hTmin : 0 < Tmin) (hT1 : Tmin ≤ T1)
    (hT1M : T1 ≤ Tmax) (hT2 : Tmin ≤ T2) (hT2M : T2 ≤ Tmax) (hgZ : ∀ k, 0 < gZ k)
    (hgZ1 : ∀ k, 0 < gZ1 k) (hEZ : ∀ k, 0 ≤ EZ k) (hEZ1 : ∀ k, 0 ≤ EZ1 k)
    (hEχ : ∀ k, EZ k ≤ chi) :
    |Real.log (sahaFactor kB T1 me h chi gZ EZ gZ1 EZ1)
        - Real.log (sahaFactor kB T2 me h chi gZ EZ gZ1 EZ1)|
      ≤ (3 / (2 * Tmin) + (chi + meanExcitation kB Tmax gZ1 EZ1) / (kB * Tmin ^ 2))
          * |T1 - T2| := by sorry

end FT15

/-! ## FT-16 extractor misspecification identity + Varah ℓ∞ gain -/
namespace FT16
open Matrix
variable {P L : Type*} [Fintype P] [Fintype L] [DecidableEq L]

theorem extractor_bias_identity (K Kt : Matrix P L ℝ) (I : L → ℝ) (η : P → ℝ)
    (hdet : IsUnit (Kᵀ * K).det) :
    ((Kᵀ * K)⁻¹ * Kᵀ).mulVec (Kt.mulVec I + η) - I
      = ((Kᵀ * K)⁻¹ * Kᵀ).mulVec ((Kt - K).mulVec I) + ((Kᵀ * K)⁻¹ * Kᵀ).mulVec η := by
  sorry

theorem linfty_le_of_rowDiagDominant [Nonempty L] (M : Matrix L L ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hdom : ∀ k, δ + ∑ j ∈ univ.erase k, |M k j| ≤ |M k k|) (x : L → ℝ) (i : L) :
    |x i| ≤ (univ.sup' univ_nonempty fun k => |(M.mulVec x) k|) / δ := by sorry

end FT16

/-! ## FT-17 Newton on the charge-neutrality equation: certified bracket -/
namespace FT17
variable {ι : Type*} [Fintype ι]

noncomputable def neutralityNewton (S Ntot : ι → ℝ) (x : ℝ) : ℝ :=
  x - (x - multiElementIonized S Ntot x) / (1 + ∑ s, Ntot s * S s / (x + S s) ^ 2)

theorem neutralityNewton_enclosure [Nonempty ι] {S Ntot : ι → ℝ} {x r : ℝ}
    (hS : ∀ s, 0 < S s) (hN : ∀ s, 0 < Ntot s) (hx : 0 ≤ x) (hr : 0 < r)
    (hfix : r = multiElementIonized S Ntot r) :
    neutralityNewton S Ntot x ≤ r ∧ r ≤ multiElementIonized S Ntot (neutralityNewton S Ntot x) ∧
      |neutralityNewton S Ntot x - r| ≤ (∑ s, Ntot s / S s ^ 2) * (x - r) ^ 2 := by sorry

end FT17

/-! ## FT-18 SA flattens the Boltzmann slope when τ is antitone in E_upper -/
namespace FT18
variable {ι : Type*} [Fintype ι]

theorem olsSlope_selfAbsorbed_ge [Nonempty ι] {E y τ : ι → ℝ} (hτ : ∀ k, 0 < τ k)
    (hanti : ∀ i j, E i ≤ E j → τ j ≤ τ i) (hvar : 0 < ∑ k, (E k - mean E) ^ 2) :
    olsSlope E y ≤ olsSlope E (fun k => y k + Real.log (selfAbsorptionFactor (τ k))) := by sorry

end FT18

/-! ## FT-19 ion vs neutral apparent temperature -/
namespace FT19
variable {ζ : Type*} [Fintype ζ] [Nonempty ζ]

theorem tiltMean_reweight_le {w b ρ : ζ → ℝ} (hw : ∀ z, 0 < w z) (hρ : ∀ z, 0 < ρ z)
    (hanti : ∀ i j, b i ≤ b j → ρ j ≤ ρ i) (a : ℝ) :
    tiltMean (fun z => w z * ρ z) b a ≤ tiltMean w b a := by sorry

end FT19

/-! ## FT-20 pair curve-of-growth identifiability boundary -/
namespace FT20

/-- Two-step (core + weak broad wing) surrogate profile. -/
noncomputable def stepProfile (η M : ℝ) : ℝ → ℝ :=
  fun x => Set.indicator (Set.Icc 0 1) (fun _ => 1) x + η * Set.indicator (Set.Icc 0 M) (fun _ => 1) x

theorem equivWidth_stepProfile {η M τ : ℝ} (hη : 0 ≤ η) (hM : 1 ≤ M) :
    equivWidth (stepProfile η M) τ
      = (1 - Real.exp (-(τ * (1 + η)))) + (M - 1) * (1 - Real.exp (-(τ * η))) := by sorry

/-- Flat-kernel pair-ratio injectivity (`cogRatio_injOn`) is not profile-generic
(numerics: η = 1/100, M = 20, r = 2 gives ratios 1.508, 1.391, 1.583 at n = 1, 3, 10). -/
theorem stepProfile_pairRatio_not_injOn :
    ¬ Set.InjOn (fun n => equivWidth (stepProfile (1 / 100) 20) (2 * n)
        / equivWidth (stepProfile (1 / 100) 20) n) (Set.Ioi 0) := by sorry

end FT20

end Slate
