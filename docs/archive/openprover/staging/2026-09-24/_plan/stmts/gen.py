import os
T = {}
FT04_DEFS = '''variable {ι κ : Type*} [Fintype ι] [DecidableEq κ]

/-- Weighted group mean of `f` over the lines of group `e` (empty group: `0/0 = 0`). -/
noncomputable def gMean (grp : ι → κ) (w f : ι → ℝ) (e : κ) : ℝ :=
  (∑ k ∈ univ.filter (fun k => grp k = e), w k * f k) /
    ∑ k ∈ univ.filter (fun k => grp k = e), w k

/-- Weighted within-group cross product. -/
noncomputable def withinCross (grp : ι → κ) (w x y : ι → ℝ) : ℝ :=
  ∑ k, w k * (x k - gMean grp w x (grp k)) * (y k - gMean grp w y (grp k))

/-- Weighted within-group sum of squares `SS_W`. -/
noncomputable def withinSS (grp : ι → κ) (w x : ι → ℝ) : ℝ := withinCross grp w x x

/-- Fixed-effects (within-element) slope. -/
noncomputable def feSlope (grp : ι → κ) (w x y : ι → ℝ) : ℝ :=
  withinCross grp w x y / withinSS grp w x
'''
def add(name, imports, ns, opens, body, pre=''):
    T[name] = (imports, ns, opens, pre + body)

add('FT04-feSlope-add-smul', ['Mathlib'], 'Plan.FT04', 'open Finset', '''
theorem feSlope_add_smul (grp : ι → κ) (w x y s : ι → ℝ) (c : ℝ) :
    feSlope grp w x (fun k => y k + c * s k) = feSlope grp w x y + c * feSlope grp w x s := by
  sorry
''', FT04_DEFS)
add('FT04-fe-identifiable-iff', ['Mathlib'], 'Plan.FT04', 'open Finset', '''
theorem fe_identifiable_iff (grp : ι → κ) (w x : ι → ℝ) (hw : ∀ k, 0 < w k) :
    (∀ (a a' : κ → ℝ) (β β' : ℝ),
        (∀ k, a (grp k) + β * x k = a' (grp k) + β' * x k) → β = β')
      ↔ 0 < withinSS grp w x := by
  sorry
''', FT04_DEFS)
add('FT04-feSlope-isMin', ['Mathlib'], 'Plan.FT04', 'open Finset', '''
theorem feSlope_isMin (grp : ι → κ) (w x y : ι → ℝ) (hw : ∀ k, 0 < w k)
    (hSS : 0 < withinSS grp w x) (a : κ → ℝ) (β : ℝ) :
    ∑ k, w k * (y k - (gMean grp w y (grp k) - feSlope grp w x y * gMean grp w x (grp k))
        - feSlope grp w x y * x k) ^ 2
      ≤ ∑ k, w k * (y k - a (grp k) - β * x k) ^ 2 := by
  sorry
''', FT04_DEFS)

FT10_DEFS = '''variable {ι : Type*} [Fintype ι]

/-- Weighted mean `Ē_w = ∑ w E / ∑ w`. -/
noncomputable def wMean (w E : ι → ℝ) : ℝ := (∑ k, w k * E k) / ∑ k, w k

/-- Weighted centred sum of squares `∑ w (E − Ē_w)²`. -/
noncomputable def wSS (w E : ι → ℝ) : ℝ := ∑ k, w k * (E k - wMean w E) ^ 2

/-- Weighted-least-squares slope weight `w_k (E_k − Ē_w) / wSS`. -/
noncomputable def wlsWeight (w E : ι → ℝ) (k : ι) : ℝ := w k * (E k - wMean w E) / wSS w E
'''
add('FT10-wls-min-noiseGain', ['Mathlib'], 'Plan.FT10', 'open Finset', '''
theorem wls_min_noiseGain {w E a : ι → ℝ} (hw : ∀ k, 0 < w k) (hSS : 0 < wSS w E)
    (ha0 : ∑ k, a k = 0) (ha1 : ∑ k, a k * E k = 1) :
    ∑ k, wlsWeight w E k ^ 2 / w k = 1 / wSS w E ∧ 1 / wSS w E ≤ ∑ k, a k ^ 2 / w k := by
  sorry
''', FT10_DEFS)
add('FT10-interceptDiff-noiseGain', ['Mathlib', 'CflibsFormal.OLS'], 'Plan.FT10', 'open Finset CflibsFormal', '''
theorem interceptDiff_noiseGain {ιa ιb : Type*} [Fintype ιa] [Fintype ιb] [Nonempty ιa]
    [Nonempty ιb] (Ea : ιa → ℝ) (Eb : ιb → ℝ)
    (hSS : 0 < ∑ k, (Ea k - mean Ea) ^ 2 + ∑ k, (Eb k - mean Eb) ^ 2) :
    let SS := ∑ k, (Ea k - mean Ea) ^ 2 + ∑ k, (Eb k - mean Eb) ^ 2
    let wa : ιa → ℝ := fun k =>
      (1 : ℝ) / (Fintype.card ιa : ℝ) - (mean Ea - mean Eb) * (Ea k - mean Ea) / SS
    let wb : ιb → ℝ := fun k =>
      -((1 : ℝ) / (Fintype.card ιb : ℝ)) - (mean Ea - mean Eb) * (Eb k - mean Eb) / SS
    ∑ k, wa k ^ 2 + ∑ k, wb k ^ 2
      = (1 : ℝ) / (Fintype.card ιa : ℝ) + (1 : ℝ) / (Fintype.card ιb : ℝ)
          + (mean Ea - mean Eb) ^ 2 / SS := by
  sorry
''')
add('FT18-olsSlope-selfAbsorbed-ge', ['Mathlib', 'CflibsFormal.OLS', 'CflibsFormal.SelfAbsorption'], 'Plan.FT18', 'open Finset CflibsFormal', '''
variable {ι : Type*} [Fintype ι]

theorem olsSlope_selfAbsorbed_ge [Nonempty ι] {E y τ : ι → ℝ} (hτ : ∀ k, 0 < τ k)
    (hanti : ∀ i j, E i < E j → τ j ≤ τ i) :
    olsSlope E y ≤ olsSlope E (fun k => y k + Real.log (selfAbsorptionFactor (τ k))) := by
  sorry
''')

# g2
add('F02M6-sahaEquilibriumNe-strictMonoOn-temp', ['Mathlib', 'CflibsFormal.SahaStability', 'CflibsFormal.SahaEquilibrium'], 'Plan.F02M6', 'open CflibsFormal', '''
variable {ι : Type*} [Fintype ι] {κ : Type*} [Fintype κ]

theorem sahaEquilibriumNe_strictMonoOn_temp [Nonempty ι] [Nonempty κ]
    {kB me h chi Ntot : ℝ} {gZ EZ : ι → ℝ} {gZ1 EZ1 : κ → ℝ}
    (hkB : 0 < kB) (hme : 0 < me) (hh : 0 < h) (_hchi : 0 ≤ chi)
    (hgZ : ∀ k, 0 < gZ k) (_hEZ : ∀ k, 0 ≤ EZ k)
    (hgZ1 : ∀ k, 0 < gZ1 k) (hEZ1 : ∀ k, 0 ≤ EZ1 k)
    (hEχ : ∀ k, EZ k ≤ chi) (hN : 0 < Ntot) :
    StrictMonoOn (fun T => sahaEquilibriumNe (sahaFactor kB T me h chi gZ EZ gZ1 EZ1) Ntot)
      (Set.Ioi 0) := by
  sorry
''')
FT02_DEF = '''
/-- Log-coordinate IPD-aware Saha inverse map, `ℓ = log n_e`, with the lowering term
`b·e^{ℓ/2}` (coefficient `b` abstract). -/
noncomputable def ipdLogMap (a b ℓ : ℝ) : ℝ := Real.log a + b * Real.exp (ℓ / 2)
'''
add('FT02-ipdLogMap-root-subsingleton', ['Mathlib'], 'Plan.FT02', 'open Filter Topology', '''
theorem ipdLogMap_root_subsingleton {a b : ℝ} (hb : 0 < b) :
    {ℓ | ipdLogMap a b ℓ = ℓ ∧ b * Real.exp (ℓ / 2) < 2}.Subsingleton := by
  sorry
''', FT02_DEF)
add('FT02-ipdLogMap-contracts', ['Mathlib'], 'Plan.FT02', 'open Filter Topology', '''
theorem ipdLogMap_contracts {a b ℓ1 q : ℝ} (hb : 0 ≤ b)
    (hq : b * Real.exp (ℓ1 / 2) / 2 ≤ q) (hq1 : q < 1)
    (hmaps : Set.MapsTo (ipdLogMap a b) (Set.Iic ℓ1) (Set.Iic ℓ1)) :
    ∃ ℓs ∈ Set.Iic ℓ1, ipdLogMap a b ℓs = ℓs ∧
      (∀ ℓ ∈ Set.Iic ℓ1, ipdLogMap a b ℓ = ℓ → ℓ = ℓs) ∧
      ∀ ℓ0 ∈ Set.Iic ℓ1, Tendsto (fun n => (ipdLogMap a b)^[n] ℓ0) atTop (𝓝 ℓs) := by
  sorry
''', FT02_DEF)
add('FT02-ipdInverse-twoPoint-sensitivity', ['Mathlib'], 'Plan.FT02', 'open Filter Topology', '''
theorem ipdInverse_twoPoint_sensitivity {a1 a2 b l1 l2 q : ℝ} (ha1 : 0 < a1) (hb : 0 ≤ b)
    (hq : q < 1) (h1 : ipdLogMap a1 b l1 = l1) (h2 : ipdLogMap a2 b l2 = l2) (ha : a1 ≤ a2)
    (hreg : b * Real.exp (max l1 l2 / 2) / 2 ≤ q) :
    Real.log a2 - Real.log a1 ≤ l2 - l1 ∧ l2 - l1 ≤ (Real.log a2 - Real.log a1) / (1 - q) := by
  sorry
''', FT02_DEF)
add('FT05-cutRatio-strictMonoOn-temp', ['Mathlib', 'CflibsFormal.Boltzmann'], 'Plan.FT05', 'open Finset CflibsFormal', '''
variable {ι : Type*} [Fintype ι]

/-- Partition function truncated to the levels strictly below the cutoff energy `cut`. -/
noncomputable def partitionFunctionCut (kB T cut : ℝ) (g E : ι → ℝ) : ℝ :=
  ∑ k ∈ univ.filter (fun k => E k < cut), g k * boltzmannFactor kB T (E k)

theorem cutRatio_strictMonoOn_temp {kB cut : ℝ} {g E : ι → ℝ} (hkB : 0 < kB)
    (hg : ∀ k, 0 < g k) (hkeep : ∃ k, E k < cut) (hdrop : ∃ k, cut ≤ E k) :
    StrictMonoOn (fun T => partitionFunction kB T g E / partitionFunctionCut kB T cut g E)
      (Set.Ioi 0) := by
  sorry
''')
FT15_DEF = '''variable {ι : Type*} [Fintype ι]

/-- Boltzmann-weighted mean excitation energy `⟨E⟩_T = ∑ g E e^{-E/kT} / U(T)`. -/
noncomputable def meanExcitation (kB T : ℝ) (g E : ι → ℝ) : ℝ :=
  (∑ k, g k * E k * boltzmannFactor kB T (E k)) / partitionFunction kB T g E
'''
add('FT15-meanExcitation-monotoneOn-temp', ['Mathlib', 'CflibsFormal.Boltzmann'], 'Plan.FT15', 'open Finset CflibsFormal', '''
theorem meanExcitation_monotoneOn_temp [Nonempty ι] {kB : ℝ} {g E : ι → ℝ} (hkB : 0 < kB)
    (hg : ∀ k, 0 < g k) :
    MonotoneOn (fun T => meanExcitation kB T g E) (Set.Ioi 0) := by
  sorry
''', FT15_DEF)
add('FT15-log-partitionFunction-lipschitz-max', ['Mathlib', 'CflibsFormal.Boltzmann'], 'Plan.FT15', 'open Finset CflibsFormal', '''
theorem log_partitionFunction_lipschitz_max [Nonempty ι] {kB T1 T2 : ℝ} {g E : ι → ℝ}
    (hkB : 0 < kB) (hT1 : 0 < T1) (hT2 : 0 < T2) (hg : ∀ k, 0 < g k) (hE : ∀ k, 0 ≤ E k) :
    |Real.log (partitionFunction kB T1 g E) - Real.log (partitionFunction kB T2 g E)|
      ≤ meanExcitation kB (max T1 T2) g E * |1 / (kB * T1) - 1 / (kB * T2)| := by
  sorry
''', FT15_DEF)

# g3
add('FT03-pasPolicy-guarantees', ['Mathlib'], 'Plan.FT03', 'open Finset', '''
/-- Three-branch refuse-to-report policy on per-item losses `l` with certified bounds
`L ≤ l ≤ U`, group weights `w`, reference cost `lam`: answer if `U ≤ lam`, refuse if
`lam < L`, and on the ambiguous set answer iff `ansA`. -/
noncomputable def pasPolicy {N : ℕ} (w l L U : Fin N → ℝ) (lam : ℝ) (ansA : Fin N → Prop)
    [DecidablePred ansA] : ℝ :=
  ∑ i, w i * (if U i ≤ lam then l i else if lam < L i then lam else if ansA i then l i else lam)

theorem pasPolicy_guarantees {N : ℕ} {w l L U : Fin N → ℝ} {lam : ℝ} (hw : ∀ i, 0 < w i)
    (hL : ∀ i, L i ≤ l i) (hU : ∀ i, l i ≤ U i) :
    pasPolicy w l L U lam (fun _ => False) ≤ (∑ i, w i) * lam ∧
    pasPolicy w l L U lam (fun _ => False) - ∑ i, w i * min (l i) lam
      ≤ ∑ i, w i * (if L i ≤ lam ∧ lam < U i then lam - L i else 0) ∧
    pasPolicy w l L U lam (fun _ => True) ≤ ∑ i, w i * l i := by
  sorry
''')
add('FT03-aitchisonDist-le-logErr', ['Mathlib', 'CflibsFormal.AitchisonIsometry'], 'Plan.FT03', 'open Finset CflibsFormal', '''
variable {ι : Type*} [Fintype ι]

theorem aitchisonDist_le_logErr [Nonempty ι] {x y : ι → ℝ} (hx : ∀ k, 0 < x k)
    (hy : ∀ k, 0 < y k) (c : ℝ) :
    aitchisonDist y x ≤ Real.sqrt (∑ s, (Real.log (y s / x s) - c) ^ 2) := by
  sorry
''')
add('FT07-classicComposition-atomicData-error-rel', ['Mathlib', 'CflibsFormal.AtomicDataPerturbation'], 'Plan.FT07', 'open Finset CflibsFormal', '''
variable {ι : Type*} [Fintype ι] {κ : Type*} [Fintype κ]

theorem classicComposition_atomicData_error_rel [Nonempty ι] [Nonempty κ]
    {kB T Fcal δ : ℝ} {N : κ → ℝ} {g E A g' E' A' : κ → ι → ℝ} {u : κ → ι}
    (hg : ∀ s k, 0 < g s k) (hg' : ∀ s k, 0 < g' s k) (hFcal : 0 < Fcal)
    (hA : ∀ s, 0 < A s (u s)) (hA' : ∀ s, 0 < A' s (u s))
    (hN : ∀ s, 0 < N s) (hδ0 : 0 ≤ δ) (hδ : δ < 1 / 2)
    (hpert : ∀ s, |responseFactor kB T (g' s) (E' s) (A' s) (u s)
                    - responseFactor kB T (g s) (E s) (A s) (u s)|
                  ≤ δ * responseFactor kB T (g s) (E s) (A s) (u s))
    (s : κ) :
    |composition (recoveredDensity kB T Fcal g E A g' E' A' u N) s - composition N s|
      ≤ (2 * δ / (1 - 2 * δ)) * composition N s := by
  sorry
''')
add('FT09-affine-gA-observational-equiv', ['Mathlib', 'CflibsFormal.ForwardMap'], 'Plan.FT09', 'open Finset CflibsFormal', '''
variable {ι : Type*} [Fintype ι]

theorem affine_gA_observational_equiv [Nonempty ι]
    {kB T N Fcal α b : ℝ} {g E A A' : ι → ℝ}
    (hkB : 0 < kB) (hT : 0 < T) (hg : ∀ k, 0 < g k) (hA : ∀ k, 0 < A k) (hN : 0 < N)
    (hFcal : 0 < Fcal) (haff : ∀ k, A' k = A k * Real.exp (-(α + b * E k)))
    (hb : b * (kB * T) < 1) :
    ∃ T' N' : ℝ, 0 < T' ∧ 0 < N' ∧ 1 / (kB * T') = 1 / (kB * T) - b ∧
      ∀ k, Real.log (lineIntensity kB T N Fcal g E A k / (g k * A' k))
        = Real.log (lineIntensity kB T' N' Fcal g E A k / (g k * A k)) := by
  sorry
''')
add('FT06-stark-bracket-rho', ['Mathlib', 'CflibsFormal.StarkBroadening'], 'Plan.FT06', 'open CflibsFormal', '''
theorem stark_bracket_rho {w ρw kOpac wTrue nRef neTrue widthMeas : ℝ} (hw : 0 < w)
    (hρ : 1 ≤ ρw) (hk : 0 < kOpac) (hnRef : 0 < nRef) (hne : 0 ≤ neTrue)
    (hwT : w / ρw ≤ wTrue ∧ wTrue ≤ w * ρw)
    (hopac : starkFWHM wTrue nRef neTrue ≤ widthMeas)
    (hbudget : widthMeas ≤ kOpac * starkFWHM wTrue nRef neTrue) :
    starkDensity w nRef widthMeas / (kOpac * ρw) ≤ neTrue ∧
      neTrue ≤ starkDensity w nRef widthMeas * ρw := by
  sorry

''')
add('FT12-olsSlope-subGaussian-tail-hetero', ['Mathlib', 'CflibsFormal.Alt.StochasticBudget'], 'Plan.FT12', 'open Finset CflibsFormal MeasureTheory ProbabilityTheory', '''
variable {ι : Type*} [Fintype ι] {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ]

theorem olsSlope_subGaussian_tail_hetero [Nonempty ι] (E : ι → ℝ) (α β : ℝ) (ε : ι → Ω → ℝ)
    {c : ι → NNReal} {δ : ℝ} (hvar : 0 < ∑ k, (E k - mean E) ^ 2) (hδ : 0 ≤ δ)
    (hindep : iIndepFun ε μ) (hsubG : ∀ k, HasSubgaussianMGF (ε k) (c k) μ) :
    μ.real {ω | δ ≤ |Alt.betaHat E α β ε ω - β|}
      ≤ 2 * Real.exp (-(δ ^ 2) / (2 * ∑ k, olsWeight E k ^ 2 * (c k : ℝ))) := by
  sorry
''')
add('FT16-kernelLS-error-linfty', ['Mathlib'], 'Plan.FT16', 'open Finset Matrix', '''
variable {P L : Type*} [Fintype P] [Fintype L] [DecidableEq L]

theorem kernelLS_error_linfty [Nonempty L] (K Kt : Matrix P L ℝ) (I Ihat : L → ℝ) (η : P → ℝ)
    {δ : ℝ} (hδ : 0 < δ)
    (hdom : ∀ k, δ + ∑ j ∈ univ.erase k, |(Kᵀ * K) k j| ≤ |(Kᵀ * K) k k|)
    (hnormal : (Kᵀ * K).mulVec Ihat = Kᵀ.mulVec (Kt.mulVec I + η)) (l : L) :
    |Ihat l - I l|
      ≤ (univ.sup' univ_nonempty fun k => |(Kᵀ.mulVec ((Kt - K).mulVec I + η)) k|) / δ := by
  sorry
''')

add('FT06-guards-evidence', ['Mathlib', 'CflibsFormal.StarkBroadening'], 'Plan.FT06g', 'open CflibsFormal', '''
/-- Guard check: without `0 < nRef`, `0 ≤ neTrue` the revised statement is false. -/
example : ¬ (∀ w ρw kOpac wTrue nRef neTrue widthMeas : ℝ, 0 < w → 1 ≤ ρw → 0 < kOpac →
    (w / ρw ≤ wTrue ∧ wTrue ≤ w * ρw) → starkFWHM wTrue nRef neTrue ≤ widthMeas →
    widthMeas ≤ kOpac * starkFWHM wTrue nRef neTrue →
    (starkDensity w nRef widthMeas / (kOpac * ρw) ≤ neTrue ∧
      neTrue ≤ starkDensity w nRef widthMeas * ρw)) := by
  intro H
  have := (H 1 1 2 1 (-1) (-1) 2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num [starkFWHM]) (by norm_num [starkFWHM])).1
  norm_num [starkDensity] at this

/-- Guard check: `0 < nRef` alone is not enough; `0 ≤ neTrue` is also load-bearing. -/
example : ¬ (∀ w ρw kOpac wTrue nRef neTrue widthMeas : ℝ, 0 < w → 1 ≤ ρw → 0 < kOpac →
    0 < nRef → (w / ρw ≤ wTrue ∧ wTrue ≤ w * ρw) → starkFWHM wTrue nRef neTrue ≤ widthMeas →
    widthMeas ≤ kOpac * starkFWHM wTrue nRef neTrue →
    (starkDensity w nRef widthMeas / (kOpac * ρw) ≤ neTrue ∧
      neTrue ≤ starkDensity w nRef widthMeas * ρw)) := by
  intro H
  have := (H 1 2 1 1 1 (-1) (-2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num [starkFWHM]) (by norm_num [starkFWHM])).2
  norm_num [starkDensity] at this
''')

# g4
FT01_DEF = '''
/-- Krasnoselskii–Mann damped map `u ↦ (1−λ)u + λ g(u)` (the pipeline uses `λ = 1/2`). -/
def dampedMap (lam : ℝ) (g : ℝ → ℝ) (u : ℝ) : ℝ := (1 - lam) * u + lam * g u
'''
add('FT01-tDamped-mobius-converges', ['Mathlib'], 'Plan.FT01', 'open Filter Topology', '''
theorem tDamped_mobius_converges {g c lam : ℝ} (hg0 : 0 < g) (hg1 : g < 1) (hc : 0 < c)
    (hl0 : 0 < lam) (hl1 : lam ≤ 1) (T0 : ℝ) (hT0 : 0 < T0) :
    Tendsto (fun n => (dampedMap lam (fun T => T / (g + c * T)))^[n] T0) atTop
      (𝓝 ((1 - g) / c)) := by
  sorry
''', FT01_DEF)
add('FT01-exists-weights-iff', ['Mathlib'], 'Plan.FT01', 'open Filter Topology', '''
theorem exists_weights_iff {a b c d : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c) :
    (∃ wT wn : ℝ, 0 < wT ∧ 0 < wn ∧ max (a + b * wn / wT) (c * wT / wn + d) < 1)
      ↔ (a < 1 ∧ d < 1 ∧ b * c < (1 - a) * (1 - d)) := by
  sorry
''')
add('FT01-dampedMap-contracts', ['Mathlib'], 'Plan.FT01', 'open Filter Topology', '''
theorem dampedMap_contracts {g g' : ℝ → ℝ} {a b m M lam : ℝ} (hlam0 : 0 < lam) (hab : a ≤ b)
    (hd : ∀ T ∈ Set.Icc a b, HasDerivAt g (g' T) T)
    (hmM : ∀ T ∈ Set.Icc a b, m ≤ g' T ∧ g' T ≤ M) (hlo : 1 - 2 / lam < m) (hhi : M < 1)
    (hmaps : Set.MapsTo (dampedMap lam g) (Set.Icc a b) (Set.Icc a b)) :
    ∃ Tstar ∈ Set.Icc a b, dampedMap lam g Tstar = Tstar ∧
      ∀ T0 ∈ Set.Icc a b, Tendsto (fun n => (dampedMap lam g)^[n] T0) atTop (𝓝 Tstar) := by
  sorry
''', FT01_DEF)
FT17_DEF = '''variable {ι : Type*} [Fintype ι]

/-- Newton map for the charge-neutrality residual `f x = x − multiElementIonized S Ntot x`. -/
noncomputable def neutralityNewton (S Ntot : ι → ℝ) (x : ℝ) : ℝ :=
  x - (x - multiElementIonized S Ntot x) / (1 + ∑ s, Ntot s * S s / (x + S s) ^ 2)
'''
add('FT17-neutralityNewton-enclosure', ['Mathlib', 'CflibsFormal.SahaEquilibrium'], 'Plan.FT17', 'open Finset CflibsFormal', '''
theorem neutralityNewton_enclosure {S Ntot : ι → ℝ} {x r : ℝ} (hS : ∀ s, 0 < S s)
    (hN : ∀ s, 0 ≤ Ntot s) (hx : 0 ≤ x) (hr : 0 ≤ r)
    (hfix : r = multiElementIonized S Ntot r) :
    neutralityNewton S Ntot x ≤ r ∧
      r ≤ multiElementIonized S Ntot (neutralityNewton S Ntot x) := by
  sorry
''', FT17_DEF)
add('FT17-neutralityNewton-tendsto', ['Mathlib', 'CflibsFormal.SahaEquilibrium'], 'Plan.FT17', 'open Finset CflibsFormal Filter Topology', '''
theorem neutralityNewton_tendsto {S Ntot : ι → ℝ} {r x0 : ℝ} (hS : ∀ s, 0 < S s)
    (hN : ∀ s, 0 ≤ Ntot s) (hr : 0 ≤ r) (hfix : r = multiElementIonized S Ntot r)
    (hx0 : 0 ≤ x0) :
    Tendsto (fun n => (neutralityNewton S Ntot)^[n] x0) atTop (𝓝 r) := by
  sorry
''', FT17_DEF)
add('FT13-escape-ge-slab', ['Mathlib', 'CflibsFormal.SelfAbsorption', 'CflibsFormal.EquivalentWidth'], 'Plan.FT13', 'open CflibsFormal MeasureTheory', '''
theorem escape_ge_slab {ψ : ℝ → ℝ} {τ0 : ℝ} (hψ0 : 0 ≤ ψ) (hψ1 : ∀ x, ψ x ≤ 1)
    (hint : Integrable ψ) (hτ : 0 < τ0) :
    selfAbsorptionFactor τ0 * (τ0 * ∫ x, ψ x) ≤ equivWidth ψ τ0 := by
  sorry
''')
add('FT13-inv-sub-inv-expm1-bounds', ['Mathlib'], 'Plan.FT13', '', '''
theorem inv_sub_inv_exp_sub_one_mem {τ : ℝ} (hτ : 0 < τ) :
    0 < 1 / τ - 1 / (Real.exp τ - 1) ∧ 1 / τ - 1 / (Real.exp τ - 1) < 1 / 2 := by
  sorry
''')
add('FT13-log-selfAbsorptionFactor-lipschitz', ['Mathlib', 'CflibsFormal.SelfAbsorption'], 'Plan.FT13', 'open CflibsFormal', '''
theorem log_selfAbsorptionFactor_lipschitz {τ τ' : ℝ} (hτ : 0 ≤ τ) (hτ' : 0 ≤ τ') :
    |Real.log (selfAbsorptionFactor τ) - Real.log (selfAbsorptionFactor τ')|
      ≤ |τ - τ'| / 2 := by
  sorry
''')

for name,(imports,ns,opens,body) in T.items():
    s = "\n".join("import "+i for i in imports) + "\n\n" + opens + "\n\nnamespace " + ns + "\n\n" + body + "\nend " + ns + "\n"
    open(name + ".lean","w").write(s)
print(len(T))
