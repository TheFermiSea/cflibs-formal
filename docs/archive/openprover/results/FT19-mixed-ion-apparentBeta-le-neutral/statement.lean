import Mathlib
import CflibsFormal.InhomogeneityBias
import CflibsFormal.SahaStability

/-!
# FT-19 (c): ion-pair apparent β is at most the neutral-pair apparent β (uniform `n_e`)

Staged queue target, 2026-09-24 audit, frontier FT-19 (assembly), REVISE applied. No new
definitions: `apparentBeta`, `mixedLineIntensity` (`InhomogeneityBias.lean`) and `sahaFactor`
(`Saha.lean`) are used as they stand on main.
-/

open CflibsFormal

namespace Plan.FT19

/-- **Mixed LTE zones at uniform `n_e`: the ion two-line apparent inverse temperature is at
most the neutral one, under an energy anchor.** Zones `z` share one electron density `n_e`,
have temperatures `T z > 0` and neutral columns `NI z > 0`; each zone is in Saha balance, so its
ion column is `NII z = NI z · S(T z)/n_e` with `S = sahaFactor` (neutral levels `gZ, EZ`, ion
levels `gZ1, EZ1`, ion energies measured from the ion ground state). The neutral spectrum is the
mixed optically-thin spectrum of `NI` on the neutral levels, the ion spectrum that of `NII` on
the ion levels. For a neutral pair `EZ i < EZ j` and an ion pair `EZ1 i' < EZ1 j'` with the
anchor `EZ j ≤ EZ1 i'` (the ion pair's lower line lies at or above the neutral pair's upper
line), the ion pair's apparent inverse temperature is at most the neutral pair's, i.e. (both
being positive) `T_app(ion) ≥ T_app(neutral)`.

Chain: `β_ion ≤ ⟨b⟩^{ion}_{EZ1 i'} ≤ ⟨b⟩^{neu}_{EZ1 i'} ≤ ⟨b⟩^{neu}_{EZ j} ≤ β_neu`, using that
the ion zone weight is the neutral zone weight times `2 θ(T)^{3/2} e^{−χ/(k_B T)}/n_e` (the
partition functions cancel), which is strictly increasing in `T` for `χ ≥ 0`.

Scope: REDUCED (uniform `n_e`, LTE per zone, optically thin, two-line pairs, not `n`-line OLS).
The ordering is consistent with the apparent temperatures reported by Aguilera & Aragón (2007,
J. Phys.: Conf. Ser. 59:210, Fe I 9890 K vs Fe II 11400 K) from multi-line plots of a
spatially resolved plasma with varying `n_e`; this theorem does not prove that measurement. -/
theorem mixed_ion_apparentBeta_le_neutral {ζ ι κ : Type*} [Fintype ζ] [Fintype ι] [Fintype κ]
    [Nonempty ζ] [Nonempty ι] [Nonempty κ]
    {kB Fcal me h chi ne : ℝ} {T NI NII : ζ → ℝ}
    {gZ EZ AI : ι → ℝ} {gZ1 EZ1 AII : κ → ℝ}
    (hkB : 0 < kB) (hme : 0 < me) (hh : 0 < h) (hchi : 0 ≤ chi) (hne : 0 < ne)
    (hFcal : 0 < Fcal) (hT : ∀ z, 0 < T z) (hNI : ∀ z, 0 < NI z)
    (hgZ : ∀ k, 0 < gZ k) (hgZ1 : ∀ k, 0 < gZ1 k)
    (hAI : ∀ k, 0 < AI k) (hAII : ∀ k, 0 < AII k)
    (hNII : ∀ z, NII z = NI z * sahaFactor kB (T z) me h chi gZ EZ gZ1 EZ1 / ne)
    (i j : ι) (hij : EZ i < EZ j) (i' j' : κ) (hij' : EZ1 i' < EZ1 j')
    (hanchor : EZ j ≤ EZ1 i') :
    apparentBeta (EZ1 i')
        (Real.log (mixedLineIntensity kB T NII Fcal gZ1 EZ1 AII i' / (gZ1 i' * AII i')))
        (EZ1 j')
        (Real.log (mixedLineIntensity kB T NII Fcal gZ1 EZ1 AII j' / (gZ1 j' * AII j')))
      ≤ apparentBeta (EZ i)
        (Real.log (mixedLineIntensity kB T NI Fcal gZ EZ AI i / (gZ i * AI i)))
        (EZ j)
        (Real.log (mixedLineIntensity kB T NI Fcal gZ EZ AI j / (gZ j * AI j))) := by
  sorry

end Plan.FT19
