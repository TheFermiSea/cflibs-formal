# F02M6: equilibrium electron density strictly increasing in temperature

**Status note for the lead (2026-09-24, statement author g2): this target is hand-trivial.** The
4-line composition proof in section 4 passed the queue verifier end to end (`verify.py`: text
checks, compile, `leanchecker` kernel replay, axioms `[Classical.choice, Quot.sound, propext]`,
elaborated type identical). The file is
`staging/2026-09-24/_g2/F02M6-sahaEquilibriumNe-strictMonoOn-temp.proof.lean`. Recommend landing
it by hand rather than spending planner budget. The rest of this dossier is written for a
planner in case it is queued anyway.

**Statement audit (2026-09-24, M6 round): FIX, docstring only; HAND-LAND, do not queue.** The
signature is unchanged. The `hEχ` bullet no longer ties the obligation to "the `chi` used in the
exponent (the lowered value when IPD is modelled)": `chi` here is one temperature-independent
constant, an IPD-lowered `χ − Δχ(n_e, T)` is outside the statement, and no IPD or cutoff policy
is assumed. The `_g2` proof file above still carries the **pre-audit** docstring; land from
`staging/2026-09-24/_hand-land/F02M6-sahaEquilibriumNe-strictMonoOn-temp.proof.lean` (the
corrected `statement.lean` docstring, the same 4-line body, and the auditor's two non-vacuity
witnesses), or copy the docstring from `statement.lean`. Landing order: see section 7.

## 1. Goal

Prove, in the statement file's namespace `Plan.F02M6` (imports: `Mathlib`,
`CflibsFormal.SahaStability`, `CflibsFormal.SahaEquilibrium`; `open CflibsFormal`):

```lean
variable {ι : Type*} [Fintype ι] {κ : Type*} [Fintype κ]

theorem sahaEquilibriumNe_strictMonoOn_temp [Nonempty ι] [Nonempty κ]
    {kB me h chi Ntot : ℝ} {gZ EZ : ι → ℝ} {gZ1 EZ1 : κ → ℝ}
    (hkB : 0 < kB) (hme : 0 < me) (hh : 0 < h) (hchi : 0 ≤ chi)
    (hgZ : ∀ k, 0 < gZ k) (hEZ : ∀ k, 0 ≤ EZ k)
    (hgZ1 : ∀ k, 0 < gZ1 k) (hEZ1 : ∀ k, 0 ≤ EZ1 k)
    (hEχ : ∀ k, EZ k ≤ chi) (hN : 0 < Ntot) :
    StrictMonoOn (fun T => sahaEquilibriumNe (sahaFactor kB T me h chi gZ EZ gZ1 EZ1) Ntot)
      (Set.Ioi 0)
```

Physics: in the reduced single-element, two-stage LTE core at fixed total elemental density,
the self-consistent electron density rises strictly with temperature.

## 2. Definitions (all on main, reused verbatim)

- `CflibsFormal.sahaFactor` (`Saha.lean:68`):
  `2 * (partitionFunction kB T gZ1 EZ1 / partitionFunction kB T gZ EZ)
     * (thermalBracket kB T me h) ^ (3 / 2 : ℝ) * Real.exp (-chi / (kB * T))`.
- `CflibsFormal.sahaEquilibriumNe` (`SahaEquilibrium.lean:90`):
  `(-S + Real.sqrt (S ^ 2 + 4 * S * Ntot)) / 2`, the positive root of `n² = S·(Ntot − n)`.

No new definitions in this target.

## 3. Proof route (Frontier 02 dossier, M6)

`T ↦ S(T)` is strictly increasing on `(0, ∞)` (landed M4), `S(T) > 0` there, and `S ↦ n_e(S)`
is strictly increasing on `(0, ∞)`. Compose: for `0 < T1 < T2`, `S(T1) < S(T2)` with both in
`Ioi 0`, so `n_e(S(T1)) < n_e(S(T2))`.

## 4. Verified proof (passes `verify.py`)

```lean
  intro T1 hT1 T2 hT2 hlt
  have hS1 := sahaFactor_pos (chi := chi) (EZ := EZ) (EZ1 := EZ1) hkB hT1 hme hh hgZ hgZ1
  have hS2 := sahaFactor_pos (chi := chi) (EZ := EZ) (EZ1 := EZ1) hkB hT2 hme hh hgZ hgZ1
  exact sahaEquilibriumNe_strictMono_S hN hS1 hS2
    (sahaFactor_strictMonoOn_temp hkB hme hh hchi hgZ hEZ hgZ1 hEZ1 hEχ hT1 hT2 hlt)
```

## 5. Repo lemmas (exact signatures, `#check`ed on the pinned toolchain)

- `CflibsFormal.sahaFactor_pos [Nonempty ι] [Nonempty κ] {kB T me h chi : ℝ} {gZ EZ : ι → ℝ}
  {gZ1 EZ1 : κ → ℝ} (hkB : 0 < kB) (hT : 0 < T) (hme : 0 < me) (hh : 0 < h)
  (hgZ : ∀ k, 0 < gZ k) (hgZ1 : ∀ k, 0 < gZ1 k) : 0 < sahaFactor kB T me h chi gZ EZ gZ1 EZ1`
  (`Saha.lean:91`).
- `CflibsFormal.sahaFactor_strictMonoOn_temp [Nonempty ι] [Nonempty κ] … (hkB) (hme) (hh)
  (_hchi : 0 ≤ chi) (hgZ) (_hEZ : ∀ k, 0 ≤ EZ k) (hgZ1) (hEZ1 : ∀ k, 0 ≤ EZ1 k)
  (hEχ : ∀ k, EZ k ≤ chi) : StrictMonoOn (fun T => sahaFactor kB T me h chi gZ EZ gZ1 EZ1)
  (Set.Ioi 0)` (`SahaStability.lean:772`).
- `CflibsFormal.sahaEquilibriumNe_strictMono_S {Ntot : ℝ} (hN : 0 < Ntot) :
  StrictMonoOn (fun S => sahaEquilibriumNe S Ntot) (Set.Ioi 0)` (`SahaEquilibrium.lean:218`).
- `CflibsFormal.sahaEquilibriumNe_pos {S Ntot : ℝ} (hS : 0 < S) (hN : 0 < Ntot) :
  0 < sahaEquilibriumNe S Ntot`.

## 6. Pitfalls

- `sahaFactor_pos` leaves `chi`, `EZ`, `EZ1` implicit and not determined by its hypotheses; a
  bare `have := sahaFactor_pos hkB hT1 …` fails with "don't know how to synthesize implicit
  argument". Pin them with named arguments as in section 4, or state the `have` type in full.
- `hT1 : T1 ∈ Set.Ioi 0` is definitionally `0 < T1`; it can be passed where `0 < T1` is expected.
- `StrictMonoOn f s` unfolds to `∀ a ∈ s, ∀ b ∈ s, a < b → f a < f b`.
- Verifier rules: keep the imports, the `variable` line and the theorem signature byte-identical
  (hypothesis names included); no new imports, no `set_option` other than heartbeat/recursion
  limits, no `#` commands; a helper lemma's name must not begin with
  `sahaEquilibriumNe_strictMonoOn_temp`.

## 7. Scope and landing notes

- Two-axis tag: own relation EXACT; `sahaFactor` EXACT (Saha–Eggert (Griem)),
  `sahaEquilibriumNe` REDUCED; predicted published tag REDUCED (cf. `scope-tags.tsv`:
  `sahaEquilibriumNe_strictMono_S` REDUCED, `sahaFactor_strictMonoOn_temp` EXACT).
- `hEχ` is worded as a cutoff obligation on the level list, not the "true for every real atom"
  phrasing of M4's docstring (the deep audit, PS-06, found 202 of 324 raw-database species
  violate it). The M4 docstring rewording itself is RF-10's job.
- `chi` is one temperature-independent constant. An IPD-lowered `χ − Δχ(n_e, T)` moves with `T`
  and `n_e`; this statement does not cover it, and with such a `chi` the closed-form root
  `sahaEquilibriumNe` no longer solves the coupled equation. The docstring therefore asserts no
  IPD or cutoff policy (both are pending owner decisions).
- **Landing order (statement audit, required).** Land together with, or after, RF-10's
  rewording of M4's `hEχ` docstring. On main, `SahaStability.lean:762` still calls `hEχ` "the
  physically universal hypothesis"; if M6 lands in `SahaStability.lean` first, the file
  contradicts itself (M6 calls the same hypothesis a cutoff obligation that raw databases
  violate).
- Landing: `SahaStability` and `SahaEquilibrium` do not import each other.
  `SahaEquilibrium` imports only `Saha`, so adding `import CflibsFormal.SahaEquilibrium` to
  `SahaStability.lean` is acyclic. `OuterLoopModelB.lean` already imports both. Needs a
  `docs/scope-tags.tsv` row and a non-vacuity witness in the file's `Fin 1` style (both of the
  statement auditor's witnesses are in the `_hand-land` file: a `Fin 1` unit instance, and a
  `Fin 2` instance with `EZ = ![0, 9/10] ≤ chi = 1`, so `hEχ` holds non-trivially).
- Optional, upstream (not applied; signature kept): under RF-10, drop `_hchi`/`_hEZ` from
  `sahaFactor_strictMonoOn_temp`, then drop `hchi`/`hEZ` here. Conforming data always
  satisfies them, so they are harmless decoration until then.
