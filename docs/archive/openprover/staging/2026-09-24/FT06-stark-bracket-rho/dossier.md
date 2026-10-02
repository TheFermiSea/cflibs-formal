# FT06-stark-bracket-rho: planning dossier

*Source: deep audit 2026-09-24 (`docs/research/audit-2026-09-24/REPORT.md` §5 FT-06, queue
decomposition item 2), the verifier's written-out statement **plus two guards** (`hnRef`, `hne`)
without which that statement is false (Lean-checked counterexamples in §5). Group g3, priority 10.
Toolchain: Lean / mathlib v4.33.1 (the built `lean-main` checkout). Every Lean snippet below was
compiled against that checkout on 2026-09-24.*

## 1. Goal

Statement file: `statement.lean`, namespace `Plan.FT06`, imports `Mathlib` and
`CflibsFormal.StarkBroadening`, `open CflibsFormal`. No section variables.

```lean
theorem stark_bracket_rho {w ρw kOpac wTrue nRef neTrue widthMeas : ℝ} (hw : 0 < w)
    (hρ : 1 ≤ ρw) (hk : 0 < kOpac) (hnRef : 0 < nRef) (hne : 0 ≤ neTrue)
    (hwT : w / ρw ≤ wTrue ∧ wTrue ≤ w * ρw)
    (hopac : starkFWHM wTrue nRef neTrue ≤ widthMeas)
    (hbudget : widthMeas ≤ kOpac * starkFWHM wTrue nRef neTrue) :
    starkDensity w nRef widthMeas / (kOpac * ρw) ≤ neTrue ∧
      neTrue ≤ starkDensity w nRef widthMeas * ρw
```

Physics: linear electron-impact Stark width `FWHM = 2·w_true·n_e/n_ref`; tabulated `w` graded to a
factor `ρ_w` of the true parameter; measured width between the true Stark width and `kOpac` times
it. Conclusion: `n_S/(kOpac·ρ_w) ≤ n_e ≤ n_S·ρ_w` with `n_S = starkDensity w nRef widthMeas`.

## 2. Definitions (in `CflibsFormal/StarkBroadening.lean`)

```lean
-- :86
noncomputable def starkFWHM (w nRef ne : ℝ) : ℝ :=
  2 * w * (ne / nRef)
-- :94
noncomputable def starkDensity (w nRef width : ℝ) : ℝ :=
  nRef * width / (2 * w)
```

Also available from that import: `starkDensity_recovers (hw : w ≠ 0) (hnRef : nRef ≠ 0) :
starkDensity w nRef (starkFWHM w nRef ne) = ne` and `starkFWHM_strictMono`. The `ρ_w = 1` prior
art (`starkDensity_brackets_true`, `starkDensity_mono_width`) lives in `StarkOpacityGuard`, which
is **not** imported and must not be added. At `ρ_w = 1` the target is that prior art
restricted to `n_e ≥ 0`: the prior art does not need `hne` (at `(w, nRef, k, n_e, W) =
(1, 1, 1, −1, −2)` its hypotheses and conclusion both hold), and `hne` is needed only once
`ρ_w > 1`.

## 3. The math

Write `W = widthMeas`. `hopac`, `hbudget` multiplied by `nRef > 0`:
`2·wT·n_e ≤ W·nRef ≤ kOpac·2·wT·n_e`. With `n_S = nRef·W/(2w)`:

- lower end: `n_S ≤ kOpac·wT·n_e/w ≤ kOpac·ρ_w·n_e` (uses `wT ≤ w·ρ_w` and `n_e ≥ 0`);
- upper end: `n_S ≥ wT·n_e/w ≥ n_e/ρ_w` (uses `w ≤ wT·ρ_w`, i.e. `w/ρ_w ≤ wT`, and `n_e ≥ 0`).

## 4. Proof route (compiled as a whole)

```lean
  obtain ⟨h1, h2⟩ := hwT
  have hρ0 : 0 < ρw := by linarith
  have hwT0 : 0 < wTrue := lt_of_lt_of_le (div_pos hw hρ0) h1
  have h1' : w ≤ wTrue * ρw := by rwa [div_le_iff₀ hρ0] at h1
  unfold starkDensity
  unfold starkFWHM at hopac hbudget
  have hA : 2 * wTrue * neTrue ≤ widthMeas * nRef := by
    have := mul_le_mul_of_nonneg_right hopac hnRef.le
    rwa [mul_assoc, div_mul_cancel₀ _ hnRef.ne'] at this
  have hB : widthMeas * nRef ≤ kOpac * (2 * wTrue * neTrue) := by
    have := mul_le_mul_of_nonneg_right hbudget hnRef.le
    rwa [mul_assoc kOpac, mul_assoc (2 * wTrue), div_mul_cancel₀ _ hnRef.ne'] at this
  constructor
  · rw [div_le_iff₀ (by positivity), div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right h2 hne, hk]
  · rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right h1' hne]
```

If a rewrite misfires after a mathlib `simp`-normal-form difference, the robust fallback is:
clear denominators by hand (`div_le_iff₀`, `le_div_iff₀` with the positivity facts `0 < w`,
`0 < ρw`, `0 < kOpac`, `0 < nRef`) and give `nlinarith` the two product facts
`mul_le_mul_of_nonneg_right h2 hne` and `mul_le_mul_of_nonneg_right h1' hne`.

## 5. Why `hnRef` and `hne` are in the statement (evidence, not for the candidate)

The audit verifier's revised statement omitted both guards and is false. Lean-checked
(`staging/2026-09-24/_plan/stmts/FT06-guards-evidence.lean`, exit 0, no messages):

```lean
-- without 0 < nRef and 0 ≤ neTrue: lower end fails at (w,ρ,k,wT,nRef,ne,W) = (1,1,2,1,−1,−1,2)
-- with 0 < nRef but without 0 ≤ neTrue: upper end fails at (1,2,1,1,1,−1,−2)
example : ¬ (∀ w ρw kOpac wTrue nRef neTrue widthMeas : ℝ, 0 < w → 1 ≤ ρw → 0 < kOpac →
    0 < nRef → (w / ρw ≤ wTrue ∧ wTrue ≤ w * ρw) → starkFWHM wTrue nRef neTrue ≤ widthMeas →
    widthMeas ≤ kOpac * starkFWHM wTrue nRef neTrue →
    (starkDensity w nRef widthMeas / (kOpac * ρw) ≤ neTrue ∧
      neTrue ≤ starkDensity w nRef widthMeas * ρw)) := by
  intro H
  have := (H 1 2 1 1 1 (-1) (-2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num [starkFWHM]) (by norm_num [starkFWHM])).2
  norm_num [starkDensity] at this
```

Also checked here: `hρ` is load-bearing beyond making `hwT` satisfiable: at `ρ_w = 0`, Lean's
`w/0 = 0` admits `w_true = 0`, and `(w,ρ,k,wT,nRef,ne,W) = (1,0,1,0,1,1,0)` breaks the upper end.
Both guards are physically trivial (`n_ref > 0`, `n_e ≥ 0`).

The `(1,1,2,1,−1,−1,2)` counterexample (first comment line above; first example in the evidence
file) also violates `hne`, so it shows only that dropping **both** guards is false, not that
`hnRef` is needed on its own. Isolating witnesses (statement
audit, `staging/2026-09-24/_statement-audit/ft06_probe.lean`, exit 0): without `hnRef` but with
every other hypothesis, `hne` included, the lower end fails at `(1, 1, 1/2, 1, −1, 1, −2)`, and
`nRef = 0` (Lean's `x/0 = 0` inside `starkFWHM`) breaks the upper end at `(1, 1, 1, 1, 0, 1, 0)`.
`hk` is not load-bearing (`_statement-audit/ft06_noK.lean`, exit 0: the conclusion holds without
it; for `n_e > 0`, `hopac` and `hbudget` force `0 < kOpac`, and at `n_e = 0` both ends are
`0 ≤ 0`). It stays in the statement for readability.

Non-degenerate witness (`ft06_probe.lean`): `(w, ρ_w, kOpac, w_true, nRef, n_e, widthMeas) =
(1, 2, 3/2, 1, 1, 1, 3)` gives `n_S = 3/2` and the bracket `[1/2, 3] ∋ n_e = 1`.

## 6. Mathlib lemmas (all resolved in v4.33.1)

`div_le_iff₀`, `le_div_iff₀`, `div_pos`, `div_mul_cancel₀`, `div_mul_eq_mul_div`, `mul_assoc`,
`mul_le_mul_of_nonneg_right`, `lt_of_lt_of_le`; tactics `nlinarith`, `positivity`, `linarith`.

## 7. Pitfalls and verifier rules

- `hne` is used only through the product facts (`h2 * n_e`, `h1' * n_e`); `nlinarith` needs them
  supplied as hints.
- Keep the statement header verbatim (two imports, `open CflibsFormal`, `namespace Plan.FT06`) and
  the target signature text up to `:=`; state it with `theorem`; do not name a helper
  `stark_bracket_rho'`.
- Forbidden: `sorry`, `admit`, `native_decide`, `axiom`, `macro`/`syntax`/`elab`, `#`-commands,
  `set_option` other than the heartbeat/recursion limits.

## 8. Scope and consumers

Scope (two-axis): relation PURE-MATH (algebra given the premises); `starkFWHM` REDUCED (linear
electron-impact law; ion broadening not modelled); published REDUCED. Citation: Griem 1974
(whitelisted). `hwT`, `hopac`, `hbudget` are assumed inputs (C14-style refusal note at landing).
Name is descriptive; no certificate number (owner decision pending). Consumers: the two-diagnostic
McWhirter certificate for [backlog-id], [backlog-id]/[backlog-id], [backlog-id]; `_resolve_ne` must keep both `n_e`
sources.
