# CF-LIBS numerical regression oracle

Turns the **verified** `CflibsFormal` spec into an executable regression oracle for the
companion numerical pipeline (CF-LIBS-improved): fixtures (`fixtures.json`) that a numerical
implementation must reproduce, where **each check instantiates a proven theorem.**

The fixtures exercise the **multi-element** problem that is the whole point of CF-LIBS (several
chemically distinct elements, each with its own atomic data and partition function `U_s`, tied
together by the closure), across the classic algorithm **and the alternative estimators** the
spec proves sound/equivalent. Two scenarios:

1. **ternary alloy** — 3 chemically-distinct elements, 4 lines each, distinct optical depths:
   checked with the classic inversion, the multi-line **OLS** Boltzmann-plot estimator, the
   **self-absorption** correction (optically-thick input + known `τ`), per-element **temperature**
   recovery, closure, and calibration-free invariance.
2. **two-stage Saha–Boltzmann** — one element in its neutral + ion stages: recover `T` and the
   **electron density `n_e`** from the two stages.

## Files

| file | role |
| --- | --- |
| `Generate.lean` | a computable **`Float` mirror** of the verified forward map, classic inversion, OLS / self-absorbed / Saha estimators; emits `fixtures.json`. Built as `lake exe oracle-fixtures`. |
| `fixtures.json` | a `scenarios` array; each scenario has a `kind`, its data, and `checks` tagged with the theorem each instantiates. |
| `check_fixtures.py` | reference checker (pure stdlib). Self-checks the fixtures; **swap the `IMPL` block for calls into your pipeline** to regression-test it. |

## Regenerate / run

```bash
lake exe oracle-fixtures > oracle/fixtures.json   # regenerate from the Lean mirror
python3 oracle/check_fixtures.py                   # check (exit 0 = pass, 1 = fail)
```

## What is and isn't verified (read this)

The definitions in `CflibsFormal/` are **`noncomputable` and ℝ-valued** (ℝ is not computable),
so they cannot be `#eval`'d. `Generate.lean` re-implements the **same formulas over `Float`**.

- **Verified:** the *formula structure* (each `Float` def matches a proven ℝ def) and the
  *invariants* (the checks below are proven theorems).
- **Not verified:** the IEEE-754 numerical evaluation (`Float ≠ ℝ`). Checks are
  **tolerance-based** (`rtol = 1e-6`) — ample for catching formula/sign/factor/inversion bugs
  (which differ by ≫ that), not a bit-exact comparison.

Inputs are **dimensionless** (matching the spec; `kB = T = 1`, `E` in units of `kB·T`). Feed
your pipeline these exact inputs. Atomic data is synthetic but **distinct per element**; swap in
NIST values (and your unit convention) freely.

## Fixture ↔ theorem map

**Scenario 1 — ternary alloy:**

| check | asserts | proven by |
| --- | --- | --- |
| `forward` | `lineIntensity` with each element's own `(g,E,A)` reproduces its lines (and `U_s` per element) | `ForwardMap.lineIntensity` + `boltzmann_plot_intensity` |
| `round_trip` | `classicDensity(lineIntensity(N)) == N` per element (own `U_s`) | `Classic.classicDensity_recovers` / `classic_sound` |
| `temperature` | 2-line Boltzmann-plot slope recovers `T`, per element | `Classic.classic_temperature_correct` |
| `ols` | OLS regression over **all** lines recovers `N` per element; OLS composition `==` classic/true | `Alt.olsDensity_recovers` / `leastSquares_sound` / `leastSquares_agrees_classic` |
| `self_absorbed` | from optically-thick intensities (`thin·SA(τ)`) + known `τ`, the corrected estimator recovers the true composition | `Alt.selfAbsorbed_sound` |
| `closure` | recovered composition `== N_s/ΣN` and sums to 1, across heterogeneous elements | `Closure.composition_sum_one` / `classic_sound` |
| `calibration_free` | scaling `Fcal` leaves composition unchanged | `Classic.classic_calibration_free` |

**Scenario 2 — two-stage Saha–Boltzmann:**

| check | asserts | proven by |
| --- | --- | --- |
| `temperature` | neutral 2-line slope recovers `T` | `Classic.classic_temperature_correct` |
| `saha` | recover `N_z`, `N_{z+1}` from the two stages; `R = N_{z+1}/N_z`; `n_e = S(T)/R == ` true `n_e`; and `R·n_e == S(T)` | `Saha.electronDensityFromRatio` / `saha_relation` / `electronDensity_antitone` / `SahaInverse.saha_joint_identifiability` |

## Why multi-element (and why a single family is insufficient)

CF-LIBS recovers the composition of *different* elements; each has a distinct partition function
`U_s(T)`, and the de-normalization `N_s = I·U_s/(Fcal·A·g·bf)` uses a **different `U_s` per
element**. A fixture that gave every element the **same** `(g,E,A)` would miss this: dropping or
sharing `U_s` still gives the right composition because the common `U` cancels in
`(N_s/U)/Σ(N_t/U) = N_s/ΣN`. With **distinct** `U_s` it does not cancel — so the multi-element
fixtures catch exactly the bugs the single-family case cannot. (Verified: dropping the
per-element `U_s` fails `round_trip` and corrupts `closure`, whereas it would pass under a single
family.)

**Why forward AND invariant checks:** a *consistent* formula error (e.g. a flipped Boltzmann sign
in BOTH the forward and inverse) cancels in the round-trip/closure checks — only the `forward`
check, comparing to the verified-spec ground truth, catches it. The invariant checks catch
inversion/closure/calibration/`n_e` bugs the forward check cannot. You need both. (Verified: a
wrong thermal-bracket power in the Saha factor fails the `saha` `n_e` check.)
