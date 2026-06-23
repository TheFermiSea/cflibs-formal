# CF-LIBS numerical regression oracle

Turns the **verified** `CflibsFormal` spec into an executable regression oracle for the
companion numerical pipeline (CF-LIBS-improved): a set of fixtures (`fixtures.json`) that a
numerical implementation must reproduce, where **each check instantiates a proven theorem.**

## Files

| file | role |
| --- | --- |
| `Generate.lean` | a computable **`Float` mirror** of the verified forward map + classic inversion; emits `fixtures.json`. Built as `lake exe oracle-fixtures`. |
| `fixtures.json` | generated fixtures: inputs, expected outputs, and the theorem each check instantiates. |
| `check_fixtures.py` | reference checker (pure stdlib). Self-checks the fixtures; **swap the `IMPL` block for calls into your pipeline** to regression-test it. |

## Regenerate / run

```bash
lake exe oracle-fixtures > oracle/fixtures.json   # regenerate from the Lean mirror
python3 oracle/check_fixtures.py                   # check (exit 0 = pass, 1 = fail)
```

## What is and isn't verified (read this)

The definitions in `CflibsFormal/` are **`noncomputable` and ℝ-valued** (ℝ is not computable),
so they cannot be `#eval`'d. `Generate.lean` re-implements the **same formulas over `Float`**;
each `Float` def mirrors its ℝ counterpart verbatim in formula (only the carrier changes). So:

- **Verified:** the *formula structure* (each `Float` def matches a proven ℝ def) and the
  *invariants* (the checks below are proven theorems).
- **Not verified:** the IEEE-754 numerical evaluation (`Float ≠ ℝ`). Checks are therefore
  **tolerance-based** (`rtol = 1e-6`) — ample for catching formula/sign/factor/inversion bugs
  (which differ by ≫ that), not a bit-exact comparison.

Inputs are **dimensionless** (matching the spec; `E` is in units of `kB·T`, so `kB = T = 1`).
Feed your pipeline these exact inputs. Atomic data is synthetic — the oracle tests the
*formulas and invariants*, not the atomic data; swap in NIST values (and your unit
convention) freely.

## Fixture ↔ theorem map

| check | asserts | proven by |
| --- | --- | --- |
| `forward` | `lineIntensity(constants, N, k)` reproduces each line intensity | `ForwardMap.lineIntensity` (def) + `boltzmann_plot_intensity` |
| `round_trip` | `classicDensity(lineIntensity(N)) == N` (each species) | `Classic.classicDensity_recovers` / `classic_sound` |
| `closure` | recovered composition `== N_s/ΣN` **and** sums to 1 | `Closure.composition_sum_one` / `classic_sound` |
| `calibration_free` | scaling `Fcal` (×1000) leaves the composition unchanged | `Classic.classic_calibration_free` |

**Why both forward and invariant checks:** a *consistent* formula error (e.g. a flipped
Boltzmann sign used in BOTH the forward and inverse) cancels in the round-trip and closure
checks — only the `forward` check, comparing to the verified-spec ground truth, catches it.
The invariant checks catch inversion/closure/calibration bugs the forward check cannot. You
need both. (Verified: injecting `exp(+E/kT)` fails all `forward` checks while the others pass.)
