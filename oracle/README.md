# CF-LIBS numerical regression oracle

Turns the **verified** `CflibsFormal` spec into an executable regression oracle for the
companion numerical pipeline (CF-LIBS-improved): fixtures (`fixtures.json`) that a numerical
implementation must reproduce, where **each check instantiates a proven theorem.**

The fixtures exercise the **multi-element** problem that is the whole point of CF-LIBS: a
sample of several **chemically distinct** elements, each with its OWN atomic data `(g, E, A)`
and hence its OWN partition function `U_s(T)`, tied together only by the closure `Σ C_s = 1`.
(A single shared atomic-data family is trivial — see *Why multi-element* below.) The verified
`Classic.classicComposition` takes per-species `g E A : κ → ι → ℝ`, so this is exactly the
generality the spec proves sound.

## Files

| file | role |
| --- | --- |
| `Generate.lean` | a computable **`Float` mirror** of the verified forward map + classic inversion; emits `fixtures.json`. Built as `lake exe oracle-fixtures`. |
| `fixtures.json` | generated fixtures: a `scenarios` array, each with `elements` (per-element `g,E,A,N,u,U,intensities`) and `checks` tagged with the theorem each instantiates. |
| `check_fixtures.py` | reference checker (pure stdlib). Self-checks the fixtures; **swap the `IMPL` block for calls into your pipeline** to regression-test it. |

## Regenerate / run

```bash
lake exe oracle-fixtures > oracle/fixtures.json   # regenerate from the Lean mirror
python3 oracle/check_fixtures.py                   # check (exit 0 = pass, 1 = fail)
```

## What is and isn't verified (read this)

The definitions in `CflibsFormal/` are **`noncomputable` and ℝ-valued** (ℝ is not computable),
so they cannot be `#eval`'d. `Generate.lean` re-implements the **same formulas over `Float`**;
each `Float` def mirrors its ℝ counterpart verbatim in formula. So:

- **Verified:** the *formula structure* (each `Float` def matches a proven ℝ def) and the
  *invariants* (the checks below are proven theorems).
- **Not verified:** the IEEE-754 numerical evaluation (`Float ≠ ℝ`). Checks are
  **tolerance-based** (`rtol = 1e-6`) — ample for catching formula/sign/factor/inversion bugs
  (which differ by ≫ that), not a bit-exact comparison.

Inputs are **dimensionless** (matching the spec; `E` in units of `kB·T`, so `kB = T = 1`).
Feed your pipeline these exact inputs. Atomic data is synthetic but **distinct per element** —
the oracle tests the *formulas and invariants*, not the atomic data; swap in NIST values (and
your unit convention) freely.

## Fixture ↔ theorem map

| check | asserts | proven by |
| --- | --- | --- |
| `forward` | `lineIntensity` with **each element's own** `(g,E,A)` reproduces its line intensities (and `U_s` matches per element) | `ForwardMap.lineIntensity` + `boltzmann_plot_intensity` |
| `round_trip` | `classicDensity(lineIntensity(N)) == N` per element, each inverted with its own `U_s` | `Classic.classicDensity_recovers` / `classic_sound` |
| `temperature` | the slope of a 2-line Boltzmann plot recovers `T`, per element | `Classic.classic_temperature_correct` |
| `closure` | recovered composition `== N_s/ΣN` (true mole fractions) **and** sums to 1, across heterogeneous elements | `Closure.composition_sum_one` / `classic_sound` |
| `calibration_free` | scaling `Fcal` (×1000) leaves the composition unchanged | `Classic.classic_calibration_free` |

## Why multi-element (and why a single family is insufficient)

CF-LIBS recovers the composition of a sample of *different* elements; each element has distinct
energy levels, transition probabilities, and a distinct partition function `U_s(T)`. The
de-normalization `N_s = I·U_s/(Fcal·A·g·bf)` therefore uses a **different `U_s` per element**,
and the closure ties heterogeneous elements together.

A fixture that gave every element the **same** `(g,E,A)` would miss this entirely: dropping
or sharing `U_s` would still give the right composition because the common `U` cancels in
`(N_s/U)/Σ(N_t/U) = N_s/ΣN`. With **distinct** `U_s` it does not cancel — so the multi-element
fixtures catch exactly the bugs the single-family case cannot. (Verified: dropping the
per-element `U_s` from the inversion fails `round_trip` and corrupts `closure` here, whereas
it would pass under a single shared family.)

**Why both forward and invariant checks:** a *consistent* formula error (e.g. a flipped
Boltzmann sign used in BOTH the forward and inverse) cancels in the round-trip/closure checks —
only the `forward` check, comparing to the verified-spec ground truth, catches it. The
invariant checks catch inversion/closure/calibration bugs the forward check cannot. You need
both.
