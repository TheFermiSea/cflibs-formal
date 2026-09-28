Prove `CflibsFormal.Alt.closureEstimate_bias` (statement and definitions fixed).

Setting: `closureEstimate I unitI s = (I s / unitI s) / ∑ t, I t / unitI t`; with `I s = lineIntensity kB T (N s) Fcal g E A (emit s)` and `unitI s = lineIntensity kB T 1 1 g E A (emit s)` one has `I s / unitI s = Fcal * N s` (linearity of `lineIntensity` in `N` and `Fcal` via `population kB T N g E k = N * g k * boltzmannFactor kB T (E k) / partitionFunction kB T g E`), provided `unitI s > 0`.

Claim: for `0 < Fcal`, `0 ≤ Nu`, `0 < ∑ t, N t`, `closureEstimate I unitI s = (N s / (∑ t, N t + Nu)) / (1 - Nu / (∑ t, N t + Nu))`.

Proof idea: the left side is `Fcal * N s / (Fcal * ∑ t, N t) = N s / ∑ t, N t`; the right side simplifies to the same because `1 - Nu/(S+Nu) = S/(S+Nu)` with `S = ∑ t, N t > 0`, so `(N s/(S+Nu)) / (S/(S+Nu)) = N s / S` (`field_simp` with `S + Nu ≠ 0`, `S ≠ 0`, `Fcal ≠ 0`, then `ring`). Only Mathlib and the imported repository modules. No `sorry`, `admit`, `native_decide`.
