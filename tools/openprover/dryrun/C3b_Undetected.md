Prove `CflibsFormal.Alt.neutralityScale_undetected` (statement and definitions fixed).

Same setting as `neutralityScale_eq_Fcal`: `lineIntensity kB T N Fcal g E A k = Fcal * A k * population kB T N g E k`, `population kB T N g E k = N * g k * boltzmannFactor kB T (E k) / partitionFunction kB T g E`, so `I s / unitI s = Fcal * N s` when `unitI s > 0`. Here neutrality holds over the observed species plus one undetected species: `ne = (∑ s, N s * R s) + Nu * Ru`.

Claim: `(∑ s, I s * R s / unitI s) / ne = Fcal * (1 - Nu * Ru / ne)` with `0 < ne`.

Proof idea: the sum equals `Fcal * ∑ s, N s * R s = Fcal * (ne - Nu * Ru)`; divide by `ne` and rewrite `(ne - Nu*Ru)/ne = 1 - Nu*Ru/ne` (`field_simp`, `ring`). Only Mathlib and the imported repository modules. No `sorry`, `admit`, `native_decide`.
