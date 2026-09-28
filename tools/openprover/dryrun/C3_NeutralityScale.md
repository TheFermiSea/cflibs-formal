Prove `CflibsFormal.Alt.neutralityScale_eq_Fcal` (the statement and definitions are fixed; do not change them).

Setting: `lineIntensity kB T N Fcal g E A k = Fcal * A k * population kB T N g E k` and `population kB T N g E k = N * g k * boltzmannFactor kB T (E k) / partitionFunction kB T g E` (module `CflibsFormal.ForwardMap` / `CflibsFormal.Boltzmann`), so `lineIntensity` is linear in `N` and in `Fcal`: `lineIntensity kB T N Fcal g E A k = Fcal * N * lineIntensity kB T 1 1 g E A k`. `chargeNeutrality z nDens ne` unfolds to `ne = ∑ s, z s * nDens s` (module `CflibsFormal.Saha`).

Claim: with `hne : 0 < ne`, `hunit : ∀ s, 0 < lineIntensity kB T 1 1 g E A (emit s)`, and neutrality `ne = ∑ s, 1 * (N s * R s)`, the estimator `(∑ s, I s * R s / unitI s) / ne` with `I s = lineIntensity kB T (N s) Fcal g E A (emit s)` and `unitI s = lineIntensity kB T 1 1 g E A (emit s)` equals `Fcal`.

Proof idea: for each `s`, `I s / unitI s = Fcal * N s` (unfold `lineIntensity` and `population`, then `field_simp`/`ring` using `hunit s`), so the sum is `Fcal * ∑ s, N s * R s = Fcal * ne`, and dividing by `ne ≠ 0` gives `Fcal`. Only Mathlib and the imported repository modules are available. No `sorry`, `admit` or `native_decide`.
