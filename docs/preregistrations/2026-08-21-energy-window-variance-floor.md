# Pre-registration — the energy-window bound on Boltzmann-plot D-optimality

**Frozen at commit:** (not yet frozen — placeholder, `prereg.sh freeze` overwrites this line)

**Status:** DRAFT. Until `./scripts/prereg.sh audit` reports `PASS FROZEN`, nothing
below is a timestamped prediction, and any theorem landed against it is
*exploratory*, not confirmatory.

- **Registrant:** Brian Squires (`squires.b@gmail.com`)
- **Written:** 2026-08-21
- **Intended module:** `CflibsFormal/LineSelectionBound.lean` (does not exist)
- **Predicted scope tags:** P1 `PURE-MATH`, P2 `PURE-MATH`, P3 `REDUCED`
- **Audit command** (scoped — see `scripts/prereg.sh` header for why a bare audit
  is meaningless in this repo):

```sh
./scripts/prereg.sh audit --results CflibsFormal/LineSelectionBound.lean \
    docs/preregistrations/2026-08-21-energy-window-variance-floor.md
```

---

## 0. Disclosure of prior state (REQUIRED — read before trusting the freeze)

A pre-registration is only worth the state of knowledge it was written against.
At the time of writing, `CflibsFormal/LineSelection.lean` **already exists in the
working tree** (uncommitted, authored by a parallel leg). I read it. It contains:

`energySpread`, `energySpread_nonneg`, `energySpreadCert_iff`,
`slopeVariance_le_of_spread_ge`, `slopeVariance_le_iff_spread_le`,
`slopeVariance_lt_of_spread_lt`, `exists_dOptimal_lineSet`, `spreadOn`,
`spreadOn_eq`, `slopeVariance_le_of_spreadOn_ge`, `exists_dOptimal_subset`,
and four `nonvacuity_*` witnesses.

Everything predicted below is deliberately **outside** that list. Specifically,
`LineSelection.lean` proves that `SS_E = ∑ₖ (Eₖ − Ē)²` *ranks* candidate line
sets and that a maximizer *exists* over a finite family — it proves nothing about
**how large `SS_E` can get** or **what the maximizer looks like**. Existence of an
argmax over a finite family is cheap; a quantitative ceiling is not. That gap is
what this registration predicts closing.

*Anything I could have predicted by reading that file is not a prediction. If a
reviewer finds a statement below that is already a corollary of a declaration in
the list above, this registration is void for that statement.*

## 1. The question

Upper-level energies are not free parameters. For a given element and ionization
stage, the lines an instrument can actually resolve occupy a bounded window
`[a, b]` of upper-level energy — set by the spectrometer range, by which levels
have usable transition probabilities, and by self-absorption. So "maximize the
spread" is not achievable without limit. The physically meaningful questions are:

1. Given the window `[a, b]` and `n` lines, **what is the largest achievable
   `SS_E`** — i.e. how good can line selection possibly get?
2. **Which selection attains it?**
3. Therefore, **what is the floor on recovered-temperature variance** that no
   choice of lines within the window can beat?

Question 3 is the one that matters for honest reporting: it converts "we chose
good lines" into "no line choice in this window could have done better than X".

## 2. Predicted statements (THE FROZEN PREDICTIONS)

Notation as in `LineSelection.lean`: `ι` a `Fintype`, `n = Fintype.card ι`,
`energySpread E = ∑ₖ (E k − mean E)²`.

**P1 — the energy-window ceiling (Popoviciu form).**

```lean
theorem energySpread_le_of_mem_Icc {a b : ℝ} (E : ι → ℝ)
    (h : ∀ k, E k ∈ Set.Icc a b) :
    energySpread E ≤ (Fintype.card ι : ℝ) * (b - a) ^ 2 / 4
```

Predicted tag `PURE-MATH`, predicted citation `—`.
**Predicted proof route** (frozen, so a switch is visible): pointwise
`0 ≤ (E k − a)(b − E k)`, sum to `∑ E² ≤ (a+b)·∑E − n·a·b`, then
`∑(E−Ē)² = ∑E² − n·Ē² ≤ n·(b−Ē)(Ē−a) ≤ n·(b−a)²/4` by AM–GM.
I do **not** assume mathlib exposes Popoviciu's inequality in a usable form; if
it does, using it is a simplification, not a deviation.
Confidence: high.

**P2 — attainment by the balanced two-point design.**

```lean
theorem energySpread_eq_of_balanced_two_point {a b : ℝ} (E : ι → ℝ) (S : Finset ι)
    (hcard : 2 * S.card = Fintype.card ι)
    (hE : ∀ k, E k = if k ∈ S then a else b) :
    energySpread E = (Fintype.card ι : ℝ) * (b - a) ^ 2 / 4
```

Predicted tag `PURE-MATH`, predicted citation `—`.
Together P1 + P2 say the ceiling is *sharp* for even `n`: half the lines at the
bottom of the window, half at the top. Confidence: medium-high — the mathematics
is elementary; the risk is that the `Finset`/`if` encoding of "exactly half"
turns out clumsy and I restate it (that restatement would be a §4(e) deviation,
not a silent edit).

**P3 — the variance floor: what no line selection can beat.**

Under the same Gauss–Markov hypotheses `LineSelection.lean` already uses
(zero-mean, homoscedastic `σ²`, pairwise uncorrelated, `L²` ordinate errors):

```lean
theorem slopeVariance_ge_of_energy_window {a b : ℝ} (E : ι → ℝ) (α β σ : ℝ)
    (ε : ι → Ω → ℝ)
    (hwin : ∀ k, E k ∈ Set.Icc a b)
    (hpos : 0 < energySpread E)
    (hL2 : ∀ k, MemLp (ε k) 2 μ)
    (huncorr : ∀ i j, i ≠ j → covariance (ε i) (ε j) μ = 0)
    (hhom : ∀ k, variance (ε k) μ = σ ^ 2) :
    4 * σ ^ 2 / ((Fintype.card ι : ℝ) * (b - a) ^ 2)
      ≤ variance (betaHat E α β ε) μ
```

Predicted tag **`REDUCED`** — *not* `EXACT`. The reduction is the Gauss–Markov
noise model on the Boltzmann-plot **ordinates**. Real ordinates are
`ln(Iλ/(gA))`, so the transformed noise is neither exactly homoscedastic nor
exactly zero-mean, and atomic-data error in `gA` is systematic, not stochastic.
The module docstring must say so. Predicted citation: `—` unless an optimal-design
source is *independently verified* first (see §3).
Confidence: medium — the inequality is P1 fed through the existing
`olsSlope_variance_eq`; the risk is hypothesis plumbing, not mathematics.

## 3. Citation prediction and the verification obligation

I predict all three land with citation `—` (pure linear algebra plus an existing
in-repo variance identity; no new physics claim). If the D-optimality framing is
attributed to an optimal-design text at landing, that source **must be checked
against the actual book/paper first**, not cited from memory. This repo has a
documented citation-defect history — 9 of 23 references defective and 2
apparently fabricated in the 2DCOS work
(`docs/2dcos/adversarial-critique.md`). A citation recorded here is a
*prediction*, never a warrant.

## 4. Deviation protocol (the reason this file is frozen at all)

If a landed theorem differs from §2, the module docstring **must** carry a
`## Deviation from pre-registration` section naming this file, the prediction
number, and the category:

- **(a) Weakened statement** — extra hypotheses or a narrower conclusion.
  Name the added hypothesis explicitly. *This is the Model-B failure mode*
  (`docs/2dcos/ERRATA.md`): a claim quietly retreats and the surrounding prose is
  rewritten to make the retreat look intended. The frozen text above is what makes
  that visible.
- **(b) Weakened scope tag** — e.g. P3 lands `APPROXIMATION`, or only for fixed
  `σ = 1`, or only for `n` even.
- **(c) Not proved** — dropped. Say so; silence is the defect.
- **(d) Vacuity discovered** — e.g. the hypotheses of P3 turn out jointly
  unsatisfiable. Record it; a green proof of a vacuous statement is worthless.
- **(e) Restated** — same mathematical content, different encoding (the P2 risk).
  Show the old and new statements side by side and argue the equivalence.
- **(f) Strengthened** — proved more than predicted. Also recorded; evidence the
  prediction was too timid.

**A green `lake build` is not evidence the prediction was met.** Only a
statement-level diff against §2 is. That is precisely the thing no present-state
gate in this repo can perform.

## 5. What this does NOT claim

- No claim of improved CF-LIBS numerical accuracy. The repo's value is rigor
  (`AGENTS.md`); a variance floor constrains an estimator under a stated noise
  model and nothing else.
- No claim that the balanced two-point design is a good *physical* choice. It is
  D-optimal for a 2-parameter model and simultaneously terrible practice: it
  gives zero leverage to detect non-linearity of the Boltzmann plot, which is the
  main diagnostic for self-absorption and non-LTE. That tension is real and stays
  as a prose caveat, not a scope tag.
- No claim about which lines are physically measurable; `[a, b]` is an input.

## 6. Present-state gates that must still pass at landing

`lake build` · `lake exe axiom-audit --root CflibsFormal` ·
`lake exe runLinter CflibsFormal` · `./scripts/stats.sh` · `./scripts/gen-docs.sh`
(a `docs/scope-tags.tsv` row is required for every new declaration) ·
`lake exe scope-check` · `python3 oracle/check_fixtures.py`.

Plus the temporal gate: the scoped audit command at the top of this file.
