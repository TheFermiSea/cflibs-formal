# Foundation audit — the framework under the Cσ / Saha–Boltzmann formalization

Date: 2026-06-26. Scope: the foundational definitions and theorems that `Alt/CSigma.lean` (and the
spec generally) builds on — `Boltzmann`, `Saha`, `ForwardMap`, `Closure`, `Classic`. Triggered by
the build-out of the Saha-coupled cross-stage Cσ master line, which newly depends on `Saha.lean`.

Method: structural search (`ripgrep`; `ast-grep` has no Lean grammar so it was not used here),
executed axiom-audit, and a definition-by-definition cross-check against the CF-LIBS literature
queried from the project's NotebookLM source notebooks ("CF-LIBS" 75 sources; "Formalization
Sources" 3 sources).

## Structural

| Check | Result |
|---|---|
| home-rolled `axiom` declarations | **0** |
| `sorry` / `admit` | **0** |
| `native_decide` (would break axiom-cleanliness via `ofReduceBool`) | **0** |
| `lake exe axiom-audit --root CflibsFormal` | clean — 516 decls, all within `{propext, Classical.choice, Quot.sound}` |

## Definitions vs. notebook-confirmed physics

Every load-bearing definition matches the standard CF-LIBS equations (NotebookLM-confirmed):

| Spec definition | Spec form | Literature form | Verdict |
|---|---|---|---|
| `ForwardMap.lineIntensity` / `population` | `Fcal·A_k·N·g_k·exp(−E_k/kT)/U` | `I = F·C·(g_k A_ki/U)·exp(−E_k/kT)` | faithful (`C ↔ N`) |
| `Boltzmann.boltzmannFactor` | `exp(−E/(kB·T))` | `exp(−E/kT)` | faithful |
| `Boltzmann.partitionFunction` | `∑ g_k·exp(−E_k/kT)` | degeneracy-weighted `U(T)` | faithful |
| `Saha.thermalBracket` | `(2π m_e kB T)/h²` | `(2π m_e kT/h²)` | faithful; `^{3/2}` = the Saha bracket |
| `Saha.sahaFactor` | `2·(U_{z+1}/U_z)·bracket^{3/2}·exp(−χ/kT)` | `2(U_{i+1}/U_i)(2πm_e kT/h²)^{3/2}exp(−χ/kT)` | **exact match** |
| `Closure.composition` | `N_s / ∑N` | `C_s` with `∑C = 1` | faithful |

## Key theorems (statement audit)

- `boltzmann_plot_intensity`: `ln(I/(g_k A_k)) = ln(F·N/U) − E_k/(kT)` — matches the literature
  Boltzmann-plot (slope `−1/kT`, intercept `ln(FN/U)`). ✓
- `Saha.saha_relation`: `n_{z+1}·n_e/n_z = sahaFactor` — the Saha ionization equilibrium. ✓
- `Saha.log_sahaFactor`: `ln S = ln 2 + (ln U_{z+1} − ln U_z) + (3/2)ln(bracket) − χ/(kT)` — the
  full closed form **including the `−χ/(kT)` term** (initially appeared truncated in a tool view;
  confirmed complete in source). This is the load-bearing lemma for the cross-stage Cσ collapse. ✓
- `Closure.composition_sum_one`: `∑ composition = 1`. ✓

## Conclusion

The foundation is **clean and faithful**. No axioms, sorries, or `native_decide`; every definition
the Cσ work rests on matches the standard CF-LIBS equations exactly (in particular the Saha factor
and the thermal bracket the cross-stage collapse uses); the key theorems are non-vacuous and
correctly stated. The Saha-coupled cross-stage Cσ master line was built on this verified base.
