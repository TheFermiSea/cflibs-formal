# 06 — Proof, model, and correspondence contracts

[Plan index](README.md)

## Four independent acceptance questions

1. **Kernel validity:** does the actual Lean declaration check under the allowed axioms?
2. **Statement adequacy:** does the statement express the intended mathematical claim without
   assuming its conclusion, omitting nondegeneracy, or exploiting an unintended totalized operation?
3. **Physical faithfulness:** are the supplied laws, constants, units, conventions, and reductions
   appropriate and accurately cited?
4. **Implementation correspondence:** does a particular numerical calculation match the specified
   equations, input domain, and error model? Float fixtures provide regression evidence, not proofs.

Passing one does not discharge the others. Do not use theorem count, no-sorry searches, a generated
catalog, or a numerical match as a substitute for these questions.

## Model assumption ledger

For every physical capstone, maintain a review record with these fields:

| Field | What the reviewer needs |
|---|---|
| Declaration | Fully qualified name and exact source revision |
| State and observable | Physical meaning of every argument and returned quantity |
| Domain | Positivity, finite/nonempty families, nonzero denominators, integrability, rank |
| Supplied equations | Relations taken as hypotheses or definitions rather than derived |
| Derived conclusion | Actual quantified result, including existence versus uniqueness versus convergence |
| Reductions | LTE, finite levels, ion stages, geometry, stationarity, optical depth, common dilution |
| Convention | Energy origin, wavelength/frequency, photon/energy observable, width definition, composition basis |
| Scope and citation | Existing tag plus exact primary-source equation/page; unverified status retained |
| Non-vacuity | A Lean witness satisfying hypotheses jointly, not separate plausible examples |
| Failure boundary | Degenerate counterexample or reason the theorem cannot apply |
| Runtime bridge | Predicate values supplied, checked, or assumed; rounding/enclosure policy |

EXACT means exact within the theorem's modeled statement; it never means experimentally exact or
free of physical assumptions. PURE-MATH theorems may be crucial and should remain so classified.
Do not relabel results merely to make a transitive scope checker pass.

## Conventions to freeze before moving proofs

- Preserve the current `log(I/(g A))` convention and its absorbed calibration factors.
- Keep the explicit `ForwardMapEnergy` conversion separate, including wavelength and geometry
  constants. Do not drop a factor because it cancels in only one downstream ratio.
- Preserve Saha's electron factor, sign of ionization energy, `h` versus reduced-Planck convention,
  and the full thermal bracket raised to `3/2`.
- Distinguish excitation temperature, kinetic temperature, and any supplied common LTE temperature.
- Distinguish Gaussian standard deviation, HWHM, FWHM, Lorentzian width, and Voigt fit parameter.
- Preserve number-density closure unless an explicit mass conversion is proved.
- An additive dimension check does not validate SI/eV/nm/cm conversion constants by itself.
- Preserve deterministic worst-case sums separately from variance/RSS combination. Independence,
  correlation, and zero-mean assumptions are mathematical hypotheses, not numerical defaults.

## Lean-specific migration safeguards

**Signature preservation:** compare fully elaborated types, universe parameters, implicit arguments,
typeclasses, namespaces, and attributes. Identical printed prose or a compiling umbrella import is
insufficient. Protect representative downstream applications of each public theorem.

**Definitional versus propositional equality:** changing a definition to an equivalent expression can
break `rfl`, reduction, simplifier behavior, and computational consumers. State an equality bridge;
change callers before retiring the representation. Check `[simp]` attributes, rewrite orientation,
instances, notation scopes, coercions, and reducibility separately.

**Namespace and audit coverage:** tools currently assume the `CflibsFormal` prefix. Keep that prefix
through the first migration. If a future extraction changes it, update axiom-audit roots and
`ScopeCheck.isCflibs` before trusting results; ensure moved constants cannot evade inspection.

**Imports and metadata:** a moved file needs its new import path, root/topic coverage, scope-tag
module key, generated references, and oracle/upstream consumers updated together. Source parsers
can miss declaration forms. Reconcile metadata with the environment when changing namespaces,
visibility, or declaration syntax. Do not hide untagged declarations behind private/protected forms.

**Axiom policy:** audit the complete chosen declaration closure. A source grep cannot establish it.
Keep `{propext, Classical.choice, Quot.sound}` unchanged. No proof placeholders, `native_decide`,
or custom physical axioms may be introduced to bridge an unfinished phase.

## Numerical correspondence

Keep Lean real-valued definitions and Python float mirrors explicitly distinct. A certificate
predicate in Lean may require exact positivity or a strict rank bound that float evaluation cannot
safely establish near zero. A future certified runtime path needs interval/rounding reasoning and
a sound mapping from checks to hypotheses; it is not achieved by renaming a Boolean “certificate.”

For representation changes, fixtures must cover ordinary inputs, threshold-near inputs, relevant
invalid-domain handling, and conversions. If expected values change, classify the change as a
scientific/convention correction and review it separately from organizational refactoring. Do not
regenerate fixtures merely to make a mismatch disappear.

## Gap annotation policy

Source comments identify missing obligations with stable IDs in [the gap register](09-gap-register.md).
They do not add theorem declarations or weaken existing claims. Each comment must say what the
current result establishes, what remains missing, and the prerequisite model assumptions. A gap is
closed only by reviewed statements, completed proofs, scope/citation updates, and the relevant gates.
A prose promise or an axiom-clean theorem assuming the desired bridge does not close it.
