# Theorem-card schema v1

Normative schema for `docs/theorems/<id>.md`. A card is the curated source of truth for what
cannot be derived from the Lean environment: the LaTeX statement, the physics, the scope
narrative and the pipeline role. Everything else (line numbers, tags, axioms, citation status) is
generated — see [Generated vs. curated](#generated-vs-curated) below. `scripts/check_cards.py`
enforces this schema; this document and the checker must agree, and the checker wins on any
dispute.

Design source: `IA-proposal.md` §2 (owner decision D21). Cross-references: D23 (disclosure), D24
(review policy), `docs/decisions.md`.

## Front-matter keys

YAML front matter, fenced by `---`. `R` = required, `O` = optional, `C` = conditional (required
when the stated condition holds).

| Key | R/O/C | Type / vocabulary | Notes |
|---|---|---|---|
| `schema` | R | literal `card/v1` | |
| `id` | R | `^[a-z0-9]+(\.[a-z0-9-]+)+$`, equal to the filename stem | Stable. A rename adds the old id to `supersedes`, never silently drops it |
| `title` | R | string | |
| `kind` | R | `result \| family \| counterexample \| model` | `family` = a headline theorem plus members, documented together |
| `depth` | R | `full \| brief` | `brief` cards have no Lean-vs-LaTeX narrative beyond §1/§3/§6 (see [Body sections](#body-sections)); a result with no card at all gets a generated stub, not a `depth` value |
| `summary` | R | string, ≤ 3 sentences | The text an agent or a pipeline-side reader reads first |
| `lean.decl` | R | fully qualified Lean name | The headline declaration. Must resolve uniquely in `docs/catalog.jsonl` |
| `lean.members` | O | list of fully qualified names | Each gets a `§1.x` subsection (`§1.6+`); resolved the same way |
| `lean.reviewed` | R | `{commit, statement_hash, by, method}` | The LaTeX-against-Lean audit record — see [Statement-hash workflow](#statement-hash-workflow) |
| `lean.not_to_confuse_with` | O | list of fully qualified names | Declarations that sound related but are not what this card documents |
| `frontier.ids` | C | list of registry ids, e.g. `FT-19`, `F02-M6` | Required exactly when `lean.decl` (or a member) appears in `registry/frontier.yaml`'s `landed` list |
| `frontier.part` | O | string, e.g. `"(i)"` | Which lettered/numbered sub-claim of the frontier item this card covers |
| `frontier.pr` | C | list of integers | The landing PR number(s) |
| `frontier.landing_commits` | C | list of `{sha, what}` | More than one entry when a result moved after landing |
| `frontier.verification` | C | list of `{decl, route: queue\|hand-land\|scratch-land, record}` | `record` is a repo-relative archive path (e.g. under `docs/archive/openprover/`) to a `verdict.json` or dossier. **Never** a node name, an hour count or a planner cost — see [Disclosure rules](#disclosure-rules-d23) |
| `citations[]` | O | list of `{key, role, supports, locator?}` | `key` must be a row in `docs/citation-whitelist.tsv`. `role` ∈ `model-source \| estimator-context \| consistent-with-measurement \| prior-art \| corroborating \| convention`. `locator` (a section/page pointer) is allowed only when the whitelist row's status is `VERIFIED` or `CORRECTED`. A source not cited by the Lean module's own docstring may be attached only with role `corroborating`, and only if `VERIFIED`/`CORRECTED` |
| `pipeline[]` | O | list of `{repo, ref, path, symbol, anchor_text, relation, note}` | `ref` is `main@<sha>` or `<branch>@<sha>`. `relation` ∈ `implements \| mirrors \| assumes \| tension \| narrows \| proposed \| none`. No `drift` field — drift is a validator *output*, never authored |
| `certificates[]` | O | list of `{id, relation}` | `id` resolves in `registry/certificates.yaml`. `relation` ∈ `implements \| building-block \| premise \| narrows \| proposes-replacement` |
| `decisions` | O | list of `D<n>` | Resolved against `docs/decisions.md` |
| `status.lean` | R | `proved \| partial \| stated \| parked` | |
| `status.pipeline` | R | `none \| referenced \| wired \| tested` | |
| `status.pipeline_reliance` | R | `none \| implicit \| explicit` | `implicit` = pipeline code computes consistently with the conclusion without naming it |
| `status.certificate` | C | `n/a \| not-implemented \| stated \| wired` | Required when `certificates[]` is non-empty |
| `open_items[]` | R (may be `[]`) | list of `{kind, text, ref?}` | `kind` ∈ `lean \| docstring \| citation \| pipeline \| model-row \| owner-decision`. `ref` is a queue target id, an issue URL, or a sub-id such as `FT-19d` |
| `provenance[]` | R | list of repo-relative path, `path#anchor`, or PR URL | E.g. `docs/archive/openprover/2026-09-27/FT19-…/dossier.md` |
| `evidence[]` | O | list of `{file, sha256, command, result}` | `file` lives under `docs/theorems/evidence/<id>/`, outside any `lean_lib` root; replayed weekly |
| `updated` | R | ISO date | |
| `supersedes` | O | list of old ids | |

**Never typed by hand** (all rendered into the generated Facts block; a card that hand-types one
of these fails `check_cards.py`): `lean.module`, `lean.line`, `lean.ref`, `lean.commit`,
`lean.axioms`, `scope.*`, `citations[].whitelist_status`/`whitelist_line`/`ref`/`metadata_checked`,
`used_by`, `depends_on.statement`, `pipeline[].drift`.

## Body sections

Fixed order, `##` (H2) headings. Every H2 is required for `depth: full`. `depth: brief` needs only
§1, §3 and §6.

0. *(generated, not a heading)* — the **Facts block**, placed directly under the title, between
   `<!-- BEGIN GENERATED facts -->` / `<!-- END GENERATED facts -->` markers. Contains, per
   declaration (headline then each member): kind, a relative link to
   `CflibsFormal/<File>.lean#L<n>`, the pretty-printed statement, own→published scope tag with
   `via`, the citation-whitelist status, axioms, used-by count, and the current statement hash
   against `lean.reviewed.statement_hash`. Regenerated by `scripts/gen_cards.py`; never hand-edited.
1. **Statement.**
   - 1.1 Symbols — table: symbol, Lean name, meaning.
   - 1.2 Definitions used.
   - 1.3 Hypotheses — every one of them, labelled `H1`, `H2`, …, each naming its Lean binder in
     backticks (this is the binder-coverage check `check_cards.py` runs against
     `lean.reviewed`'s `forallTelescope` binder list).
   - 1.4 Conclusion.
   - 1.5 Lean correspondence — binder → label table, plus any Lean convention that matters to
     reading the statement (`a / 0 = 0`, `rpow` vs `^`, closed vs. open intervals).
   - 1.6+ — one subsection per `lean.members` entry, same shape as 1.1–1.5 scaled to that member.
2. **Physical meaning.**
3. **Scope and validity.**
   - The tags line (generated sentence: own tag → published tag, `via`).
   - Idealizations encoded.
   - **What it does NOT claim** — required, non-empty, every card.
   - Hypothesis sharpness and non-vacuity — a witness, or a pointer to one under `evidence[]`.
4. **Proof idea**, naming the Lean lemmas and helpers actually used.
5. **Role in the composition-extraction pipeline.**
   - Current state.
   - Proposed use.
   - **What it would change** — required. Per `AGENTS.md`: rigor, not accuracy. Never pitch a card
     as improving measurement accuracy.
   - How it would be validated — falsifiable, with its falsification arm stated.
6. **Status and remaining work.** Mirrors `open_items[]`; every entry there gets a line here.
7. **Literature.** Roles only, in prose. The bibliographic string, DOI and verification status are
   never retyped here — they live once in `docs/citation-whitelist.tsv` and are rendered.
8. **Provenance.** Mirrors `provenance[]`.

### Claim-status markers

Put one in prose wherever a claim is not the Lean statement itself:

- `[proved: decl]` — a different, already-landed declaration backs this sentence.
- `[scratch: evidence/<file>]` — checked in scratch Lean/Python under this card's `evidence/`, not
  landed in `CflibsFormal/`.
- `[derivation, unchecked]` — the card author's own algebra, not independently verified.
- `[numerics: evidence/<file>]` — a numerical claim (a root, a minimum, an enclosure) backed by a
  replayable script under `evidence/`.
- `[cited: key, locator]` — attributed to a whitelist source.

`check_cards.py` checks only that a referenced declaration or evidence file exists — whether the
marker is the *honest* one for the claim is a review judgment (D24), not something the linter can
grade.

### GitHub math rules

- `$$` display math on its own lines; never mix inline `$…$` across a table cell boundary.
- No math in a table cell that itself contains a literal `|` (breaks the row).
- Write `\le`, `\ge`, `\ne`, never a bare `<`/`>` immediately before a letter (GitHub's Markdown
  parser can read it as a tag).
- `\texttt{}` for Lean identifiers written inside math mode; backticks for a Lean identifier in
  prose.

GitHub rendering of these rules was **not verified in a browser** when Phase 1 tooling was written
(pass-2 synthesis, 2026-09-28). The first cards PR must be checked in GitHub's PR preview before
the rest of Phase 1 is authored against this schema.

## Id convention

`<registry-id>.<slug>` for a card that documents a frontier item, e.g.
`ft19.ion-apparent-temperature`, `ft14i.kirchhoff-source-planck`. `<module>.<slug>` otherwise, e.g.
`certificates.energy-spread-rank`. The filename (minus `.md`) equals `id`, enforced by
`check_cards.py`. A card that is renamed keeps its old id(s) in `supersedes`; nothing that once
resolved should silently 404.

## Frontier numbering: `FT-NN` vs. `Fnn`

Two independent numbering schemes exist in this repo. Do not conflate them in new prose.

- **`FT-NN`** (`FT-01` … `FT-20`, plus `F02-M6`) means the **2026-09-24 audit slate**:
  `docs/research/audit-2026-09-24/frontier.json` and `REPORT.md` §5. This is the id space
  `registry/frontier.yaml` is keyed on, and the one Phase-1 cards cite in `frontier.ids`.
- **`Fnn`** (bare `F01`…`F13`, e.g. `F02`) means a **legacy planning dossier**,
  `docs/frontiers/NN-*.md`, predating the 2026-09-24 audit.
- The two schemes are related only where `registry/frontier.yaml`'s `legacy_crosswalk` field says
  so; most `FT-NN` items have no `Fnn` counterpart, and most `Fnn` dossiers were never re-audited
  into an `FT-NN` id. `check_cards.py` rejects the ambiguous short form — the word "frontier"
  immediately followed by a bare number, with nothing marking which scheme is meant — anywhere in
  new card prose; write `FT-01` or `F01` (docs/frontiers/01-…) explicitly instead.
- `F02-M6` is a milestone of the legacy `F02` dossier (`docs/frontiers/02-saha-monotonicity.md`
  §M6) that was landed directly, without going through the 2026-09-24 audit; it is tracked in
  `registry/frontier.yaml` alongside the `FT-NN` ids because it is a headline landed result, not
  because it is an `FT-NN` item.

## Generated vs. curated

| Curated (typed by a human/agent, reviewed) | Generated (never hand-typed; regenerated by tooling) |
|---|---|
| This schema; `_template.md`; card prose (§1–§8 above); `lean.reviewed`, `citations[]`, `pipeline[]`, `certificates[]`, `status.*`, `open_items[]`, `provenance[]`, `evidence[]` | The Facts block inside each card; `docs/catalog.jsonl`; `docs/theorem-catalog.md` / `docs/module-reference.md`'s line numbers and card column; `docs/theorems/README.md` (index); `docs/theorems/open-items.md`; `docs/graph.json` |
| `docs/scope-tags.tsv`, `docs/citation-whitelist.tsv` (curated spines, unchanged by this schema) | `docs/scope-published.tsv` (existing generator) |
| `registry/frontier.yaml`, `registry/certificates.yaml`, `registry/cards.yaml` (small, hand-maintained; built once from source documents, then kept current by hand as results land) | — |

A card must never retype a declaration's line number, its axiom list, its scope tag, or a
citation's bibliographic string/DOI/status — those come from the catalog, `scope-tags.tsv`/
`scope-published.tsv`, and `citation-whitelist.tsv` respectively, and are rendered into the Facts
block or the Literature section by `scripts/gen_cards.py`.

## Statement-hash workflow

`lean.reviewed.statement_hash` records the exact Lean statement the card's LaTeX was audited
against. It is computed **by scripts, not by Lean**:

```
statement_hash = sha256(
    for headline, then each member in card order:
        name + "\n" + type + "\n" + ",".join(binders) + "\n"
)
```

where `type` is the declaration's type pretty-printed with fixed options
(`pp.fullNames true`, `pp.numericTypes true`, `pp.unicode.fun true`, width 100 — the same options
`tools/ExportCatalog.lean` uses for `docs/catalog.jsonl`'s `type` field, so the two are always
computed from the same string) and `binders` is the outermost forall-binder name list from
`forallTelescope` (anonymous binder → `_`).

**Workflow.** A Lean PR that changes a carded declaration's statement changes its `type` in
`docs/catalog.jsonl`, which changes the hash `check_cards.py` recomputes from the catalog. That no
longer equals the card's stored `lean.reviewed.statement_hash`, and CI fails with "LaTeX must be
re-reviewed." The author or the card-review agent then re-checks §1 and §3 of the card binder by
binder against the new statement, runs `scripts/gen_cards.py --stamp <id>` to recompute and write
the new hash plus `commit`/`by`/`method`, and commits both the card and the (regenerated) Facts
block together. A toolchain bump that changes only pretty-printing (no statement change) re-stamps
in bulk, but only after a diff review of the newly printed statements — the stamp step is never
run blind.

## Disclosure rules (D23)

cflibs-formal is public; CF-LIBS-improved is private. A card, its evidence, and anything under
`docs/archive/openprover/` may:

- name CF-LIBS-improved **file paths and function/class symbol names** (`pipeline[].path`,
  `.symbol`, `.anchor_text` as a short text snippet identifying the anchor, not a code excerpt);
- describe what that code does in the card author's own prose.

A card, its evidence, and the archive may **not**:

- quote CF-LIBS-improved source code (no fenced code block copied from the private repo — describe
  it, or cite `path#symbol` and let the reader with access open it);
- cite a CF-LIBS-improved backlog id — `BL-xx`, `R#-xx`, the gap-fill-round ids, `TS-xx`, `SC-xx`,
  `W3-x` — these live only on the unmerged, private `overhaul/2026-09` branch and are dropped, not
  paraphrased, from any curated field);
- name a machine/host, a proof-queue node id, wall-clock hours, or a planner dollar cost anywhere
  (`frontier.verification[].record` points to a *scrubbed* archive file instead — see
  `docs/archive/openprover/README.md`);
- include an absolute local filesystem path: a per-user home-directory prefix on Linux or macOS,
  or a Windows drive letter. `scripts/check_cards.py` greps every card and every file in its
  `evidence/<id>/` directory for these patterns, for private IPv4 addresses and for the backlog-id
  forms above, and fails closed — write paths repo-relative (`CflibsFormal/Foo.lean`), never
  rooted at a user's home directory. Host names are not listed in the (public) checker, since the
  list would itself disclose them: a maintainer keeps them in a git-ignored `.disclosure-denylist`
  (one regex per line; or `CARDS_DENYLIST=<file>`), which the checker reads when present.

## Review rules (D24)

Every card is **drafted by one agent** and **adversarially reviewed by a different agent**: the
reviewer re-derives the LaTeX from the Lean statement binder by binder (§1.3/§1.5), checks the
physics narrative (§2–§4) against the cited literature and the pipeline claims (§5) against the
named `path#symbol` anchors, and checks that §3's "does not claim" is actually non-vacuous and
that every `citations[].key` and `pipeline[]` anchor resolves. Only after that review does
`scripts/gen_cards.py --stamp <id>` write `lean.reviewed` and lock the statement hash — stamping
before review defeats the mechanism in [Statement-hash workflow](#statement-hash-workflow).

The repository owner **spot-checks every card that carries an `EXACT` relation tag** (own or
published, per `docs/scope-tags.tsv`/`scope-published.tsv`'s two-axis rule, D15) before it merges
to `main`. A card whose headline or any member publishes `EXACT` is not "done" (per `AGENTS.md`'s
definition of done) until that spot-check has happened; note it as an `open_items[]` entry of kind
`owner-decision` until it has.
