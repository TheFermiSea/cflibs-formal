# Citation whitelist — a short guide

**Single source of truth: `docs/citation-whitelist.tsv`.** This page explains what the columns
mean, how to add a row, and how theorem cards (`docs/theorems/`, D21) cite one. It does not
duplicate the whitelist's own header comments — read those in the TSV for the full status
vocabulary and seeding provenance. Nothing here changes `scripts/check-citations.sh`'s blocking
behavior: this is documentation, not a gate.

## What the whitelist records

A row is **not** proof that a paper exists. It is a record of what was actually *done* to check
it — whether a primary source was opened and a specific claimed sentence or equation was located
in it, per `.claude/skills/citation-integrity/SKILL.md`. Run that skill before adding or changing
any row; it is the only thing in this repo that verifies a citation.

## Columns

| # | Column | Meaning |
|---|---|---|
| 1 | `citation` | The canonical citation string. One spelling per source — check for an existing row before minting a new one (two papers by the same authors in the same year, e.g. the two 2007 Aguilera & Aragón papers, get two distinct strings). This is the **key** cards and `docs/scope-tags.tsv` column 4 cite by. |
| 2 | `status` | `VERIFIED \| CORRECTED \| AUDIT-VETTED \| UNVERIFIED \| SUSPECT \| CONVENTION`. See the whitelist header for what each one means and requires. |
| 3 | `year` | Publication year, or `—` for a `CONVENTION` row (a law/equation name, nothing to open). |
| 4 | `evidence / provenance` | Free text: what was opened, how, and where the claimed content was located (equation/page/section) — or, for `UNVERIFIED`/`SUSPECT`, what was attempted and why it failed. |
| 5 | `doi` | **Added 2026-09-28.** A bare DOI (`10.1016/j.sab.2007.03.024`, no `https://doi.org/` prefix) or, if the source has none, a stable URL. Empty if unknown. **Bibliographic metadata only** — it never carries evidentiary weight and adding one never changes a row's status. Most values were extracted mechanically from a DOI already stated in that row's own evidence column; see the whitelist header for the two rows whose DOI came from Crossref instead. |

## How to add or change a row

1. **Run the citation-integrity skill first.** Name the exact claim (constant, sign, functional
   form, or attributed result) and the exact citation string before searching.
2. **Check the whitelist for an existing row on the same claim.** `VERIFIED`/`CORRECTED` for this
   claim → reuse the string, done. `AUDIT-VETTED`/`UNVERIFIED`, or the claim is new → continue.
3. Discover (Asta/Semantic Scholar/WebSearch/arXiv), check metadata (Crossref/DOI landing page),
   then **open the primary source** (full text, not an abstract) and locate the claim.
4. Write the row with the outcome you actually reached — `UNVERIFIED` is a legitimate, expected
   outcome when a source could not be opened; never leave that outcome unrecorded, and never
   upgrade a status without a located sentence/equation to point to.
5. Run `scripts/check-citations.sh`. It is advisory string-hygiene except for one blocking check
   (a `docs/scope-tags.tsv` citation with no whitelist row, or whitelisted `SUSPECT`) — it cannot
   verify anything by itself.

Keep every existing row's status unless you have new evidence for *that same claim*; do not
downgrade or upgrade without saying why in the evidence column.

## How cards cite by key

A theorem card's `citations[]` front-matter entries are `{key, role, supports, locator?}`
(`docs/theorems/` schema, D21):

- **`key`** must be an existing whitelist row's citation string, exactly. Cards never restate the
  bibliographic string, DOI, status or evidence — those live once, here.
- **`role`** is one of `model-source \| estimator-context \| consistent-with-measurement \|
  prior-art \| corroborating \| convention`.
- **`locator`** (e.g. an equation or page number within the source) is allowed **only** when the
  row's status is `VERIFIED` or `CORRECTED` — a card cannot point a reader at "Eq. (5)" of a
  source nobody has opened.
- A source not cited by the Lean module it appears on may only be attached with role
  `corroborating`, and only if its whitelist row is `VERIFIED` or `CORRECTED`.
- A row whitelisted `SUSPECT` may not back any card citation.

The card validator (`scripts/check_cards.py`, when it lands) checks the `key`/`role`/`locator`
rules above mechanically; it does not and cannot verify a source's content — that is still the
citation-integrity skill's job, run once, at the whitelist row.

## What `scripts/check-citations.sh` does and does not prove

It is offline, dependency-light (bash + python3 stdlib) and reads only this repo. It proves
string-level facts — which citations are off-whitelist, whitelisted `SUSPECT`, singleton,
textually similar to another string, or short of `VERIFIED`/`CORRECTED` — plus, now, how many
whitelist rows carry a `doi` value. **It cannot open a paper, confirm a DOI resolves to the
correct record, or catch an invented result attributed to a real author** (the failure mode
behind `docs/2dcos/adversarial-critique.md`'s "Noda Wronskian"). A clean run means no string-level
anomaly was found, never that any citation has been verified.
