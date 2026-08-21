---
name: citation-integrity
description: Use BEFORE a constant, sign, inequality direction, functional form, or attributed result enters a `## Literature` docstring in CflibsFormal/, or the citation column of docs/scope-tags.tsv, or docs/citation-whitelist.tsv — and whenever asked to "check the citations", "verify the attribution", "confirm this is what the paper says", or to add/repair a reference anywhere in this repo. Enforces an opened-primary-source rule of evidence and a four-outcome verdict (VERIFIED / CORRECTED / UNVERIFIED / SUSPECT-OR-FABRICATED). Do NOT use for verifying Lean proofs (that is `lake build` + axiom-audit) or for scope-tag grading (that is scope-check).
---

# Citation integrity

## Why this exists (this repo's own failure)

The theorems in `CflibsFormal` cannot be wrong as logic — Lean checks them. Everything that can
still be wrong lives at the boundary between the formalization and the literature: a constant, a
sign, an inequality direction, or **who is claimed to have shown what**. That boundary is where
this project has actually been burned:

- **`docs/2dcos/adversarial-critique.md` §6: nine of twenty-three references defective, two
  apparently fabricated.** "Corsi et al. (2000), *Appl. Spectrosc.* 54(4) 623–633, C-sigma
  graphs" does not exist — its title was lifted from Aragón & Aguilera (2014) and its DOI
  resolves to an unrelated Panne et al. paper. "Moon et al. (2020) Curve of Growth,
  *Spectrochim. Acta B* 164, 105741" was unfindable. Four more DOIs resolved to the wrong paper
  — including **the Noda 1993 reference to Noda's own founding paper**.
- **The "Noda Wronskian" (§3.2).** Model B asserted that "Noda showed the asynchronous
  correlation represents a temporal cross-peak *Wronskian* integral." Noda never framed it that
  way; the term was invented and then load-bearing. A Hilbert transform is not a derivative, so
  the whole flux identity — and the `n_e` elimination resting on it — collapsed.

Both failures share one mechanism: **a citation was produced from memory or from a search-result
snippet, and was then trusted as if a source had been read.** A plausible-looking reference is
exactly what a language model produces when it has not opened anything. This skill exists to make
that step impossible to skip silently.

## Rule of evidence (non-negotiable)

> **A citation counts ONLY when the primary source was OPENED and the specific claimed
> sentence/equation was LOCATED in it.**

Everything short of that is an **assertion**, not evidence:

| Not evidence | Why |
|---|---|
| A search hit / result list entry | Titles and years in a hit list are metadata, not content. The Corsi 2000 fabrication had a plausible title, journal, volume, pages and DOI. |
| An abstract | Abstracts do not contain the constant, the sign, or the equation number you are about to cite. |
| A TLDR / snippet / AI summary | Second-hand paraphrase; the exact coefficient is precisely what paraphrase drops. |
| "I know this paper" / recall | This is how the Noda Wronskian happened. |
| A DOI that resolves | Resolution proves a record exists, not that it is *this* record. Four repo DOIs resolved to the *wrong paper*. |
| Another paper's citation of it | Citation chains propagate errors; that is how the wrong Noda DOI spread. |
| A previous audit's verdict | `AUDIT-VETTED` sanctions *continued* use. A **new** constant/sign/claim needs the source opened again. |

**"Opened" means, per tool:**

- **WebFetch** — fetched the publisher landing page, the full-text HTML, or the PDF, and quoted
  the sentence/equation back. A fetch that returns a paywall stub, a cookie wall, or an
  abstract-only page is **not** opened.
- **arXiv MCP** (`mcp__gpd-arxiv__*`) — `download_paper` + `read_paper` (or `download_source` for
  the LaTeX) and located the equation. `search_papers` / `semantic_search` / `get_abstract`
  alone are **not** opened.
- **Asta / Semantic Scholar** (`asta-literature-search`, `semantic-scholar`, `find-literature`) —
  these are **discovery** tools. They establish that a paper plausibly exists and give you an
  identifier to fetch. On their own they are never evidence for a claim's content. They *are*
  decisive in the negative direction: a thorough Asta + WebSearch miss is the main input to
  SUSPECT-OR-FABRICATED.
- **NotebookLM** (`mcp__notebooklm-mcp__notebook_query`, the CF-LIBS source notebooks) — counts
  as opened **only when the answer returns a quoted passage attributed to a named source in the
  notebook**, and you record which source. A synthesized answer with no quoted passage is a
  summary, not the paper. NotebookLM cannot verify a paper that is not in the notebook.
- **DOI / Crossref** — `https://doi.org/<doi>` and `https://api.crossref.org/works/<doi>`
  establish or refute **metadata** (title, authors, year, journal, volume, pages). This is how
  you catch the "DOI resolves to the wrong paper" class. It never establishes *content*.
- **WebSearch** — discovery and negative evidence only, same status as Asta.

Verify **metadata via Crossref** and **content via the opened full text**. Both, separately. The
Corsi 2000 entry would have survived a content-free metadata check and a metadata-free content
check; it only dies when you do both.

## Trigger

Run this skill **before** any of the following text is written:

1. A **constant** (prefactor, coefficient, exponent) in a `## Literature` docstring — e.g.
   `1.6×10¹²`, `0.5346 / 0.2166`, `(2π mₑ k_B T/h²)^{3/2}`.
2. A **sign** or **inequality direction** attributed to a source — the `+χ` abscissa shift vs the
   subtracted Saha bracket, `n_e ≥ …`, a monotonicity direction, a bias direction.
3. A **functional form** presented as "the published equation".
4. An **attributed result** — "X showed", "following X", "the X criterion". This is the Noda
   Wronskian slot. Attributing a result to an author is a factual claim about that author.
5. Any new or changed value in **`docs/scope-tags.tsv` column 4**.
6. Any new or changed row in **`docs/citation-whitelist.tsv`**.

If you are only restating something already formalized and already cited, no new claim enters and
the trigger does not fire. If you find yourself typing an author's name next to a number, it does.

## The four outcomes — never binary

Every citation you touch ends in exactly one of these. "Fine" and "not fine" is not the
vocabulary; the whole point is that "could not check" is a *reportable outcome*, not a pass.

### VERIFIED
Primary source opened; the specific claimed sentence/equation located.
**Record:** how it was opened (DOI / arXiv id / notebook source name), and *where* in the source
the claim lives (equation number, page, section). Cite the located text in the report.
> `VERIFIED — Olivero & Longbothum (1977), JQSRT 17:233, Eq. (5): the Voigt FWHM approximation
> coefficients 0.5346 and 0.2166 appear exactly as encoded in VoigtWidth.lean. Opened: publisher
> full text via WebFetch.`

### CORRECTED
Source opened; the claim holds but the **metadata in the repo is wrong**. Do not just say
"corrected" — **give the fix**, in full, and say what was wrong.
> `CORRECTED — Noda (1993) DOI in the source draft was …067520, which resolves to a different
> paper. Correct DOI …067694; "Generalized Two-Dimensional Correlation Method Applicable to
> Infrared, Raman, and other Types of Spectroscopy", Appl. Spectrosc. 47:1329. Crossref record
> checked; PDF opened and the sequential-order rules located in §III.`

Also CORRECTED when the source is real and open but **does not support the claim it is cited
for** — say so explicitly and either re-attribute or drop the claim. (Repo precedent: Colgan 2014
is a pure Fe₂O₃ ab-initio spectrum paper and does not support the geological/high-Z matrix-error
claim it was cited for; and `equivWidth_lorentzian_sqrt_sharp` was re-attributed from
Gornushkin 1999 to Ladenburg–Reiche 1913.)

### UNVERIFIED
You could not open the source — paywall, no digital copy, tool failure, out of budget.
**Say so explicitly. Never let this pass silently, and never soften it into a VERIFIED-shaped
sentence.** An unopened source is not a small problem to be tidied away; it is the exact state
that produced this repo's fabrications.

Where it gets recorded so it cannot vanish:
- a row in `docs/citation-whitelist.tsv` with `status = UNVERIFIED` and the reason in the
  evidence column, **and**
- if a claim in a `## Literature` docstring depends on it, a visible qualifier in that docstring
  (e.g. "attribution not verified against the primary source"), **and**
- the outcome stated in your report to the user.

If the claim is load-bearing (a constant that enters a `def`, a sign that enters a theorem
statement), UNVERIFIED means **do not land it** — either verify it or restate the result so it
does not depend on the attribution.

### SUSPECT-OR-FABRICATED
You searched properly and no such paper is findable, or what you found is internally inconsistent
(title belongs to a different paper, DOI resolves elsewhere, author never wrote it, the claimed
result does not exist in the claimed author's work).

**Flag loudly.** Say plainly: *this reference appears not to exist.* Name what you searched
(Asta/Semantic Scholar, WebSearch, Crossref, arXiv) so the negative is auditable.

**Never invent a plausible replacement entry.** Do not "fix" a fabricated citation by supplying
a different paper that sounds right — that is the same failure mode wearing a repair costume. You
may either (a) name a real source you have OPENED that genuinely supports the claim, and mark it
VERIFIED with located evidence, or (b) **remove the claim**. Nothing in between.

This outcome also covers **invented results attributed to real authors** — the Noda Wronskian
case. The paper existed; the result did not. When a claim takes the form "X showed Y", verifying
that X's paper exists is *not* verifying Y. Locate Y in the text or report SUSPECT.

## Repo whitelist discipline

`docs/citation-whitelist.tsv` is the repo's record of citation status. Columns:
`citation <TAB> status <TAB> year <TAB> evidence/provenance`.

Statuses: `VERIFIED`, `CORRECTED`, `AUDIT-VETTED`, `UNVERIFIED`, `SUSPECT`, `CONVENTION`
(a law/equation *name* such as `Boltzmann` or `Saha–Eggert (Griem)`, which has nothing to open).

Rules:

1. **A citation string may enter `docs/scope-tags.tsv` column 4 only if it is on the whitelist.**
   `scripts/check-citations.sh` reports any that are not.
2. **Adding a whitelist row requires running this skill first.** The status you write must be the
   outcome you actually reached. You may add an `UNVERIFIED` row without opening anything —
   that is what the status is for — but you may not write `VERIFIED` without a located
   sentence/equation in the evidence column.
3. **Reuse the exact existing string.** One canonical spelling per source. Variants
   ("Bulajic 2002" vs "Bulajić et al. 2002") fragment the set and defeat the singleton check.
   Check the whitelist for an existing row before minting a new string.
4. **`AUDIT-VETTED` is not a blank cheque.** It records that the 2026-07-09 whole-corpus audit
   (`docs/literature-validation.md`, `reviews/literature-validity-audit.md`) checked that source.
   Continued use in an existing context is sanctioned. A **new** constant, sign, or attributed
   result pinned on that source still requires opening it and promoting the row to `VERIFIED`
   with the located equation.
5. **Never delete a `SUSPECT` row to make a report clean.** Retracted references stay on record
   with their verdict; that is how the repo remembers.
6. **The whitelist is not evidence of existence.** It is a record of what was done. Only
   `VERIFIED` / `CORRECTED` rows carry first-hand evidence, and only in their evidence column.

## Procedure

1. **Name the claim.** Write the exact constant / sign / equation / attributed result, and the
   exact citation string, before searching. If you cannot state the claim precisely, you cannot
   verify it.
2. **Check the whitelist.** Already present as `VERIFIED`/`CORRECTED` *for this same claim*?
   Reuse the string, done. Present as `AUDIT-VETTED`/`UNVERIFIED`, or the claim is new? Continue.
3. **Discover.** Asta / Semantic Scholar / WebSearch / arXiv search for the paper. Get an
   identifier (DOI, arXiv id). *No verdict yet.*
4. **Metadata check.** Crossref (`https://api.crossref.org/works/<doi>`) or the DOI landing page.
   Do title, authors, year, journal, volume, pages match the citation as written? Mismatch →
   heading for CORRECTED or SUSPECT.
5. **Open it.** WebFetch the full text / PDF, or arXiv `download_paper` + `read_paper`, or a
   NotebookLM query that returns a quoted passage from a named notebook source.
6. **Locate the claim.** Find the sentence or equation. Copy it. Compare digit by digit: every
   coefficient, every exponent, the direction of every inequality, which side of the ratio each
   quantity sits on. A `U_{z+1}/U_z` written upside down is a silent physics error.
7. **Assign one of the four outcomes** and record it: whitelist row, docstring text, and report.
8. **Run `scripts/check-citations.sh`** (advisory, exit 0) to catch mechanical fallout — a new
   string that is a variant of an existing one, a singleton, an off-whitelist entry.

## Tools available in this repo

| Tool | Use for | Counts as "opened"? |
|---|---|---|
| `asta-literature-search`, `asta-research`, `semantic-scholar`, `find-literature` | discovery; negative evidence for SUSPECT | **No** |
| `WebSearch` | discovery; negative evidence | **No** |
| `WebFetch` | DOI landing page, Crossref API, full text / PDF | **Yes**, if it returns the actual text |
| `mcp__gpd-arxiv__search_papers` / `semantic_search` / `get_abstract` | discovery | **No** |
| `mcp__gpd-arxiv__download_paper` + `read_paper` / `download_source` | preprint full text | **Yes** |
| `mcp__notebooklm-mcp__notebook_query` (CF-LIBS notebooks) | passages from the curated corpus | **Yes**, only with a quoted passage from a named source |
| `mcp__notebooklm-mcp__source_get_content` | full text of a notebook source | **Yes** |
| Crossref via WebFetch (`api.crossref.org/works/<doi>`) | metadata truth | metadata only |
| `citation-management`, `pyzotero` | BibTeX formatting / metadata handling | **No** |

`docs/2dcos/ERRATA.md` and `docs/2dcos/adversarial-critique.md` (Appendix B) hold the repo's
already-adjudicated corrections — consult them before re-litigating a known-bad reference.

## Reporting

State every outcome. A report that lists only the VERIFIED ones is the failure this skill exists
to prevent.

```
CITATION INTEGRITY — <what was checked>

VERIFIED (n)
  <citation> — <where opened> — <located: eq/page/section> — <claim it supports>
CORRECTED (n)
  <citation as written> → <corrected form> — <what was wrong> — <how confirmed>
UNVERIFIED (n)
  <citation> — <what was attempted> — <why it could not be opened> — <recorded in: …>
SUSPECT-OR-FABRICATED (n)
  <citation> — <what was searched> — <what was found / not found> — <claim now: removed | re-attributed to a VERIFIED source>
```

## Anti-patterns

- Writing a reference that "looks right" because the physics is right. The physics being right is
  not evidence about who published it.
- Upgrading UNVERIFIED to VERIFIED because the paper is famous / standard / obviously exists.
- Replacing a fabricated citation with a guessed real one instead of opening a source or deleting
  the claim.
- Reporting "citations checked" when only some were opened.
- Letting a search snippet's phrasing become the docstring's phrasing.
- Treating `scripts/check-citations.sh` exiting 0 as verification. It is a **string-hygiene**
  check. It cannot open a paper, and it says so in its own header. Only this skill's procedure
  verifies anything.
