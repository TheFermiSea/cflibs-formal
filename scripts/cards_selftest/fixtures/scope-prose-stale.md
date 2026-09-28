---
schema: card/v1
id: scope-prose-stale
title: "Synthetic good-reference card (selftest positive control)"
kind: result
depth: full
summary: >
  A synthetic, fully schema-valid card used only to prove that check_cards.py does not reject a
  well-formed card. It is the positive control alongside the deliberately broken fixtures in this
  directory: if this one fails, the checker itself is broken, not the fixtures.
lean:
  decl: CflibsFormal.goodThm
  members:
    - {decl: CflibsFormal.goodHelper, kind: def}
  reviewed:
    commit: "0000000000000000000000000000000000000000"
    statement_hash: "bfa9efc24eb6f7477c817095c547ad54024160d54b690d7d51dd4de5d707b5bf"
    by: selftest
    method: "synthetic fixture, not a real review"
frontier:
  ids: [FT-TEST]
citations:
  - {key: "Good Citation 2020", role: model-source, supports: goodThm}
certificates:
  - {id: C1, relation: building-block}
decisions: [D1]
status:
  lean: proved
  pipeline: none
  pipeline_reliance: none
  certificate: stated
open_items: []
provenance:
  - docs/theorems/registry/frontier.yaml
evidence:
  - {file: "evidence/good/proof.lean", sha256: "4c12697d984bfee61d356494a9b7d9c6e15c8955d5237a71debf0f81508a587c", command: "n/a", result: "n/a"}
updated: 2026-09-28
---

# Synthetic good-reference card

<!-- BEGIN GENERATED facts -->
<!-- END GENERATED facts -->

## 1. Statement

**Hypotheses.** H1 `hx`: a positive real. H2 `hy`: not equal to one.

## 2. Physical meaning

None; synthetic.

## 3. Scope and validity

The relation is **EXACT** (stale: the published tag is REDUCED).

**What it does NOT claim.** This card claims nothing about any physical system; it exists only
to exercise check_cards.py's happy path.

## 4. Proof idea

None; synthetic.

## 5. Role in the composition-extraction pipeline

None; synthetic.

## 6. Status and remaining work

Nothing outstanding.

## 7. Literature

See citations above.

## 8. Provenance

See front matter.
