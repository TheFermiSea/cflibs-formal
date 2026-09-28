---
schema: card/v1
id: dup.decl-a
title: "Synthetic repo-wide fixture: card A claims goodThm"
kind: result
depth: full
summary: >
  Deliberately claims the same headline declaration as card-b.md, to exercise
  check_cards.py's repo-wide one-card-per-declaration check (DUP-DECL).
lean:
  decl: CflibsFormal.goodThm
  reviewed:
    commit: "0000000000000000000000000000000000000000"
    statement_hash: "bfa9efc24eb6f7477c817095c547ad54024160d54b690d7d51dd4de5d707b5bf"
    by: selftest
    method: "synthetic fixture, not a real review"
status:
  lean: proved
  pipeline: none
  pipeline_reliance: none
open_items: []
provenance:
  - docs/theorems/registry/frontier.yaml
updated: 2026-09-28
---

# Card A (duplicate-declaration fixture)
