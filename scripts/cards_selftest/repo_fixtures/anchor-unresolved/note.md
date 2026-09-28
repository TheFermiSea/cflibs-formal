# Synthetic repo-wide fixture: an unresolved cross-reference anchor

This narrative doc contains a Lean-file-and-declaration cross-reference that does not resolve in
the catalog, to exercise check_cards.py's docs-wide anchor check: see
`NoSuchModule.lean#noSuchDecl` for details.

It also contains a GitHub line-number fragment, [`CflibsFormal/GoodModule.lean#L42`](x), of
exactly the kind the generated Facts block itself links — this must NOT be treated as an
unresolved declaration reference and must NOT be reported (the check's own false-positive
regression test: an earlier version of this checker flagged every such line-number link it had
just generated).
