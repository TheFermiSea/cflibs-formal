# Refactoring execution handbook

[Plan index](../README.md)

These procedures are for the **future implementation**. This planning change adds documents and
gap comments only. Run commands from the formal repository root in a dedicated worktree.

| Guide | Use |
|---|---|
| [Working rules and gate protocol](01-working-rules.md) | Before every change; proof/API/metadata protection |
| [F0–F2: baseline, first slice, reuse](02-foundation-phases.md) | Establish evidence and prove the migration pattern |
| [F3–F6: domain migration and science](03-domain-phases.md) | Reorganize remaining work, retire safely, fill real gaps |
| [Review and recovery](04-review-and-recovery.md) | Change receipts, failure handling, rollback, external trials |

## Common phase discipline

Every phase needs an entry record, a bounded change, a verification record, a semantic review, and
an exit decision. The exit decision is one of: accepted; blocked with evidence; or deliberately
split into a smaller completed part and an explicit remaining obligation. A skipped gate is not a
pass. A deferred science gap is not an implemented feature.

Record work using the repository's agreed issue/review mechanism. These guides describe acceptance
procedures; they are not a second live task-status database. Do not check off proposed work merely
because this document was written.
