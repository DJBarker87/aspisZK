# D422 compliance repairs — work in progress

Branch `codex/pv-fix-20261028`, base `1a3cd3de26c0129eaefd6913b34e03fde119bf1f`.
Host directory `/home/dombarker/project-offloads/codex-pv-fix-20261028/`.
Only IDs62000–62099, maximum15 Lean attempts; no native scopes or Kani.

41466 is VOID under ruling(t): admitted about127 seconds after its refusal.
The reverse import graph identifies eight affected modules in `affected-order.json`.
They will be recompiled unchanged at their recorded blobs, in dependency order.
A separate inspection-only wrapper prints the full restoring statement and axioms.

The failed61199 wrapper receives one added namespace-opening line for `endpoint`.
`replay-before-after.diff` compares the exact failed text with this minimal repair.
It changes no theorem text or proof; inherited multi-site qualifications are replaced
by this single-line repair. No privacy endpoint premise is removed or added.
