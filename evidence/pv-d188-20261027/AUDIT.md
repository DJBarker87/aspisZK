# D300 / D188 mutable-state fidelity audit

Audit base: `b3d109c8ffa47e452b57c5e4a7fe71cfb98e7146`, branch
`codex/pv-d188-20261027`, worktree `/Users/dominic/ZK/.worktrees/pv-d188`.
No implementation or proof source is modified. Target not yet established.

## Inventory checkpoint

The read-only scanner `tools/pv-d188-20261027/scan.py` starts with the requested
PV/ProverRw families, including private source cohorts stored under evidence,
then follows imports. `inventory.json` records each emission's SHA256 and every
embedded Rust source/function attribution. `import-edges.json` retains candidate
import edges. Shared module resolution uses the EJR rebuild record where present;
remaining ambiguous candidates are explicitly retained, not silently selected.
This is an overinclusive audit envelope, not a release dependency manifest.
Library imports without repository sources are listed separately.

At this checkpoint: 2,016 root files, 3,084 closure candidates, 401 emission or
source-annotated modules. `static-matches.json` records 1,170 overinclusive lexical
matches (including safe writebacks and names containing `fallback`);
`rust-mutable-sites.json` records source-side assignments and borrow sites.
A match alone is not a defect or a verdict. Per-function adjudication follows.

## Scope and evidence discipline

The P3 finding is newer than this branch's P2 document. The audit reads it with
`git show research:...`; it does not merge research or edit the shared ledger.
The authority is the common file's rulings (a)–(n), including correction (h').
No shared env-J source is written. Env-J 28100–28299 is reserved for small tests;
40 Lean attempts maximum, no Kani; native scopes sequential, 6G/8G/swap0/Tasks64.
