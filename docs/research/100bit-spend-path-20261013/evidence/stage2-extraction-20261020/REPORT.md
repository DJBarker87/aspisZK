# Stage-2 extraction inventory (2026-10-20)

Stage 1 only: inventory and frozen-source continuity audit. No verifier source
change, new extraction, new Lean theorem, runtime regression or SBF rebuild.
The adopted source already has retained extraction blockers. Per the assignment,
stop before any source refactor; stages 2 and 3 require a lead decision.

The base's older R14 statement predates existing partial stage-2 packets. Their
scope and the exact failed attempts will be indexed here without relabelling
historical receipts as new runs.

## Inventory and pins

Frozen source: `9a71031d3a95f838ac6d75bd5c58eeafeb62a9e1`; publication base:
`e90cf2f80`. All inventoried Rust files and explicit backend-frontier files
are byte-identical to the frozen Git blobs; see `pins/source-hashes.json`.
The adopted verifier artifact pin is
`8cf8d84ed0fe340a190b4f40a9f953f0e0523370299ba3ec8bbed9d65b88ace3`
(1,405,680 bytes), as recorded by the adoption packet; no ELF was rebuilt or
independently rehashed here.

`pins/cone.json` inventories **76 named declarations**: 36 functions,
11 types/aliases, 29 globals; **16 source closures**. Of the named declarations,
66 are shared by the adopted stage-1 and authenticated stage-2 paths and 10
are stage-2-only. Ten closures are shared and six are stage-2-only. These are
source-cut counts, not a full compiler-expanded cone count. Standard library,
field arithmetic, Weights/pairing, allocation, digest backend and SDK/account
frontiers are explicitly enumerated and whole-file pinned; their recursively
expanded declarations/monomorphizations are not counted. No LLBC completeness
or successful extraction of that full cone is claimed.

The accepted older tx1 kit has six exact fragment matches: `mark`, `View`,
`Prepared`, `Accumulator`, `Variant::folds`, `Variant::final_len`. The 66
shared declarations must not be reported as 66 already accepted Lean owners.
The old integrated declaration report is at af828dec, before this freeze;
R13/R12 re-pins and source/model joins remain necessary.

## Reused extraction receipts (not new runs)

All six Charon/Aeneas receipts are copied unmodified under `receipts/`, together
with available commands, timing and error excerpts. The manifest records their
original locations, SHA256, tool hashes and original caps. All swaps are zero;
no attempt below was killed by memory pressure. `#print axioms`: inapplicable
for failed translations; no new theorem in this packet.

| Exact retained cut | Charon exit / wall s / peak KiB | Aeneas exit / wall s / peak KiB | Aeneas SHA prefix |
|---|---|---|---|
| finish_relation, original pinned static | 0 / 0.403 / 212608 | 2 / 0.603 / 94864 | 4632746d |
| corrected-opacity adopted caller v2 | 0 / 0.403 / 204688 | 2 / 0.602 / 99616 | 22232f96 |
| corrected-layout adopted resume v2 | 0 / 0.403 / 216572 | 2 / 1.605 / 246400 | 22232f96 |

The required pinned binary is `4632746d…`; the other two rows are historical
diagnostic-tool attempts, **not** executions of that required binary. The
finish failure alone reproduces the obstruction with exactly the required
Charon/driver/Aeneas pins and High6G/Max8G/Swap0 caps. The other two original
scopes used High512MiB/Max2GiB/Swap0, as their checked receipts state. Their
legacy human-readable reservation notes are stale and are not used here.

`pins/predecessor-continuity.json` checks exact current/frozen root bytes
against retained fragment hashes and original Git revisions. Finish and resume
also match the retained assembled input files. Caller v2 retains only its
input pins in this repository; its fragment hashes and original Git source
are checked, and that weaker retained-input availability is explicitly marked.

## Stop point and next decision

The original pinned tool fails `finish_relation` shared-borrow loop replay
with `Not_found` in `InterpReduceCollapse`. Corrected diagnostic cuts additionally
show `resume`'s escaping mutable region and `tx2_common`'s bottom in the whole
Accumulator borrowed after `pending.finish(&mut a.weights)`.

A concrete existing finish proposal is indexed in the design note: scalar
round helper plus slice-based indexed dot helper. It extracts as a candidate,
but it is not adopted and its source/effect equivalence and CU gates are open.
There is **no established sufficient minimal refactor for the whole cone**.
A source refactor is not logically proved unavoidable: new verified tool
lowering could preserve Rust. Under the required pinned pipeline, however,
unchanged whole-cone extraction is blocked. The lead must choose an authorized
source change or further tool/refinement work before stages 2/3 proceed.
No proposal was applied or tested here, and no new Lean file was added.

Per the assignment's stop-on-refactor condition and AGENTS rule 5, unchanged
failed jobs were not rerun. The sole completed stage is this inventory.
Codec 1,233 / ordered trace / checkpoint gates were not rerun because covered
Rust/artifacts did not change. The freeze and all deployed bytes remain intact.
