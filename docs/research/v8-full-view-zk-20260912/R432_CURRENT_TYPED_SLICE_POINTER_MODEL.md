# R432: typed immutable slice-pointer model

R432 proves a typed immutable allocation/pointer fragment and derives its counted-fold load correspondence from stored cells. It replaces R193's arbitrary in-bounds load premise within this model. It does not prove the actual Rust constructor or fold, pointer/aliasing semantics, source input validity or a frame/lifetime bridge. It does not close privacy or soundness.

## Compilation and custody

Exact target: `AspisV8R19/R432PointerPrimitive.lean`. Source revision at the focused jobs: `cacf6c885a3beffc89fd6be7e8f3801cd8786d2e`. The promoted source is byte-for-byte successful attempt C, SHA256 `29e8517db5f986359fe70e9120bb2bc48601ddb1c9188e59729a44f17f47717f`.

| Attempt | Result | Wall time | GNU peak RSS | Swap |
| --- | --- | --- | --- | --- |
| A | exit 0, 8-lemma predecessor | 1.61 s | 2,545,852 KiB | 0 |
| B | exit 1, added bridge has wrong Result namespace | 1.88 s | 2,541,012 KiB | 0 |
| C | exit 0, corrected namespace, 12 reports | 1.90 s | 2,552,236 KiB | 0 |

A was not repeated unchanged. B added distance, slice-view and counted-fold bridge lemmas; its namespace errors and `sorryAx` in failed output are retained as rejected history. C corrects `Aeneas.Result` to `Aeneas.Std.Result`. C's 12 complete `#print axioms` reports match its receipt and contain only standard `propext`, `Classical.choice` and `Quot.sound`. No sorry or additional axiom appears in the successful output. The complete A/B/C logs, sources, commands, metrics and reports remain saved.

All jobs used pinned Lean 4.32.0, commit `8c9756b28d64dab099da31a4c09229a9e6a2ef35`, the cached workspace, `lake env lean -j1 -M4500`, and their own scopes with MemoryHigh=5 GiB, MemoryMax=7 GiB, MemorySwapMax=0, TasksMax=128. C's terminal cgroup peak is 321,474,560 bytes with zero swap and no OOM events. This cgroup value and GNU RSS are retained separately; the saved records do not explain their difference. Source before/after and six artifact-copy receipts agree. The independent custody verifier and lead checked the saved successful evidence without rerunning Lean.

## Precisely proved boundary

The model represents pointers with an address and optional allocation/byte-offset provenance. It represents an initialized typed cell list in one immutable allocation, with explicit non-null base, alignment4, signed-offset extent bound and no address wrap. Stride16 describes the proposed selected QM31 cell image; the generic payload parameter is not a claim that arbitrary Rust types have this layout.

Zero-offset addition preserves a pointer without requiring an allocation. Empty iterator construction therefore retains the dangling-empty case; the equal-address distance rule also returns zero without an allocation. These theorems do not make arbitrary invalid Rust references legal.

For a named modeled allocation present in the heap and a cell range bounded by its length, the proof establishes scaled pointer addition, start/end construction, empty equivalence, unsigned distance, reads, view length, byte bounds and exact list-view loads. One-past pointers can be used for arithmetic; list lookup prevents a one-past element read. The load theorem derives cell contents from allocation storage rather than accepting a free load oracle.

`countedFold_pointer_view` applies the already verified R193 theorem to these derived loads. It covers any FnMut result behavior represented by that model, including failure/divergence. An arbitrary unsupported-result fallback is explicit and is unreachable for every in-bounds modeled read. `None` remains an unsupported/invalid fragment diagnostic; neither it nor the fallback is asserted to be a Rust error or unwind semantics. The heap remains fixed by definition; that is not a source frame/aliasing proof.

R431 separately exposes the actual source constructor and fold, with exact metadata, raw-pointer creation, transmute/cast operations, branch, offset, storage and cleanup/unwind paths. R432 does not yet interpret or identify that native AST with this model. R430 likewise remains a constant-fragment proof with an explicit primitive boundary. No library contract, native pointer behavior or source safety premise has been silently assumed closed.

## First remaining proposition

Reflect and bind the exact actual R431 constructor86/fold70 into justified source operation semantics. Identify the R430 constant graph after capture ID renaming; connect shared slice input to initialized storage with legal empty/dangling cases; justify metadata, transmute and pointer primitives; prove the closure preserves slice storage and restores its captured power; and prove actual unchecked-add and check/drop/unwind behavior. Only then can these modeled load facts close the actual source fold correspondence. Vec::extend remains separate.

Whole freeze and inverse Domain behavior, full callback/oracle chronology, universal joint C1/H1/G compatibility including p0/p2 and adaptive/degenerate prefixes, a faithful whole published-view simulator and shared-oracle losses, coherent pre-beta quotient extraction and optimized-to-source acceptance remain open. All selected security parameters and genuine 999,790 / 999,532 CU results are preserved. No benchmark, unchanged regression, deployment, merge, transaction or wallet operation occurred.
