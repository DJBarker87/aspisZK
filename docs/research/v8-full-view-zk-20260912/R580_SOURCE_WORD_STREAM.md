# R580: deterministic source word stream and sampler output

The focused canonical target [R580SourceWordStream.lean](lean/AspisV8R19/R580SourceWordStream.lean) compiled on the pinned Lean 4.32 cached workspace. Final receipt: `1791085916138346000`; source revision `7021f3ad2d1bd4507570173f5a9c15a05d539990`; source SHA256 `297538faee8ac73ad4fe367e36ebf31e3938599dfa2eb371f2c82cb7d135e029`. Exit 0, wall time 1.86 seconds, peak Lean-child RSS 3,279,476 KiB, swap 0. Cgroup limits: MemoryHigh 5G, MemoryMax 7G, MemorySwapMax 0, TasksMax 128; Lean flags `-j1 -M4500`.

## Precise proved boundary

For every total duplex answer function H and initial state, the existing source-shaped `QM31SamplerProgram` read execution returns the next source-format little-endian word and the exact corresponding cursor. After consuming a positive multiple of eight words, the cursor remains at index eight in the consumed block; refill happens on the next read. The initial squeeze is preserved even for a zero draw budget.

The source masked 31-bit word equals the decoded rejection alphabet entry. For every draw budget and cursor, bounded rejection returns exactly the sequential word-program result and advanced cursor, including exhaustion. For every limb count, the source execution with eight draws per limb preserves the sequential program's accepted list or failure and final cursor. `challenge_stream` specializes this to the existing ordinary four-limb challenge model and preserves its final transcript state. This does not multiply marginal limb probabilities or assume fresh oracle answers.

Thirteen complete `#print axioms` reports are saved. Two evaluator results use no axioms; remaining reports use only subsets of `propext`, `Classical.choice`, and `Quot.sound`. No admitted theorem or new execution/probability premise is introduced. The final successful source is byte-identical to the canonical file. Direct dependency source copies and checksums are saved.

## Limits and first remaining proposition

This milestone concerns the deterministic total-H source-shaped model's result and state. It does not prove full oracle-call trace equality, native hash failure/divergence correspondence for the new R569 checked sampler, independence of actual shared-oracle blocks, or an end-to-end simulator/security theorem. Earlier native correspondence and the ongoing checked-sampler bridge must be composed explicitly before claiming actual current execution.

The first remaining probability proposition is to couple the actual source oracle chronology (including squeeze output and advance calls, retries, memoization and stopping) to the finite block/word tape, with explicitly justified freshness conditions and collision losses. R579 supplies the independent four-block projection law; it does not justify those conditions for the actual shared oracle. Universal joint C1/H1/G compatibility, full-view simulation, original-quotient extraction and complete soundness losses remain open.

## Evidence

[Evidence directory](evidence/r580-source-word-stream/) contains all five focused attempts, complete logs/receipts/source snapshots, final complete axiom output, the exact runner and direct source imports. Failed memory-guard axiom reports are not proof results. [Memory replacement](evidence/r580-source-word-stream/MEMORY_REPLACEMENT.md) records both failures and the successful symbolic-budget replacement. No verifier, security parameter, authentication check or benchmark was changed. The preserved genuine verifier measurements remain 999,790 / 999,532 CU; no CU benchmark or unchanged regression suite was rerun.
