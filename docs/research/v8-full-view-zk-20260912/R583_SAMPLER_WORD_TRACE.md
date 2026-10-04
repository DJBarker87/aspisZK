# R583: sampler word trace

R583 proves that the existing total-`H` source-shaped `QM31SamplerProgram` ordinary challenge view is the finite sequential-word tape view. It keeps the initial eager squeeze and reconstructs every later squeeze output/advance pair in order. Each draw consumes the next word; refills occur only when the previous eight-word block is exhausted; success, rejection exhaustion, stopping, returned result/error, and final state remain in the view. There are no extra calls and no trace erasure in this total-`H` model.

The final theorems are `challenge_view_tape` and `challenge_program_view_tape`. They identify the full `challengeRun` and `eval H (challengeProgram s)` views with the mapped result of `R578FiniteWordTape.runTape 32 (limbs 8 4 0) (R579FourBlockTape.blockTape (sourceBlocks H s))`.

## Verification

- Canonical source: `lean/AspisV8R19/R583SamplerWordTrace.lean`
- Original draft: `.r21-scratch/R583SamplerWordTrace.UNVERIFIED.lean`
- Canonical/draft SHA256: `41580eaf56b27761a5b046644e4b167df552b4f05af7e38265b489763d352252` (byte-identical)
- Source revision: `a11c00dcdf04c2fd3565ed2dd0e81a2ac2adb137`
- Canonical module-path target: `AspisV8R19/R583SamplerWordTrace.lean`
- Final focused run: `1791086629581085000`; exit 0; wall 1.59 s; Lean-child peak RSS 3,272,644 KiB; swap 0.
- Resources: `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, `TasksMax=128`; Lean `-j1 -M4500`.
- The final log preserves eleven complete `#print axioms` reports. Each uses only the standard foundational axioms `[propext, Classical.choice, Quot.sound]`, or a subset thereof; no `sorryAx` appears in the final result.

| Receipt | Result | Wall | Peak RSS | Saved boundary |
| --- | --- | ---: | ---: | --- |
| `1791086431262097000` | exit 1 | 1.35 s | 3,249,348 KiB | failed draft, including its complete saved axiom output |
| `1791086455925924000` | exit 0 | 1.45 s | 3,266,352 KiB | word reads and scan trace |
| `1791086591396666000` | exit 0 | 1.57 s | 3,272,584 KiB | recursive limbs trace |
| `1791086629581085000` | exit 0 | 1.59 s | 3,272,644 KiB | complete ordinary challenge view, canonical module path |

All four exact source snapshots, logs, receipts, the focused runner, direct R582 dependency source pin, publish-path JSON, and recursive SHA manifest are in `evidence/r583-sampler-word-trace/`. No Lean job was rerun for this promotion.

## Boundary

R583 proves the total-`H` existing source-shaped `QM31SamplerProgram` full ordinary challenge view equals a finite sequential-word tape, with exact reconstructed squeeze output/advance calls in order, including the initial eager squeeze. It preserves rejection/failure/stopping/result and state. It does not prove native R569 checked-hash-failure correspondence or a current whole-callback trace; independently uniform actual blocks; a shared-oracle law; privacy; or security.

The first remaining proposition is the independent source-program paired-reply-bank law, then actual shared-oracle losses.
