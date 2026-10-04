# R582: sequential tape execution

R582 connects the existing four-block abstract tape to the deterministic source-shaped total oracle `H`. It proves a strong cursor invariant for the generic sampler program: every `ask` is at the current cursor and every return carries the cursor after all consumed words. Under a matching tape/answer relation, `runTape` is exactly `some (eval answer program)`.

For the selected four-block sampler shape, `sourceBlocks H s` is mapped by `R579FourBlockTape.blockTape`; each of its 32 words agrees with `R580SourceWordStream.streamAnswer H s`. The final theorems preserve both ordinary challenge result/error and the advanced state:

- `source_challenge_result_tape` equates `some (challengeRun H s).2.1` with the mapped finite tape result.
- `source_challenge_state_tape` equates `some (challengeRun H s).2` with the finite tape result paired with `(globalCursor H s v.2.2).state`.

## Verification

- Canonical source: `lean/AspisV8R19/R582SequentialTapeExecution.lean`
- Original draft: `.r21-scratch/R582SequentialTapeExecution.UNVERIFIED.lean`
- Canonical/draft SHA256: `c1ad4066ce19d8783034660ce995c9c8225b4254f37fe10a9934397fa6e8f3eb` (byte-identical)
- Source revision: `a11c00dcdf04c2fd3565ed2dd0e81a2ac2adb137`
- Canonical module-path target: `AspisV8R19/R582SequentialTapeExecution.lean`
- Final focused run: `1791086366648542000`; exit 0; wall 1.30 s; Lean-child peak RSS 3,259,760 KiB; swap 0.
- Resources: `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, `TasksMax=128`; Lean `-j1 -M4500`.
- The final log has eight complete `#print axioms` reports. The four source/tape bridge theorems depend only on `[propext, Classical.choice, Quot.sound]`; `sequential_bind`, `scan_sequential`, and `limbs_sequential` have no axioms; `runTape_eval` depends on `[propext, Quot.sound]`.

The saved focused history is complete for this result:

| Receipt | Result | Wall | Peak RSS | Note |
| --- | --- | ---: | ---: | --- |
| `1791086219573553000` | exit 1 | 1.20 s | 3,242,928 KiB | failed draft; its full log, source snapshot, receipt, and axiom output are preserved |
| `1791086245242831000` | exit 0 | 1.24 s | 3,259,176 KiB | generic cursor/tape core |
| `1791086321284431000` | exit 0 | 1.32 s | 3,259,376 KiB | source-block coupling |
| `1791086366648542000` | exit 0 | 1.30 s | 3,259,760 KiB | final canonical-module-path result |

All logs, exact source snapshots, receipts, runner, direct `R580SourceWordStream` source pin, and recursive SHA manifest are in `evidence/r582-sequential-tape-execution/`. `PUBLISH_PATHS.json` gives the exact three paths for review. No Lean job was rerun for this promotion.

## Boundary

This is a strong sequential address-and-returned-cursor invariant, an abstract word-view `runTape_eval` result, and a deterministic source-shaped total-`H` four-block tape result/error plus advanced state equality. It does not prove actual source oracle-call trace equality, independently uniform actual blocks, native R569 checked-failure correspondence, privacy, or security.

The first remaining proposition is actual call chronology, followed by the independent paired-reply law and shared-oracle losses.
