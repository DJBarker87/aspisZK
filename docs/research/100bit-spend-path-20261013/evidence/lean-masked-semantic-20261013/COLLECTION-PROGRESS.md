# Interim masked semantic capture (superseded)

This file is the earlier partial capture and is retained as history. The final
22-attempt evidence index is in [`README.md`](README.md) and
[`manifest.json`](manifest.json).

This is an interim inventory, not a gate-closure statement. Captured focused
Lean attempts use source base revision `3c17bdf902eac67d12796ef029007305b358821e`,
pinned workspace `/home/dombarker/project-offloads/aspis-r1-concrete-decoder-20261013`,
`MemoryHigh=4G`, `MemoryMax=6G`, `MemorySwapMax=0`, `TasksMax=128`, and Lean
threshold 5000 MB. Every listed receipt records its source hash, wall time,
peak RSS, swap, and exit status. Passing targets' `#print axioms` outputs are
retained in attempt logs; the successful runs reported only standard Lean
axioms `[propext, Classical.choice, Quot.sound]` (some declarations use a
subset). Failed `CircleSampler-a` and `SemD2-a` logs include `sorryAx` only
after unknown-constant diagnostics; failed `BytePass-a/b` had placeholder
proofs and are retained as failures.

| Target / attempt | Source SHA-256 | Result | Wall | Peak RSS | Swap | Cap |
|---|---|---:|---:|---:|---:|---|
| `R0P/MaskValue` a | `0f2747b346e2c8880e067b4877f94ee26fd8610c0555384262013a16780edd4a` | pass | 0:03.17 | 3,569,664 KiB | 0 | `4G/6G/0` |
| `R0P/CircleSampler` a | `00c6f8cf0999b7d97591aa500bd6d671345963d543a02a0125bfd1eeecbea100` | fail | 0:09.01 | 3,558,100 KiB | 0 | `4G/6G/0` |
| `R0P/CircleSampler` b | `00c6f8cf0999b7d97591aa500bd6d671345963d543a02a0125bfd1eeecbea100` | pass | 0:09.11 | 3,579,352 KiB | 0 | `4G/6G/0` |
| `R0P/SemD2` a | `2b68437dfd6ba62cd023013a5b514987255550124c0eca4abb03a26a560397c0` | fail | 0:02.48 | 3,569,276 KiB | 0 | `4G/6G/0` |
| `R0P/SemD2` b | `2b68437dfd6ba62cd023013a5b514987255550124c0eca4abb03a26a560397c0` | pass | 0:02.57 | 3,587,472 KiB | 0 | `4G/6G/0` |
| `R0P/SemD3Glue` a | `60830349937666ec050499c10bdb51e5c17811a949edd494f9205f0ee45ad852` | fail | 0:00.47 | 1,083,288 KiB | 0 | `4G/6G/0` |
| `R0P/SemD3Glue` b | `60830349937666ec050499c10bdb51e5c17811a949edd494f9205f0ee45ad852` | fail | 0:00.48 | 1,083,008 KiB | 0 | `4G/6G/0` |
| `R0P/SemD3Glue` c | `60830349937666ec050499c10bdb51e5c17811a949edd494f9205f0ee45ad852` | fail | 0:28.64 | 3,648,072 KiB | 0 | `4G/6G/0` |
| `R0P/SemDecision` a | `cf8c98e1bf6d5da3a2e725efd3790c4efc7e75fc32b0c650c310d875bf1f8971` | pass | 0:01.73 | 3,552,624 KiB | 0 | `4G/6G/0` |
| `R0P/SemPad` a | `b5cd6f82b930644a81bbeabdfc4003425e52ddf5eefdc0c9485698d9e82de164` | pass | 0:02.15 | 3,575,516 KiB | 0 | `4G/6G/0` |
| `R0P/SemView` a | `a8e8fab6e0efaa76bf64f1197edb5ab51327f8906aecdb668c55885e94837fbd` | pass | 0:01.86 | 3,561,040 KiB | 0 | `4G/6G/0` |
| `R1SamplerBytePass` a | `e135c136bb9231ed0ab2d4871100715053cb37cd3d8f91b0975a3c9a3724065c` | fail | 0:01.63 | 3,783,052 KiB | 0 | `4G/6G/0` |
| `R1SamplerBytePass` b | `e826b2061660e45532d37f67fd153859eefc220e9dc8f9bc9419ac10613dea80` | fail | 0:01.73 | 3,784,892 KiB | 0 | `4G/6G/0` |
| `R1SamplerBytePass` c | `31a64db268f34228105a160ce96d525060d31b22c19722ab7581a8d533feadbc` | pass | 0:01.79 | 3,800,684 KiB | 0 | `4G/6G/0` |

Observed first diagnostics: `R1SamplerBytePass-a` lacks `four` and `numeral`;
`R1SamplerBytePass-b` has an array/list equality mismatch; `R0P/CircleSampler-a`
and `R0P/SemD2-a` reference the removed old tower namespace/prime fact;
`R0P/SemD3Glue-a` cannot find `R0C.CircleRows`, and b cannot find
`AspisV8R19.SamplerCirclePolicy`; c reaches stale
`deployedPrimeFact` references in `SemD3Glue`, after which Lean emits failed
declarations with `sorryAx` and self-named axioms (including
`sourceDataWithFallback` and `decision_semantic_head`). The later
`CircleSampler-b` and `SemD2-b` runs pass after exact qualified-name updates.
`SemD3Glue` a/b/c remain failed attempts, with a/b stopping at missing objects.
Passing `MaskValue-a`, `CircleSampler-b`, `SemD2-b`, `SemView-a`,
`SemDecision-a`, `SemPad-a`, and `R1SamplerBytePass-c` reported only standard
Lean axioms; failed attempts' self-named axioms and `sorryAx` are preserved in
their logs and are not conflated with those passes. Exact attempt bytes, source
snapshots, and passing objects are under `attempts/`, `sources/`, and
`objects/`. Newer targets are still being collected; this note and the capture
metadata remain provisional.
