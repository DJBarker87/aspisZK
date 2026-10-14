# Reseed and opening decoder evidence

Source base: `6d0b82129fb619d927a04fa50c4da0bddfeeeb29`.

Sixteen final targets connect the row-26 reseed and rows 27–30 ordinary
opening decoders to the actual experiment. Prefix recovery also supplies the
known-cell/read facts before query row 31. The manifest records 23 attempts:
6 failed, 1 superseded success (a comment clarification), and 16 final successes.
Every attempt's exact source snapshot matches its receipt and hash sidecar.

The combined checkpoint passed once after dependencies in 1.38 s, with
3,531,264 KiB peak RSS, zero swap, and 24 axiom reports restricted to
`propext`, `Classical.choice` and `Quot.sound`. All jobs ran with
MemoryHigh=4G, MemoryMax=6G, MemorySwapMax=0, TasksMax=128 and Lean's
5000 MB threshold, reusing the pinned Linux workspace/cache and Lean 4.32.0.

The deterministic final-object archive SHA-256 is
`df733e2bc332e5c751ec986a314ebd2c2496b4d42ecf5178745a8366c9d6a7f2`.
`source-manifest.json` lists exact sources, objects, attempt classifications,
runner/environment snapshots and resource receipts. `ROOT-VALIDATION.json`
records root's audit of final sources, all attempts, resource/compiler logs,
archive members, runner/environment and fourteen unchanged runtime pins.
Root also inspected the theorem premises and proof connections.
`SHA256SUMS` seals every other file in this directory.

This is not a complete security or privacy certificate. Query-case completion,
correct global dispatch, the full generic/numerical instance and implementation
correspondence remain open. The fixed-prefix bounds in the sampler-law transfer
are explicit premises. See [the scope document](../../UNIFIED-RESEED-OPENING.md).
