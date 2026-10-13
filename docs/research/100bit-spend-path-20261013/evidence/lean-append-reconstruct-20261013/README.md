# Generic append reconstruction bridge

Source snapshot at start of work: `3a73ee4bb67558ffbc608abfea81d74b4d2fa2a4`.
The source change in `IncrementalMerkleV1.lean` is import-only: it replaces
`Mathlib` with `Mathlib.Tactic` and imports `Mathlib.Data.List.GetD` for the
five `List.getD_*` declarations used by the unchanged theorem bodies. The
`FormatV1.lean` change replaces only `Mathlib` with `Mathlib.Tactic`.

## Focused NUC checks

All checks used the pinned NUC workspace's `compile-one.sh`, with
`MemoryHigh=4G`, `MemoryMax=6G`, `MemorySwapMax=0`, `TasksMax=128`, and Lean
threshold 5,000 MiB. The runner's reservation check passed before each
invocation.

| Target / attempt | Result | Wall time | Peak RSS | Source SHA-256 |
|---|---:|---:|---:|---|
| `AspisFormal/Pool/FormatV1` a | pass | 1.72 s | 3,332,984 KiB | `f050cff00067efd5e880e79d0af9ae528ca349e1383f3c49272f3bdce2b6568f` |
| `AspisFormal/Pool/IncrementalMerkleV1` a | fail: missing `List.getD_append`, `List.getD_append_right`, `List.getD_replicate` imports | 2.77 s | 3,346,712 KiB | `bdc1d72af69b3762862280dd453249d05fe0b7e91d46fcd1a7c74c07124e91ba` |
| `AspisFormal/Pool/IncrementalMerkleV1` b | pass | 2.89 s | 3,373,948 KiB | `935baa3ba1c20a001f0d2c34b6a50189bdedf701dd42635b499e943692371e7a` |
| `R1AppendReconstruct` a | pass | 1.45 s | 3,310,804 KiB | `11d97e3489ccad2aeaa73c9c8c7226c4aaed61e9689ecefc1e93b7f3770c7e5d` |

Every run used zero swap. The corresponding receipts, Lean output, timings,
and source hashes are retained alongside this note. The failed incremental
source snapshot is `AspisFormal_Pool_IncrementalMerkleV1-a.source.lean`; the
pre-change source snapshots are `FormatV1-before.lean` and
`IncrementalMerkleV1-before.lean`.

The new theorem `AspisPool.IncrementalMerkleV1.append_reconstruct_afterstate`
uses the exact `appendCarry` case split. Its `#print axioms` output is
`[propext, Classical.choice, Quot.sound]`, with no `sorryAx`. This is a focused
theorem result, pending root inspection; it makes no source-refinement or
release-gate claim.

## Indexed reconstruction chain

The focused target `R1ReconstructChain` compiles
`lean/ReconstructChain.lean`, SHA-256
`6f2272c50c98a1403848e3dcae7d97b503c2a4119fae1e5bc9ed5800dd5259aa`. Attempt
a failed during the head-case rewrite; its exact source is
`R1ReconstructChain-a.source.lean`. Attempt b passed in 1.52 seconds, at
3,321,160 KiB peak RSS and zero swap, under the same 4G/6G/0 scope and
5,000 MiB Lean threshold. Its axiom audit for
`AspisPool.IncrementalMerkleV1.reconstruct_ofFn_chain` is
`[propext, Quot.sound]`, with no `sorryAx`. Both attempts have their runner
receipts, outputs, timing logs, and source hashes retained here. The theorem
is a structural sequence-to-`reconstructFrom` fact only; it does not instantiate
the parent operation or frozen empty-root table.
