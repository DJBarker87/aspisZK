# Public index Aeneas bridge: focused Lean evidence

This bundle preserves attempts a–d for `R1PublicIndexAeneas`. Attempts a, b, and c failed during proof plumbing; d compiled successfully from the hash-matched final source. The theorem states, unconditionally for every `Array U8 8#usize`, that Aeneas `core.num.U64.from_le_bytes` has the same natural value as the retained two-word `PublicIndexCodec.decode` applied to those eight bytes.

Attempt d: exit 0, 2.22 s, peak RSS 3,804,904 KiB, zero swap, one standard axiom report (`propext`, `Classical.choice`, `Quot.sound`), with `MemoryHigh=4G`, `MemoryMax=6G`, `MemorySwapMax=0`, and `TasksMax=128`. All four attempts retain exact source snapshots, receipts, sidecars, output logs, and time logs.

The object archive contains the target plus its custom codec imports. The Aeneas primitive source pin is included. The result concerns the existing Aeneas primitive and mathematical codec; it does not prove correspondence to the current Aspis public-index parser or its callers.
