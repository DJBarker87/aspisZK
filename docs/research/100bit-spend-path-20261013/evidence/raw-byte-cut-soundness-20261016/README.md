# Unrestricted-byte commitment-cut soundness steps

These six focused Lean checks prove one shared collision-event bound
`12 Q² / 256³²` for the actual eleven byte-target parsers, then reuse the
existing Merkle recovery, recorded-witness, log-extension, and table-membership
proofs to establish:

- accepted openings recover from the literal log strictly before the commitment's first read;
- the entire recovered word (every path, including missing leaves) equals full-log recovery outside that same event, without a union over leaves;
- recovery depends only on the oracle table available at that cut, independent of consistent record order or duplication.

The oracle address type is unrestricted finite byte strings. No adversarial
input-length limit or padded-address fallback is assumed. The opening theorem
keeps actual opening-program acceptance and read containment as source
obligations. The stability theorem derives those facts from recorded recovery.
Concrete causal decoder round completion, accepted Rust execution to terminal
checks, efficient extraction, and the final 100-bit theorem remain open.

Each target exited 0 on the NUC with Lean 4.32.0, MemoryHigh=4G,
MemoryMax=6G, MemorySwapMax=0, and zero reported process swaps. The 27
`#print axioms` reports contain only `propext`, `Classical.choice`, and
`Quot.sound`. Existing raw receipts record the exact source hashes, import
pins, cache base revision, command, time, memory and axiom output. No broad
regression was run for these proof edits.

| Target | GNU wall time | Peak RSS (KiB) | Axiom reports |
|---|---:|---:|---:|
| `AllAddressCollision` | 0:01.42 | 1824136 | 5 |
| `AllAddressCollisionTrace` | 0:01.32 | 1820708 | 4 |
| `RawByteCollisionTargets` | 0:01.06 | 1825320 | 6 |
| `RawByteCutRecovery` | 0:01.01 | 1823496 | 5 |
| `RawByteCutStability` | 0:00.85 | 1816824 | 4 |
| `RawByteCutTable` | 0:00.91 | 1814892 | 3 |
