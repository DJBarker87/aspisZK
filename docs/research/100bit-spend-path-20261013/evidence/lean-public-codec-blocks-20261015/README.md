# Public codec blocks focused Lean evidence

This bundle preserves `R1PublicFieldBlockCodec` attempts a (failed proof-plumbing compile) and b (green), plus `R1PublicByteCursor` attempt a (green). The field-block module composes the exact M31 list codec with the fixed-width decoder to obtain generic field-block, digest, and frontier roundtrips and lengths. The byte cursor proves encoded-input and successful-read list identities.

Green metrics:

- `R1PublicFieldBlockCodec` b: exit 0, 1.50 s, peak RSS 3,314,024 KiB, zero swap, nine standard axiom reports.
- `R1PublicByteCursor` a: exit 0, 0.66 s, peak RSS 1,505,852 KiB, zero swap, two standard axiom reports.

Both targets used source revision `136b746805f3438507732622c9b4e50f36bf49f9`, with `MemoryHigh=4G`, `MemoryMax=6G`, `MemorySwapMax=0`, and `TasksMax=128`. Every attempt has its exact source snapshot, receipt, hash sidecars, output log, and time log. The object archive includes both targets and the two custom direct-import objects for the field-block module. `Mathlib.Data.List.OfFn` is pinned through the captured Lean environment.

These are mathematical codec results, not Rust source-refinement or caller-layout claims.
