# S4 format payload alignment (source-only)

`AspisR1S4FormatPayloadAlignmentV1.payload_partitions` proves byte framing for the two packed-choice payloads: kind 0 is the first 480 bytes of the selected 608-byte opening, and kind 1 is the following 128 bytes. It consumes the source-wire binding and the exact query/opening slice equations. It establishes no Merkle authentication or caller reachability.

The focused Lean 4.32 run exited 0. The named `#print axioms` output is exactly `[propext, Classical.choice, Quot.sound]`. Launch revision is recorded in `receipt/preflight.json`; wall/RSS/swap and object digest are in `receipt/receipt.json`. The generated `.olean` is intentionally not included.

Attempts v1-v5 were diagnostics only. v1-v3 exposed setup/namespace and simplification issues; v4 had redundant tactics (`No goals to be solved`); v5 isolated the `min 480 608` equality. The accepted v6 source is frozen here.
