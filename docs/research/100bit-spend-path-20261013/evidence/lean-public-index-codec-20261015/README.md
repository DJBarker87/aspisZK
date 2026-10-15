# Public index codec focused Lean evidence

This bundle records focused target `R1PublicIndexCodec`: attempt a failed during proof elaboration; attempt b compiled successfully in 1.77 s at 3,319,112 KiB peak RSS with zero swap under MemoryHigh 4G, MemoryMax 6G, MemorySwapMax 0, TasksMax 128. Its three `#print axioms` reports use only `propext`, `Classical.choice`, and `Quot.sound`.

The module defines a mathematical index as `Fin (2^64)` and eight bytes as `Fin 8 → Byte`; it splits the byte sequence into two four-byte words, using the retained 32-bit little-endian codec for low and high halves. It proves the value equation and both codec round trips. The direct import source/object is pinned.

This is a model-level codec result and does not prove that a Rust parser, caller, or protocol uses this representation. Exact receipt, source, runner, object, and hash details are in `source-manifest.json`; the earlier failed attempt is retained.
