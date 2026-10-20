# Actual loop0 whole-prefix proof (focused)

This packet records a focused Lean proof for the actual extracted
`weights.s2_grouped_inactive_pair_loop0`. The theorem preserves decoded
per-accumulator prefix meaning and canonicality across the actual 64-iteration
loop. Its explicit unresolved boundary is a per-index `decodeField` success
and semantic-value equation; it does not yet derive that premise from the
Rust bytes/parser caller.

The field group cast is pure `UScalar.cast`; its value transport uses
`U8.cast_Usize_val_eq`. The group table, complete operations, generated loop
body, and range semantics are pinned by source and selected object hashes in
`manifest.json`.

The accepted target was compiled on Lean 4.32 with `-j1 -M4400`, in a verified
1 GiB MemoryHigh / 2 GiB MemoryMax / zero-swap scope. The accepted object is
retained only in the native cache; this packet includes no compiled object or
other binary. Earlier focused diagnostics remain under `diagnostics/` and are
not counted as accepted results.
