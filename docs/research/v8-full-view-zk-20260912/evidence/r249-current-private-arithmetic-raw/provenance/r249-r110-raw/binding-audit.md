# R249 R110 raw adapter binding audit

Mechanical declaration-text extraction and pinned-name binding; no Lean/build execution.

The adapter preserves 16 generated leaf bodies and both generated globals, for 18 retained definitions, and defines the requested aliases `B := Std.U32`, `C := B × B`.

The only source-body substitutions are:

- `core.num.U32.wrapping_add` → `Std.U32.wrapping_add` (2 occurrence(s)).
- `core.num.U32.wrapping_sub` → `Std.U32.wrapping_sub` (1 occurrence(s)).
- `core.num.U64.wrapping_add` → `Std.U64.wrapping_add` (2 occurrence(s)).
- `core.num.U64.wrapping_sub` → `Std.U64.wrapping_sub` (1 occurrence(s)).
- `Std.U32.wrapping_shr self 1#i32` → `Std.U32.wrapping_shr self 1#u32` (1 occurrence(s)).
- `Std.U32.wrapping_shl i1 30#i32` → `Std.U32.wrapping_shl i1 30#u32` (1 occurrence(s)).
- `Std.U64.wrapping_shr x 31#i32` → `Std.U64.wrapping_shr x 31#u32` (1 occurrence(s)).

The generated `aspis_core.field.P`, `reduce_u64`, `M31.reduce_u64`, and `CM31.new` blocks were checked against pinned R156 declarations after whitespace normalization; all four match. The adapter declares no local copies, and `open AspisR156FullFreeze` binds those names to R156.

The transitive reducer chain reuses the existing R239 R156/R221 declaration audit for `M31.mul`, reducer, bounded product, raw add/sub, and P dependencies. This is text/binding evidence only; it makes no source-semantics or runtime claim.

The adapter adds `count_one`, `count_thirty`, and `count_thirty_one` ground `decide` lemmas for the generated signed literals and their pinned unsigned API counts. No build or Lean execution was run.

SHA-256 checksums are recorded in `binding-audit.SHA256SUMS`.
