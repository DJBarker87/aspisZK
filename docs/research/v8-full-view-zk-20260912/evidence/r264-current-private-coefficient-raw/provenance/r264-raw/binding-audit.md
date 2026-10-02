# R264 private coefficient raw binding audit

Declaration-text/binding comparison only; no compilation or source-semantics conclusion.

The raw adapter copies the three requested aliases and four function bodies exactly, preserving their docstrings and attributes. The selected bodies required zero replacements.

The generated `QM31` structure was compared with the pinned R156 `QM31` declaration and is not locally redeclared.

Every reachable generated helper body is compared against the R249 private adapter, the R259 Option/C-input adapter, or the pinned R156 field declaration. R249 comparisons allow only the recorded wrapper qualification and unsigned literal count adaptations:

- `core.num.U32.wrapping_add` → `Std.U32.wrapping_add`
- `core.num.U32.wrapping_sub` → `Std.U32.wrapping_sub`
- `core.num.U64.wrapping_add` → `Std.U64.wrapping_add`
- `core.num.U64.wrapping_sub` → `Std.U64.wrapping_sub`
- `Std.U32.wrapping_shr self 1#i32` → `Std.U32.wrapping_shr self 1#u32`
- `Std.U32.wrapping_shl i1 30#i32` → `Std.U32.wrapping_shl i1 30#u32`
- `Std.U64.wrapping_shr x 31#i32` → `Std.U64.wrapping_shr x 31#u32`

Reachable generated helper declarations checked: 24.

No unresolved declaration-body mismatches were found within the audited dependency closure.

The audit records input/output SHA-256 values in `binding-audit.json`; the reproducible generator and checksum file are in this directory. No build or Lean execution was run.
