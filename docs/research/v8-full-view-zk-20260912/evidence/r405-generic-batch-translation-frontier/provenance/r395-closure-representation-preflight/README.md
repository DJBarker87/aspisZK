# R395 closure representation preflight

Read-only inventory of the retained R327 LLBC closure rows and the already saved R357 predicate-environment staging artifacts. `inventory.json` records the input SHA, declaration IDs, fields/generic-region counts, source spans, the Fun36 local/statement path, and opaque Fun47 target. `audit_r395.py` decodes Charon hash-cons references and regenerates the inventory from the saved inputs; it does not compile or modify the LLBC.

The LLBC rows describe TypeDecl 7 (`batch::closure`) as an empty struct and TypeDecl 15 (`Iterator::any::check::closure`) as a one-field struct whose field is TypeDecl 7. The saved R357 staging artifact spells the first type as `Unit` and places the original Rust predicate at `r110_norm.rs:62`. This report does not infer any concrete memory layout, zero-sized/singleton behavior, lifetime equivalence, optimization, or runtime dispatch. The explicit LLBC edge observed in Fun36 is to Fun47, whose body is opaque. Fun35 is separately inventoried as structured source body.

No build, translation, or Lean job was run for this task.
