# Reference Rust compilation gates

The absence of an in-file cfg attribute is not an absence of a compilation gate.
At base 92d3db0b2f these six modules are reached as follows:

| File under tools/r1-builder-reference | Declaring parent and gate |
| --- | --- |
| drop.rs | src/lib.rs:24–26: `#[cfg(kani)] mod trace_drop` |
| drop_iterator.rs | src/lib.rs:28–30: `#[cfg(kani)] mod trace_drop_iterator` |
| records.rs | crates/aspis-statement/src/pool_v1/pair_forest_copy_builder.rs:376–378: `#[cfg(kani)] mod records_proofs` |
| glue_tree.rs | records.rs:371–372: child of cfg(kani)-gated records_proofs |
| glue_append.rs | records.rs:374–375: child of cfg(kani)-gated records_proofs |
| records_reference.rs | pair_forest_copy_builder.rs:381–383: `#[cfg(any(kani, aeneas_ref))] mod records_reference` |

These files have no in-file cfg; they inherit the module declaration's gate.
The reference helper also participates in explicitly enabled `aeneas_ref`
extraction builds, so describing all six as exclusively cfg(kani) would be
incorrect. There is no cfg(test) gate on these six declarations. The normal
prover/program builds have neither kani nor aeneas_ref enabled. This is a
source configuration statement, not a new ELF reproducibility certificate.
No Rust source change is made for this confirmation.
