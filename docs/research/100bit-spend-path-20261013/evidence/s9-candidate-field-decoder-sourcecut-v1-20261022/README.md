# S9 candidate field + decoder source cut (v1)

This focused extraction follows the exact candidate `weights::field` reader into the actual `aspis_core::field::WideExact` decoder. It is source-translation evidence only: no Lean theorem, compilation, axiom audit, runtime correctness result, or production adoption is claimed.

`input/src/field.rs` and `input/src/field/wide_exact.rs` are byte-for-byte copies of the complete frozen production field module files. The candidate and frozen `weights.rs` files are preserved as source snapshots. Their exact 90-byte `field` function declaration/body is identical in both files and in the cut (`SHA-256 0be69c81…`). The only context adjustment is the shim import alias `crate::field::WideExact as E`; the copied field function declaration itself is unchanged. `check_sourcecut.py` verifies the snapshots, copies, and body identity.

The cut contains no replacement `unreachable!()` implementation for either the field reader or decoder. Charon followed the field reader into the real, transparent `WideExact::from_le_bytes` and `WideExact::from_limbs` bodies. Aeneas emitted source-backed Lean definitions for all three declarations. The exact extraction output and command/receipt/admission evidence are under `attempt1/`.

The generated LLBC leaves only these relevant children foreign: core slice range indexing, slice length, `u32::from_le_bytes`, and `Option::unwrap`. Their Rust 1.98 source paths and source-file pins are listed in `core-boundary-pins.json`; the note records source statements but does not prove them in Lean. These are the remaining library boundaries for a checked parser adapter. This packet does not substitute axioms for them or claim their formal behavior. The generated translation is therefore a concrete source-body bridge with explicit remaining Rust-core contracts, not a closed end-to-end parser proof.

## Run result

Both Charon and Aeneas exited successfully under fresh shared admission, each in a verified systemd scope capped at 2 GiB `MemoryHigh`, 4 GiB `MemoryMax`, and 0 swap. Charon emitted LLBC SHA `e8e00fd3…` with `has_errors=false`; Aeneas emitted the checked `Funs.lean` and `Types.lean` artifacts. The packet checker passes. No Lean compile was run.
